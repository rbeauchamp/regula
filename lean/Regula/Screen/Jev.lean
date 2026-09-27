import Lean.Data.Json
import RegulaPolicy.Screening

/-! # System One endpoint client

Operational client for TypeSafe's System One endpoint (`POST /v1/systemone`), used only by
the opt-in `intentScreen` executable.

Trusted and unverified here: the `curl` and `shasum` processes, the network, the service and
its answers, and the filesystem cache. The API key is read from `TYPESAFE_API_KEY` and handed
to `curl` on standard input as a configuration line, so it appears in no argument list, file,
log or cache entry. Every request is cached under the SHA-256 of its exact compressed JSON
(model, state and questions); a cache entry is reused only when its stored request equals the
current one, and a cached run needs no key and makes no network call. Answers are admitted
through the pure `RegulaPolicy.Screening.probability?`; a malformed answer, an answer from a
model other than the pinned one, or a failed call makes the whole request unavailable, never
a guessed probability. -/

namespace Regula.Screen.Jev

open Lean System
open RegulaPolicy.Screening

/-- The System One endpoint URL every request is POSTed to. -/
def endpoint : String := "https://api.typesafe.ai/v1/systemone"

/-- One typed answer. `support` is the Noul probability; a Choice answer carries every
option's probability and its distribution confidence. -/
inductive Answer where
  /-- A true/false (Noul) answer: the probability that the question's `true` criterion holds. -/
  | noul (probability : Probability)
  /-- A multiple-choice answer: each option's probability, and the distribution's
  confidence. -/
  | choice (probabilities : List (String × Probability)) (confidence : Probability)

/-- One completed request: the versioned model that answered, answers by question id, the
request digest and the input tokens the service billed (`none` when it reported none).
`cached` records whether this run reused an earlier response; `attempts` is the number of
POSTs this run sent for it, retries included (0 when cached). -/
structure Response where
  /-- The model version the service answered with; a response is admitted only when it is
  the pinned model. -/
  model : String
  /-- The admitted answer to each question, keyed by question id. -/
  answers : List (String × Answer)
  /-- The SHA-256 digest of the request, which names its cache entry. -/
  digest : String
  /-- The input tokens the service billed, or `none` when it reported none. -/
  inputTokens : Option Nat
  /-- Whether this run reused a cached response instead of sending the request. -/
  cached : Bool
  /-- POSTs this run sent for the request, retries included; 0 when cached. -/
  attempts : Nat

/-- The request body: model, state and questions, keys in canonical order. -/
def request (model : PinnedModel) (state : Json) (questions : List (String × Json)) : Json :=
  Json.mkObj [("model", .str model.val), ("state", state), ("questions", Json.mkObj questions)]

private def run (cmd : String) (args : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd, args }

/-- SHA-256 of a file, by the trusted external `shasum`. -/
def sha256File (path : FilePath) : IO String := do
  let out ← run "shasum" #["-a", "256", path.toString]
  unless out.exitCode == 0 do throw <| IO.userError s!"shasum failed: {out.stderr}"
  let some digest := (out.stdout.splitOn " ").head?
    | throw <| IO.userError "shasum printed no digest"
  unless digest.length == 64 && digest.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f') do
    throw <| IO.userError "shasum printed a malformed digest"
  return digest

private def probabilityOf (value : Json) : Except String Probability := do
  let .num n := value | throw "probability is not a number"
  match probability? n.mantissa n.exponent with
  | some p => pure p
  | none => throw s!"probability outside [0, 1]: {value.compress}"

/-- The option names a Choice question defines (its criteria keys), sorted. -/
def choiceOptions (question : Json) : List String :=
  match question.getObjVal? "criteria" with
  | .ok (.obj fields) => (fields.toList.map (·.1)).mergeSort (· ≤ ·)
  | _ => []

/-- Admit one answer of the question that was asked. A Choice answer must give a probability
for exactly the options asked, summing to at most one exactly. -/
def parseAnswer (question : Json) (value : Json) : Except String Answer := do
  let asked ← question.getObjValAs? String "type"
  let type ← value.getObjValAs? String "type"
  unless type == asked do throw s!"answer type {type} differs from question type {asked}"
  match type with
  | "noul" => return .noul (← probabilityOf (← value.getObjVal? "noul"))
  | "choice" =>
    let .obj probabilities ← value.getObjVal? "probabilities" | throw "choice probabilities are not an object"
    let pairs ← probabilities.toList.mapM fun (option, p) => do pure (option, ← probabilityOf p)
    unless (pairs.map (·.1)).mergeSort (· ≤ ·) == choiceOptions question do
      throw "choice answer options differ from the options asked"
    let total := pairs.foldl (fun acc (_, p) => acc.add p.val) (⟨0, 0⟩ : Decimal)
    unless total ≤ Decimal.one do throw "choice probabilities sum to more than one"
    return .choice pairs (← probabilityOf (← value.getObjVal? "confidence"))
  | other => throw s!"unsupported answer type {other}"

/-- Admit a response body for the exact questions asked of the pinned model. -/
def parseResponse (model : PinnedModel) (questions : List (String × Json)) (body : Json) :
    Except String (String × List (String × Answer) × Option Nat) := do
  let answered ← body.getObjValAs? String "model"
  unless answered == model.val do
    throw s!"the service answered with model {answered}, not the pinned {model.val}"
  let answers ← body.getObjVal? "answers"
  let parsed ← questions.mapM fun (id, question) => do
    pure (id, ← parseAnswer question (← answers.getObjVal? id))
  let tokens := ((body.getObjVal? "usage").bind (·.getObjValAs? Nat "input_tokens")).toOption
  return (answered, parsed, tokens)

/-- A key the curl configuration line can carry verbatim: printable ASCII without `"` or `\`. -/
def keyAdmissible (key : String) : Bool :=
  !key.isEmpty && key.all fun c => ' ' < c && c.toNat < 127 && c != '"' && c != '\\'

/-- POST the body with `curl`, the key on standard input. Returns the HTTP status and body. -/
private def post (key : String) (bodyFile responseFile : FilePath) : IO (Nat × String) := do
  let child ← IO.Process.spawn {
    cmd := "curl"
    args := #["--silent", "--show-error", "--max-time", "120", "--config", "-",
      "--request", "POST", "--header", "Content-Type: application/json",
      "--data-binary", s!"@{bodyFile}", "--output", responseFile.toString,
      "--write-out", "%{http_code}", endpoint]
    stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.putStr s!"header = \"Authorization: Bearer {key}\"\n"
  stdin.flush
  let stdout ← child.stdout.readToEnd
  let stderr ← child.stderr.readToEnd
  let exit ← child.wait
  unless exit == 0 do throw <| IO.userError s!"curl failed ({exit}): {stderr}"
  let some status := stdout.trimAscii.toString.toNat? | throw <| IO.userError "curl printed no HTTP status"
  return (status, ← IO.FS.readFile responseFile)

/-- The most POST attempts one request makes: the first and up to four retries after HTTP 429,
529 or 5xx. -/
def maxAttempts : Nat := 5

/-- Answer one request whose exact compressed body is in the private file `pending` and has
`digest`, sending at most `limit` POSTs. A new cache entry is written to a unique file and
renamed into place, so a reader never sees a partial entry and concurrent runs cannot mix
requests and responses. -/
private def askAt (cache : FilePath) (model : PinnedModel) (questions : List (String × Json))
    (body : String) (pending responseFile : FilePath) (digest : String) (limit : Nat) : IO Response := do
  let entry := cache / s!"{digest}.json"
  if ← entry.pathExists then
    let stored ← IO.ofExcept <| Json.parse (← IO.FS.readFile entry)
    let storedRequest ← IO.ofExcept <| stored.getObjVal? "request"
    unless storedRequest.compress == body do
      throw <| IO.userError s!"cache entry {entry} does not hold this request"
    let (answered, answers, tokens) ← IO.ofExcept <|
      parseResponse model questions (← IO.ofExcept <| stored.getObjVal? "response")
    return { model := answered, answers, digest, inputTokens := tokens, cached := true, attempts := 0 }
  let some key ← IO.getEnv "TYPESAFE_API_KEY"
    | throw <| IO.userError "intent screening is opt-in: set TYPESAFE_API_KEY (no cached response for this request)"
  unless keyAdmissible key do
    throw <| IO.userError "TYPESAFE_API_KEY is empty or contains characters outside printable ASCII, a quote or a backslash"
  if limit == 0 then throw <| IO.userError "no POST attempt is allowed for this request"
  let mut attempt := 0
  repeat
    attempt := attempt + 1
    let (status, text) ← try post key pending responseFile
      catch e => throw <| IO.userError s!"{e} (after {attempt} POST attempt(s) for this request)"
    if status == 200 then
      let json ← IO.ofExcept <| Json.parse text
      let (answered, answers, tokens) ← IO.ofExcept <| parseResponse model questions json
      let staged := cache / s!"{digest}.{← IO.monoNanosNow}.partial"
      IO.FS.writeFile staged (Json.mkObj [("request", ← IO.ofExcept <| Json.parse body),
        ("response", json)]).pretty
      IO.FS.rename staged entry
      return { model := answered, answers, digest, inputTokens := tokens, cached := false, attempts := attempt }
    if (status == 429 || status == 529 || status ≥ 500) && attempt < limit then
      IO.sleep (UInt32.ofNat (1000 * 2 ^ (attempt - 1)))
    else
      throw <| IO.userError
        s!"TypeSafe request failed with HTTP {status} after {attempt} POST attempt(s): {text.take 500}"
  throw <| IO.userError "unreachable retry exit"

/-- Ask one request, reusing a cached response for an identical request, sending at most
`limit` POSTs (never more than `maxAttempts`). The request and response travel through unique
temporary files, removed afterwards whatever the outcome. -/
def ask (cache : FilePath) (model : PinnedModel) (state : Json) (questions : List (String × Json))
    (limit : Nat := maxAttempts) : IO Response := do
  IO.FS.createDirAll cache
  let body := (request model state questions).compress
  let (requestHandle, pending) ← IO.FS.createTempFile
  let (_, responseFile) ← IO.FS.createTempFile
  try
    requestHandle.putStr body
    requestHandle.flush
    askAt cache model questions body pending responseFile (← sha256File pending) (min limit maxAttempts)
  finally
    for f in [pending, responseFile] do
      if ← f.pathExists then IO.FS.removeFile f

end Regula.Screen.Jev
