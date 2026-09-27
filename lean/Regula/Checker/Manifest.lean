import Regula.Checker.PolicyCodec
import Regula.Checker.Common
import Regula.Checker.Policy
import RegulaPolicy.Guards
import RegulaCore.Assembly
import Lean.Elab.Command

/-! # Strict surface-manifest parsing

Strict surface-manifest parsing. Unknowns and omissions fail closed. The pure `parse` is
the executed parser. `parse_sound` proves what every accepted manifest satisfies;
`parse_input` proves it has the allowed keys and schema version and that each entry is, in
order, the decoding of its JSON element, including the `execution` field;
`parse_emptyExclusions` proves empty exclusion arrays are accepted whenever the surfaces are.
`parse` is the text parser followed by `parseValue` (`parse_ok`), and `parseValue_ok` proves
that `parseValue` accepts exactly the values encoding a valid manifest, returning that manifest.
`parseValue_toJson` is the round trip at the `Json` value boundary; `structural_roundtrip`
applies it to the structural copy. The text boundary (`Json.compress`, which is `partial`,
and `PolicyCodec.parse`, which runs core `partial` parsers) stays trusted.
The refusal-class theorems prove the message of malformed JSON, an unknown top-level or surface
key, a non-2 schema version, empty surfaces and a bad surface `execution`, each given an
otherwise accepted prefix. `load` adds only file IO. -/

namespace Regula.Checker.Manifest

open Lean System
open Regula.Checker.Policy RegulaPolicy.Guards

/-- The default manifest location: `foundation_manifest.json` at the project root `repo`. -/
def defaultPath (repo : FilePath) : FilePath :=
  repo / "foundation_manifest.json"

/-- Every library the manifest names: the claimed surfaces' libraries, then the excluded ones. -/
def libraries (manifest : Manifest) : Array String :=
  manifest.surfaces.map (·.library) ++ manifest.excludedLibraries.map (·.library)

/-- Every executable the manifest names: the claimed surfaces' executables, then the excluded
ones. -/
def executables (manifest : Manifest) : Array String :=
  manifest.surfaces.flatMap (·.executables)
    ++ manifest.excludedExecutables.map (·.executable)

/-- A well-formed target name: nonempty, no surrounding or inner whitespace, no comma. -/
def TargetName (value : String) : Prop :=
  value ≠ "" ∧ value.trimAscii.toString = value ∧ ∀ c ∈ value.toList, ¬c.isWhitespace ∧ c ≠ ','

private def objectWithKeys (value : Json) (allowed : Array String) (location : String) :
    Except String Unit := do
  let object ← value.getObj?
  let unknown := object.keysArray.filter (!allowed.contains ·)
  unless unknown.isEmpty do
    throw s!"manifest-schema: {location} has unknown key(s): {repr unknown.toList}"

/-- The JSON object's keys are all allowed. -/
def KeysAllowed (value : Json) (allowed : Array String) : Prop :=
  ∃ object, value.getObj? = .ok object ∧ ∀ key ∈ object.keysArray, key ∈ allowed

theorem objectWithKeys_sound {value : Json} {allowed : Array String} {location : String} {u : Unit}
    (h : objectWithKeys value allowed location = .ok u) : KeysAllowed value allowed := by
  unfold objectWithKeys at h
  simp only [bind_eq_ok] at h
  obtain ⟨object, hobj, h⟩ := h
  refine ⟨object, hobj, fun key hkey => ?_⟩
  split at h
  · rename_i hempty
    have hnil := Array.isEmpty_iff.mp hempty
    by_cases hk : key ∈ allowed
    · exact hk
    · have hmem : key ∈ object.keysArray.filter (fun x => !allowed.contains x) := by
        rw [Array.mem_filter]
        exact ⟨hkey, by simpa [Array.contains_iff_mem] using hk⟩
      rw [hnil] at hmem
      simp at hmem
  · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem objectWithKeys_complete {value : Json} {allowed : Array String} {location : String}
    (h : KeysAllowed value allowed) : objectWithKeys value allowed location = .ok () := by
  obtain ⟨object, hobj, hkeys⟩ := h
  simpa [objectWithKeys, hobj, bind, Except.bind, pure, Except.pure] using hkeys

private def stringField (value : Json) (key location : String) : Except String String := do
  match ← value.getObjVal? key with
  | .str text => return text
  | _ => throw s!"manifest-schema: {location}.{key} must be a string"

theorem stringField_ok {value : Json} {key location text : String}
    (h : stringField value key location = .ok text) : value.getObjVal? key = .ok (.str text) := by
  unfold stringField at h
  simp only [bind_eq_ok] at h
  obtain ⟨field, hfield, h⟩ := h
  split at h
  · simp only [pure_eq_ok] at h
    exact h ▸ hfield
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- Returns `value` when it is a well-formed target name (`TargetName`, by `targetName_sound`);
otherwise fails with a `manifest-incomplete` message naming `location` and `kind`. -/
def targetName (kind value location : String) : Except String String := do
  if value.isEmpty || value.trimAscii.toString != value
      || value.toList.any (fun c => c.isWhitespace || c == ',') then
    throw s!"manifest-incomplete: {location} must be a nonempty {kind} name"
  return value

/-- Returns `value` when it is not blank after trimming ASCII whitespace; otherwise fails with a
`manifest-incomplete` message that `location.rationale` is required. -/
def rationale (value location : String) : Except String String := do
  if value.trimAscii.isEmpty then
    throw s!"manifest-incomplete: {location}.rationale is required"
  return value

theorem targetName_sound {kind value location name : String}
    (h : targetName kind value location = .ok name) : name = value ∧ TargetName value := by
  unfold targetName at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at h
  · rename_i hc
    simp only [pure_eq_ok] at h
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.any_eq_true, not_or,
      not_exists, not_and, String.isEmpty_iff] at hc
    refine ⟨h.symm, hc.1.1, by simpa using hc.1.2, fun c hc' => ?_⟩
    have := hc.2 c hc'
    simpa using this


/-- Record each executable once, refusing a malformed or repeated name. -/
def addExecutables (location : String) : Array String → List String → Except String (Array String)
  | seen, [] => pure seen
  | seen, exe :: rest => do
    let _ ← targetName "executable" exe s!"{location}.executables"
    if seen.contains exe then throw s!"manifest-schema: duplicate executable '{exe}'"
    addExecutables location (seen.push exe) rest

theorem push_nodup {xs : Array String} {x : String} (h : xs.toList.Nodup) (hx : xs.contains x = false) :
    (xs.push x).toList.Nodup := by
  simp only [Array.toList_push]
  rw [List.nodup_append]
  refine ⟨h, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
  intro a ha b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb
  intro heq
  subst heq
  simp only [Array.contains_eq_mem, decide_eq_false_iff_not] at hx
  exact hx (by simpa using ha)

theorem addExecutables_sound {location : String} :
    ∀ {seen out : Array String} {names : List String}, seen.toList.Nodup →
      addExecutables location seen names = .ok out →
      out = seen ++ names.toArray ∧ out.toList.Nodup ∧ ∀ n ∈ names, TargetName n
  | seen, out, [], hn, h => by
    simp only [addExecutables, pure_eq_ok] at h
    subst h
    simp [hn]
  | seen, out, exe :: rest, hn, h => by
    simp only [addExecutables, bind_eq_ok] at h
    obtain ⟨name, hname, h⟩ := h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · rename_i hc
      have hc : seen.contains exe = false := by simpa using hc
      obtain ⟨hout, hnd, hnames⟩ := addExecutables_sound (push_nodup hn hc) h
      refine ⟨by simp [hout], hnd, ?_⟩
      intro n hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact (targetName_sound hname).2
      · exact hnames n hmem


/-- Parsing state: the manifest so far plus every library and executable name seen. -/
structure Acc where
  /-- The claimed surfaces accepted so far, in manifest order. -/
  surfaces : Array Surface := #[]
  /-- The excluded libraries accepted so far, in manifest order. -/
  excludedLibraries : Array ExcludedLibrary := #[]
  /-- The excluded executables accepted so far, in manifest order. -/
  excludedExecutables : Array ExcludedExecutable := #[]
  /-- Every library name accepted so far, claimed or excluded, used to refuse a duplicate. -/
  seen : Array String := #[]
  /-- Every executable name accepted so far, claimed or excluded, used to refuse a duplicate. -/
  seenExes : Array String := #[]

/-- The manifest accumulated so far, without the duplicate-tracking name lists. -/
def Acc.manifest (acc : Acc) : Manifest := ⟨acc.surfaces, acc.excludedLibraries, acc.excludedExecutables⟩

/-- A surface names a well-formed library and executables, a conforming claim and a rationale. -/
def SurfaceOK (s : Surface) : Prop :=
  TargetName s.library ∧ (∀ e ∈ s.executables, TargetName e) ∧
    s.claim ≠ .compilerTrusting ∧ s.rationale.trimAscii.isEmpty = false

/-- The parsing invariant: the seen-name lists are exactly the accumulated manifest's library
and executable names and have no duplicates, every surface satisfies `SurfaceOK`, and every
exclusion has a well-formed name and a nonblank rationale. -/
def Acc.Inv (acc : Acc) : Prop :=
  acc.seen = libraries acc.manifest ∧ acc.seen.toList.Nodup ∧
  acc.seenExes = executables acc.manifest ∧ acc.seenExes.toList.Nodup ∧
  (∀ s ∈ acc.surfaces, SurfaceOK s) ∧
  (∀ l ∈ acc.excludedLibraries, TargetName l.library ∧ l.rationale.trimAscii.isEmpty = false) ∧
  (∀ e ∈ acc.excludedExecutables, TargetName e.executable ∧ e.rationale.trimAscii.isEmpty = false)

theorem rationale_sound {value location r : String} (h : rationale value location = .ok r) :
    r = value ∧ value.trimAscii.isEmpty = false := by
  unfold rationale at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at h
  · rename_i hc
    simp only [pure_eq_ok] at h
    exact ⟨h.symm, by simpa using hc⟩

/-- Refuse a name already recorded. -/
def fresh (seen : Array String) (name message : String) : Except String Unit :=
  if seen.contains name then throw message else pure ()

theorem fresh_sound {seen : Array String} {name message : String} {u : Unit}
    (h : fresh seen name message = .ok u) : seen.contains name = false := by
  unfold fresh at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rename_i hc
    simpa using hc

/-- A fold whose every step appends the string of a JSON string item decodes exactly those items. -/
theorem foldlM_strings {f : Array String → Json → Except String (Array String)}
    (hf : ∀ r item r', f r item = .ok r' → ∃ t, item = .str t ∧ r' = r.push t) :
    ∀ (xs : List Json) (acc out : Array String), xs.foldlM f acc = .ok out →
      ∃ ys : List String, out.toList = acc.toList ++ ys ∧ xs = ys.map .str
  | [], acc, out, h => by
    simp only [List.foldlM_nil, pure_eq_ok] at h
    exact ⟨[], by simp [h], rfl⟩
  | x :: rest, acc, out, h => by
    simp only [List.foldlM_cons, bind_eq_ok] at h
    obtain ⟨mid, hmid, h⟩ := h
    obtain ⟨t, rfl, rfl⟩ := hf _ _ _ hmid
    obtain ⟨ys, hout, hrest⟩ := foldlM_strings hf rest _ _ h
    exact ⟨t :: ys, by simp [hout], by simp [hrest]⟩

/-- `stringArray` returns exactly the strings of the JSON array it accepts, in order. -/
theorem stringArray_items {what : String} {value : Json} {out : Array String}
    (h : stringArray what value = .ok out) : value = .arr (out.map .str) := by
  unfold stringArray at h
  split at h
  · rw [← Array.foldlM_toList] at h
    obtain ⟨ys, hout, hxs⟩ := foldlM_strings (fun r item r' hs => by
      split at hs
      · split at hs
        · simp [throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at hs
        · simp only [pure_eq_ok] at hs
          exact ⟨_, rfl, hs.symm⟩
      · simp [throw, throwThe, MonadExceptOf.throw] at hs) _ _ _ h
    congr
    apply Array.toList_inj.mp
    simp [hxs, hout]
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A surface's optional executables, defaulting to none. -/
def surfaceExecutables (item : Json) (location : String) : Except String (Array String) :=
  match item.getObjVal? "executables" with
  | .error _ => pure #[]
  | .ok value => stringArray s!"{location}.executables" value

/-- Reads a surface's required `claim` string as a `Profile`, refusing any value other than
`kernel-only`, `choice-free` or `standard-logical`. -/
def surfaceClaim (item : Json) (location : String) : Except String Profile := do
  let claimText ← stringField item "claim" location
  let some claim := Profile.parse? claimText
    | throw <| s!"manifest-schema: {location}.claim must be one of " ++
        "kernel-only, choice-free, standard-logical"
  if claim = .compilerTrusting then
    throw <| s!"manifest-schema: {location}.claim must be one of " ++
      "kernel-only, choice-free, standard-logical"
  return claim

theorem surfaceClaim_sound {item : Json} {location : String} {claim : Profile}
    (h : surfaceClaim item location = .ok claim) : claim ≠ .compilerTrusting := by
  unfold surfaceClaim at h
  simp only [bind_eq_ok] at h
  obtain ⟨_, _, h⟩ := h
  split at h
  · rename_i c _
    cases c <;> simp only [↓reduceIte, throw, throwThe, MonadExceptOf.throw, pure, Except.pure,
      bind_eq_ok, reduceCtorEq, Except.ok.injEq, false_and, exists_const] at h <;> subst h <;>
      decide
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- Reads a surface's optional `execution` field: `report` when absent, otherwise the parsed
`ExecutionClaim` of the string, refusing any other value. -/
def surfaceExecution (item : Json) (location : String) : Except String ExecutionClaim :=
  match item.getObjVal? "execution" with
  | .error _ => pure .report
  | .ok (.str text) => match ExecutionClaim.parse? text with
    | some mode => pure mode
    | none => throw s!"manifest-schema: {location}.execution must be \"report\" or \"checked\""
  | .ok _ => throw s!"manifest-schema: {location}.execution must be a string"

theorem surfaceExecutables_ok {item : Json} {location : String} {out : Array String}
    (h : surfaceExecutables item location = .ok out) :
    ((∃ e, item.getObjVal? "executables" = .error e) ∧ out = #[]) ∨
      item.getObjVal? "executables" = .ok (.arr (out.map .str)) := by
  unfold surfaceExecutables at h
  split at h
  · rename_i e he
    simp only [pure_eq_ok] at h
    exact .inl ⟨⟨e, he⟩, h.symm⟩
  · rename_i value hv
    exact .inr (hv.trans (congrArg _ (stringArray_items h)))

theorem surfaceClaim_ok {item : Json} {location : String} {claim : Profile}
    (h : surfaceClaim item location = .ok claim) :
    ∃ text, item.getObjVal? "claim" = .ok (.str text) ∧ Profile.parse? text = some claim := by
  unfold surfaceClaim at h
  simp only [bind_eq_ok] at h
  obtain ⟨text, htext, h⟩ := h
  split at h
  · rename_i c hc
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at h
    · simp only [pure_eq_ok] at h
      exact ⟨text, stringField_ok htext, h ▸ hc⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem surfaceExecution_ok {item : Json} {location : String} {execution : ExecutionClaim}
    (h : surfaceExecution item location = .ok execution) :
    ((∃ e, item.getObjVal? "execution" = .error e) ∧ execution = .report) ∨
      ∃ text, item.getObjVal? "execution" = .ok (.str text) ∧
        ExecutionClaim.parse? text = some execution := by
  unfold surfaceExecution at h
  split at h
  · rename_i e he
    simp only [pure_eq_ok] at h
    exact .inl ⟨⟨e, he⟩, h.symm⟩
  · rename_i text htext
    split at h
    · rename_i mode hmode
      simp only [pure_eq_ok] at h
      exact .inr ⟨text, htext, h ▸ hmode⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `s` is the decoding of the JSON surface `item`: every field is its JSON value, an absent
`executables` is empty and an absent `execution` is `report`. -/
def SurfaceDecodes (item : Json) (s : Surface) : Prop :=
  item.getObjVal? "library" = .ok (.str s.library) ∧
  (((∃ e, item.getObjVal? "executables" = .error e) ∧ s.executables = #[]) ∨
    item.getObjVal? "executables" = .ok (.arr (s.executables.map .str))) ∧
  (∃ text, item.getObjVal? "claim" = .ok (.str text) ∧ Profile.parse? text = some s.claim) ∧
  (((∃ e, item.getObjVal? "execution" = .error e) ∧ s.execution = .report) ∨
    ∃ text, item.getObjVal? "execution" = .ok (.str text) ∧
      ExecutionClaim.parse? text = some s.execution) ∧
  item.getObjVal? "rationale" = .ok (.str s.rationale)

/-- `l` is the decoding of the excluded-library JSON object `item`: its `library` and `rationale`
strings. -/
def ExcludedLibraryDecodes (item : Json) (l : ExcludedLibrary) : Prop :=
  item.getObjVal? "library" = .ok (.str l.library) ∧ item.getObjVal? "rationale" = .ok (.str l.rationale)

/-- `e` is the decoding of the excluded-executable JSON object `item`: its `executable` and
`rationale` strings. -/
def ExcludedExecutableDecodes (item : Json) (e : ExcludedExecutable) : Prop :=
  item.getObjVal? "executable" = .ok (.str e.executable) ∧
    item.getObjVal? "rationale" = .ok (.str e.rationale)

/-- Parses the surface at `surfaces[index]` and appends it to `acc`, refusing an unknown key, a
malformed or duplicate library or executable name, a bad claim or execution, or a blank
rationale. -/
def parseSurface (acc : Acc) (index : Nat) (item : Json) : Except String Acc := do
  let location := s!"surfaces[{index}]"
  objectWithKeys item #["library", "executables", "claim", "execution", "rationale"] location
  let library ← targetName "library" (← stringField item "library" location) s!"{location}.library"
  fresh acc.seen library s!"manifest-schema: duplicate library '{library}'"
  let executables ← surfaceExecutables item location
  let seenExes ← addExecutables location acc.seenExes executables.toList
  let claim ← surfaceClaim item location
  let execution ← surfaceExecution item location
  let why ← rationale (← stringField item "rationale" location) location
  let surface : Surface := ⟨library, executables, claim, execution, why⟩
  return { acc with seen := acc.seen.push library, seenExes, surfaces := acc.surfaces.push surface }

theorem parseSurface_inv {acc out : Acc} {index : Nat} {item : Json} (hi : acc.Inv)
    (hex : acc.excludedLibraries = #[] ∧ acc.excludedExecutables = #[])
    (h : parseSurface acc index item = .ok out) :
    out.Inv ∧ out.excludedLibraries = #[] ∧ out.excludedExecutables = #[] ∧
      out.surfaces.size = acc.surfaces.size + 1 := by
  unfold parseSurface at h
  simp only [bind_eq_ok, pure_eq_ok] at h
  obtain ⟨_, _, lt, _, library, hlib, ⟨⟩, hfresh, execs, _, seenExes, hadd, claim, hclaim,
    execution, _, rt, _, why, hwhy, rfl⟩ := h
  obtain ⟨hseen, hnd, hexes, hxnd, hs, hl, he⟩ := hi
  have hf := fresh_sound hfresh
  obtain ⟨rfl, hname⟩ := targetName_sound hlib
  obtain ⟨hout, hxnd', hnames⟩ := addExecutables_sound hxnd hadd
  obtain ⟨rfl, hr⟩ := rationale_sound hwhy
  refine ⟨⟨?_, push_nodup hnd hf, ?_, hxnd', ?_, hl, he⟩, hex.1, hex.2, by simp⟩
  · simp [hseen, libraries, Acc.manifest, hex.1]
  · simp [hout, hexes, executables, Acc.manifest, hex.2]
  · intro s hs'
    simp only [Array.mem_push] at hs'
    rcases hs' with hs' | rfl
    · exact hs s hs'
    · exact ⟨hname, fun e he' => hnames e (by simpa using he'), surfaceClaim_sound hclaim, hr⟩


/-- Parses the entry at `excluded-libraries[index]` and appends it to `acc`, refusing an unknown
key, a malformed or duplicate library name, or a blank rationale. -/
def parseExcludedLibrary (acc : Acc) (index : Nat) (item : Json) : Except String Acc := do
  let location := s!"excluded-libraries[{index}]"
  objectWithKeys item #["library", "rationale"] location
  let library ← targetName "library" (← stringField item "library" location) s!"{location}.library"
  fresh acc.seen library s!"manifest-schema: duplicate library '{library}'"
  let why ← rationale (← stringField item "rationale" location) location
  let excluded : ExcludedLibrary := ⟨library, why⟩
  return { acc with seen := acc.seen.push library, excludedLibraries := acc.excludedLibraries.push excluded }

theorem parseExcludedLibrary_inv {acc out : Acc} {index : Nat} {item : Json} (hi : acc.Inv)
    (hex : acc.excludedExecutables = #[]) (h : parseExcludedLibrary acc index item = .ok out) :
    out.Inv ∧ out.excludedExecutables = #[] ∧ out.surfaces = acc.surfaces := by
  unfold parseExcludedLibrary at h
  simp only [bind_eq_ok, pure_eq_ok] at h
  obtain ⟨_, _, lt, _, library, hlib, ⟨⟩, hfresh, rt, _, why, hwhy, rfl⟩ := h
  obtain ⟨hseen, hnd, hexes, hxnd, hs, hl, he⟩ := hi
  obtain ⟨rfl, hname⟩ := targetName_sound hlib
  obtain ⟨rfl, hr⟩ := rationale_sound hwhy
  refine ⟨⟨?_, push_nodup hnd (fresh_sound hfresh), ?_, hxnd, hs, ?_, he⟩, hex, rfl⟩
  · simp [hseen, libraries, Acc.manifest]
  · simp [hexes, executables, Acc.manifest]
  · intro l hl'
    simp only [Array.mem_push] at hl'
    rcases hl' with hl' | rfl
    · exact hl l hl'
    · exact ⟨hname, hr⟩

/-- Parses the entry at `excluded-executables[index]` and appends it to `acc`, refusing an
unknown key, a malformed or duplicate executable name, or a blank rationale. -/
def parseExcludedExecutable (acc : Acc) (index : Nat) (item : Json) : Except String Acc := do
  let location := s!"excluded-executables[{index}]"
  objectWithKeys item #["executable", "rationale"] location
  let executable ← targetName "executable" (← stringField item "executable" location) s!"{location}.executable"
  fresh acc.seenExes executable s!"manifest-schema: duplicate executable '{executable}'"
  let why ← rationale (← stringField item "rationale" location) location
  let excluded : ExcludedExecutable := ⟨executable, why⟩
  return { acc with seenExes := acc.seenExes.push executable, excludedExecutables := acc.excludedExecutables.push excluded }

theorem parseExcludedExecutable_inv {acc out : Acc} {index : Nat} {item : Json} (hi : acc.Inv)
    (h : parseExcludedExecutable acc index item = .ok out) :
    out.Inv ∧ out.surfaces = acc.surfaces := by
  unfold parseExcludedExecutable at h
  simp only [bind_eq_ok, pure_eq_ok] at h
  obtain ⟨_, _, lt, _, executable, hexe, ⟨⟩, hfresh, rt, _, why, hwhy, rfl⟩ := h
  obtain ⟨hseen, hnd, hexes, hxnd, hs, hl, he⟩ := hi
  obtain ⟨rfl, hname⟩ := targetName_sound hexe
  obtain ⟨rfl, hr⟩ := rationale_sound hwhy
  refine ⟨⟨?_, hnd, ?_, push_nodup hxnd (fresh_sound hfresh), hs, hl, ?_⟩, rfl⟩
  · simp [hseen, libraries, Acc.manifest]
  · simp [hexes, executables, Acc.manifest]
  · intro e he'
    simp only [Array.mem_push] at he'
    rcases he' with he' | rfl
    · exact he e he'
    · exact ⟨hname, hr⟩

/-- Fold one parsing step over an array with its indices, stopping at the first refusal. -/
def parseAll (step : Acc → Nat → Json → Except String Acc) :
    List Json → Nat → Acc → Except String Acc
  | [], _, acc => pure acc
  | item :: rest, index, acc => do parseAll step rest (index + 1) (← step acc index item)

theorem parseAll_inv (step : Acc → Nat → Json → Except String Acc) (P : Acc → Prop)
    (hstep : ∀ acc out index item, P acc → step acc index item = .ok out → P out) :
    ∀ {items : List Json} {index : Nat} {acc out : Acc}, P acc →
      parseAll step items index acc = .ok out → P out
  | [], _, acc, out, hp, h => by
    simp only [parseAll, pure_eq_ok] at h
    exact h ▸ hp
  | item :: rest, index, acc, out, hp, h => by
    simp only [parseAll, bind_eq_ok] at h
    obtain ⟨mid, hmid, h⟩ := h
    exact parseAll_inv step P hstep (hstep _ _ _ _ hp hmid) h


/-- Everything a successfully parsed manifest guarantees about its own contents. -/
def Valid (m : Manifest) : Prop :=
  m.surfaces ≠ #[] ∧ (libraries m).toList.Nodup ∧ (executables m).toList.Nodup ∧
  (∀ s ∈ m.surfaces, SurfaceOK s) ∧
  (∀ l ∈ m.excludedLibraries, TargetName l.library ∧ l.rationale.trimAscii.isEmpty = false) ∧
  (∀ e ∈ m.excludedExecutables, TargetName e.executable ∧ e.rationale.trimAscii.isEmpty = false)

/-- Exactly the JSON number `2`. `JsonNumber`'s derived equality decides it; `Json`'s own `BEq`
is a `partial def`, so no theorem could discharge a check written with it. On numbers both
compare the same `JsonNumber` fields, and every other value is refused. -/
def schemaVersion2 : Json → Bool
  | .num n => decide (n = 2)
  | _ => false

theorem schemaVersion2_iff {value : Json} : schemaVersion2 value = true ↔ value = Json.num 2 := by
  cases value <;> simp [schemaVersion2]

/-- The top-level object: exact keys, schema version 2, and three arrays with nonempty surfaces. -/
def topLevel (value : Json) : Except String (Array Json × Array Json × Array Json) := do
  objectWithKeys value #["schema-version", "surfaces", "excluded-libraries", "excluded-executables"]
    "top level"
  unless schemaVersion2 (← value.getObjVal? "schema-version") do
    throw "manifest-schema: schema-version must be exactly 2"
  let .arr surfaceValues ← value.getObjVal? "surfaces"
    | throw "manifest-schema: surfaces must be an array"
  let .arr excludedValues ← value.getObjVal? "excluded-libraries"
    | throw "manifest-schema: excluded-libraries must be an array"
  let .arr excludedExeValues ← value.getObjVal? "excluded-executables"
    | throw "manifest-schema: excluded-executables must be an array"
  if surfaceValues.isEmpty then
    throw "manifest-incomplete: surfaces must be a nonempty array"
  return (surfaceValues, excludedValues, excludedExeValues)

theorem topLevel_sound {value : Json} {s l e : Array Json} (h : topLevel value = .ok (s, l, e)) :
    KeysAllowed value #["schema-version", "surfaces", "excluded-libraries", "excluded-executables"] ∧
    value.getObjVal? "schema-version" = .ok (Json.num 2) ∧
    value.getObjVal? "surfaces" = .ok (.arr s) ∧ value.getObjVal? "excluded-libraries" = .ok (.arr l) ∧
    value.getObjVal? "excluded-executables" = .ok (.arr e) ∧ s ≠ #[] := by
  unfold topLevel at h
  simp only [bind_eq_ok] at h
  obtain ⟨_, hkeys, schema, hschema, h⟩ := h
  split at h
  · rename_i hv
    simp only [bind_eq_ok] at h
    obtain ⟨sj, hsj, h⟩ := h
    split at h
    · rename_i sv
      simp only [bind_eq_ok] at h
      obtain ⟨lj, hlj, h⟩ := h
      split at h
      · rename_i lv
        simp only [bind_eq_ok] at h
        obtain ⟨ej, hej, h⟩ := h
        split at h
        · rename_i ev
          split at h
          · simp [throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at h
          · rename_i hne
            simp only [pure_eq_ok, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ⟨objectWithKeys_sound hkeys,
              schemaVersion2_iff.mp (by simpa using hv) ▸ hschema, hsj, hlj, hej,
              by simpa using hne⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem empty_inv : ({} : Acc).Inv := by
  simp [Acc.Inv, libraries, executables, Acc.manifest]

/-- The JSON value stage of `parse`: the top-level object, then the three ordered folds. -/
def parseValue (value : Json) : Except String Manifest := do
  let (surfaceValues, excludedValues, excludedExeValues) ← topLevel value
  let acc ← parseAll parseSurface surfaceValues.toList 0 {}
  let acc ← parseAll parseExcludedLibrary excludedValues.toList 0 acc
  let acc ← parseAll parseExcludedExecutable excludedExeValues.toList 0 acc
  return acc.manifest

/-- The executed manifest parser: parses `text` as JSON (a failure is `manifest-malformed`,
naming `path`) and then decodes it with `parseValue`. -/
def parse (path text : String) : Except String Manifest := do
  let value ← (Regula.Checker.PolicyCodec.parse text).mapError
    (fun error => s!"manifest-malformed: {path}: {error}")
  parseValue value

/-- `parse` accepts exactly what `parseValue` accepts of the text parser's value. -/
theorem parse_ok {path text : String} {m : Manifest} :
    parse path text = .ok m ↔
      ∃ value, Regula.Checker.PolicyCodec.parse text = .ok value ∧ parseValue value = .ok m := by
  unfold parse
  cases Regula.Checker.PolicyCodec.parse text <;>
    simp [Except.mapError, bind, Except.bind]

theorem parseValue_sound {value : Json} {m : Manifest} (h : parseValue value = .ok m) : m.Valid := by
  unfold parseValue at h
  simp only [bind_eq_ok, pure_eq_ok] at h
  obtain ⟨⟨sv, lv, ev⟩, htop, a1, h1, a2, h2, a3, h3, rfl⟩ := h
  obtain ⟨-, -, -, -, -, hne⟩ := topLevel_sound htop
  -- Surfaces: at least one step runs, and every step keeps the invariant.
  have hs : a1.Inv ∧ a1.excludedLibraries = #[] ∧ a1.excludedExecutables = #[] ∧ a1.surfaces ≠ #[] := by
    obtain ⟨first, rest, hfr⟩ : ∃ first rest, sv.toList = first :: rest := by
      cases hsv : sv.toList with
      | nil => exact absurd (Array.toList_eq_nil_iff.mp hsv) hne
      | cons a r => exact ⟨a, r, rfl⟩
    rw [hfr] at h1
    simp only [parseAll, bind_eq_ok] at h1
    obtain ⟨mid, hmid, h1⟩ := h1
    obtain ⟨hinv, hl, he, hsize⟩ := parseSurface_inv empty_inv ⟨rfl, rfl⟩ hmid
    refine parseAll_inv parseSurface
      (fun acc => acc.Inv ∧ acc.excludedLibraries = #[] ∧ acc.excludedExecutables = #[] ∧
        acc.surfaces ≠ #[]) ?_ ⟨hinv, hl, he, ?_⟩ h1
    · intro acc out index item ⟨hi, hl, he, hn⟩ hstep
      obtain ⟨hi', hl', he', hsz⟩ := parseSurface_inv hi ⟨hl, he⟩ hstep
      exact ⟨hi', hl', he', by intro hemp; simp [hemp] at hsz⟩
    · intro hemp; simp [hemp] at hsize
  have hl : a2.Inv ∧ a2.excludedExecutables = #[] ∧ a2.surfaces ≠ #[] :=
    parseAll_inv parseExcludedLibrary
      (fun acc => acc.Inv ∧ acc.excludedExecutables = #[] ∧ acc.surfaces ≠ #[])
      (fun acc out index item ⟨hi, he, hn⟩ hstep => by
        obtain ⟨hi', he', hsurf⟩ := parseExcludedLibrary_inv hi he hstep
        exact ⟨hi', he', hsurf ▸ hn⟩)
      ⟨hs.1, hs.2.2.1, hs.2.2.2⟩ h2
  have he : a3.Inv ∧ a3.surfaces ≠ #[] :=
    parseAll_inv parseExcludedExecutable (fun acc => acc.Inv ∧ acc.surfaces ≠ #[])
      (fun acc out index item ⟨hi, hn⟩ hstep => by
        obtain ⟨hi', hsurf⟩ := parseExcludedExecutable_inv hi hstep
        exact ⟨hi', hsurf ▸ hn⟩)
      ⟨hl.1, hl.2.2⟩ h3
  obtain ⟨⟨hseen, hnd, hexes, hxnd, hsok, hlok, heok⟩, hsne⟩ := he
  exact ⟨hsne, hseen ▸ hnd, hexes ▸ hxnd, hsok, hlok, heok⟩

theorem parse_sound {path text : String} {m : Manifest} (h : parse path text = .ok m) : m.Valid := by
  obtain ⟨_, _, h⟩ := parse_ok.mp h
  exact parseValue_sound h


/-- Every item a successful fold consumed satisfies what one successful step establishes. -/
theorem parseAll_each (step : Acc → Nat → Json → Except String Acc) (Q : Json → Prop)
    (hstep : ∀ acc out index item, step acc index item = .ok out → Q item) :
    ∀ {items : List Json} {index : Nat} {acc out : Acc},
      parseAll step items index acc = .ok out → ∀ item ∈ items, Q item
  | [], _, _, _, _ => by simp
  | item :: rest, index, acc, out, h => by
    simp only [parseAll, bind_eq_ok] at h
    obtain ⟨mid, hmid, h⟩ := h
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hstep _ _ _ _ hmid
    · exact parseAll_each step Q hstep h x hx

/-- `D` relates the two lists element by element, in order. -/
def Decodes {α : Type} (D : Json → α → Prop) (items : List Json) (ys : List α) : Prop :=
  items.length = ys.length ∧ ∀ p ∈ items.zip ys, D p.1 p.2

/-- A fold whose every step appends one decoding of its item to `f` pairs the items, in
order, with the appended entries. -/
theorem parseAll_decodes {α : Type} (step : Acc → Nat → Json → Except String Acc)
    (f : Acc → Array α) (D : Json → α → Prop)
    (hstep : ∀ acc out index item, step acc index item = .ok out →
      ∃ x, f out = (f acc).push x ∧ D item x) :
    ∀ {items : List Json} {index : Nat} {acc out : Acc}, parseAll step items index acc = .ok out →
      ∃ ys : List α, (f out).toList = (f acc).toList ++ ys ∧ Decodes D items ys
  | [], _, acc, out, h => by
    simp only [parseAll, pure_eq_ok] at h
    exact ⟨[], by simp [h], by simp [Decodes]⟩
  | item :: rest, index, acc, out, h => by
    simp only [parseAll, bind_eq_ok] at h
    obtain ⟨mid, hmid, h⟩ := h
    obtain ⟨x, hx, hd⟩ := hstep _ _ _ _ hmid
    obtain ⟨ys, hys, hall⟩ := parseAll_decodes step f D hstep h
    refine ⟨x :: ys, by simp [hys, hx], by simp [hall.1], ?_⟩
    intro p hp
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hd
    · exact hall.2 p hp


theorem parseSurface_input {acc out : Acc} {index : Nat} {item : Json}
    (h : parseSurface acc index item = .ok out) :
    KeysAllowed item #["library", "executables", "claim", "execution", "rationale"] ∧
      (∃ s, out.surfaces = acc.surfaces.push s ∧ SurfaceDecodes item s) ∧
      out.excludedLibraries = acc.excludedLibraries ∧ out.excludedExecutables = acc.excludedExecutables := by
  unfold parseSurface at h
  simp only [bind_eq_ok, pure_eq_ok] at h
  obtain ⟨_, hkeys, _, hlt, _, hlib, _, _, _, hexecs, _, _, _, hclaim, _, hexec, _, hrt, _, hwhy,
    rfl⟩ := h
  obtain ⟨rfl, -⟩ := targetName_sound hlib
  obtain ⟨rfl, -⟩ := rationale_sound hwhy
  exact ⟨objectWithKeys_sound hkeys, ⟨_, rfl, stringField_ok hlt, surfaceExecutables_ok hexecs,
    surfaceClaim_ok hclaim, surfaceExecution_ok hexec, stringField_ok hrt⟩, rfl, rfl⟩

theorem parseExcludedLibrary_input {acc out : Acc} {index : Nat} {item : Json}
    (h : parseExcludedLibrary acc index item = .ok out) :
    KeysAllowed item #["library", "rationale"] ∧
      (∃ l, out.excludedLibraries = acc.excludedLibraries.push l ∧ ExcludedLibraryDecodes item l) ∧
      out.surfaces = acc.surfaces ∧ out.excludedExecutables = acc.excludedExecutables := by
  unfold parseExcludedLibrary at h
  simp only [bind_eq_ok, pure_eq_ok] at h
  obtain ⟨_, hkeys, _, hlt, _, hlib, _, _, _, hrt, _, hwhy, rfl⟩ := h
  obtain ⟨rfl, -⟩ := targetName_sound hlib
  obtain ⟨rfl, -⟩ := rationale_sound hwhy
  exact ⟨objectWithKeys_sound hkeys, ⟨_, rfl, stringField_ok hlt, stringField_ok hrt⟩, rfl, rfl⟩

theorem parseExcludedExecutable_input {acc out : Acc} {index : Nat} {item : Json}
    (h : parseExcludedExecutable acc index item = .ok out) :
    KeysAllowed item #["executable", "rationale"] ∧
      (∃ e, out.excludedExecutables = acc.excludedExecutables.push e ∧
        ExcludedExecutableDecodes item e) ∧
      out.surfaces = acc.surfaces ∧ out.excludedLibraries = acc.excludedLibraries := by
  unfold parseExcludedExecutable at h
  simp only [bind_eq_ok, pure_eq_ok] at h
  obtain ⟨_, hkeys, _, hlt, _, hexe, _, _, _, hrt, _, hwhy, rfl⟩ := h
  obtain ⟨rfl, -⟩ := targetName_sound hexe
  obtain ⟨rfl, -⟩ := rationale_sound hwhy
  exact ⟨objectWithKeys_sound hkeys, ⟨_, rfl, stringField_ok hlt, stringField_ok hrt⟩, rfl, rfl⟩


/-- `value` is a JSON encoding of `m`: exactly the allowed top-level and per-entry keys, schema
version 2, and three arrays that are, element by element in order, decoded to `m`'s arrays. -/
def Encodes (value : Json) (m : Manifest) : Prop :=
  ∃ sv lv ev,
    KeysAllowed value #["schema-version", "surfaces", "excluded-libraries", "excluded-executables"] ∧
    value.getObjVal? "schema-version" = .ok (Json.num 2) ∧
    value.getObjVal? "surfaces" = .ok (.arr sv) ∧ value.getObjVal? "excluded-libraries" = .ok (.arr lv) ∧
    value.getObjVal? "excluded-executables" = .ok (.arr ev) ∧
    Decodes SurfaceDecodes sv.toList m.surfaces.toList ∧
    Decodes ExcludedLibraryDecodes lv.toList m.excludedLibraries.toList ∧
    Decodes ExcludedExecutableDecodes ev.toList m.excludedExecutables.toList ∧
    (∀ item ∈ sv, KeysAllowed item #["library", "executables", "claim", "execution", "rationale"]) ∧
    (∀ item ∈ lv, KeysAllowed item #["library", "rationale"]) ∧
    (∀ item ∈ ev, KeysAllowed item #["executable", "rationale"])

/-- Input fidelity of the JSON value stage: every accepted value encodes its manifest. -/
theorem parseValue_input {value : Json} {m : Manifest} (h : parseValue value = .ok m) :
    Encodes value m := by
  unfold parseValue at h
  simp only [bind_eq_ok, pure_eq_ok] at h
  obtain ⟨⟨sv, lv, ev⟩, htop, a1, h1, a2, h2, a3, h3, rfl⟩ := h
  obtain ⟨hkeys, hschema, hs, hl, he, -⟩ := topLevel_sound htop
  obtain ⟨y1, e1, d1⟩ := parseAll_decodes parseSurface (·.surfaces) SurfaceDecodes
    (fun _ _ _ _ hs => (parseSurface_input hs).2.1) h1
  obtain ⟨y2, e2, d2⟩ := parseAll_decodes parseExcludedLibrary (·.excludedLibraries)
    ExcludedLibraryDecodes (fun _ _ _ _ hs => (parseExcludedLibrary_input hs).2.1) h2
  obtain ⟨y3, e3, d3⟩ := parseAll_decodes parseExcludedExecutable (·.excludedExecutables)
    ExcludedExecutableDecodes (fun _ _ _ _ hs => (parseExcludedExecutable_input hs).2.1) h3
  -- Later folds leave earlier arrays unchanged.
  have k2 := parseAll_inv parseExcludedLibrary (fun acc => acc.surfaces = a1.surfaces ∧
      acc.excludedExecutables = a1.excludedExecutables)
    (fun _ _ _ _ ⟨hs', he'⟩ hstep => by
      obtain ⟨-, -, hs'', he''⟩ := parseExcludedLibrary_input hstep
      exact ⟨hs''.trans hs', he''.trans he'⟩) ⟨rfl, rfl⟩ h2
  have k1 := parseAll_inv parseSurface (fun acc => acc.excludedLibraries = #[] ∧
      acc.excludedExecutables = #[])
    (fun _ _ _ _ ⟨hl', he'⟩ hstep => by
      obtain ⟨-, -, hl'', he''⟩ := parseSurface_input hstep
      exact ⟨hl''.trans hl', he''.trans he'⟩) ⟨rfl, rfl⟩ h1
  have k3 := parseAll_inv parseExcludedExecutable (fun acc => acc.surfaces = a2.surfaces ∧
      acc.excludedLibraries = a2.excludedLibraries)
    (fun _ _ _ _ ⟨hs', hl'⟩ hstep => by
      obtain ⟨-, -, hs'', hl''⟩ := parseExcludedExecutable_input hstep
      exact ⟨hs''.trans hs', hl''.trans hl'⟩) ⟨rfl, rfl⟩ h3
  refine ⟨sv, lv, ev, hkeys, hschema, hs, hl, he, ?_, ?_, ?_,
    fun item hi => parseAll_each parseSurface _ (fun _ _ _ _ hs => (parseSurface_input hs).1) h1 item
      (by simpa using hi),
    fun item hi => parseAll_each parseExcludedLibrary _
      (fun _ _ _ _ hs => (parseExcludedLibrary_input hs).1) h2 item (by simpa using hi),
    fun item hi => parseAll_each parseExcludedExecutable _
      (fun _ _ _ _ hs => (parseExcludedExecutable_input hs).1) h3 item (by simpa using hi)⟩
  · simp only [Acc.manifest, k3.1, k2.1]; simp only at e1; simpa [e1] using d1
  · simp only [Acc.manifest, k3.2]; simp only [k1.1] at e2; simpa [e2] using d2
  · simp only [Acc.manifest]; simp only [k2.2, k1.2] at e3; simpa [e3] using d3

/-- Input fidelity: the parsed manifest comes from well-formed JSON with exactly the allowed
top-level and per-entry keys and schema version 2, and each of its three arrays is, element by
element in order, the decoding of the corresponding JSON array. -/
theorem parse_input {path text : String} {m : Manifest} (h : parse path text = .ok m) :
    ∃ value sv lv ev, Regula.Checker.PolicyCodec.parse text = .ok value ∧
      KeysAllowed value #["schema-version", "surfaces", "excluded-libraries", "excluded-executables"] ∧
      value.getObjVal? "schema-version" = .ok (Json.num 2) ∧
      value.getObjVal? "surfaces" = .ok (.arr sv) ∧ value.getObjVal? "excluded-libraries" = .ok (.arr lv) ∧
      value.getObjVal? "excluded-executables" = .ok (.arr ev) ∧
      Decodes SurfaceDecodes sv.toList m.surfaces.toList ∧
      Decodes ExcludedLibraryDecodes lv.toList m.excludedLibraries.toList ∧
      Decodes ExcludedExecutableDecodes ev.toList m.excludedExecutables.toList ∧
      (∀ item ∈ sv, KeysAllowed item #["library", "executables", "claim", "execution", "rationale"]) ∧
      (∀ item ∈ lv, KeysAllowed item #["library", "rationale"]) ∧
      (∀ item ∈ ev, KeysAllowed item #["executable", "rationale"]) := by
  obtain ⟨value, hvalue, h⟩ := parse_ok.mp h
  obtain ⟨sv, lv, ev, rest⟩ := parseValue_input h
  exact ⟨value, sv, lv, ev, hvalue, rest⟩

/-- `topLevel` accepts every value meeting the conditions `topLevel_sound` establishes. -/
theorem topLevel_complete {value : Json} {sv lv ev : Array Json}
    (hkeys : KeysAllowed value
      #["schema-version", "surfaces", "excluded-libraries", "excluded-executables"])
    (hschema : value.getObjVal? "schema-version" = .ok (Json.num 2))
    (hs : value.getObjVal? "surfaces" = .ok (.arr sv))
    (hl : value.getObjVal? "excluded-libraries" = .ok (.arr lv))
    (he : value.getObjVal? "excluded-executables" = .ok (.arr ev)) (hne : sv ≠ #[]) :
    topLevel value = .ok (sv, lv, ev) := by
  have hne : sv.isEmpty = false := by simpa [Array.isEmpty_iff] using hne
  simp [topLevel, objectWithKeys_complete hkeys, hschema, schemaVersion2, hs, hl, he, hne, bind, Except.bind,
    pure, Except.pure]

/-- Completeness for empty exclusions: well-formed top-level JSON whose exclusion arrays are
empty is accepted whenever its surfaces are, with exactly the parsed surfaces. -/
theorem parse_emptyExclusions {path text : String} {value : Json} {sv : Array Json} {acc : Acc}
    (hvalue : Regula.Checker.PolicyCodec.parse text = .ok value)
    (hkeys : KeysAllowed value
      #["schema-version", "surfaces", "excluded-libraries", "excluded-executables"])
    (hschema : value.getObjVal? "schema-version" = .ok (Json.num 2))
    (hs : value.getObjVal? "surfaces" = .ok (.arr sv))
    (hl : value.getObjVal? "excluded-libraries" = .ok (.arr #[]))
    (he : value.getObjVal? "excluded-executables" = .ok (.arr #[])) (hne : sv ≠ #[])
    (hsurfaces : parseAll parseSurface sv.toList 0 {} = .ok acc) :
    parse path text = .ok acc.manifest := by
  have htop := topLevel_complete hkeys hschema hs hl he hne
  simp [parse, parseValue, hvalue, htop, hsurfaces, parseAll, Except.mapError, bind, Except.bind, pure,
    Except.pure]

/-! Completeness. `parseValue` accepts every JSON value that encodes a valid manifest, with
exactly that manifest; with `parseValue_sound` and `parseValue_input` this characterizes
acceptance (`parseValue_ok`). -/

theorem stringField_complete {value : Json} {key location text : String}
    (h : value.getObjVal? key = .ok (.str text)) : stringField value key location = .ok text := by
  simp [stringField, h, bind, Except.bind, pure, Except.pure]

theorem targetName_complete {kind value location : String} (h : TargetName value) :
    targetName kind value location = .ok value := by
  obtain ⟨hne, htrim, hchars⟩ := h
  have hany : value.toList.any (fun c => c.isWhitespace || c == ',') = false := by
    simp only [List.any_eq_false, Bool.or_eq_true, beq_iff_eq, not_or]
    exact hchars
  have hempty : value.isEmpty = false := by simpa [String.isEmpty_iff] using hne
  have htrim : value.trimAscii.copy = value := by simpa using htrim
  simp [targetName, hany, hempty, htrim, pure, Except.pure]

theorem rationale_complete {value location : String} (h : value.trimAscii.isEmpty = false) :
    rationale value location = .ok value := by
  simp [rationale, h, pure, Except.pure]

theorem fresh_complete {seen : Array String} {name message : String}
    (h : seen.contains name = false) : fresh seen name message = .ok () := by
  have h : name ∉ seen := by simpa using h
  simp [fresh, h, pure, Except.pure]

/-- A name after a duplicate-free prefix is not in that prefix. -/
theorem contains_false_of_nodup {acc : Array String} {y : String} {ys : List String}
    (h : (acc.toList ++ y :: ys).Nodup) : acc.contains y = false := by
  have hdisj := (List.nodup_append.mp h).2.2
  cases hc : acc.contains y
  · rfl
  · exact absurd rfl (hdisj y (by simpa [Array.contains_iff_mem] using hc) y (by simp))

/-- A fold whose every step appends a fresh nonempty JSON string accepts exactly those strings. -/
theorem foldlM_strings_complete {f : Array String → Json → Except String (Array String)}
    (hf : ∀ r t, t ≠ "" → r.contains t = false → f r (.str t) = .ok (r.push t)) :
    ∀ (ys : List String) (acc : Array String), (acc.toList ++ ys).Nodup → (∀ y ∈ ys, y ≠ "") →
      (ys.map Json.str).foldlM f acc = .ok (acc ++ ys.toArray)
  | [], acc, _, _ => by simp [pure, Except.pure]
  | y :: ys, acc, hnd, hne => by
    rw [List.map_cons, List.foldlM_cons, hf acc y (hne y (by simp)) (contains_false_of_nodup hnd)]
    refine (foldlM_strings_complete hf ys (acc.push y) (by simpa using hnd)
      (fun z hz => hne z (by simp [hz]))).trans ?_
    simp

/-- `stringArray` accepts every array of distinct nonempty strings, returning it unchanged. -/
theorem stringArray_complete {what : String} {xs : Array String} (hne : ∀ x ∈ xs, x ≠ "")
    (hnd : xs.toList.Nodup) : stringArray what (.arr (xs.map .str)) = .ok xs := by
  unfold stringArray
  simp only
  rw [← Array.foldlM_toList, Array.toList_map]
  refine (foldlM_strings_complete ?_ xs.toList #[] (by simpa using hnd)
    (fun x hx => hne x (by simpa using hx))).trans (by simp)
  intro r t ht hc
  have ht : t.isEmpty = false := by simpa [String.isEmpty_iff] using ht
  have hc : t ∉ r := by simpa using hc
  simp [ht, hc, pure, Except.pure]

theorem addExecutables_complete {location : String} :
    ∀ (seen : Array String) (names : List String), (seen.toList ++ names).Nodup →
      (∀ n ∈ names, TargetName n) → addExecutables location seen names = .ok (seen ++ names.toArray)
  | seen, [], _, _ => by simp [addExecutables, pure, Except.pure]
  | seen, exe :: rest, hnd, hnames => by
    simp only [addExecutables, bind, Except.bind, targetName_complete (hnames exe (by simp)),
      contains_false_of_nodup hnd, Bool.false_eq_true, ↓reduceIte]
    refine (addExecutables_complete (seen.push exe) rest (by simpa using hnd)
      (fun n hn => hnames n (by simp [hn]))).trans (by simp)

theorem surfaceExecutables_complete {item : Json} {location : String} {xs : Array String}
    (hd : ((∃ e, item.getObjVal? "executables" = .error e) ∧ xs = #[]) ∨
      item.getObjVal? "executables" = .ok (.arr (xs.map .str)))
    (hne : ∀ x ∈ xs, x ≠ "") (hnd : xs.toList.Nodup) : surfaceExecutables item location = .ok xs := by
  rcases hd with ⟨⟨e, he⟩, rfl⟩ | h
  · simp [surfaceExecutables, he, pure, Except.pure]
  · simp [surfaceExecutables, h, stringArray_complete hne hnd]

theorem surfaceClaim_complete {item : Json} {location : String} {claim : Profile}
    (hd : ∃ text, item.getObjVal? "claim" = .ok (.str text) ∧ Profile.parse? text = some claim)
    (hc : claim ≠ .compilerTrusting) : surfaceClaim item location = .ok claim := by
  obtain ⟨text, htext, hparse⟩ := hd
  simp [surfaceClaim, stringField_complete htext, hparse, hc, bind, Except.bind, pure, Except.pure]

theorem surfaceExecution_complete {item : Json} {location : String} {execution : ExecutionClaim}
    (hd : ((∃ e, item.getObjVal? "execution" = .error e) ∧ execution = .report) ∨
      ∃ text, item.getObjVal? "execution" = .ok (.str text) ∧
        ExecutionClaim.parse? text = some execution) :
    surfaceExecution item location = .ok execution := by
  rcases hd with ⟨⟨e, he⟩, rfl⟩ | ⟨text, htext, hparse⟩
  · simp [surfaceExecution, he, pure, Except.pure]
  · simp [surfaceExecution, htext, hparse, pure, Except.pure]

/-- The parsing state after accepting surface `s`. -/
def Acc.addSurface (acc : Acc) (s : Surface) : Acc :=
  { acc with
    seen := acc.seen.push s.library
    seenExes := acc.seenExes ++ s.executables
    surfaces := acc.surfaces.push s }

/-- The parsing state after accepting excluded library `l`. -/
def Acc.addExcludedLibrary (acc : Acc) (l : ExcludedLibrary) : Acc :=
  { acc with
    seen := acc.seen.push l.library
    excludedLibraries := acc.excludedLibraries.push l }

/-- The parsing state after accepting excluded executable `e`. -/
def Acc.addExcludedExecutable (acc : Acc) (e : ExcludedExecutable) : Acc :=
  { acc with
    seenExes := acc.seenExes.push e.executable
    excludedExecutables := acc.excludedExecutables.push e }

theorem parseSurface_complete {acc : Acc} {index : Nat} {item : Json} {s : Surface}
    (hkeys : KeysAllowed item #["library", "executables", "claim", "execution", "rationale"])
    (hd : SurfaceDecodes item s) (hok : SurfaceOK s) (hfresh : acc.seen.contains s.library = false)
    (hexes : (acc.seenExes.toList ++ s.executables.toList).Nodup) :
    parseSurface acc index item = .ok (acc.addSurface s) := by
  obtain ⟨hlib, hexecs, hclaim, hexec, hwhy⟩ := hd
  obtain ⟨hname, hnames, hc, hr⟩ := hok
  have hx := fun location => surfaceExecutables_complete (location := location) hexecs
    (fun x hx => (hnames x hx).1) (List.nodup_append.mp hexes).2.1
  have ha := fun location => addExecutables_complete (location := location) acc.seenExes
    s.executables.toList hexes (fun n hn => hnames n (by simpa using hn))
  simp [parseSurface, objectWithKeys_complete hkeys, stringField_complete hlib,
    targetName_complete hname, fresh_complete hfresh, hx, ha, surfaceClaim_complete hclaim hc,
    surfaceExecution_complete hexec, stringField_complete hwhy, rationale_complete hr, bind,
    Except.bind, pure, Except.pure, Acc.addSurface]

theorem parseExcludedLibrary_complete {acc : Acc} {index : Nat} {item : Json} {l : ExcludedLibrary}
    (hkeys : KeysAllowed item #["library", "rationale"]) (hd : ExcludedLibraryDecodes item l)
    (hok : TargetName l.library ∧ l.rationale.trimAscii.isEmpty = false)
    (hfresh : acc.seen.contains l.library = false) :
    parseExcludedLibrary acc index item = .ok (acc.addExcludedLibrary l) := by
  obtain ⟨hlib, hwhy⟩ := hd
  simp [parseExcludedLibrary, objectWithKeys_complete hkeys, stringField_complete hlib,
    targetName_complete hok.1, fresh_complete hfresh, stringField_complete hwhy,
    rationale_complete hok.2, bind, Except.bind, pure, Except.pure, Acc.addExcludedLibrary]

theorem parseExcludedExecutable_complete {acc : Acc} {index : Nat} {item : Json}
    {e : ExcludedExecutable} (hkeys : KeysAllowed item #["executable", "rationale"])
    (hd : ExcludedExecutableDecodes item e)
    (hok : TargetName e.executable ∧ e.rationale.trimAscii.isEmpty = false)
    (hfresh : acc.seenExes.contains e.executable = false) :
    parseExcludedExecutable acc index item = .ok (acc.addExcludedExecutable e) := by
  obtain ⟨hexe, hwhy⟩ := hd
  simp [parseExcludedExecutable, objectWithKeys_complete hkeys, stringField_complete hexe,
    targetName_complete hok.1, fresh_complete hfresh, stringField_complete hwhy,
    rationale_complete hok.2, bind, Except.bind, pure, Except.pure, Acc.addExcludedExecutable]

/-- A fold accepts items paired, in order, with entries whose every step keeps `I` on the
remaining entries. -/
theorem parseAll_complete {α : Type} (step : Acc → Nat → Json → Except String Acc)
    (D : Json → α → Prop) (I : Acc → List α → Prop)
    (hstep : ∀ acc index item x rest, I acc (x :: rest) → D item x →
      ∃ out, step acc index item = .ok out ∧ I out rest) :
    ∀ {items : List Json} {xs : List α} {index : Nat} {acc : Acc}, I acc xs → Decodes D items xs →
      ∃ out, parseAll step items index acc = .ok out ∧ I out []
  | [], [], _, acc, hi, _ => ⟨acc, rfl, hi⟩
  | [], _ :: _, _, _, _, h => absurd h.1 (by simp)
  | _ :: _, [], _, _, _, h => absurd h.1 (by simp)
  | item :: items, x :: xs, index, acc, hi, hd => by
    obtain ⟨mid, hmid, hi'⟩ := hstep acc index item x xs hi (hd.2 (item, x) (by simp))
    obtain ⟨out, hout, hfin⟩ := parseAll_complete step D I hstep (index := index + 1) hi'
      ⟨by simpa using hd.1, fun p hp => hd.2 p (by simp [hp])⟩
    exact ⟨out, by simp [parseAll, hmid, hout, bind, Except.bind], hfin⟩

theorem Decodes.withKeys {α : Type} {D : Json → α → Prop} {K : Json → Prop} {items : List Json}
    {ys : List α} (hk : ∀ item ∈ items, K item) (hd : Decodes D items ys) :
    Decodes (fun item y => K item ∧ D item y) items ys :=
  ⟨hd.1, fun p hp => ⟨hk p.1 (List.of_mem_zip hp).1, hd.2 p hp⟩⟩

/-- Completeness: `parseValue` accepts every value encoding a valid manifest, with exactly that
manifest, including the order and every field of each entry. -/
theorem parseValue_complete {value : Json} {m : Manifest} (hv : m.Valid) (he : Encodes value m) :
    parseValue value = .ok m := by
  obtain ⟨sv, lv, ev, hkeys, hschema, hs, hl, he', d1, d2, d3, k1, k2, k3⟩ := he
  obtain ⟨hne, hlibs, hexes, hsok, hlok, heok⟩ := hv
  have hsv : sv ≠ #[] := by
    intro h
    subst h
    have := d1.1
    simp only [List.length_nil] at this
    exact hne (Array.toList_eq_nil_iff.mp (List.length_eq_zero_iff.mp this.symm))
  have htop := topLevel_complete hkeys hschema hs hl he' hsv
  have hlibs : (m.surfaces.toList.map (·.library) ++
      m.excludedLibraries.toList.map (·.library)).Nodup := by
    simpa [libraries] using hlibs
  have hexes : (m.surfaces.toList.flatMap (·.executables.toList) ++
      m.excludedExecutables.toList.map (·.executable)).Nodup := by
    simpa [executables] using hexes
  -- Surfaces: the state holds exactly the accepted prefix of `m.surfaces`.
  obtain ⟨a1, h1, pre1, hpre1, hsurf1, hseen1, hsx1, hel1, hee1⟩ := parseAll_complete (acc := {}) (index := 0)
    parseSurface
    (fun item s => KeysAllowed item #["library", "executables", "claim", "execution", "rationale"] ∧
      SurfaceDecodes item s)
    (fun acc rest => ∃ pre, pre ++ rest = m.surfaces.toList ∧ acc.surfaces.toList = pre ∧
      acc.seen.toList = pre.map (·.library) ∧
      acc.seenExes.toList = pre.flatMap (·.executables.toList) ∧
      acc.excludedLibraries = #[] ∧ acc.excludedExecutables = #[])
    (fun acc index item s rest ⟨pre, hpre, hsurf, hseen, hsx, hel, hee⟩ ⟨hk, hd⟩ => by
      have hmem : s ∈ m.surfaces := by
        rw [← Array.mem_toList_iff, ← hpre]; simp
      have hl : (acc.seen.toList ++ s.library :: rest.map (·.library)).Nodup := by
        have := (List.nodup_append.mp hlibs).1
        rw [← hpre] at this
        simpa [hseen] using this
      have hx : (acc.seenExes.toList ++ s.executables.toList).Nodup := by
        have := (List.nodup_append.mp hexes).1
        rw [← hpre] at this
        simp only [List.flatMap_append, List.flatMap_cons] at this
        rw [hsx]
        exact (List.nodup_append.mp (by simpa only [List.append_assoc] using this)).1
      refine ⟨_, parseSurface_complete hk hd (hsok s hmem) (contains_false_of_nodup hl) hx,
        pre ++ [s], by simp [hpre], ?_, ?_, ?_, hel, hee⟩ <;>
        simp [Acc.addSurface, hsurf, hseen, hsx])
    ⟨[], rfl, rfl, rfl, rfl, rfl, rfl⟩
    (Decodes.withKeys (fun item hi => k1 item (by simpa using hi)) d1)
  simp only [List.append_nil] at hpre1
  subst hpre1
  have hs1 : a1.surfaces = m.surfaces := Array.toList_inj.mp hsurf1
  -- Excluded libraries: the surfaces stay fixed and the state holds the accepted prefix.
  obtain ⟨a2, h2, pre2, hpre2, hsurf2, hlib2, hseen2, hsx2, hee2⟩ :=
    parseAll_complete (index := 0) parseExcludedLibrary
    (fun item l => KeysAllowed item #["library", "rationale"] ∧ ExcludedLibraryDecodes item l)
    (fun acc rest => ∃ pre, pre ++ rest = m.excludedLibraries.toList ∧ acc.surfaces = m.surfaces ∧
      acc.excludedLibraries.toList = pre ∧
      acc.seen.toList = m.surfaces.toList.map (·.library) ++ pre.map (·.library) ∧
      acc.seenExes.toList = m.surfaces.toList.flatMap (·.executables.toList) ∧
      acc.excludedExecutables = #[])
    (fun acc index item l rest ⟨pre, hpre, hsurf, hlib, hseen, hsx, hee⟩ ⟨hk, hd⟩ => by
      have hmem : l ∈ m.excludedLibraries := by
        rw [← Array.mem_toList_iff, ← hpre]; simp
      have hl : (acc.seen.toList ++ l.library :: rest.map (·.library)).Nodup := by
        rw [← hpre] at hlibs
        simpa [hseen] using hlibs
      refine ⟨_, parseExcludedLibrary_complete hk hd (hlok l hmem) (contains_false_of_nodup hl),
        pre ++ [l], by simp [hpre], hsurf, ?_, ?_, hsx, hee⟩ <;>
        simp [Acc.addExcludedLibrary, hlib, hseen])
    ⟨[], rfl, hs1, by simp [hel1], by simp [hseen1], hsx1, hee1⟩
    (Decodes.withKeys (fun item hi => k2 item (by simpa using hi)) d2)
  simp only [List.append_nil] at hpre2
  subst hpre2
  -- Excluded executables: the other arrays stay fixed.
  obtain ⟨a3, h3, pre3, hpre3, hsurf3, hlib3, hexe3, hsx3⟩ :=
    parseAll_complete (index := 0) parseExcludedExecutable
    (fun item e => KeysAllowed item #["executable", "rationale"] ∧ ExcludedExecutableDecodes item e)
    (fun acc rest => ∃ pre, pre ++ rest = m.excludedExecutables.toList ∧ acc.surfaces = m.surfaces ∧
      acc.excludedLibraries = m.excludedLibraries ∧ acc.excludedExecutables.toList = pre ∧
      acc.seenExes.toList = m.surfaces.toList.flatMap (·.executables.toList) ++
        pre.map (·.executable))
    (fun acc index item e rest ⟨pre, hpre, hsurf, hlib, hexe, hsx⟩ ⟨hk, hd⟩ => by
      have hmem : e ∈ m.excludedExecutables := by
        rw [← Array.mem_toList_iff, ← hpre]; simp
      have hx : (acc.seenExes.toList ++ e.executable :: rest.map (·.executable)).Nodup := by
        rw [← hpre] at hexes
        simpa [hsx] using hexes
      refine ⟨_, parseExcludedExecutable_complete hk hd (heok e hmem)
        (contains_false_of_nodup hx), pre ++ [e], by simp [hpre], hsurf, hlib, ?_, ?_⟩ <;>
        simp [Acc.addExcludedExecutable, hexe, hsx])
    ⟨[], rfl, hsurf2, Array.toList_inj.mp hlib2, by simp [hee2], by simp [hsx2]⟩
    (Decodes.withKeys (fun item hi => k3 item (by simpa using hi)) d3)
  simp only [List.append_nil] at hpre3
  subst hpre3
  simp only [parseValue, htop, h1, h2, h3, bind, Except.bind, pure, Except.pure, Acc.manifest,
    hsurf3, hlib3, Array.toList_inj.mp hexe3]

/-- Exact characterization of the JSON value stage: it accepts `value` with `m` exactly when
`m` is valid and `value` encodes it. -/
theorem parseValue_ok {value : Json} {m : Manifest} :
    parseValue value = .ok m ↔ m.Valid ∧ Encodes value m :=
  ⟨fun h => ⟨parseValue_sound h, parseValue_input h⟩, fun ⟨hv, he⟩ => parseValue_complete hv he⟩

/-! Refusal classes. Each isolated defect, after an otherwise accepted prefix, yields exactly
its documented `manifest-malformed`, `manifest-schema` or `manifest-incomplete` message. -/

/-- A step refusing an item after an accepted prefix is the fold's refusal. -/
theorem parseAll_refuses (step : Acc → Nat → Json → Except String Acc) {item : Json}
    {rest : List Json} {msg : String} :
    ∀ {pre : List Json} {index : Nat} {acc mid : Acc}, parseAll step pre index acc = .ok mid →
      step mid (index + pre.length) item = .error msg →
      parseAll step (pre ++ item :: rest) index acc = .error msg
  | [], index, acc, mid, hpre, h => by
    simp only [parseAll, pure_eq_ok] at hpre
    subst hpre
    simp only [List.length_nil, Nat.add_zero] at h
    rw [List.nil_append, parseAll, h]
    rfl
  | x :: pre, index, acc, mid, hpre, h => by
    simp only [parseAll, bind_eq_ok] at hpre
    obtain ⟨next, hnext, hpre⟩ := hpre
    have h' : step mid (index + 1 + pre.length) item = .error msg := by
      rw [show index + 1 + pre.length = index + (x :: pre).length by
        simp only [List.length_cons]; omega]
      exact h
    rw [List.cons_append, parseAll, hnext]
    exact parseAll_refuses step hpre h'

theorem objectWithKeys_unknown {value : Json} {allowed : Array String} {location : String}
    {object : Std.TreeMap.Raw String Json compare} (hobj : value.getObj? = .ok object)
    (hunknown : object.keysArray.filter (!allowed.contains ·) ≠ #[]) :
    objectWithKeys value allowed location = .error
      s!"manifest-schema: {location} has unknown key(s): {repr (object.keysArray.filter (!allowed.contains ·)).toList}" := by
  have hne : (object.keysArray.filter (!allowed.contains ·)).isEmpty = false := by
    simpa [Array.isEmpty_iff] using hunknown
  unfold objectWithKeys
  simp only [hobj, bind, Except.bind, hne, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem parse_malformed {path text error : String}
    (h : Regula.Checker.PolicyCodec.parse text = .error error) :
    parse path text = .error s!"manifest-malformed: {path}: {error}" := by
  simp [parse, h, Except.mapError, bind, Except.bind]

/-- A top-level refusal of well-formed JSON is the refusal of `parse`. -/
theorem parse_topLevel_refuses {path text msg : String} {value : Json}
    (hvalue : Regula.Checker.PolicyCodec.parse text = .ok value) (h : topLevel value = .error msg) :
    parse path text = .error msg := by
  simp [parse, parseValue, hvalue, h, Except.mapError, bind, Except.bind]

/-- An unknown top-level key yields the `objectWithKeys_unknown` message. -/
theorem topLevel_unknownKey {value : Json} {msg : String}
    (h : objectWithKeys value #["schema-version", "surfaces", "excluded-libraries",
      "excluded-executables"] "top level" = .error msg) :
    topLevel value = .error msg := by
  unfold topLevel
  simp only [bind, Except.bind, h]

theorem topLevel_schemaVersion {value schema : Json}
    (hkeys : KeysAllowed value
      #["schema-version", "surfaces", "excluded-libraries", "excluded-executables"])
    (hschema : value.getObjVal? "schema-version" = .ok schema) (hv : schema ≠ Json.num 2) :
    topLevel value = .error "manifest-schema: schema-version must be exactly 2" := by
  have hv : schemaVersion2 schema = false := by
    cases h : schemaVersion2 schema
    · rfl
    · exact absurd (schemaVersion2_iff.mp h) hv
  simp [topLevel, objectWithKeys_complete hkeys, hschema, hv, bind, Except.bind,
    throw, throwThe, MonadExceptOf.throw]

theorem topLevel_emptySurfaces {value : Json} {lv ev : Array Json}
    (hkeys : KeysAllowed value
      #["schema-version", "surfaces", "excluded-libraries", "excluded-executables"])
    (hschema : value.getObjVal? "schema-version" = .ok (Json.num 2))
    (hs : value.getObjVal? "surfaces" = .ok (.arr #[]))
    (hl : value.getObjVal? "excluded-libraries" = .ok (.arr lv))
    (he : value.getObjVal? "excluded-executables" = .ok (.arr ev)) :
    topLevel value = .error "manifest-incomplete: surfaces must be a nonempty array" := by
  simp [topLevel, objectWithKeys_complete hkeys, hschema, schemaVersion2, hs, hl, he, bind, Except.bind,
    throw, throwThe, MonadExceptOf.throw]

/-- A refusal of one surface after accepted earlier surfaces is the refusal of `parse`. -/
theorem parse_surface_refuses {path text msg : String} {value : Json} {sv lv ev : Array Json}
    {pre rest : List Json} {item : Json} {acc : Acc}
    (hvalue : Regula.Checker.PolicyCodec.parse text = .ok value)
    (htop : topLevel value = .ok (sv, lv, ev)) (hsv : sv.toList = pre ++ item :: rest)
    (hpre : parseAll parseSurface pre 0 {} = .ok acc)
    (h : parseSurface acc pre.length item = .error msg) : parse path text = .error msg := by
  have hall := parseAll_refuses parseSurface (rest := rest) hpre (by simpa using h)
  simp [parse, parseValue, hvalue, htop, hsv, hall, Except.mapError, bind, Except.bind]

/-- An unknown surface key yields the `objectWithKeys_unknown` message. -/
theorem parseSurface_unknownKey {acc : Acc} {index : Nat} {item : Json} {msg : String}
    (h : objectWithKeys item #["library", "executables", "claim", "execution", "rationale"]
      s!"surfaces[{index}]" = .error msg) :
    parseSurface acc index item = .error msg := by
  unfold parseSurface
  simp only [bind, Except.bind, h]

/-- Every check `parseSurface` runs before decoding `execution` accepts the item. -/
def SurfacePrefixOK (acc : Acc) (index : Nat) (item : Json) : Prop :=
  let location := s!"surfaces[{index}]"
  objectWithKeys item #["library", "executables", "claim", "execution", "rationale"] location = .ok () ∧
  ∃ text library executables seenExes claim,
    stringField item "library" location = .ok text ∧
    targetName "library" text s!"{location}.library" = .ok library ∧
    acc.seen.contains library = false ∧
    surfaceExecutables item location = .ok executables ∧
    addExecutables location acc.seenExes executables.toList = .ok seenExes ∧
    surfaceClaim item location = .ok claim

theorem parseSurface_execution_refuses {acc : Acc} {index : Nat} {item : Json} {msg : String}
    (hp : SurfacePrefixOK acc index item)
    (h : surfaceExecution item s!"surfaces[{index}]" = .error msg) :
    parseSurface acc index item = .error msg := by
  obtain ⟨hkeys, text, library, executables, seenExes, claim, htext, hlib, hfresh, hexecs, hadd,
    hclaim⟩ := hp
  unfold parseSurface
  simp only [bind, Except.bind, hkeys, htext, hlib, fresh, hfresh, Bool.false_eq_true, ↓reduceIte,
    pure, Except.pure, hexecs, hadd, hclaim, h]

theorem surfaceExecution_unknown {item : Json} {location text : String}
    (hfield : item.getObjVal? "execution" = .ok (.str text)) (hparse : ExecutionClaim.parse? text = none) :
    surfaceExecution item location =
      .error s!"manifest-schema: {location}.execution must be \"report\" or \"checked\"" := by
  simp [surfaceExecution, hfield, hparse, throw, throwThe, MonadExceptOf.throw]

theorem surfaceExecution_nonString {item field : Json} {location : String}
    (hfield : item.getObjVal? "execution" = .ok field) (hnot : ∀ text, field ≠ .str text) :
    surfaceExecution item location = .error s!"manifest-schema: {location}.execution must be a string" := by
  unfold surfaceExecution
  split
  · rename_i e he; simp [hfield] at he
  · rename_i text htext; exact absurd (Except.ok.inj (hfield.symm.trans htext)) (hnot text)
  · simp [throw, throwThe, MonadExceptOf.throw]

/-- Reads and parses the manifest file at `path`, failing with `manifest-missing` when it does not
exist. -/
def load (path : FilePath) : IO Manifest := do
  if !(← path.pathExists) then
    throw <| IO.userError s!"manifest-missing: {path}"
  IO.ofExcept (parse path.toString (← IO.FS.readFile path))

/-- The Lake targets a checker must build so every claimed module is
elaborated and resolvable: each claimed library and claimed executable. -/
def positiveTargets (manifest : Manifest) : Array String :=
  manifest.surfaces.foldl
    (fun targets surface => targets.push surface.library ++ surface.executables) #[]

/-- The actual manifest's `claimed` surfaces, with every other actual library and executable
excluded. Both name sets equal the actual manifest's by construction. -/
def structuralManifest (actual : Manifest) (claimed : Array String) : Manifest :=
  let surfaces := actual.surfaces.filter (claimed.contains ·.library)
  let claimedLibs := surfaces.map (·.library)
  let claimedExes := surfaces.flatMap (·.executables)
  { surfaces
    excludedLibraries := (libraries actual).filter (!claimedLibs.contains ·) |>.map
      fun library => ⟨library, "structural control: excluded"⟩
    excludedExecutables := (executables actual).filter (!claimedExes.contains ·) |>.map
      fun executable => ⟨executable, "structural control: excluded"⟩ }

private theorem filter_split {xs ys : Array String} (hsub : ∀ x ∈ xs, x ∈ ys) (x : String) :
    x ∈ xs ++ ys.filter (fun y => !xs.contains y) ↔ x ∈ ys := by
  simp only [Array.mem_append, Array.mem_filter, Bool.not_eq_true']
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact hsub x h
    · exact h
  · intro h
    by_cases hx : x ∈ xs
    · exact Or.inl hx
    · exact Or.inr ⟨h, by simpa [Array.contains_iff_mem] using hx⟩

/-- A duplicate-free prefix followed by the rest of a duplicate-free array is duplicate-free. -/
private theorem filter_split_nodup {xs ys : Array String} (hxs : xs.toList.Nodup)
    (hys : ys.toList.Nodup) : (xs ++ ys.filter (fun y => !xs.contains y)).toList.Nodup := by
  simp only [Array.toList_append, Array.toList_filter]
  refine List.nodup_append.mpr ⟨hxs, hys.filter _, ?_⟩
  intro a ha b hb hab
  subst hab
  simp only [List.mem_filter, Bool.not_eq_true'] at hb
  have : xs.contains a = true := by simpa [Array.contains_iff_mem] using ha
  simp_all

private theorem flatMap_filter_sublist {α β : Type} (p : α → Bool) (f : α → List β) :
    ∀ l : List α, ((l.filter p).flatMap f).Sublist (l.flatMap f)
  | [] => by simp
  | x :: xs => by
    have ih := flatMap_filter_sublist p f xs
    by_cases h : p x
    · simpa [List.filter_cons, h] using ih.append_left (f x)
    · simpa [List.filter_cons, h] using ih.trans (List.sublist_append_right (f x) _)

/-- The copy's libraries: its claimed surfaces' libraries, then every other actual library. -/
theorem libraries_structuralManifest (actual : Manifest) (claimed : Array String) :
    libraries (structuralManifest actual claimed) =
      (actual.surfaces.filter (claimed.contains ·.library)).map (·.library) ++
        (libraries actual).filter (fun y =>
          !((actual.surfaces.filter (claimed.contains ·.library)).map (·.library)).contains y) := by
  simp only [structuralManifest, libraries, Array.map_map]
  congr 1
  ext1 <;> simp [Function.comp_def]

/-- The copy's executables: its claimed surfaces' executables, then every other actual one. -/
theorem executables_structuralManifest (actual : Manifest) (claimed : Array String) :
    executables (structuralManifest actual claimed) =
      (actual.surfaces.filter (claimed.contains ·.library)).flatMap (·.executables) ++
        (executables actual).filter (fun y =>
          !((actual.surfaces.filter (claimed.contains ·.library)).flatMap (·.executables)).contains y) := by
  simp only [structuralManifest, executables, Array.map_map]
  congr 1
  ext1 <;> simp [Function.comp_def]

/-- Every actual library is classified in the copy, and the copy names no other library. -/
theorem structural_libraries (actual : Manifest) (claimed : Array String) (l : String) :
    l ∈ libraries (structuralManifest actual claimed) ↔ l ∈ libraries actual := by
  have hsub : ∀ x ∈ (actual.surfaces.filter (claimed.contains ·.library)).map (·.library),
      x ∈ libraries actual := by
    intro x hx
    simp only [Array.mem_map, Array.mem_filter] at hx
    obtain ⟨s, ⟨hs, -⟩, rfl⟩ := hx
    exact Array.mem_append_left _ (Array.mem_map_of_mem hs)
  rw [libraries_structuralManifest]
  exact filter_split hsub l

/-- Every actual executable is classified in the copy, and the copy names no other executable. -/
theorem structural_executables (actual : Manifest) (claimed : Array String) (e : String) :
    e ∈ executables (structuralManifest actual claimed) ↔ e ∈ executables actual := by
  have hsub : ∀ x ∈ (actual.surfaces.filter (claimed.contains ·.library)).flatMap (·.executables),
      x ∈ executables actual := by
    intro x hx
    simp only [Array.mem_flatMap, Array.mem_filter] at hx
    obtain ⟨s, ⟨hs, -⟩, hx⟩ := hx
    exact Array.mem_append_left _ (Array.mem_flatMap.mpr ⟨s, hs, hx⟩)
  rw [executables_structuralManifest]
  exact filter_split hsub e

/-- A slice whose first character is not whitespace has a nonblank ASCII trim. -/
theorem trimAscii_isEmpty_eq_false {u : String.Slice} (h : u.startPos ≠ u.endPos)
    (hc : (u.startPos.get h).isWhitespace = false) : u.trimAscii.isEmpty = false := by
  have hskip : u.startPos.skipWhile Char.isWhitespace = u.startPos :=
    String.Slice.Pos.skipWhile_bool_eq_self_iff_get.mpr fun _ => hc
  have hstart : u.trimAsciiStart = u := by
    simp only [String.Slice.trimAsciiStart, String.Slice.dropWhile, String.Slice.skipPrefixWhile,
      hskip, String.Slice.sliceFrom_startPos]
  rw [String.Slice.trimAscii, hstart, String.Slice.trimAsciiEnd, String.Slice.dropEndWhile]
  refine String.Slice.isEmpty_sliceTo_eq_false_iff.mpr fun hsuf => ?_
  have := String.Slice.apply_eq_true_of_skipSuffixWhile_le_bool (p := Char.isWhitespace)
    (pos := u.startPos) (by rw [hsuf]; exact Std.le_refl _) ((String.Slice.Pos.lt_endPos_iff _).mpr h)
  simp [hc] at this

/-- The copy of a valid manifest is valid whenever it claims at least one actual surface. -/
theorem structuralManifest_valid {actual : Manifest} {claimed : Array String} (hv : actual.Valid)
    (hne : actual.surfaces.filter (claimed.contains ·.library) ≠ #[]) :
    (structuralManifest actual claimed).Valid := by
  obtain ⟨-, hlibs, hexes, hsok, hlok, heok⟩ := hv
  have hlibName : ∀ l ∈ libraries actual, TargetName l := by
    intro l hl
    simp only [libraries, Array.mem_append, Array.mem_map] at hl
    rcases hl with ⟨s, hs, rfl⟩ | ⟨x, hx, rfl⟩
    · exact (hsok s hs).1
    · exact (hlok x hx).1
  have hexeName : ∀ e ∈ executables actual, TargetName e := by
    intro e he
    simp only [executables, Array.mem_append, Array.mem_flatMap, Array.mem_map] at he
    rcases he with ⟨s, hs, he⟩ | ⟨x, hx, rfl⟩
    · exact (hsok s hs).2.1 e he
    · exact (heok x hx).1
  have hwhy : "structural control: excluded".trimAscii.isEmpty = false :=
    trimAscii_isEmpty_eq_false (by decide) (by decide)
  refine ⟨hne, ?_, ?_, ?_, ?_, ?_⟩
  · rw [libraries_structuralManifest]
    refine filter_split_nodup (List.Nodup.sublist ?_ hlibs) hlibs
    simp only [libraries, Array.toList_map, Array.toList_filter, Array.toList_append]
    exact ((List.filter_sublist).map _).trans (List.sublist_append_left _ _)
  · rw [executables_structuralManifest]
    refine filter_split_nodup (List.Nodup.sublist ?_ hexes) hexes
    simp only [executables, Array.toList_flatMap, Array.toList_filter, Array.toList_append,
      Array.toList_map]
    exact (flatMap_filter_sublist _ _ _).trans (List.sublist_append_left _ _)
  · intro s hs
    exact hsok s (Array.mem_filter.mp hs).1
  · intro l hl
    simp only [structuralManifest, Array.mem_map, Array.mem_filter] at hl
    obtain ⟨library, ⟨hl, -⟩, rfl⟩ := hl
    exact ⟨hlibName library hl, hwhy⟩
  · intro e he
    simp only [structuralManifest, Array.mem_map, Array.mem_filter] at he
    obtain ⟨executable, ⟨he, -⟩, rfl⟩ := he
    exact ⟨hexeName executable he, hwhy⟩

/-- One surface in the checker's own JSON schema. -/
def surfaceJson (s : Surface) : Json :=
  Json.mkObj [
    ("library", .str s.library), ("executables", Json.arr (s.executables.map .str)),
    ("claim", .str s.claim.toString), ("execution", .str (ExecutionClaim.toString s.execution)),
    ("rationale", .str s.rationale)]

/-- One excluded library in the checker's own JSON schema. -/
def excludedLibraryJson (l : ExcludedLibrary) : Json :=
  Json.mkObj [("library", .str l.library), ("rationale", .str l.rationale)]

/-- One excluded executable in the checker's own JSON schema. -/
def excludedExecutableJson (e : ExcludedExecutable) : Json :=
  Json.mkObj [("executable", .str e.executable), ("rationale", .str e.rationale)]

/-- The manifest in the checker's own JSON schema; `parse` reads exactly these keys. -/
def toJson (m : Manifest) : Json :=
  Json.mkObj [
    ("schema-version", Json.num 2),
    ("surfaces", Json.arr (m.surfaces.map surfaceJson)),
    ("excluded-libraries", Json.arr (m.excludedLibraries.map excludedLibraryJson)),
    ("excluded-executables", Json.arr (m.excludedExecutables.map excludedExecutableJson))]

/-! Round trip. `toJson` encodes every manifest, so the JSON value stage of the executed `parse`
recovers exactly the valid ones (`parseValue_toJson`). The text stage is not covered:
`Json.compress` is `partial` and `PolicyCodec.parse` runs core `partial` parsers, so no Lean
theorem can state their behaviour; `parse_of_encodes` names what they must deliver. -/

theorem keysAllowed_of_keys {value : Json} {object : Std.TreeMap.Raw String Json compare}
    {keys allowed : Array String} (hobj : value.getObj? = .ok object) (hkeys : object.keysArray = keys)
    (h : ∀ key ∈ keys, key ∈ allowed) : KeysAllowed value allowed :=
  ⟨object, hobj, hkeys ▸ h⟩

theorem Decodes.map {α : Type} {D : Json → α → Prop} {f : α → Json} :
    ∀ {xs : List α}, (∀ x ∈ xs, D (f x) x) → Decodes D (xs.map f) xs
  | [], _ => ⟨rfl, by simp⟩
  | x :: xs, h => by
    obtain ⟨-, hall⟩ := Decodes.map (xs := xs) (fun y hy => h y (by simp [hy]))
    refine ⟨by simp, fun p hp => ?_⟩
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact h x (by simp)
    · exact hall p hp

/-- `toJson m` encodes `m` for every manifest, valid or not. -/
theorem toJson_encodes (m : Manifest) : Encodes (toJson m) m := by
  refine ⟨m.surfaces.map surfaceJson, m.excludedLibraries.map excludedLibraryJson,
    m.excludedExecutables.map excludedExecutableJson,
    keysAllowed_of_keys (keys := #["excluded-executables", "excluded-libraries", "schema-version",
      "surfaces"]) rfl rfl (by simp), rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Array.toList_map]
    exact Decodes.map fun s _ => ⟨rfl, .inr rfl, ⟨_, rfl, (Profile.parse?_eq_some_iff _ _).mpr rfl⟩,
      .inr ⟨_, rfl, RegulaPolicy.ExecutionClaim.roundtrip _⟩, rfl⟩
  · rw [Array.toList_map]
    exact Decodes.map fun _ _ => ⟨rfl, rfl⟩
  · rw [Array.toList_map]
    exact Decodes.map fun _ _ => ⟨rfl, rfl⟩
  · intro item hi
    obtain ⟨s, -, rfl⟩ := Array.mem_map.mp hi
    exact keysAllowed_of_keys (keys := #["claim", "executables", "execution", "library", "rationale"])
      rfl rfl (by simp)
  · intro item hi
    obtain ⟨l, -, rfl⟩ := Array.mem_map.mp hi
    exact keysAllowed_of_keys (keys := #["library", "rationale"]) rfl rfl (by simp)
  · intro item hi
    obtain ⟨e, -, rfl⟩ := Array.mem_map.mp hi
    exact keysAllowed_of_keys (keys := #["executable", "rationale"]) rfl rfl (by simp)

/-- Round trip at the `Json` value boundary: the value stage of the executed `parse` returns
`m` from `toJson m` exactly when `m` is valid, so surfaces, excluded libraries and excluded
executables come back with their order, fields and rationales. -/
theorem parseValue_toJson {m : Manifest} : parseValue (toJson m) = .ok m ↔ m.Valid :=
  ⟨parseValue_sound, fun hv => parseValue_complete hv (toJson_encodes m)⟩

/-- The text boundary, conditionally: whenever the text parser returns a value that encodes a
valid `m` (as `toJson m` does), the executed `parse` returns exactly `m`. -/
theorem parse_of_encodes {path text : String} {value : Json} {m : Manifest}
    (hvalue : Regula.Checker.PolicyCodec.parse text = .ok value) (he : Encodes value m)
    (hv : m.Valid) : parse path text = .ok m :=
  parse_ok.mpr ⟨value, hvalue, parseValue_complete hv he⟩

/-- What the structural gate reads: for any manifest the executed `parse` accepted, the JSON value
stage recovers the in-memory structural copy exactly from its `toJson` whenever the copy claims
an actual surface (the guard `structuralBase` runs before building it). -/
theorem structural_roundtrip {path text : String} {actual : Manifest} {claimed : Array String}
    (h : parse path text = .ok actual)
    (hne : actual.surfaces.filter (claimed.contains ·.library) ≠ #[]) :
    parseValue (toJson (structuralManifest actual claimed)) = .ok (structuralManifest actual claimed) :=
  parseValue_toJson.mpr (structuralManifest_valid (parse_sound h) hne)

end Regula.Checker.Manifest

-- Exact dependency ceiling for the manifest-parser guarantees: Standard-Logical.
run_cmd do
  for name in #[``Regula.Checker.Manifest.parse_sound, ``Regula.Checker.Manifest.parse_input,
      ``Regula.Checker.Manifest.parse_emptyExclusions, ``Regula.Checker.Manifest.parse_malformed,
      ``Regula.Checker.Manifest.parse_topLevel_refuses, ``Regula.Checker.Manifest.topLevel_unknownKey,
      ``Regula.Checker.Manifest.objectWithKeys_unknown,
      ``Regula.Checker.Manifest.topLevel_schemaVersion,
      ``Regula.Checker.Manifest.topLevel_emptySurfaces,
      ``Regula.Checker.Manifest.parse_surface_refuses,
      ``Regula.Checker.Manifest.parseSurface_unknownKey,
      ``Regula.Checker.Manifest.parseSurface_execution_refuses,
      ``Regula.Checker.Manifest.surfaceExecution_unknown,
      ``Regula.Checker.Manifest.surfaceExecution_nonString,
      ``Regula.Checker.Manifest.structural_libraries,
      ``Regula.Checker.Manifest.structural_executables,
      ``Regula.Checker.Manifest.parse_ok, ``Regula.Checker.Manifest.parseValue_ok,
      ``Regula.Checker.Manifest.parseValue_complete, ``Regula.Checker.Manifest.toJson_encodes,
      ``Regula.Checker.Manifest.parseValue_toJson, ``Regula.Checker.Manifest.parse_of_encodes,
      ``Regula.Checker.Manifest.structuralManifest_valid,
      ``Regula.Checker.Manifest.structural_roundtrip] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun ax => #[`propext, `Quot.sound, `Classical.choice].contains ax) do
      throwError "manifest theorem {name} exceeds Standard-Logical: {axioms}"
