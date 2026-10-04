import RegulaProvision
import Regula.Contract
import Regula.Decision

/-! # Decision contracts of local provisioning

The decision kind of each pure decision `RegulaProvision` runs, with its `@[regula_decision]`
registration. The provisioning program imports only the toolchain, because `scripts/provision.sh`
runs it with `lean --run` before the package is built. This second module of its library imports
it together with the two checker interfaces, and nothing the program runs imports this module.
Each kind restates a theorem of the program about the same definition, or for `component?`
follows from its definition, and adds the witnesses a kind requires. -/
namespace RegulaProvision

/-- `buildMode?` accepts only the spelling of a build mode (`buildMode?_sound`), and it accepts
`source`. That it accepts every spelling is not claimed. -/
theorem checked_buildMode : Regula.ExecutableContract buildMode?
    (Regula.DecidesSoundly (·.isSome = true)
      (fun text => ∃ mode : BuildMode, mode.spelling = text)) :=
  ⟨{ sound := fun text accepted => by
       cases parsed : buildMode? text with
       | some mode => exact ⟨mode, buildMode?_sound text mode parsed⟩
       | none => rw [parsed] at accepted; exact absurd accepted Bool.false_ne_true
     accepted := ⟨"source", by decide⟩ }⟩

/-- `component?` accepts exactly a text that passes `isComponent`: it accepts `a` and refuses the
empty text. That the admitted component is that text is in its definition, not in the kind. -/
theorem checked_component : Regula.ExecutableContract component?
    (Regula.Decides (·.isSome = true) (fun text => isComponent text = true)) :=
  have admitted (text : String) : (component? text).isSome = true ↔ isComponent text = true := by
    by_cases passes : isComponent text = true <;> simp [component?, passes]
  ⟨.of_iff admitted ⟨"a", (admitted "a").mpr (by simp [isComponent])⟩
    ⟨"", fun accepted => absurd ((admitted "").mp accepted) (by decide)⟩⟩

/-- `resumes` accepts exactly a source-mode stage whose observed inputs are the expected ones
(`resumes_iff`): it accepts equal inputs in source mode and refuses them in upstream-cache mode. -/
theorem checked_resumes : Regula.ExecutableContract resumes (fun resume =>
    Regula.Decides (· = true)
      (fun input : (BuildMode × StageInputs) × StageInputs =>
        input.1.1 = .source ∧ input.1.2 = input.2)
      (Function.uncurry (Function.uncurry resume))) :=
  let inputs : StageInputs :=
    { artifactPolicy := 0, configuration := "", manifest := "", toolchain := "", source := "" }
  ⟨.of_iff (fun input => resumes_iff input.1.1 input.1.2 input.2)
    ⟨((.source, inputs), inputs), (resumes_iff _ _ _).mpr ⟨rfl, rfl⟩⟩
    ⟨((.upstreamCache, inputs), inputs), fun accepted =>
      nomatch ((resumes_iff .upstreamCache inputs inputs).mp accepted).1⟩⟩

/-- What `admits_sound` establishes of an admitted receipt: it records the requested Mathlib
revision, compiler commit, artifact mode and generated import module, a source-mode receipt
records the current artifact policy, and it holds no package at another revision than a pin of
the same name. -/
def Admitted (receipt : Receipt) (mode : BuildMode) (mathlibRev githash : String)
    (pins : Array Pin) (source : String) : Prop :=
  receipt.mathlibRev = mathlibRev ∧ receipt.leanGithash = githash ∧ receipt.mode = mode ∧
    (mode = .source → receipt.artifactPolicy = sourceArtifactPolicy) ∧
    receipt.source = source ∧
    ∀ pin ∈ pins, ∀ held ∈ receipt.packages, held.name = pin.name → held.rev = pin.rev

/-- `admits` accepts only a receipt that is `Admitted` for the request (`admits_sound`), and it
accepts an upstream-cache receipt for the request it records. That it accepts every such receipt
is not claimed: the receipt's schema version is checked as well. -/
theorem checked_admits : Regula.ExecutableContract @admits
    (fun (admission : Receipt → BuildMode → String → String → Array Pin → String → Bool) =>
    Regula.DecidesSoundly (· = true)
      (fun input : ((((Receipt × BuildMode) × String) × String) × Array Pin) × String =>
        Admitted input.1.1.1.1.1 input.1.1.1.1.2 input.1.1.1.2 input.1.1.2 input.1.2 input.2)
      (Function.uncurry (Function.uncurry (Function.uncurry (Function.uncurry
        (Function.uncurry admission)))))) :=
  ⟨{ sound := fun input accepted =>
       admits_sound input.1.1.1.1.1 input.1.1.1.1.2 input.1.1.1.2 input.1.1.2 input.1.2 input.2
         accepted
     accepted := ⟨((((({ schemaVersion := receiptSchema, mathlibRev := "", leanGithash := "",
                         leanVersion := "", packages := #[] }, .upstreamCache), ""), ""), #[]),
                    ""), by simp [Function.uncurry, admits, receiptSchema]⟩ }⟩

/-- `mathlibStep` keeps the path exactly when it already links the shared checkout
(`mathlibStep_keep_iff`): it keeps a link to the target and does not keep an absent path. -/
theorem checked_mathlibStep : Regula.ExecutableContract mathlibStep (fun step =>
    Regula.Decides (· = Step.keep)
      (fun input : String × Observed => input.2 = .link input.1)
      (Function.uncurry step)) :=
  ⟨.of_iff (fun input => mathlibStep_keep_iff input.1 input.2)
    ⟨("", .link ""), (mathlibStep_keep_iff _ _).mpr rfl⟩
    ⟨("", .absent), fun accepted => nomatch (mathlibStep_keep_iff "" .absent).mp accepted⟩⟩

/-- `cloneStep` replaces only a link or a clean Git checkout (`cloneStep_replace`), and it
replaces a link. That it replaces every link and clean checkout is not claimed: a clean checkout
at the pinned revision is kept. -/
theorem checked_cloneStep : Regula.ExecutableContract cloneStep (fun step =>
    Regula.DecidesSoundly (· = Step.replace)
      (fun input : String × Observed =>
        (∃ resolved, input.2 = .link resolved) ∨ ∃ head, input.2 = .directory (some head) true)
      (Function.uncurry step)) :=
  ⟨{ sound := fun input replaced => cloneStep_replace input.1 input.2 replaced
     accepted := ⟨("", .link ""), rfl⟩ }⟩

/-- `found` identifies a directory as shared or being removed only when its receipt names it
(`found_identified`), and it identifies the directory named by a receipt's key. That it
identifies every directory a receipt names is not claimed. -/
theorem checked_found : Regula.ExecutableContract found (fun identify =>
    Regula.DecidesSoundly (· ≠ Found.foreign)
      (fun input : String × Option Receipt =>
        ∃ receipt, input.2 = some receipt ∧
          (input.1 = receipt.key ∨ input.1.startsWith (removingPrefix receipt.key) = true))
      (Function.uncurry identify)) :=
  ⟨{ sound := fun input identified => found_identified input.1 input.2 identified
     accepted := by
       let receipt : Receipt :=
         { schemaVersion := receiptSchema, mathlibRev := "", leanGithash := "", leanVersion := ""
           packages := #[] }
       exact ⟨(receipt.key, some receipt), by simp [Function.uncurry, found]⟩ }⟩

/-- `prunes` removes only a directory that is not the current one and that no registered copy
still links (`prunes_sound`), and it removes another directory with no registered copy. That it
removes every such directory is not claimed. -/
theorem checked_prunes : Regula.ExecutableContract prunes (fun removes =>
    Regula.DecidesSoundly (· = true)
      (fun input : (String × String) × Array (String × Bool) =>
        input.1.2 ≠ input.1.1 ∧ ∀ copy ∈ input.2, copy.2 = false)
      (Function.uncurry (Function.uncurry removes))) :=
  ⟨{ sound := fun input removed => prunes_sound input.1.1 input.1.2 input.2 removed
     accepted := ⟨(("current", "other"), #[]), by simp [Function.uncurry, prunes]⟩ }⟩

attribute [regula_decision]
  buildMode? component? resumes admits mathlibStep cloneStep found prunes

end RegulaProvision
