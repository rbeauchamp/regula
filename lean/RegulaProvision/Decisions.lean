import RegulaProvision
import Regula.Contract
import Regula.Decision

/-! # Decision contracts of local provisioning

The decision kind of each pure decision `RegulaProvision` runs, with its `@[regula_decision]`
registration. The provisioning program imports only the toolchain, because `scripts/provision.sh`
runs it with `lean --run` before the package is built. This second module of its library imports
it together with the two checker interfaces, and nothing the program runs imports this module.
Each kind restates a theorem of the program about the same definition, or for `component?`
follows from its definition and `isComponent_iff` and for `selectPins` from its definition and
`selectPins_sound` (`selectPins_shares_iff`), and adds the witnesses a kind requires. -/
namespace RegulaProvision

/-- One path component that is not hidden and has no separator, stated over the text and its
characters: the text is not empty, it is not a period and then a rest, and each of its
characters is an ASCII letter or digit (Lean's own `Char.isAlphanum`), `-`, `_` or `.`. The
statement has no test of `isComponent`, which decides it (`isComponent_iff`). -/
def IsComponent (text : String) : Prop :=
  text ≠ "" ∧ (∀ rest, text ≠ "." ++ rest) ∧
    ∀ c ∈ text.toList, c.isAlphanum = true ∨ c = '-' ∨ c = '_' ∨ c = '.'

/-- A text does not start with a period exactly when it is not a period and then a rest. -/
private theorem not_hidden_iff (text : String) :
    text.startsWith "." = false ↔ ∀ rest, text ≠ "." ++ rest := by
  rw [String.startsWith_string_eq_false_iff]
  constructor
  · rintro shown rest rfl
    exact shown ⟨rest.toList, by simp⟩
  · rintro shown ⟨rest, split⟩
    exact shown (String.ofList rest) (by rw [← String.toList_inj]; simp [← split])

/-- The executed test accepts exactly the path components. -/
theorem isComponent_iff (text : String) : isComponent text = true ↔ IsComponent text := by
  simp only [isComponent, IsComponent, Bool.and_eq_true, Bool.not_eq_true',
    String.isEmpty_eq_false_iff, not_hidden_iff, String.all_bool_eq, List.all_eq_true,
    Bool.or_eq_true, beq_iff_eq, and_assoc, or_assoc]

/-- `component?` accepts exactly a path component (`IsComponent`): it accepts `a` and refuses the
empty text. That the admitted component is that text is in its definition, not in the kind. -/
theorem checked_component : Regula.ExecutableContract component?
    (Regula.Decides (·.isSome = true) IsComponent) :=
  have admitted (text : String) : (component? text).isSome = true ↔ IsComponent text := by
    rw [← isComponent_iff]
    by_cases passes : isComponent text = true <;> simp [component?, passes]
  ⟨.of_iff admitted
    ⟨"a", (admitted "a").mpr ((isComponent_iff "a").mp (by simp [isComponent]))⟩
    ⟨"", fun accepted =>
      absurd ((isComponent_iff "").mpr ((admitted "").mp accepted)) (by decide)⟩⟩

/-- What receipt admission establishes about the exact stable store and compatible pins. -/
def Admitted (receipt : Receipt) (mathlibRev githash : String) (pins : Array Pin) : Prop :=
  receipt.mathlibRev = mathlibRev ∧ receipt.leanGithash = githash ∧
    receipt.artifactPolicy = 0 ∧ receipt.source = "" ∧
    ∀ pin ∈ pins, ∀ held ∈ receipt.packages, held.name = pin.name → held.rev = pin.rev

/-- Admission is sound for its requested revisions and accepts a matching stable receipt. -/
theorem checked_admits : Regula.ExecutableContract @admits
    (fun (admission : Receipt → String → String → Array Pin → Bool) =>
    Regula.DecidesSoundly (· = true)
      (fun input : ((Receipt × String) × String) × Array Pin =>
        Admitted input.1.1.1 input.1.1.2 input.1.2 input.2)
      (Function.uncurry (Function.uncurry (Function.uncurry admission)))) :=
  ⟨{ sound := fun input accepted =>
       admits_sound input.1.1.1 input.1.1.2 input.1.2 input.2 accepted
     accepted := ⟨((({ schemaVersion := receiptSchema, mathlibRev := "", leanGithash := "", leanVersion := "", packages := #[] }, ""), ""), #[]),
       by simp [Function.uncurry, admits, receiptSchema]⟩ }⟩

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

/-- The integration preflight accepts equal selectors and refuses different ones. -/
theorem checked_mathlibApplies : Regula.ExecutableContract mathlibApplies (fun applies =>
    Regula.Decides (· = true) (fun input : String × String => input.1 = input.2)
      (Function.uncurry applies)) :=
  ⟨.of_iff (fun input => mathlibApplies_iff input.1 input.2)
    ⟨("", ""), (mathlibApplies_iff _ _).mpr rfl⟩
    ⟨("a", "b"), fun accepted => by
      have same := (mathlibApplies_iff "a" "b").mp accepted
      simp at same⟩⟩

/-- `retires` removes exactly a registered link that still links its shared directory, is the
copy's retired link and is not the link the run provisions (`retires_iff`): it removes such a
link and keeps the link the run provisions. -/
theorem checked_retires : Regula.ExecutableContract retires (fun removes =>
    Regula.Decides (· = true)
      (fun input : ((String × String) × String) × Bool =>
        input.2 = true ∧ input.1.2 = input.1.1.2 ∧ input.1.2 ≠ input.1.1.1)
      (Function.uncurry (Function.uncurry (Function.uncurry removes)))) :=
  ⟨.of_iff (fun input => retires_iff input.1.1.1 input.1.1.2 input.1.2 input.2)
    ⟨((("new", "old"), "old"), true),
      (retires_iff "new" "old" "old" true).mpr ⟨rfl, rfl, by decide⟩⟩
    ⟨((("new", "new"), "new"), true), fun accepted =>
      ((retires_iff "new" "new" "new" true).mp accepted).2.2 rfl⟩⟩

/-- A full Git commit name, stated over the text and its characters: forty characters, each a
decimal digit (Lean's own `Char.isDigit`) or a lowercase letter from `a` to `f`. The statement has
no test of `isObjectName`, which decides it (`isObjectName_iff`). -/
def IsObjectName (text : String) : Prop :=
  text.length = 40 ∧ ∀ c ∈ text.toList, c.isDigit = true ∨ ('a' ≤ c ∧ c ≤ 'f')

/-- The executed test accepts exactly the full commit names. -/
theorem isObjectName_iff (text : String) : isObjectName text = true ↔ IsObjectName text := by
  simp only [isObjectName, IsObjectName, Bool.and_eq_true, beq_iff_eq, String.all_bool_eq,
    List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq]

/-- Text that the shared workspace's configuration can quote: no character of it is a quotation
mark, a backslash or a line feed. -/
def Quotable (text : String) : Prop :=
  ∀ c ∈ text.toList, c ≠ '"' ∧ c ≠ '\\' ∧ c ≠ '\n'

/-- A Git entry that names a subdirectory of its checkout. -/
def InSubdirectory (entry : Lake.PackageEntry) : Prop :=
  ∃ url rev inputRev dir, entry.src = .git url rev inputRev (some dir)

/-- The executed test accepts exactly the Git entries that name a subdirectory. -/
theorem inSubdirectory_iff (entry : Lake.PackageEntry) :
    inSubdirectory entry = true ↔ InSubdirectory entry := by
  unfold inSubdirectory InSubdirectory
  split <;> simp_all

/-- Git pins that the shared workspace can hold, with Mathlib pinned at `rev` from `url`: no pin
names a subdirectory, the revision is a full commit name, the URL can be quoted, and the names of
the checkout directories are path components, no two of them the same. -/
def PinsAdmissible (url rev : String) (git : Array (Lake.PackageEntry × Pin)) : Prop :=
  (∀ pin ∈ git, ¬InSubdirectory pin.1) ∧ IsObjectName rev ∧ Quotable url ∧
    (∀ pin ∈ git, IsComponent pin.2.name) ∧ (git.toList.map (·.2.name)).Nodup

/-- `pinsRefusal` refuses nothing exactly for admissible pins. -/
theorem pinsRefusal_eq_none_iff (url rev : String) (git : Array (Lake.PackageEntry × Pin)) :
    pinsRefusal url rev git = none ↔ PinsAdmissible url rev git := by
  have hSub : (∀ pin ∈ git, ¬InSubdirectory pin.1) ↔
      git.find? (inSubdirectory ·.1) = none := by
    simp [Array.find?_eq_none, inSubdirectory_iff]
  have hComp : (∀ pin ∈ git, IsComponent pin.2.name) ↔
      git.find? (!isComponent ·.2.name) = none := by
    simp [Array.find?_eq_none, isComponent_iff]
  have hUrl : (url.all fun c => c != '"' && c != '\\' && c != '\n') = true ↔ Quotable url := by
    simp [Quotable, String.all_bool_eq, List.all_eq_true, and_assoc]
  rw [PinsAdmissible, hSub, hComp, ← isObjectName_iff, ← hUrl]
  unfold pinsRefusal
  cases h1 : git.find? (inSubdirectory ·.1) with
  | some found => simp
  | none =>
    cases h2 : isObjectName rev <;>
      cases h3 : (url.all fun c => c != '"' && c != '\\' && c != '\n') <;>
      cases h4 : git.find? (!isComponent ·.2.name) <;> simp_all

/-- What an admitted pin set establishes of the Mathlib package's manifest, the entries of its
package overrides file and whether the entry selected for `regula` is Regula's own integration
entry (`readOwnRegula`), over the entries that Lake selects (`rootEntries`, `selectedEntry`): the
manifest records a packages directory; each selected path entry is the one for `regula`, and it is
Regula's own; the entry selected for `mathlib` is a Git entry, and the Git pins are admissible
(`PinsAdmissible`). -/
def Shareable (input : (Lake.Manifest × Array Lake.PackageEntry) × Bool) : Prop :=
  input.1.1.packagesDir? ≠ none ∧
    (∀ entry dir, selectedEntry (rootEntries input.1.1 input.1.2) entry.name = some entry →
      entry.src = .path dir → entry.name = `regula ∧ input.2 = true) ∧
    ∃ entry url rev inputRev subDir,
      selectedEntry (rootEntries input.1.1 input.1.2) `mathlib = some entry ∧
        entry.src = .git url rev inputRev subDir ∧
        PinsAdmissible url rev (gitPins (rootEntries input.1.1 input.1.2))

/-- `selectPins` admits a pin set exactly for a shareable input. -/
theorem selectPins_shares_iff (manifest : Lake.Manifest) (overrides : Array Lake.PackageEntry)
    (ownRegula : Bool) :
    (∃ pins, selectPins manifest overrides ownRegula = .ok (some pins)) ↔
      Shareable ((manifest, overrides), ownRegula) := by
  constructor
  · rintro ⟨pins, h⟩
    obtain ⟨hDir, ⟨entry, inputRev, subDir, hEntry, hSrc⟩, hGit, hPath, hRefusal⟩ :=
      selectPins_sound h
    exact ⟨by simp [hDir], pathRefusal_eq_none_iff.mp hPath, entry, pins.mathlibUrl,
      pins.mathlibRev, inputRev, subDir, hEntry, hSrc,
      (pinsRefusal_eq_none_iff _ _ _).mp (hGit ▸ hRefusal)⟩
  · rintro ⟨hDir, hPaths, entry, url, rev, inputRev, subDir, hEntry, hSrc, hPins⟩
    dsimp only at hDir hPaths hEntry hPins
    obtain ⟨packagesDir, hRecorded⟩ := Option.ne_none_iff_exists'.mp hDir
    refine ⟨
      { packagesDir, mathlibUrl := url, mathlibRev := rev
        git := gitPins (rootEntries manifest overrides) }, ?_⟩
    simp only [selectPins, hRecorded, hEntry, Option.map_some, hSrc,
      pathRefusal_eq_none_iff.mpr hPaths, (pinsRefusal_eq_none_iff _ _ _).mpr hPins]

/-- A Git entry of `mathlib` at a commit, from a URL that the shared workspace's configuration can
quote. -/
private def shareableEntry : Lake.PackageEntry :=
  { name := `mathlib, inherited := false
    src := .git "https://example.invalid/mathlib4" "0000000000000000000000000000000000000000"
      none none }

/-- A Mathlib package's manifest that records its packages directory and has one entry,
`shareableEntry`. -/
private def shareableManifest : Lake.Manifest :=
  { name := `regula_mathlib, lakeDir := ".lake", fixedToolchain := false
    packagesDir? := some ".lake/packages", packages := #[shareableEntry] }

/-- Without an overrides file, the one Git pin of `shareableManifest` is its entry, in the checkout
directory `mathlib`. -/
private theorem shareable_gitPins : gitPins (rootEntries shareableManifest #[]) =
    #[(shareableEntry, ⟨"mathlib", "0000000000000000000000000000000000000000"⟩)] := by
  simp [gitPins, rootEntries, selectedEntry, shareableManifest, shareableEntry, List.eraseDups_cons]
  rfl

/-- `selectPins` admits a pin set exactly for a shareable input (`selectPins_shares_iff`): it
admits one for a manifest that pins `mathlib` by Git at a commit, with no overrides file and no
path entry, and refuses the same manifest without a packages directory. That the pins it admits
are those of the entries that Lake selects is `selectPins_sound`. -/
theorem checked_selectPins : Regula.ExecutableContract selectPins (fun select =>
    Regula.Decides (fun result : Except String (Option Pins) => ∃ pins, result = .ok (some pins))
      Shareable (Function.uncurry (Function.uncurry select))) :=
  ⟨.of_iff (fun input => selectPins_shares_iff input.1.1 input.1.2 input.2)
    ⟨((shareableManifest, #[]), false), (selectPins_shares_iff shareableManifest #[] false).mpr
      ⟨by simp [shareableManifest], fun entry dir hSelected hPath => by
        have hMem := (selectedEntry_some hSelected).2
        simp only [rootEntries, shareableManifest, Array.append_empty, Array.mem_singleton] at hMem
        subst hMem
        simp [shareableEntry] at hPath,
        shareableEntry, _, _, none, none, rfl, rfl, (pinsRefusal_eq_none_iff _ _ _).mp (by
          rw [shareable_gitPins]
          simp [pinsRefusal, shareableEntry, isObjectName, isComponent, inSubdirectory]
          rfl)⟩⟩
    ⟨(({ shareableManifest with packagesDir? := none }, #[]), false), fun ⟨_, refused⟩ => by
      simp [Function.uncurry, selectPins] at refused⟩⟩

attribute [regula_decision]
  component? admits mathlibStep cloneStep found prunes retires mathlibApplies selectPins

end RegulaProvision
