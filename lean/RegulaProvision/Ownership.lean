import RegulaProvision
import RegulaCore.Filesystem

/-! # The read of Regula's own integration entry, in the filesystem model

`RegulaProvision.ownRegulaWith` reads whether the entry that Lake selects for `regula` is Regula's
own integration entry, the path entry whose directory resolves to the Regula root being provisioned,
and `RegulaProvision.pinsWith` gives the pins that `selectPins` admits with that reading. The driver
runs both at `observeRealPath` (`readPins`). This module states their runs in a model of the
filesystem of `RegulaCore.Filesystem` that satisfies `Regula.Filesystem.ReadsReal`, and carries them
to the runs of the same definitions in `IO` at a read of a real path that agrees with the model's
(`pinsWith_admitted_io`), as each set of operations does at the model whose states are the worlds
(`observeRealPath_admitted`). The driver imports only the toolchain's libraries, because
`scripts/provision.sh` runs it with `lean --run` before the package is built; so this module of
its library imports it with the model, and nothing that the driver runs imports this module.

* `ownRegula_run`: a run changes nothing, never fails, and gives `true` exactly for Regula's own
  entry in the state it starts from (`OwnRegula`).
* `pinsWith_admitted`: when the pins are admitted, each path entry that Lake selects is the one for
  `regula`, and it is Regula's own (`PathsOwn`). With `pathRefusal_eq_none_iff`, this is the
  Boolean that `selectPins` takes, read from the model.

They rest on `ReadsReal` alone. Lake's readers of the manifest and the overrides file, which give
the entries, have no model here; their facts are the `Assumes:` entries of `readRoot` and of
`ownRegulaWith`. -/

namespace RegulaProvision

open System Regula.StateTriple Regula.Filesystem

/-- Regula's own integration entry among `entries`, the entries of the Mathlib package of the
Regula root `repo`, in the state `w` of the model `M`: the entry selected for `regula` is a path
entry that Lake does not copy (`copy` false), whose directory, joined to the Mathlib package's
directory as Lake joins it, has a real path, and that real path is the real path of `repo`. -/
def OwnRegula (M : Model) (w : M.World) (repo : FilePath) (entries : Array Lake.PackageEntry) :
    Prop :=
  ∃ dir, (selectedEntry entries `regula).map Lake.PackageEntry.src = some (.path dir false) ∧
    ∃ real, M.real w (Lake.joinRelative (repo / mathlibPackage) dir) = some real ∧
      M.real w repo = some real

/-- Each path entry that Lake selects among `entries`, whether Lake copies it or not, is the one for
`regula`, and it is Regula's own integration entry in the state `w` of the model `M` (`OwnRegula`),
which Lake does not copy. -/
def PathsOwn (M : Model) (w : M.World) (repo : FilePath) (entries : Array Lake.PackageEntry) :
    Prop :=
  ∀ entry dir copy, selectedEntry entries entry.name = some entry → entry.src = .path dir copy →
    entry.name = `regula ∧ OwnRegula M w repo entries

/-- A run of `resolveWith` at the model's read of a real path changes nothing, never fails, and
gives the model's real path of the path, `none` when it has none. -/
theorem resolve_run (M : Model) (readsReal : ReadsReal M) (path : FilePath) (before : M.World) :
    Satisfies ((resolveWith M.ops.realPath path).run before)
      (fun found w => w = before ∧ found = M.real before path) (fun _ _ => False) := by
  have h := (triple_iff _ _ _ _).mp (readsReal path before) before rfl
  simp only [resolveWith, run_tryCatch, EStateM.run_bind, EStateM.run_pure]
  revert h
  cases (M.ops.realPath path).run before with
  | ok real w => intro h; exact ⟨h.1, h.2.symm⟩
  | error e w => intro h; exact ⟨h.1, h.2.symm⟩

/-- A run of `ownRegulaWith` at the model's read of a real path changes nothing, never fails, and
gives `true` exactly for Regula's own integration entry in the state it starts from
(`OwnRegula`). -/
theorem ownRegula_run (M : Model) (readsReal : ReadsReal M) (repo : FilePath)
    (entries : Array Lake.PackageEntry) (before : M.World) :
    Satisfies ((ownRegulaWith M.ops.realPath repo entries).run before)
      (fun own w => w = before ∧ (own = true ↔ OwnRegula M before repo entries))
      (fun _ _ => False) := by
  unfold ownRegulaWith
  match hSelected : (selectedEntry entries `regula).map Lake.PackageEntry.src with
  | none => exact ⟨rfl, by simp [OwnRegula, hSelected]⟩
  | some (.git ..) | some (.path _ true) => exact ⟨rfl, by simp [OwnRegula, hSelected]⟩
  | some (.path dir false) =>
    refine Satisfies.bind (resolve_run M readsReal _ before) ?_
    rintro resolved w ⟨rfl, hResolved⟩
    refine Satisfies.bind (resolve_run M readsReal _ w) ?_
    rintro root w' ⟨rfl, hRoot⟩
    rcases resolved with _ | resolved <;> rcases root with _ | root <;>
      exact ⟨rfl, by simp [OwnRegula, hSelected, ← hResolved, ← hRoot]⟩

/-- A run of `pinsWith` at the model's read of a real path changes nothing, never fails, and gives
what `selectPins` gives with a Boolean that is `true` exactly for Regula's own integration entry in
the state it starts from (`OwnRegula`). -/
theorem pinsWith_run (M : Model) (readsReal : ReadsReal M) (repo : FilePath)
    (manifest : Lake.Manifest) (overrides : Array Lake.PackageEntry) (before : M.World) :
    Satisfies ((pinsWith M.ops.realPath repo manifest overrides).run before)
      (fun result w => w = before ∧ ∃ own, result = selectPins manifest overrides own ∧
        (own = true ↔ OwnRegula M before repo (rootEntries manifest overrides)))
      (fun _ _ => False) := by
  unfold pinsWith
  refine Satisfies.bind (ownRegula_run M readsReal repo _ before) ?_
  rintro own w ⟨rfl, hOwn⟩
  exact ⟨rfl, own, rfl, hOwn⟩

/-- When a run of `pinsWith` at the model's read of a real path admits pins, each path entry that
Lake selects is the one for `regula`, and it is Regula's own integration entry in the state the run
starts from, which the run does not change (`PathsOwn`). -/
theorem pinsWith_admitted (M : Model) (readsReal : ReadsReal M) (repo : FilePath)
    (manifest : Lake.Manifest) (overrides : Array Lake.PackageEntry) (before : M.World) :
    Satisfies ((pinsWith M.ops.realPath repo manifest overrides).run before)
      (fun result w => w = before ∧ ∀ pins, result = .ok (some pins) →
        PathsOwn M before repo (rootEntries manifest overrides))
      (fun _ _ => False) := by
  refine (pinsWith_run M readsReal repo manifest overrides before).mono ?_ (fun _ _ h => h)
  rintro result w ⟨rfl, own, rfl, hOwn⟩
  refine ⟨rfl, fun pins admitted entry dir copy hSelected hPath => ?_⟩
  have ⟨hName, hTrue, _⟩ :=
    pathRefusal_eq_none_iff.mp (selectPins_sound admitted).2.2.2.1 entry dir copy hSelected hPath
  exact ⟨hName, hOwn.mp hTrue⟩

/-! ## The runs in `IO` -/

section IO

variable {σ : Type} {view : Void IO.RealWorld → σ} {realPath : FilePath → IO FilePath}
  {modelPath : FilePath → EStateM IO.Error σ FilePath}

/-- `resolveWith` at a read of a real path that agrees with a model's runs as `resolveWith` in the
model. -/
theorem resolve_agrees (agrees : ∀ path, Agrees view (realPath path) (modelPath path))
    (path : FilePath) : Agrees view (resolveWith realPath path) (resolveWith modelPath path) :=
  Agrees.tryCatch (Agrees.bind (agrees path) fun _ => Agrees.pure view _)
    fun _ => Agrees.pure view none

/-- `ownRegulaWith` at a read of a real path that agrees with a model's runs as `ownRegulaWith` in
the model. -/
theorem ownRegula_agrees (agrees : ∀ path, Agrees view (realPath path) (modelPath path))
    (repo : FilePath) (entries : Array Lake.PackageEntry) :
    Agrees view (ownRegulaWith realPath repo entries) (ownRegulaWith modelPath repo entries) := by
  unfold ownRegulaWith
  split
  · refine Agrees.bind (resolve_agrees agrees _) fun resolved => ?_
    refine Agrees.bind (resolve_agrees agrees _) fun root => ?_
    rcases resolved with _ | _ <;> rcases root with _ | _ <;> exact Agrees.pure view _
  · exact Agrees.pure view false

/-- `pinsWith` at a read of a real path that agrees with a model's runs as `pinsWith` in the
model. -/
theorem pinsWith_agrees (agrees : ∀ path, Agrees view (realPath path) (modelPath path))
    (repo : FilePath) (manifest : Lake.Manifest) (overrides : Array Lake.PackageEntry) :
    Agrees view (pinsWith realPath repo manifest overrides)
      (pinsWith modelPath repo manifest overrides) :=
  Agrees.bind (ownRegula_agrees agrees repo _) fun _ => Agrees.pure view _

end IO

/-- When `pinsWith` in `IO`, at a read of a real path that agrees with the model's, admits pins,
each path entry that Lake selects is the one for `regula`, and it is Regula's own integration entry
in the state that the world it starts from is read as (`pinsWith_admitted`). -/
theorem pinsWith_admitted_io {M : Model} {view : Void IO.RealWorld → M.World}
    {realPath : FilePath → IO FilePath}
    (agrees : ∀ path, Agrees view (realPath path) (M.ops.realPath path)) (readsReal : ReadsReal M)
    (repo : FilePath) (manifest : Lake.Manifest) (overrides : Array Lake.PackageEntry)
    (w : Void IO.RealWorld) :
    RunsTo view (pinsWith realPath repo manifest overrides w)
      (fun result after => after = view w ∧ ∀ pins, result = .ok (some pins) →
        PathsOwn M (view w) repo (rootEntries manifest overrides))
      (fun _ _ => False) :=
  (pinsWith_agrees agrees repo manifest overrides).transfer w
    (pinsWith_admitted M readsReal repo manifest overrides (view w))

/-- When the driver's `pinsWith`, at its read of a real path `observeRealPath`, admits pins, each
path entry that Lake selects is the one for `regula`, and it is Regula's own integration entry in
the world the run starts from, at the model of the worlds whose read of a real path satisfies
`ReadsReal`. `filesystemOps` is any set of filesystem operations whose read of a real path is the
driver's; no other operation of it appears in the hypotheses. -/
theorem observeRealPath_admitted (filesystemOps : Ops IO)
    (realPath : filesystemOps.realPath = observeRealPath)
    (entry : Void IO.RealWorld → FilePath → Option IO.FS.FileType)
    (real : Void IO.RealWorld → FilePath → Option FilePath)
    (ident : Void IO.RealWorld → FilePath → Option FileId)
    (readsReal : ReadsReal (Model.ofIO filesystemOps entry real ident))
    (repo : FilePath) (manifest : Lake.Manifest) (overrides : Array Lake.PackageEntry)
    (w : Void IO.RealWorld) :
    RunsTo id (pinsWith observeRealPath repo manifest overrides w)
      (fun result after => after = w ∧ ∀ pins, result = .ok (some pins) →
        PathsOwn (Model.ofIO filesystemOps entry real ident) w repo
          (rootEntries manifest overrides))
      (fun _ _ => False) :=
  pinsWith_admitted_io (realPath ▸ (corresponds_ofIO filesystemOps entry real ident).2.1)
    readsReal repo manifest overrides w

end RegulaProvision
