import RegulaCore.Filesystem
import RegulaCore.CopyProgram

/-! # The filesystem contract of tree construction

The specification uses the existing filesystem model's entry kinds, tree relation and file
identities. `Captured` records the complete selected source enumeration; `Holds` says that the
constructed tree contains exactly its directory/file instructions, including alternate names of
the same file. Primitive assumptions concern only metadata, directory enumeration, byte reads,
mkdir and exclusive file writes. No assumption asserts the result of a copy or of its walk.
-/

namespace Regula.Filesystem.Construction

/-- Index-component admission decides exact membership in the observer's stored names. No
case-folding function enters the implementation or this proposition. -/
theorem admitGitName_iff (name : String) (stored : List String) :
    admitGitName (name, stored) = .ok () ↔ name ∈ stored := by
  simp [admitGitName]

/-- The executed index-component guard decides its complete exact-name domain. -/
theorem checked_admitGitName : Regula.ExecutableContract admitGitName
    (Regula.Decides (· = .ok ()) (fun pair => pair.1 ∈ pair.2)) :=
  ⟨.of_iff (fun pair => admitGitName_iff pair.1 pair.2)
    ⟨("entry", ["entry"]), rfl⟩ ⟨("entry", []), by simp [admitGitName]⟩⟩

attribute [regula_decision] admitGitName

open System Regula.StateTriple

/-- The decision the cold source entrypoint actually executes agrees on every input with its
source-domain proposition. -/
theorem checked_projectRelative : Regula.ExecutableContract projectRelative
    (Regula.Decides (· = true) ProjectRelative) :=
  ⟨.of_iff (fun _ => ⟨of_decide_eq_true, decide_eq_true⟩)
    ⟨["lean"], by decide⟩ ⟨["tmp"], by decide⟩⟩

attribute [regula_decision] projectRelative

/-- The explicit-selection decision includes exactly prefixes of its selected paths. -/
theorem checked_requiredPath : Regula.ExecutableContract requiredPath
    (fun f => ∀ required relative, f required relative = true ↔ RequiredPath required relative) :=
  ⟨fun _ _ => ⟨of_decide_eq_true, decide_eq_true⟩⟩

/-- Every ancestor of an explicitly selected path survives the executed selection decision. -/
theorem requiredPath_ancestor (required : List (List String)) (path relative : List String)
    (selected : path ∈ required) (ancestor : relative.IsPrefix path) :
    requiredPath required relative = true :=
  decide_eq_true ⟨path, selected, ancestor⟩

/-- The package pruning decision agrees with its proposition on every input. -/
theorem checked_packageSource : Regula.ExecutableContract packageSource
    (fun f => ∀ source dependencies path,
      f source dependencies path = true ↔ PackageSource source dependencies path) :=
  ⟨fun _ _ _ => ⟨of_decide_eq_true, decide_eq_true⟩⟩

/-- A capture root, such as that of an owned package in the packages directory, is never pruned
from its own pass. -/
theorem packageSource_owned (source : List String) (dependencies : List (List String)) :
    packageSource source dependencies source = true :=
  decide_eq_true (Or.inr rfl)

/-- Package pruning keeps every entry that is not a recorded dependency directory. -/
theorem packageSource_other (source : List String) (dependencies : List (List String))
    (path : List String) (other : path ∉ dependencies) :
    packageSource source dependencies path = true :=
  decide_eq_true (Or.inl other)

/-- Package pruning leaves out only a recorded dependency directory other than the capture root. -/
theorem packageSource_dependency (source : List String) (dependencies : List (List String))
    (path : List String) (pruned : packageSource source dependencies path = false) :
    path ∈ dependencies ∧ path ≠ source :=
  have kept : ¬ PackageSource source dependencies path := of_decide_eq_false pruned
  ⟨Decidable.of_not_not fun absent => kept (Or.inl absent), fun same => kept (Or.inr same)⟩

/-- The executed selection of a capture pass prunes an entry only when it is the directory of a
dependency package that Lake's loaded workspace records in the packages directory, and not the
pass's own root. -/
theorem CopyFilter.omission_pruned (filter : CopyFilter) (path : List String)
    (pruned : filter.omission path = some .pruned) :
    path ∈ filter.dependencies ∧ path ≠ filter.source := by
  unfold CopyFilter.omission at pruned
  cases excluded : filter.exclusion path with
  | some exclusion => simp [excluded] at pruned
  | none =>
    cases kept : packageSource filter.source filter.dependencies path with
    | true => simp [excluded, kept] at pruned
    | false => exact packageSource_dependency _ _ _ kept

/-- Every other entry, in the packages directory or not, is left out or selected exactly as the
exclusions decide. -/
theorem CopyFilter.omission_other (filter : CopyFilter) (path : List String)
    (other : path ∉ filter.dependencies) :
    filter.omission path = (filter.exclusion path).map .excluded := by
  unfold CopyFilter.omission
  cases filter.exclusion path with
  | some exclusion => rfl
  | none => simp [packageSource_other filter.source filter.dependencies path other]

/-- A pass leaves out no entry on the way from its root to `path`, `path` included, exactly when
`firstOmission` finds none. A copy refuses each file of its domain for which it finds one. -/
theorem CopyFilter.firstOmission_eq_none (filter : CopyFilter) (path : List String) :
    filter.firstOmission path = none ↔ ∀ length, filter.source.length ≤ length →
      length ≤ path.length → filter.omission (path.take length) = none := by
  simp only [CopyFilter.firstOmission, List.findSome?_eq_none_iff, List.mem_range'_1,
    Option.map_eq_none_iff]
  exact ⟨fun selected length lower upper => selected length ⟨lower, by omega⟩,
    fun selected length bounds => selected length bounds.1 (by omega)⟩

/-- File filtering retains every directory and exactly the selected regular files, without
altering any instruction's path or payload. The statement covers every name and entry kind. -/
theorem selectFiles_mem (selected : List String → Bool) (items : List Item) (item : Item) :
    item ∈ selectFiles selected items ↔ item ∈ items ∧
      (item.payload.kind = .dir ∨ selected item.relative = true) := by
  cases item with
  | mk relative payload => cases payload <;> simp [selectFiles, Payload.kind]

/-- The executed file filter has the complete kind-aware membership contract. -/
theorem checked_selectFiles : Regula.ExecutableContract selectFiles
    (fun f => ∀ selected items item, item ∈ f selected items ↔ item ∈ items ∧
      (item.payload.kind = .dir ∨ selected item.relative = true)) :=
  ⟨selectFiles_mem⟩

/-- No regular-file predicate can remove a captured directory instruction. -/
theorem selectFiles_directory (selected : List String → Bool) (items : List Item)
    (relative : List String) (present : ⟨relative, .directory⟩ ∈ items) :
    ⟨relative, .directory⟩ ∈ selectFiles selected items :=
  (selectFiles_mem selected items _).mpr ⟨present, Or.inl rfl⟩

/-- The executed preconstruction guard accepts exactly complete consumer file domains. -/
theorem checked_covers : Regula.ExecutableContract covers
    (fun f => ∀ required items, f required items = true ↔ Covers required items) :=
  ⟨fun _ _ => ⟨of_decide_eq_true, decide_eq_true⟩⟩

/-- Every instruction has a plain entry kind. -/
theorem Payload.plain (payload : Payload) : payload.kind = .dir ∨ payload.kind = .file := by
  cases payload <;> simp [Payload.kind]

/-- Two paths name the same entry, either by spelling or by the filesystem's stable identity.
This includes case-folded and normalized spellings without treating them as extra copied files. -/
def SameEntry (M : Model) (w : M.World) (left right : FilePath) : Prop :=
  left = right ∨ ∃ file, M.ident w left = some file ∧ M.ident w right = some file

/-- The root is a directory, each instruction exists with its specified kind, and every present
entry of the root's tree is the root or an instruction, up to another name of that same entry.
Absent names below a directory do not add entries. This states kinds and placement, not bytes,
permissions or a guarantee against changes after construction returns. -/
def Holds (M : Model) (root : FilePath) (items : List Item) (w : M.World) : Prop :=
  M.entry w root = some .dir ∧
  (∀ item ∈ items, M.entry w (location root item.relative) = some item.payload.kind) ∧
  ∀ path kind, M.Below w root path → M.entry w path = some kind →
    (SameEntry M w path root ∧ kind = .dir) ∨
      ∃ item ∈ items, SameEntry M w path (location root item.relative) ∧ kind = item.payload.kind

/-- An exact constructed tree contains no symbolic link or special entry. -/
theorem Holds.plain {M : Model} {root : FilePath} {items : List Item} {w : M.World}
    (holds : Holds M root items w) (path : FilePath) (kind : IO.FS.FileType)
    (below : M.Below w root path) (present : M.entry w path = some kind) :
    kind = .dir ∨ kind = .file := by
  rcases holds.2.2 path kind below present with h | ⟨item, _, _, h⟩
  · exact Or.inl h.2
  · rw [h]; exact item.payload.plain

/-- Recording the already established root directory changes no entry. -/
theorem Holds.root {M : Model} {root : FilePath} {items : List Item} {w : M.World}
    (holds : Holds M root items w) : Holds M root (items ++ [⟨[], .directory⟩]) w := by
  refine ⟨holds.1, ?_, ?_⟩
  · intro item mem
    rcases List.mem_append.mp mem with mem | mem
    · exact holds.2.1 item mem
    · simp only [List.mem_singleton] at mem
      subst item
      exact holds.1
  · intro path kind below present
    rcases holds.2.2 path kind below present with h | ⟨item, mem, same, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨item, List.mem_append_left _ mem, same, h⟩

/-- Additional filesystem observation vocabulary and the construction operations. Metadata and
real-path reads are the existing model's operations, not separate decisions about an IO copy. -/
structure CopyModel where
  /-- The filesystem model whose tree the theorem describes. -/
  filesystem : Model
  /-- Stored immediate directory-entry names, with no links followed. -/
  names : filesystem.World → FilePath → List String
  /-- Construction operations over that filesystem's states. -/
  ops : Ops (EStateM IO.Error filesystem.World)
  /-- The construction program uses the filesystem model's no-follow metadata operation. -/
  metadata : ops.metadata = filesystem.ops.symlinkMetadata
  /-- The construction program uses the filesystem model's real-path operation. -/
  realPath : ops.realPath = filesystem.ops.realPath

/-- Directory enumeration changes no state and returns every stored name. An empty listing of a
directory contains no entry below it. Completeness, including aliases, is an external filesystem
fact, not inferred from a spelling comparison.

Assumes: Lean v4.34.1 `Init/System/IO.lean:1141-1142`, `runtime/io.cpp:1076-1098`
enumerates with readdir and omits dot and dot-dot. Trusted: readdir reaches EOF without error;
the core wrapper does not distinguish EOF from an enumeration error. No concurrent writer changes
the source or destination during an observation. -/
@[regula_assumption filesystem (lean "v4.34.1" "Init/System/IO.lean#L1135-L1142")
  (lean "v4.34.1" "runtime/io.cpp#L1076-L1098")
  (trusted "readdir reaches EOF without error; the core wrapper does not distinguish them")]
def ReadsNames (C : CopyModel) : Prop :=
  (∀ path before, Satisfies ((C.ops.names path).run before)
    (fun names after => after = before ∧ names = C.names before path) (fun _ after => after = before)) ∧
  (∀ path before, C.filesystem.entry before path = some .dir → C.names before path = [] →
    Holds C.filesystem path [] before) ∧
  (∀ path before child kind, child.parent = some path → child.fileName.isSome = true →
    C.filesystem.entry before child = some kind →
    ∃ name ∈ C.names before path, SameEntry C.filesystem before child (path / name))

/-- Reading bytes changes no filesystem state. File-content fidelity is a trusted
IO boundary; the construction theorem describes entry kinds and locations.

Assumes: Lean v4.34.1 `Init/System/IO.lean:1211-1221` readBinFile only observes the source;
no concurrent writer changes the source. -/
@[regula_assumption filesystem (lean "v4.34.1" "Init/System/IO.lean#L1211-L1221")
  (trusted "reading bytes preserves the modeled filesystem state")]
def ReadsBytes (C : CopyModel) : Prop :=
  ∀ path before, Satisfies ((C.ops.bytes path).run before)
    (fun _ after => after = before) (fun _ after => after = before)

/-- Exclusive mkdir creates an empty root at an absent destination, or adds one empty child
directory to an existing exact tree. The frame includes every other tree entry.

Assumes: Lean v4.34.1 `Init/System/IO.lean:900`, `runtime/io.cpp:1181-1195`, POSIX mkdir create
only that directory and fail when the exact destination is occupied. No concurrent writer changes
an ancestor or adds another entry during construction. -/
@[regula_assumption filesystem (lean "v4.34.1" "Init/System/IO.lean#L894-L900")
  (lean "v4.34.1" "runtime/io.cpp#L1181-L1195")
  (document filesystem "POSIX.1-2024, mkdir(): exclusive directory creation")]
def CreatesDirectories (C : CopyModel) : Prop :=
  (∀ root before, C.filesystem.entry before root = none →
    Satisfies ((C.ops.directory root).run before)
      (fun _ after => Holds C.filesystem root [] after) (fun _ _ => True)) ∧
  (∀ root done relative before, Relative relative → relative ≠ [] →
    Holds C.filesystem root done before →
    Satisfies ((C.ops.directory (location root relative)).run before)
      (fun _ after => Holds C.filesystem root (done ++ [⟨relative, .directory⟩]) after)
      (fun _ _ => True))

/-- Exclusive file creation adds exactly one regular entry to the constructed tree. Opening
writeNew fails on every existing final entry, including a directory, FIFO and dangling link.

Assumes: Lean v4.34.1 `Init/System/IO.lean:651-660`, `runtime/io.cpp:409` use O_EXCL. Writes,
flush and chmod act only on the created regular file; the destination has no concurrent writer.
This theorem does not establish permission or byte preservation. -/
@[regula_assumption filesystem (lean "v4.34.1" "Init/System/IO.lean#L651-L660")
  (lean "v4.34.1" "runtime/io.cpp#L409")
  (document filesystem "POSIX.1-2024, open(): O_CREAT and O_EXCL never follow a final link")]
def CreatesFiles (C : CopyModel) : Prop :=
  ∀ root done relative bytes rights before, Relative relative → relative ≠ [] →
    Holds C.filesystem root done before →
    Satisfies ((C.ops.file (location root relative) bytes rights).run before)
      (fun _ after => Holds C.filesystem root (done ++ [⟨relative, .file bytes rights⟩]) after)
      (fun _ _ => True)

mutual
/-- The complete selected source tree, recorded in directory order. The directory constructor
accounts for every name in the model's complete listing. A refused source kind has no constructor.
Bytes are the captured bytes, whose correspondence to file contents remains trusted. -/
inductive Captured (C : CopyModel) (before : C.filesystem.World) (selected : FilePath → Bool) :
    FilePath → List String → List Item → Prop where
  /-- An excluded source entry is omitted, with its whole subtree. -/
  | excluded {source relative} : selected source = false → Captured C before selected source relative []
  /-- A selected regular source file is recorded as one regular-file instruction. -/
  | file {source relative bytes rights} : selected source = true → Relative relative →
      C.filesystem.entry before source = some .file →
      Captured C before selected source relative [⟨relative, .file bytes rights⟩]
  /-- A selected directory and every selected child of its complete listing are recorded. -/
  | directory {source relative children} : selected source = true → Relative relative →
      C.filesystem.entry before source = some .dir →
      CapturedChildren C before selected source relative (C.names before source) children →
      Captured C before selected source relative (⟨relative, .directory⟩ :: children)

/-- Every named child is captured, in listing order, with no truncated suffix. -/
inductive CapturedChildren (C : CopyModel) (before : C.filesystem.World)
    (selected : FilePath → Bool) : FilePath → List String → List String → List Item → Prop where
  /-- An empty listing has no child instructions. -/
  | nil {source relative} : CapturedChildren C before selected source relative [] []
  /-- One child and every remaining child are accounted for. -/
  | cons {source relative name names first rest} : Component name →
      Captured C before selected (source / name) (relative ++ [name]) first →
      CapturedChildren C before selected source relative names rest →
      CapturedChildren C before selected source relative (name :: names) (first ++ rest)
end

/-- Successful emission adds exactly the instructions, through the native primitive contracts.
Invalid paths and occupied destinations can fail; no theorem assumes they are admitted. -/
theorem emit_sound (C : CopyModel) (directories : CreatesDirectories C) (files : CreatesFiles C)
    (root : FilePath) (items : List Item) (done : List Item)
    (before after : C.filesystem.World) (initial : Holds C.filesystem root done before)
    (ran : (emitWith C.ops root items).run before = .ok () after) :
    Holds C.filesystem root (done ++ items) after := by
  induction items generalizing done before with
  | nil =>
    simp only [emitWith, EStateM.run_pure, EStateM.Result.ok.injEq] at ran
    cases ran.2
    simpa using initial
  | cons item rest ih =>
    rcases item with ⟨relative, payload⟩
    by_cases valid : Relative relative
    · cases payload with
      | directory =>
        by_cases empty : relative = []
        · subst relative
          simp [emitWith, valid] at ran
          have result := ih (done ++ [⟨[], .directory⟩]) before (Holds.root initial) ran
          simpa [List.append_assoc] using result
        · have notEmpty : relative.isEmpty = false := by cases relative <;> simp_all
          simp only [emitWith, valid, notEmpty, ↓reduceIte] at ran
          have step := directories.2 root done relative before valid empty initial
          cases created : (C.ops.directory (location root relative)).run before with
          | error error state => simp [created] at ran
          | ok result state =>
            cases result
            simp [created] at ran
            rw [created] at step
            simp only [Satisfies] at step
            have result := ih (done ++ [⟨relative, .directory⟩]) state step ran
            simpa [List.append_assoc] using result
      | file bytes rights =>
        by_cases empty : relative = []
        · subst relative
          simp [emitWith, valid, EStateM.run_bind, run_throw] at ran
        · have notEmpty : relative.isEmpty = false := by cases relative <;> simp_all
          simp only [emitWith, valid, notEmpty, ↓reduceIte] at ran
          have step := files root done relative bytes rights before valid empty initial
          cases created : (C.ops.file (location root relative) bytes rights).run before with
          | error error state => simp [created] at ran
          | ok result state =>
            cases result
            simp [created] at ran
            rw [created] at step
            simp only [Satisfies] at step
            have result := ih (done ++ [⟨relative, .file bytes rights⟩]) state step ran
            simpa [List.append_assoc] using result
    · simp [emitWith, valid, EStateM.run_bind, run_throw] at ran

/-- The construction and existing model kind reads are definitionally the same program. -/
theorem kind_eq (C : CopyModel) (path : FilePath) :
    kindWith C.ops path = entryType C.filesystem.ops path := by
  unfold kindWith entryType
  rw [C.metadata]
  rfl

/-- Construction's kind read is the existing filesystem model's no-follow kind read. -/
theorem kind_run (C : CopyModel) (reads : ReadsEntry C.filesystem) (path : FilePath)
    (before : C.filesystem.World) :
    Satisfies ((kindWith C.ops path).run before)
      (fun found after => after = before ∧ found = C.filesystem.entry before path)
      (fun _ after => after = before) := by
  rw [kind_eq]
  exact entryType_run C.filesystem reads path before

/-- Successful root establishment proves an empty tree from primitive reads and exclusive mkdir.
It never assumes the result of the root-establishment program itself. -/
theorem begin_sound (C : CopyModel) (readsEntry : ReadsEntry C.filesystem)
    (readsReal : ReadsReal C.filesystem) (names : ReadsNames C)
    (directories : CreatesDirectories C) (root : FilePath) (before after : C.filesystem.World)
    (ran : (beginWith C.ops root).run before = .ok () after) :
    Holds C.filesystem root [] after := by
  have realRead (path : FilePath) : Satisfies ((C.ops.realPath path).run before)
      (fun real state => state = before ∧ C.filesystem.real before path = some real)
      (fun _ state => state = before ∧ C.filesystem.real before path = none) := by
    rw [C.realPath]
    exact (triple_iff _ _ _ _).mp (readsReal path before) before rfl
  cases parentFound : root.parent with
  | none => simp [beginWith, parentFound, run_throw] at ran
  | some parent =>
    have parentRead := realRead parent
    simp only [beginWith, parentFound, EStateM.run_bind] at ran
    cases parentRan : (C.ops.realPath parent).run before with
    | error error state => simp [parentRan] at ran
    | ok real state =>
      rw [parentRan] at parentRead
      simp only [Satisfies] at parentRead
      have unchanged := parentRead.1
      subst state
      simp only [parentRan] at ran
      by_cases parentOwn : real = parent
      · simp only [parentOwn, BEq.rfl, ↓reduceIte] at ran
        have read := kind_run C readsEntry root before
        cases kindRan : (kindWith C.ops root).run before with
        | error error state => simp [kindRan] at ran
        | ok found state =>
          rw [kindRan] at read
          simp only [Satisfies] at read
          have unchanged := read.1
          subst state
          simp only [EStateM.run_bind, kindRan] at ran
          cases found with
          | none =>
            have created := directories.1 root before read.2.symm
            simp only [ran, Satisfies] at created
            exact created
          | some kind =>
            cases kind with
            | file | symlink | other => simp [run_throw] at ran
            | dir =>
              have rootRead := realRead root
              simp only [EStateM.run_bind] at ran
              cases rootRan : (C.ops.realPath root).run before with
              | error error state => simp [rootRan] at ran
              | ok real state =>
                rw [rootRan] at rootRead
                simp only [Satisfies] at rootRead
                have unchanged := rootRead.1
                subst state
                simp only [rootRan] at ran
                by_cases rootOwn : real = root
                · simp only [rootOwn, BEq.rfl, ↓reduceIte, EStateM.run_bind] at ran
                  have listed := names.1 root before
                  cases namesRan : (C.ops.names root).run before with
                  | error error state => simp [namesRan] at ran
                  | ok found state =>
                    rw [namesRan] at listed
                    simp only [Satisfies] at listed
                    have unchanged := listed.1
                    subst state
                    simp only [namesRan] at ran
                    cases found with
                    | cons name rest => simp [run_throw] at ran
                    | nil =>
                      simp only [List.isEmpty_nil, ↓reduceIte, EStateM.run_pure,
                        EStateM.Result.ok.injEq] at ran
                      cases ran.2
                      exact names.2.1 root before read.2.symm listed.2.symm
                · have different : (real == root) = false := by simpa using rootOwn
                  simp [different, run_throw, EStateM.run_bind] at ran
      · have different : (real == parent) = false := by simpa using parentOwn
        simp [different, run_throw, EStateM.run_bind] at ran

/-- A successful call of the actual generic constructor holds exactly its instructions, with
no link or special entry, under the listed native primitive contracts. -/
theorem construct_sound (C : CopyModel) (readsEntry : ReadsEntry C.filesystem)
    (readsReal : ReadsReal C.filesystem) (names : ReadsNames C)
    (directories : CreatesDirectories C) (files : CreatesFiles C) (root : FilePath)
    (items : List Item) (before after : C.filesystem.World)
    (ran : (constructWith C.ops root items).run before = .ok () after) :
    Holds C.filesystem root items after := by
  simp only [constructWith, EStateM.run_bind] at ran
  cases started : (beginWith C.ops root).run before with
  | error error state => simp [started] at ran
  | ok result state =>
    cases result
    simp only [started] at ran
    have initial := begin_sound C readsEntry readsReal names directories root before state started
    exact emit_sound C directories files root items [] state after initial ran

/-- The source loop accounts for every child in the listing. This lemma's hypothesis is the
smaller-depth result of `capture_run`, not an assumption about the external filesystem. -/
theorem capture_children_run (C : CopyModel) (selected : FilePath → Bool) (depth : Nat)
    (before : C.filesystem.World)
    (children : ∀ source relative, Satisfies ((captureWith C.ops selected depth source relative).run before)
      (fun items after => after = before ∧ Captured C before selected source relative items)
      (fun _ after => after = before)) (source : FilePath) (relative : List String)
    (names : List String) (acc : List Item) :
    Satisfies ((names.foldlM (fun items name => do
      unless Component name do throw <| IO.userError s!"invalid directory entry: {name}"
      return items ++ (← captureWith C.ops selected depth (source / name) (relative ++ [name]))) acc).run before)
      (fun items after => after = before ∧ ∃ rest,
        CapturedChildren C before selected source relative names rest ∧ items = acc ++ rest)
      (fun _ after => after = before) := by
  induction names generalizing acc with
  | nil =>
    simp only [List.foldlM_nil, EStateM.run_pure, Satisfies]
    exact ⟨True.intro, [], .nil, by simp⟩
  | cons name names ih =>
    by_cases valid : Component name
    · simp only [List.foldlM_cons, valid, ↓reduceIte, bind_assoc, pure_bind]
      apply Satisfies.bind (children (source / name) (relative ++ [name]))
      intro first state captured
      have unchanged := captured.1
      subst state
      exact (ih (acc ++ first)).mono (fun items after h => by
        rcases h.2 with ⟨rest, accounted, result⟩
        exact ⟨h.1, first ++ rest, .cons valid captured.2 accounted,
          by simpa [List.append_assoc] using result⟩) (fun _ _ h => h)
    · simp [List.foldlM_cons, valid, run_throw, EStateM.run_bind, Satisfies]

/-- Capture preserves the filesystem state and records the complete selected source tree. A
link, special entry, invalid component or depth exhaustion has no successful truncated result. -/
theorem capture_run (C : CopyModel) (readsEntry : ReadsEntry C.filesystem)
    (names : ReadsNames C) (bytes : ReadsBytes C) (selected : FilePath → Bool) (depth : Nat)
    (source : FilePath) (relative : List String) (before : C.filesystem.World) :
    Satisfies ((captureWith C.ops selected depth source relative).run before)
      (fun items after => after = before ∧ Captured C before selected source relative items)
      (fun _ after => after = before) := by
  induction depth generalizing source relative with
  | zero => simp [captureWith, run_throw, Satisfies]
  | succ depth ih =>
    by_cases chosen : selected source = true
    · by_cases valid : Relative relative
      · simp only [captureWith, chosen, valid, ↓reduceIte, EStateM.run_bind]
        have read := (triple_iff _ _ _ _).mp (readsEntry source before) before rfl
        rw [← C.metadata] at read
        cases metadataRan : (C.ops.metadata source).run before with
        | error error state =>
          rw [metadataRan] at read
          simp only [Satisfies] at read
          simpa only [metadataRan, Satisfies] using read.1
        | ok metadata state =>
          rw [metadataRan] at read
          simp only [Satisfies] at read
          have unchanged := read.1
          subst state
          dsimp only
          cases kind : metadata.type with
          | other | symlink => simp [run_throw, Satisfies]
          | file =>
            simp only [EStateM.run_bind]
            have readBytes := bytes source before
            cases bytesRan : (C.ops.bytes source).run before with
            | error error state =>
              rw [bytesRan] at readBytes
              simpa only [bytesRan, Satisfies] using readBytes
            | ok pair state =>
              rw [bytesRan] at readBytes
              simp only [Satisfies] at readBytes
              subst state
              rcases pair with ⟨data, rights⟩
              simp only [EStateM.run_pure, Satisfies]
              exact ⟨True.intro, .file chosen valid (by simpa only [kind] using read.2)⟩
          | dir =>
            simp only [EStateM.run_bind]
            have listed := names.1 source before
            cases namesRan : (C.ops.names source).run before with
            | error error state =>
              rw [namesRan] at listed
              simpa only [namesRan, Satisfies] using listed
            | ok found state =>
              rw [namesRan] at listed
              simp only [Satisfies] at listed
              have unchanged := listed.1
              subst state
              dsimp only
              apply Satisfies.bind (capture_children_run C selected depth before ih source relative found [])
              intro items state children
              have unchanged := children.1
              subst state
              rcases children.2 with ⟨rest, accounted, result⟩
              simp only [List.nil_append] at result
              subst items
              simp only [Satisfies]
              exact ⟨rfl, .directory chosen valid (by simpa only [kind] using read.2)
                (listed.2 ▸ accounted)⟩
      · simp [captureWith, chosen, valid, run_throw, EStateM.run_bind, Satisfies]
    · have excluded : selected source = false := by simpa using chosen
      simp only [captureWith, excluded, Bool.false_eq_true, ↓reduceIte, EStateM.run_pure, Satisfies]
      exact ⟨True.intro, .excluded excluded⟩

/-- The function every source-copy adapter runs constructs exactly the complete selected source
directory/file tree. Its hypotheses are native primitive contracts over the existing filesystem
model. It has no assumption about an unmodeled cp, ln, completed-copy inspection or whole copy.
Errors can leave a partial destination for its private owner to remove; no error is acceptance. -/
theorem copy_sound (C : CopyModel) (readsEntry : ReadsEntry C.filesystem)
    (readsReal : ReadsReal C.filesystem) (names : ReadsNames C) (bytes : ReadsBytes C)
    (directories : CreatesDirectories C) (files : CreatesFiles C) (selected : FilePath → Bool)
    (depth : Nat) (source target : FilePath) (before after : C.filesystem.World) (items : List Item)
    (ran : (copyWith C.ops source target selected depth).run before = .ok items after) :
    Captured C before selected source [] items ∧ Holds C.filesystem target items after := by
  simp only [copyWith, EStateM.run_bind] at ran
  have captured := capture_run C readsEntry names bytes selected depth source [] before
  cases observed : (captureWith C.ops selected depth source []).run before with
  | error error state => simp [observed] at ran
  | ok found state =>
    rw [observed] at captured
    simp only [Satisfies] at captured
    have unchanged := captured.1
    subst state
    simp only [observed] at ran
    cases created : (constructWith C.ops target found).run before with
    | error error state => simp [created] at ran
    | ok result state =>
      cases result
      simp only [created, EStateM.run_pure, EStateM.Result.ok.injEq] at ran
      rcases ran with ⟨rfl, rfl⟩
      exact ⟨captured.2,
        construct_sound C readsEntry readsReal names directories files target found before state created⟩

/-- Construction operations in IO run as the operations of a model, under the same world view. -/
def CopyCorresponds (ops : Ops IO) (C : CopyModel)
    (view : Void IO.RealWorld → C.filesystem.World) : Prop :=
  (∀ path, Agrees view (ops.metadata path) (C.ops.metadata path)) ∧
  (∀ path, Agrees view (ops.names path) (C.ops.names path)) ∧
  (∀ path, Agrees view (ops.realPath path) (C.ops.realPath path)) ∧
  (∀ path, Agrees view (ops.bytes path) (C.ops.bytes path)) ∧
  (∀ path, Agrees view (ops.directory path) (C.ops.directory path)) ∧
  (∀ path bytes rights, Agrees view (ops.file path bytes rights) (C.ops.file path bytes rights))

/-- A monadic list fold keeps agreement of its primitive steps. -/
theorem foldlM_agrees {α β σ : Type} (view : Void IO.RealWorld → σ)
    (f : β → α → IO β) (g : β → α → EStateM IO.Error σ β)
    (steps : ∀ acc item, Agrees view (f acc item) (g acc item)) (items : List α) (acc : β) :
    Agrees view (items.foldlM f acc) (items.foldlM g acc) := by
  induction items generalizing acc with
  | nil => simpa only [List.foldlM_nil] using Agrees.pure view acc
  | cons item rest ih =>
    simp only [List.foldlM_cons]
    exact (steps acc item).bind (fun next => ih next)

/-- The no-follow kind read is the same program in IO and in the model. -/
theorem kind_agrees {ops : Ops IO} {C : CopyModel} {view : Void IO.RealWorld → C.filesystem.World}
    (corresponds : CopyCorresponds ops C view) (path : FilePath) :
    Agrees view (kindWith ops path) (kindWith C.ops path) := by
  unfold kindWith
  apply Agrees.tryCatch
  · exact (corresponds.1 path).bind (fun metadata => Agrees.pure view (some metadata.type))
  · intro error
    cases error <;> first | exact Agrees.pure view _ | exact Agrees.throw view _

/-- Root establishment keeps agreement; it is not a second inspection implementation. -/
theorem begin_agrees {ops : Ops IO} {C : CopyModel} {view : Void IO.RealWorld → C.filesystem.World}
    (corresponds : CopyCorresponds ops C view) (root : FilePath) :
    Agrees view (beginWith ops root) (beginWith C.ops root) := by
  unfold beginWith
  cases root.parent with
  | none => exact Agrees.throw view _
  | some parent =>
    apply (corresponds.2.2.1 parent).bind
    intro real
    have remaining : Agrees view
        (do let found ← kindWith ops root
            match found with
            | none => ops.directory root
            | some .dir => do
                unless (← ops.realPath root) == root do
                  throw <| IO.userError s!"copy root is not at its own place: {root}"
                unless (← ops.names root).isEmpty do
                  throw <| IO.userError s!"copy root is occupied: {root}"
            | _ => throw <| IO.userError s!"copy root is not a directory: {root}")
        (do let found ← kindWith C.ops root
            match found with
            | none => C.ops.directory root
            | some .dir => do
                unless (← C.ops.realPath root) == root do
                  throw <| IO.userError s!"copy root is not at its own place: {root}"
                unless (← C.ops.names root).isEmpty do
                  throw <| IO.userError s!"copy root is occupied: {root}"
            | _ => throw <| IO.userError s!"copy root is not a directory: {root}") := by
      apply (kind_agrees corresponds root).bind
      intro found
      cases found with
      | none => exact corresponds.2.2.2.2.1 root
      | some kind =>
        cases kind with
        | file | symlink | other => exact Agrees.throw view _
        | dir =>
          apply (corresponds.2.2.1 root).bind
          intro real
          have listed : Agrees view
              (do unless (← ops.names root).isEmpty do
                    throw <| IO.userError s!"copy root is occupied: {root}")
              (do unless (← C.ops.names root).isEmpty do
                    throw <| IO.userError s!"copy root is occupied: {root}") := by
            apply (corresponds.2.1 root).bind
            intro names
            split <;> first | exact Agrees.pure view _ | exact Agrees.throw view _
          split
          · exact listed
          · exact (Agrees.throw view _).bind (fun _ => listed)
    split
    · exact remaining
    · exact (Agrees.throw view _).bind (fun _ => remaining)

/-- Emission keeps agreement with the same directory/file program in the model. -/
theorem emit_agrees {ops : Ops IO} {C : CopyModel} {view : Void IO.RealWorld → C.filesystem.World}
    (corresponds : CopyCorresponds ops C view) (root : FilePath) (items : List Item) :
    Agrees view (emitWith ops root items) (emitWith C.ops root items) := by
  induction items with
  | nil => simpa only [emitWith] using Agrees.pure view ()
  | cons item rest ih =>
    rw [emitWith, emitWith]
    have proceed (result : Unit) : Agrees view
        ((fun _ : Unit =>
          match item.payload with
          | .directory =>
            if item.relative.isEmpty then emitWith ops root rest
            else ops.directory (location root item.relative) >>= fun _ => emitWith ops root rest
          | .file bytes rights =>
            if item.relative.isEmpty then
              throw (IO.userError "a construction root must be a directory") >>= fun _ : Unit =>
                ops.file (location root item.relative) bytes rights >>= fun _ => emitWith ops root rest
            else ops.file (location root item.relative) bytes rights >>= fun _ => emitWith ops root rest) result)
        ((fun _ : Unit =>
          match item.payload with
          | .directory =>
            if item.relative.isEmpty then emitWith C.ops root rest
            else C.ops.directory (location root item.relative) >>= fun _ => emitWith C.ops root rest
          | .file bytes rights =>
            if item.relative.isEmpty then
              throw (IO.userError "a construction root must be a directory") >>= fun _ : Unit =>
                C.ops.file (location root item.relative) bytes rights >>= fun _ => emitWith C.ops root rest
            else C.ops.file (location root item.relative) bytes rights >>= fun _ => emitWith C.ops root rest) result) := by
      dsimp only
      cases payload : item.payload with
      | directory =>
        dsimp only
        split
        · exact ih
        · exact (corresponds.2.2.2.2.1 _).bind (fun _ => ih)
      | file bytes rights =>
        dsimp only
        split
        · exact (Agrees.throw view _).bind (fun _ =>
                (corresponds.2.2.2.2.2 _ _ _).bind (fun _ => ih))
        · exact (corresponds.2.2.2.2.2 _ _ _).bind (fun _ => ih)
    split
    · exact proceed ()
    · exact (Agrees.throw view _).bind proceed

/-- The actual constructor agrees, including its root establishment, under primitive agreement. -/
theorem construct_agrees {ops : Ops IO} {C : CopyModel}
    {view : Void IO.RealWorld → C.filesystem.World} (corresponds : CopyCorresponds ops C view)
    (root : FilePath) (items : List Item) :
    Agrees view (constructWith ops root items) (constructWith C.ops root items) := by
  unfold constructWith
  exact (begin_agrees corresponds root).bind (fun _ => emit_agrees corresponds root items)

/-- Source capture keeps agreement for every depth and selection, including every refusal. -/
theorem capture_agrees {ops : Ops IO} {C : CopyModel} {view : Void IO.RealWorld → C.filesystem.World}
    (corresponds : CopyCorresponds ops C view) (selected : FilePath → Bool) (depth : Nat)
    (source : FilePath) (relative : List String) :
    Agrees view (captureWith ops selected depth source relative)
      (captureWith C.ops selected depth source relative) := by
  induction depth generalizing source relative with
  | zero => simpa only [captureWith] using Agrees.throw view _
  | succ depth ih =>
    rw [captureWith, captureWith]
    have observe : Agrees view
        (do let metadata ← ops.metadata source
            match metadata.type with
            | .file =>
              let (bytes, rights) ← ops.bytes source
              return [⟨relative, .file bytes rights⟩]
            | .dir =>
              let names ← ops.names source
              let children ← names.foldlM (fun items name => do
                unless Component name do throw <| IO.userError s!"invalid directory entry: {name}"
                return items ++ (← captureWith ops selected depth (source / name) (relative ++ [name]))) []
              return ⟨relative, .directory⟩ :: children
            | kind => throw <| IO.userError s!"copy refused {source}: {repr kind} is not a directory or \
                a regular file")
        (do let metadata ← C.ops.metadata source
            match metadata.type with
            | .file =>
              let (bytes, rights) ← C.ops.bytes source
              return [⟨relative, .file bytes rights⟩]
            | .dir =>
              let names ← C.ops.names source
              let children ← names.foldlM (fun items name => do
                unless Component name do throw <| IO.userError s!"invalid directory entry: {name}"
                return items ++ (← captureWith C.ops selected depth (source / name) (relative ++ [name]))) []
              return ⟨relative, .directory⟩ :: children
            | kind => throw <| IO.userError s!"copy refused {source}: {repr kind} is not a directory or \
                a regular file") := by
      apply (corresponds.1 source).bind
      intro metadata
      cases metadata.type with
      | file =>
        exact (corresponds.2.2.2.1 source).bind (fun pair =>
          Agrees.pure view ([⟨relative, .file pair.1 pair.2⟩] : List Item))
      | dir =>
        apply (corresponds.2.1 source).bind
        intro names
        apply (foldlM_agrees (β := List Item) view _ _ (fun acc name => ?_) names []).bind
        · intro children
          exact Agrees.pure view ((⟨relative, .directory⟩ : Item) :: children)
        · have child := (ih (source / name) (relative ++ [name])).bind (fun items =>
            Agrees.pure view (acc ++ items))
          split
          · exact child
          · exact (Agrees.throw view _).bind (fun _ => child)
      | symlink | other => exact Agrees.throw view _
    split
    · split
      · exact observe
      · exact (Agrees.throw view _).bind (fun _ => observe)
    · exact Agrees.pure view []

/-- The same source-copy function runs at the observer and the filesystem model. -/
theorem copy_agrees {ops : Ops IO} {C : CopyModel} {view : Void IO.RealWorld → C.filesystem.World}
    (corresponds : CopyCorresponds ops C view) (selected : FilePath → Bool) (depth : Nat)
    (source target : FilePath) :
    Agrees view (copyWith ops source target selected depth) (copyWith C.ops source target selected depth) := by
  unfold copyWith
  apply (capture_agrees corresponds selected depth source []).bind
  intro items
  exact (construct_agrees corresponds target items).bind (fun _ => Agrees.pure view items)

/-- The model of the actual IO construction operations. Its underlying filesystem is precisely
Model.ofIO of the existing observer; agreement is checked, not an external filesystem assumption. -/
def CopyModel.ofIO (filesystemOps : Regula.Filesystem.Ops IO) (ops : Ops IO)
    (metadata : ops.metadata = filesystemOps.symlinkMetadata)
    (realPath : ops.realPath = filesystemOps.realPath)
    (entry : Void IO.RealWorld → FilePath → Option IO.FS.FileType)
    (real : Void IO.RealWorld → FilePath → Option FilePath)
    (ident : Void IO.RealWorld → FilePath → Option FileId)
    (names : Void IO.RealWorld → FilePath → List String) : CopyModel where
  filesystem := Model.ofIO filesystemOps entry real ident
  names := names
  ops := {
    metadata := fun path => ofEIO (ops.metadata path)
    names := fun path => ofEIO (ops.names path)
    realPath := fun path => ofEIO (ops.realPath path)
    bytes := fun path => ofEIO (ops.bytes path)
    directory := fun path => ofEIO (ops.directory path)
    file := fun path bytes rights => ofEIO (ops.file path bytes rights) }
  metadata := by rw [metadata]; rfl
  realPath := by rw [realPath]; rfl

/-- Every actual IO operation agrees with its action over IO worlds. No filesystem behavior is
assumed by this theorem; those behaviors are the hypotheses of copy_sound. -/
theorem copy_corresponds_ofIO (filesystemOps : Regula.Filesystem.Ops IO) (ops : Ops IO)
    (metadata : ops.metadata = filesystemOps.symlinkMetadata)
    (realPath : ops.realPath = filesystemOps.realPath)
    (entry : Void IO.RealWorld → FilePath → Option IO.FS.FileType)
    (real : Void IO.RealWorld → FilePath → Option FilePath)
    (ident : Void IO.RealWorld → FilePath → Option FileId)
    (names : Void IO.RealWorld → FilePath → List String) :
    CopyCorresponds ops (CopyModel.ofIO filesystemOps ops metadata realPath entry real ident names) id :=
  ⟨fun _ => ofEIO_agrees _, fun _ => ofEIO_agrees _, fun _ => ofEIO_agrees _,
    fun _ => ofEIO_agrees _, fun _ => ofEIO_agrees _, fun _ _ _ => ofEIO_agrees _⟩

/-- The actual IO copy has the complete source receipt and exact plain destination tree when
its observer's native primitives satisfy the stated contracts. This is the IO transfer of the
theorem about the same copyWith program, not a theorem about a second copy implementation. -/
theorem copy_io {ops : Ops IO} {C : CopyModel} {view : Void IO.RealWorld → C.filesystem.World}
    (corresponds : CopyCorresponds ops C view) (readsEntry : ReadsEntry C.filesystem)
    (readsReal : ReadsReal C.filesystem) (names : ReadsNames C) (bytes : ReadsBytes C)
    (directories : CreatesDirectories C) (files : CreatesFiles C)
    (source target : FilePath) (selected : FilePath → Bool) (depth : Nat) (w : Void IO.RealWorld) :
    RunsTo view (copyWith ops source target selected depth w)
      (fun items after => Captured C (view w) selected source [] items ∧
        Holds C.filesystem target items after) (fun _ _ => True) := by
  apply (copy_agrees corresponds selected depth source target).transfer w
  cases ran : (copyWith C.ops source target selected depth).run (view w) with
  | error error state => trivial
  | ok items state =>
    exact copy_sound C readsEntry readsReal names bytes directories files selected depth source target
      (view w) state items ran

/-- The generated-workspace constructor has the exact plain tree its instructions specify,
under the same observer-model primitive contracts as source copies. -/
theorem construct_io {ops : Ops IO} {C : CopyModel} {view : Void IO.RealWorld → C.filesystem.World}
    (corresponds : CopyCorresponds ops C view) (readsEntry : ReadsEntry C.filesystem)
    (readsReal : ReadsReal C.filesystem) (names : ReadsNames C)
    (directories : CreatesDirectories C) (files : CreatesFiles C) (target : FilePath)
    (items : List Item) (w : Void IO.RealWorld) :
    RunsTo view (constructWith ops target items w)
      (fun _ after => Holds C.filesystem target items after) (fun _ _ => True) := by
  apply (construct_agrees corresponds target items).transfer w
  cases ran : (constructWith C.ops target items).run (view w) with
  | error error state => trivial
  | ok result state =>
    cases result
    exact construct_sound C readsEntry readsReal names directories files target items (view w) state ran

/-- The selected-domain constructor actually run by project copies cannot succeed with a
missing consumer input. Each required path is a regular file in its exact constructed tree.
The receipt retains captured payloads. Byte fidelity, original discovery completeness, stored
spellings and the stability of native observations remain the stated external boundaries. -/
theorem constructSelected_io {ops : Ops IO} {C : CopyModel}
    {view : Void IO.RealWorld → C.filesystem.World}
    (corresponds : CopyCorresponds ops C view) (readsEntry : ReadsEntry C.filesystem)
    (readsReal : ReadsReal C.filesystem) (names : ReadsNames C)
    (directories : CreatesDirectories C) (files : CreatesFiles C) (target : FilePath)
    (required : List (List String)) (items : List Item) (w : Void IO.RealWorld) :
    RunsTo view (constructSelectedWith ops target required items w)
      (fun _ after => Covers required items ∧ Holds C.filesystem target items after ∧
        ∀ path ∈ required, C.filesystem.entry after (location target path) = some .file)
      (fun _ _ => True) := by
  by_cases complete : covers required items = true
  · have domain : Covers required items := of_decide_eq_true complete
    simp only [constructSelectedWith, complete, ↓reduceIte]
    have built := construct_io corresponds readsEntry readsReal names directories files target items w
    cases ran : constructWith ops target items w with
    | error error after => trivial
    | ok result after =>
      rw [ran] at built
      refine ⟨domain, built, ?_⟩
      intro path selected
      obtain ⟨item, present, relative, kind⟩ := domain path selected
      have entry := built.2.1 item present
      simpa only [relative, kind] using entry
  · have missing : covers required items = false := by simpa using complete
    simp only [constructSelectedWith, missing, Bool.false_eq_true, ↓reduceIte]
    rw [eio_bind_error (eio_throw _ w)]
    trivial

/-- The indexed regular-file representation, stated without the adapter's search or Boolean
tests. Ordinary bytes belong to the captured source receipt. A tracked link's supplied blob
becomes one regular-file instruction containing exactly that target text. -/
inductive GitRepresentation (captured : List Item) : GitEntry → Item → Prop where
  /-- Index mode 100644 uses captured file bytes and rights 0644. -/
  | regular {relative bytes rights} : ⟨relative, .file bytes rights⟩ ∈ captured →
      GitRepresentation captured ⟨relative, .regular⟩ ⟨relative, .file bytes 420⟩
  /-- Index mode 100755 uses captured file bytes and rights 0755. -/
  | executable {relative bytes rights} : ⟨relative, .file bytes rights⟩ ∈ captured →
      GitRepresentation captured ⟨relative, .executable⟩ ⟨relative, .file bytes 493⟩
  /-- Index mode 120000 is a target-text regular file, with no link instruction. -/
  | link {relative text} :
      GitRepresentation captured ⟨relative, .link text⟩ ⟨relative, .file text 420⟩

/-- Every index entry and precisely its one representation, in order. -/
inductive GitRepresentations (captured : List Item) : List GitEntry → List Item → Prop where
  /-- No index entries produce no worktree files. -/
  | nil : GitRepresentations captured [] []
  /-- One represented index entry and all remaining entries. -/
  | cons {entry item entries items} : GitRepresentation captured entry item →
      GitRepresentations captured entries items →
      GitRepresentations captured (entry :: entries) (item :: items)

/-- Every successful indexed file instruction has precisely its independent representation. -/
theorem gitItem_sound (captured : List Item) (entry : GitEntry) (item : Item)
    (ran : gitItem captured entry = .ok item) : GitRepresentation captured entry item := by
  rcases entry with ⟨relative, mode⟩
  cases mode with
  | link text =>
    change Except.ok ⟨relative, .file text⟩ = .ok item at ran
    cases ran
    exact .link
  | regular | executable =>
    cases found : captured.find? (fun item => item.relative == relative) with
    | none => simp [gitItem, found] at ran
    | some original =>
      have member := List.mem_of_find?_eq_some found
      have same : original.relative = relative := by
        simpa using List.find?_some found
      rcases original with ⟨path, payload⟩
      cases payload with
      | directory => simp [gitItem, found] at ran
      | file bytes rights =>
        simp [gitItem, found] at ran
        change Except.ok _ = .ok item at ran
        cases ran
        simp only at same
        subst path
        first | exact .regular member | exact .executable member

/-- Indexed instruction derivation accounts for every entry, in order, with no extra files. -/
theorem gitFiles_sound (captured : List Item) (entries : List GitEntry) (items : List Item)
    (ran : gitFiles captured entries = .ok items) :
    GitRepresentations captured entries items := by
  induction entries generalizing items with
  | nil =>
    change Except.ok [] = .ok items at ran
    cases ran
    exact .nil
  | cons entry rest ih =>
    cases first : gitItem captured entry with
    | error error =>
      simp [gitFiles, first] at ran
      change Except.error error = .ok items at ran
      cases ran
    | ok item =>
      cases remaining : gitFiles captured rest with
      | error error =>
        simp [gitFiles, first, remaining] at ran
        change Except.error error = .ok items at ran
        cases ran
      | ok tail =>
        simp [gitFiles, first, remaining] at ran
        change Except.ok (item :: tail) = .ok items at ran
        cases ran
        exact .cons (gitItem_sound captured entry item first) (ih tail remaining)

/-- The build-output selection retains exactly captured regular files beneath this package's
own build directory whose paths are absent from the index. -/
theorem gitBuildFiles_mem (captured : List Item) (entries : List GitEntry) (item : Item) :
    item ∈ gitBuildFiles captured entries ↔ item ∈ captured ∧
      (∃ bytes rights, item.payload = .file bytes rights) ∧
      [".lake", "build"].IsPrefix item.relative ∧
      ∀ entry ∈ entries, entry.relative ≠ item.relative := by
  rcases item with ⟨relative, payload⟩
  cases payload <;> simp [gitBuildFiles, List.isPrefixOf_iff_prefix]

/-- The executed build-output selector has the complete membership contract above. -/
theorem checked_gitBuildFiles : Regula.ExecutableContract gitBuildFiles
    (fun f => ∀ captured entries item, item ∈ f captured entries ↔ item ∈ captured ∧
      (∃ bytes rights, item.payload = .file bytes rights) ∧
      [".lake", "build"].IsPrefix item.relative ∧
      ∀ entry ∈ entries, entry.relative ≠ item.relative) :=
  ⟨gitBuildFiles_mem⟩

/-- A successful preparation consists of exactly the indexed worktree, admitted untracked
build outputs and captured Git metadata, whose config receives the target-text setting. Directory layout adds
only the parents of those instructions. Git's snapshot/blob fidelity is an external boundary. -/
theorem prepareGit_sound (metadata captured : List Item) (entries : List GitEntry)
    (items : List Item) (ran : prepareGit metadata captured entries = .ok items) :
    ∃ files, GitRepresentations captured entries files ∧
      items = layout (gitMetadata metadata ++ files ++ gitBuildFiles captured entries) := by
  cases found : metadata.find? (fun item => item.relative == [".git", "config"]) with
  | none => simp [prepareGit, found] at ran
  | some config =>
    rcases config with ⟨relative, payload⟩
    cases payload with
    | directory => simp [prepareGit, found] at ran
    | file bytes rights =>
      cases prepared : gitFiles captured entries with
      | error error =>
        simp [prepareGit, found, prepared] at ran
        change Except.error error = .ok items at ran
        cases ran
      | ok files =>
        simp [prepareGit, found, prepared] at ran
        change Except.ok (layout (gitMetadata metadata ++ (files ++ gitBuildFiles captured entries))) =
          .ok items at ran
        cases ran
        exact ⟨files, gitFiles_sound captured entries files prepared, by simp only [List.append_assoc]⟩

/-- The Git writer the cold clone adapter actually runs constructs exactly the indexed account,
admitted untracked build files and required Git metadata. Each indexed link has a target-text regular-file instruction. The
filesystem-model guarantee establishes kinds and placement, including absence of all links.
Destination byte fidelity and Git index/blob completeness remain trusted observations, not
consequences of this entry-kind model. No hypothesis asserts that a completed copy is safe. -/
theorem gitConstruct_io {ops : Ops IO} {C : CopyModel}
    {view : Void IO.RealWorld → C.filesystem.World}
    (corresponds : CopyCorresponds ops C view) (readsEntry : ReadsEntry C.filesystem)
    (readsReal : ReadsReal C.filesystem) (names : ReadsNames C)
    (directories : CreatesDirectories C) (files : CreatesFiles C) (target : FilePath)
    (metadata captured : List Item) (entries : List GitEntry) (w : Void IO.RealWorld) :
    RunsTo view (gitConstructWith ops target metadata captured entries w)
      (fun items after =>
        (∃ indexed, GitRepresentations captured entries indexed ∧
          items = layout (gitMetadata metadata ++ indexed ++ gitBuildFiles captured entries)) ∧
        Holds C.filesystem target items after) (fun _ _ => True) := by
  cases prepared : prepareGit metadata captured entries with
  | error error =>
    simp [gitConstructWith, prepared, eio_throw, RunsTo]
  | ok items =>
    have represented := prepareGit_sound metadata captured entries items prepared
    have built := construct_io corresponds readsEntry readsReal names directories files target items w
    simp only [gitConstructWith, prepared]
    cases ran : constructWith ops target items w with
    | error error after =>
      rw [eio_bind_error ran]
      trivial
    | ok result after =>
      rw [eio_bind_ok ran, eio_pure]
      rw [ran] at built
      exact ⟨represented, built⟩

/-- The shared source capture preserves the observed world and gives its complete selected
source receipt. This applies when a caller combines captured subtrees and generated instructions
before running `constructWith`, as project relocation does. -/
theorem capture_io {ops : Ops IO} {C : CopyModel} {view : Void IO.RealWorld → C.filesystem.World}
    (corresponds : CopyCorresponds ops C view) (readsEntry : ReadsEntry C.filesystem)
    (names : ReadsNames C) (bytes : ReadsBytes C) (selected : FilePath → Bool)
    (depth : Nat) (source : FilePath) (relative : List String) (w : Void IO.RealWorld) :
    RunsTo view (captureWith ops selected depth source relative w)
      (fun items after => after = view w ∧ Captured C (view w) selected source relative items)
      (fun _ after => after = view w) :=
  (capture_agrees corresponds selected depth source relative).transfer w
    (capture_run C readsEntry names bytes selected depth source relative (view w))

/-- Appending instructions with the same writer retains the exact previous plain tree and adds
exactly the named directories/files. The initial tree is an explicit precondition; the theorem
does not authenticate an arbitrary pre-existing workspace or a later fixture mutation. -/
theorem emit_io {ops : Ops IO} {C : CopyModel} {view : Void IO.RealWorld → C.filesystem.World}
    (corresponds : CopyCorresponds ops C view) (directories : CreatesDirectories C)
    (files : CreatesFiles C) (target : FilePath) (done items : List Item) (w : Void IO.RealWorld)
    (initial : Holds C.filesystem target done (view w)) :
    RunsTo view (emitWith ops target items w)
      (fun _ after => Holds C.filesystem target (done ++ items) after) (fun _ _ => True) := by
  apply (emit_agrees corresponds target items).transfer w
  cases ran : (emitWith C.ops target items).run (view w) with
  | error error state => trivial
  | ok result state =>
    cases result
    exact emit_sound C directories files target items done (view w) state initial ran

/-- Admitting an already established directory changes no state. An alias can still be refused;
the result is conditional on success, while every error also preserves the observed world. -/
theorem ensure_present_run (C : CopyModel) (readsEntry : ReadsEntry C.filesystem)
    (readsReal : ReadsReal C.filesystem) (depth : Nat) (parent : FilePath)
    (before : C.filesystem.World) (present : C.filesystem.entry before parent = some .dir) :
    Satisfies ((ensureDirectoryWith C.ops depth parent).run before)
      (fun _ after => after = before) (fun _ after => after = before) := by
  cases depth with
  | zero => simp [ensureDirectoryWith, run_throw, Satisfies]
  | succ depth =>
    simp only [ensureDirectoryWith]
    apply (kind_run C readsEntry parent before).bind
    intro found state read
    rcases read with ⟨unchanged, found⟩
    subst state
    rw [present] at found
    subst found
    have realRead : Satisfies ((C.ops.realPath parent).run before)
        (fun real state => state = before ∧ C.filesystem.real before parent = some real)
        (fun _ state => state = before ∧ C.filesystem.real before parent = none) := by
      rw [C.realPath]
      exact (triple_iff _ _ _ _).mp (readsReal parent before) before rfl
    apply (realRead.mono (fun _ _ h => h.1) (fun _ _ h => h.1)).bind
    intro real state unchanged
    subst state
    cases same : real == parent <;> simp [run_throw, Satisfies]

/-- The actual leaf writer extends an established plain parent with exactly one regular file.
Admission of an arbitrary existing parent is not a claim that its old entries were plain. -/
theorem appendFile_run (C : CopyModel) (readsEntry : ReadsEntry C.filesystem)
    (readsReal : ReadsReal C.filesystem) (directories : CreatesDirectories C)
    (files : CreatesFiles C) (parent : FilePath) (name : String) (bytes : ByteArray)
    (rights : UInt32) (done : List Item) (before : C.filesystem.World)
    (initial : Holds C.filesystem parent done before) :
    Satisfies ((appendFileWith C.ops parent name bytes rights).run before)
      (fun _ after => Holds C.filesystem parent (done ++ [⟨[name], .file bytes rights⟩]) after)
      (fun _ _ => True) := by
  unfold appendFileWith
  apply ((ensure_present_run C readsEntry readsReal 4096 parent before initial.1).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)).bind
  intro result state unchanged
  subst state
  cases result
  cases ran : (emitWith C.ops parent [⟨[name], .file bytes rights⟩]).run before with
  | error error state => trivial
  | ok result state =>
    cases result
    exact emit_sound C directories files parent [⟨[name], .file bytes rights⟩] done before state initial ran

/-- Ancestor admission is the same recursive program at the real observer and model. -/
theorem ensureDirectory_agrees {ops : Ops IO} {C : CopyModel}
    {view : Void IO.RealWorld → C.filesystem.World} (corresponds : CopyCorresponds ops C view)
    (depth : Nat) (path : FilePath) :
    Agrees view (ensureDirectoryWith ops depth path) (ensureDirectoryWith C.ops depth path) := by
  induction depth generalizing path with
  | zero => exact Agrees.throw view _
  | succ depth ih =>
    simp only [ensureDirectoryWith]
    apply (kind_agrees corresponds path).bind
    intro found
    cases found with
    | none =>
      cases path.parent with
      | none => exact Agrees.throw view _
      | some parent => exact (ih parent).bind (fun _ => corresponds.2.2.2.2.1 path)
    | some kind =>
      cases kind with
      | file | symlink | other => exact Agrees.throw view _
      | dir =>
        apply (corresponds.2.2.1 path).bind
        intro real
        split
        · exact Agrees.pure view ()
        · exact Agrees.throw view _

/-- The leaf writer used by copyFile and generated-file creation keeps checked IO correspondence. -/
theorem appendFile_agrees {ops : Ops IO} {C : CopyModel}
    {view : Void IO.RealWorld → C.filesystem.World} (corresponds : CopyCorresponds ops C view)
    (parent : FilePath) (name : String) (bytes : ByteArray) (rights : UInt32) :
    Agrees view (appendFileWith ops parent name bytes rights)
      (appendFileWith C.ops parent name bytes rights) := by
  unfold appendFileWith
  exact (ensureDirectory_agrees corresponds 4096 parent).bind
    (fun _ => emit_agrees corresponds parent [⟨[name], .file bytes rights⟩])

/-- The actual IO leaf writer retains a previously constructed plain parent and adds precisely
its regular-file instruction, including its ancestor admission. Native creation remains assumed. -/
theorem appendFile_io {ops : Ops IO} {C : CopyModel}
    {view : Void IO.RealWorld → C.filesystem.World} (corresponds : CopyCorresponds ops C view)
    (readsEntry : ReadsEntry C.filesystem) (readsReal : ReadsReal C.filesystem)
    (directories : CreatesDirectories C) (files : CreatesFiles C) (parent : FilePath)
    (name : String) (bytes : ByteArray) (rights : UInt32) (done : List Item)
    (w : Void IO.RealWorld) (initial : Holds C.filesystem parent done (view w)) :
    RunsTo view (appendFileWith ops parent name bytes rights w)
      (fun _ after => Holds C.filesystem parent (done ++ [⟨[name], .file bytes rights⟩]) after)
      (fun _ _ => True) :=
  (appendFile_agrees corresponds parent name bytes rights).transfer w
    (appendFile_run C readsEntry readsReal directories files parent name bytes rights done (view w) initial)

end Regula.Filesystem.Construction
