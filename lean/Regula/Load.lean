/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

public import Lean.Environment
public import Regula.Input
public import Regula.Rules
import Lean.Compiler.ExternAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Util.Path
import Lean.Compiler.Old

/-!
# The loader of the closed input

What reads a loaded environment into the closed input (`Regula.Closed.Input`), and refuses, as an
error that makes the run `incomplete` (RG2001), what it cannot read. `Regula.Workspace` holds the
part that calls Lake. `Facts.input` is a pure function of the
environment, and `specification/RegulaSpecification/Proofs/Load.lean` states what it gives in terms
of the environment. What that leaves assumed about Lean and Lake is in the specification's trusted
base.

What it reads, and through what:

- The constants: each constant of an environment that `Lean.importModules` loads with `loadExts :=
  false`, so no extension state is built and no initializer of a loaded module runs, and at the
  level `.private`, so a `module` file gives each constant with its body, exposed or not
  (`Lean/Environment.lean:1871` and `:2183` at v4.35.0).
  `getImplementedBy?` and `isExtern` read the module entries of an extension (`getModuleEntries`),
  which `importModules` sets whatever `loadExts` is, and no extension's built state.
- Each loaded module's own constants: `header.moduleData`, which Lean keeps as each `.olean` holds
  them, so that a constant that Lean's import replaced is read too. What any of them mentions, and
  whether it is an axiom, counts for its name (`Facts.stated`), in a dependency as in a claimed
  module. A claimed module's own constant must also fit the rules itself (`Facts.unread?`).
- The place of each module: where `Lean.findOLean` finds its `.olean` on Lake's search path. A
  claimed module lies below the root package's library directory; a constant of the toolchain is one
  whose module lies below the toolchain's library directory. `Facts` carries that its modules are
  those of the environment's header and what each place decides, and `readModules` constructs both.
-/

public section

namespace Regula.Load

open Lean (ConstantInfo Environment Name findOLean isExtern)
open System (FilePath)
open Regula.Closed

/-- Refuse the input: the run is `incomplete`. -/
def refuse {α : Type} (why : String) : IO α :=
  throw <| IO.userError why

/-- The components of a path, as Lean normalizes it. -/
def parts (p : FilePath) : List String :=
  p.normalize.components.filter (!·.isEmpty)

/-- Whether `path` lies below the directory `dir`, by their components. -/
def below (dir path : FilePath) : Bool :=
  (parts dir).isPrefixOf (parts path) && parts dir != parts path

/-- The kind of a constant: its `ConstantInfo` constructor. -/
def kindOf : ConstantInfo → Kind
  | .axiomInfo _ => .axiom
  | .defnInfo _ => .definition
  | .thmInfo _ => .theorem
  | .opaqueInfo _ => .opaque
  | .quotInfo _ => .quotient
  | .inductInfo _ => .inductive
  | .ctorInfo _ => .constructor
  | .recInfo _ => .recursor

/-- The names of `all`, each once. -/
def dedup (all : Array Name) : Array Name :=
  all.foldl (fun acc n => if acc.contains n then acc else acc.push n) #[]

/-- The constants a constant mentions, the fields that `Lean.collectAxioms` walks: the type and
value of a definition, theorem or opaque constant, the type of an axiom, constructor or recursor,
the type and constructors of an inductive type, and nothing of a quotient
(`Lean/Util/CollectAxioms.lean`). -/
def usesOf (info : ConstantInfo) : Array Name :=
  dedup <| match info with
    | .axiomInfo v => v.type.getUsedConstants
    | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
    | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
    | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
    | .quotInfo _ => #[]
    | .ctorInfo v => v.type.getUsedConstants
    | .recInfo v => v.type.getUsedConstants
    | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

/-- What the input states a constant mentions: what the constant that the environment keeps mentions
and what each constant in `stated`, those of its name that the loaded modules state, mentions. -/
def usesIn (info : ConstantInfo) (stated : List ConstantInfo) : Array Name :=
  dedup (stated.foldl (fun acc v => acc ++ usesOf v) (usesOf info))

/-- The kind the input states of a constant: an axiom when a constant in `stated`, those of its name
that the loaded modules state, is one, and otherwise the kind of the constant the environment keeps.
-/
def kindIn (info : ConstantInfo) (stated : List ConstantInfo) : Kind :=
  if stated.any (kindOf · == .axiom) then .axiom else kindOf info

/-- The constants that the value of a definition, theorem or opaque constant mentions, and nothing
of any other constant. -/
def valueUsesOf : ConstantInfo → Array Name
  | .defnInfo v => v.value.getUsedConstants
  | .thmInfo v => v.value.getUsedConstants
  | .opaqueInfo v => v.value.getUsedConstants
  | .axiomInfo _ | .quotInfo _ | .inductInfo _ | .ctorInfo _ | .recInfo _ => #[]

/-- The safety of a constant, from Lean's two flags. Lean sets at most one of them on a constant
(`ConstantInfo.isUnsafe` and `ConstantInfo.isPartial`). -/
def safetyOf (info : ConstantInfo) : Safety :=
  if info.isUnsafe then .unsafe else if info.isPartial then .partial else .safe

/-- One module that an environment loaded, with where its `.olean` lies and what that place
decides. -/
structure LoadedModule where
  /-- The module. -/
  name : Name
  /-- Where its `.olean` lies. -/
  olean : FilePath
  /-- Whether it lies in the toolchain's library. -/
  inToolchain : Bool
  /-- Whether it lies in the root package's library: the module is claimed. -/
  claimed : Bool

/-- A module at the place `olean`, with what that place decides under the two library directories.
-/
def LoadedModule.ofPlace (toolchainDir rootDir : FilePath) (name : Name) (olean : FilePath) :
    LoadedModule :=
  { name, olean, inToolchain := below toolchainDir olean, claimed := below rootDir olean }

/-- What the loader knows of one loaded environment. -/
structure Facts where
  /-- The loaded environment. -/
  env : Environment
  /-- The toolchain's library directory. -/
  toolchainDir : FilePath
  /-- The root package's library directory. -/
  rootDir : FilePath
  /-- Each module of the environment, by its index. -/
  modules : Array LoadedModule
  /-- These are the modules of the environment's header, in its order. -/
  names : modules.toList.map (·.name) = env.header.moduleNames.toList
  /-- What each module's place decides is what its fields say. -/
  placed : ∀ m ∈ modules, m = LoadedModule.ofPlace toolchainDir rootDir m.name m.olean

/-- Each of the modules `names`, in that order, with where Lean finds its `.olean` on Lake's search
path. The result carries that it is these modules and what each place decides. -/
def readModules (toolchainDir rootDir : FilePath) : (names : List Name) →
    IO { ms : List LoadedModule // ms.map (·.name) = names ∧
      ∀ m ∈ ms, m = LoadedModule.ofPlace toolchainDir rootDir m.name m.olean }
  | [] => pure ⟨[], rfl, by simp⟩
  | n :: rest => do
    let olean ← try findOLean n catch e =>
      refuse s!"the module {n} was loaded and has no .olean on Lake's search path: {e}"
    let ⟨ms, hn, hp⟩ ← readModules toolchainDir rootDir rest
    pure ⟨LoadedModule.ofPlace toolchainDir rootDir n olean :: ms,
      by simp [LoadedModule.ofPlace, hn],
      by
        intro m hm
        rcases List.mem_cons.mp hm with rfl | hm
        · rfl
        · exact hp m hm⟩

/-- The facts of `env`, from where the `.olean` of each of its modules lies. -/
def Facts.load (env : Environment) (toolchainDir rootDir : FilePath) : IO Facts := do
  let ⟨ms, hn, hp⟩ ← readModules toolchainDir rootDir env.header.moduleNames.toList
  return { env, toolchainDir, rootDir, modules := ms.toArray, names := by simpa using hn,
           placed := by simpa using hp }

/-- The modules that are claimed. -/
def Facts.claimed (f : Facts) : List Name :=
  (f.modules.toList.filter (·.claimed)).map (·.name)

/-- The loaded module whose `.olean` holds constant `n`. -/
def Facts.info? (f : Facts) (n : Name) : Option LoadedModule :=
  (f.env.getModuleIdxFor? n).bind fun idx => f.modules[idx.toNat]?

/-- The name of the module whose `.olean` holds constant `n`. -/
def Facts.moduleOf? (f : Facts) (n : Name) : Option Name :=
  (f.info? n).map (·.name)

/-- Each constant of each name, as the own data of each loaded module states it, claimed or not.
Lean's import keeps one constant of a name (`Facts.shown`), so this is what the others say. -/
def Facts.stated (f : Facts) : Std.HashMap Name (List ConstantInfo) :=
  f.env.header.moduleData.foldl (init := {}) fun acc data =>
    (data.constNames.zip data.constants).foldl (init := acc) fun acc x =>
      acc.insert x.1 (x.2 :: acc.getD x.1 [])

/-- The constant `n` of the module `m`, as the closed input states it: `info` is the constant that
the environment keeps, and `stated` those of its name that the loaded modules state. -/
def Facts.declIn (f : Facts) (n : Name) (m : LoadedModule) (info : ConstantInfo)
    (stated : List ConstantInfo) : Decl where
  name := n
  module := m.name
  kind := kindIn info stated
  safety := safetyOf info
  uses := (usesIn info stated).toList
  valueUses := (valueUsesOf info).toList
  implementedBy := Lean.Compiler.getImplementedBy? f.env n
  isExtern := isExtern f.env n
  inToolchain := m.inToolchain

/-- The constant `n` as the closed input states it, or the refusal of a constant that no loaded
module holds. -/
def Facts.decl (f : Facts) (n : Name) (info : ConstantInfo) (stated : List ConstantInfo) :
    Except String Decl :=
  match f.info? n with
  | some m => .ok (f.declIn n m info stated)
  | none => .error s!"the constant {n} was loaded, and Lean gives it no module"

/-- What running a function of `Except` over a list gives, member by member. -/
theorem mapM_ok {α β ε : Type} (g : α → Except ε β) (name : β → Name) (key : α → Name)
    (hname : ∀ a b, g a = .ok b → name b = key a) (l : List α) (r : List β)
    (h : l.mapM g = .ok r) :
    (∀ b ∈ r, ∃ a ∈ l, g a = .ok b) ∧ (∀ a ∈ l, ∃ b ∈ r, g a = .ok b) ∧
      r.map name = l.map key := by
  induction l generalizing r with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  | cons a l ih =>
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases hg : g a with
    | error e =>
      rw [hg] at h
      cases h
    | ok b =>
      rw [hg] at h
      simp only at h
      cases hl : l.mapM g with
      | error e =>
        rw [hl] at h
        cases h
      | ok r' =>
        rw [hl] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨h1, h2, h3⟩ := ih r' hl
        refine ⟨?_, ?_, ?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact ⟨a, List.mem_cons_self .., hg⟩
          · obtain ⟨x, hx, hxy⟩ := h1 y hy
            exact ⟨x, List.mem_cons_of_mem _ hx, hxy⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨b, List.mem_cons_self .., hg⟩
          · obtain ⟨y, hy, hxy⟩ := h2 x hx
            exact ⟨y, List.mem_cons_of_mem _ hy, hxy⟩
        · simp [hname a b hg, h3]

/-- What `Facts.decl` gives has the name it was asked for. -/
theorem Facts.decl_name (f : Facts) {n : Name} {info : ConstantInfo} {stated : List ConstantInfo}
    {d : Decl} (h : f.decl n info stated = .ok d) : d.name = n := by
  simp only [Facts.decl] at h
  split at h
  · cases h
    rfl
  · cases h

/-- The constants that the environment keeps have distinct names, so a reading of them has too: the
keys of a hash map are distinct (`Std.HashMap.distinct_keys_toList`). -/
theorem Facts.decls_nodup (f : Facts) {stated : Name → List ConstantInfo} {decls : List Decl}
    (h : f.env.constants.map₁.toList.mapM (fun x => f.decl x.1 x.2 (stated x.1)) = .ok decls) :
    (decls.map (·.name)).Nodup := by
  rw [(mapM_ok _ (·.name) (·.1) (fun _ _ hb => f.decl_name hb) _ _ h).2.2]
  refine List.pairwise_map.mpr (Std.HashMap.distinct_keys_toList.imp ?_)
  intro a b hab heq
  simp [heq] at hab

/-- What the rules read of a constant: its kind, its safety and what it mentions. -/
def readOf (info : ConstantInfo) : Kind × Safety × List Name × List Name :=
  (kindOf info, safetyOf info, (usesOf info).toList, (valueUsesOf info).toList)

/-- Each constant of each claimed module, with its module, as that module's `.olean` states it. -/
def Facts.claimedConstants (f : Facts) : List (Name × Name × ConstantInfo) :=
  ((f.modules.zip f.env.header.moduleData).toList.filter (·.1.claimed)).flatMap fun (m, data) =>
    (data.constNames.zip data.constants).toList.map fun (n, info) => (m.name, n, info)

/-- Whether the environment shows a constant of a claimed module to the rules: it holds a constant
of that name of which the rules read the same, in a claimed module. Lean's import merges two
theorems of one name and type, and a theorem with an axiom of that name and type: it keeps one, and
gives the name the first module that holds it (`subsumesInfo` and `finalizeImport`,
`Lean/Environment.lean:2269` and `2336-2345`). So a module's own constant can be one that no rule
reads as a subject. What a dropped constant mentions, and whether it is an axiom, the input still
states of its name (`Facts.stated`), in every loaded module; this check decides whether the rules
read a claimed module's own constant as a subject. -/
def Facts.shown (f : Facts) (x : Name × Name × ConstantInfo) : Bool :=
  match f.env.constants.map₁[x.2.1]?, f.info? x.2.1 with
  | some kept, some m => decide (readOf kept = readOf x.2.2) && m.claimed
  | none, _ | some _, none => false

/-- Whether a constant `n` that the environment does not show is what the rules would admit: a
theorem, safe, with no name that the compiler reads as a recursion helper's, whose value mentions no
loop construct, and each constant it mentions is held and reaches only axioms that the profile
admits. Lean regenerates a definition's equation lemmas in each module that needs them, so such a
constant can be conforming. -/
def fitsUnshown {i : Input} (t : Tables i) (n : Name) (info : ConstantInfo) : Bool :=
  kindOf info == .theorem && safetyOf info == .safe &&
    (Lean.Compiler.isUnsafeRecName? n).isNone &&
    loopConstructs.all (!(valueUsesOf info).contains ·) &&
    (usesOf info).all fun u => t.index.contains u && (t.axiomSet u).all (t.admits i.profile ·)

/-- The first constant of a claimed module that the environment does not show and that
`fitsUnshown` does not admit, with its module. -/
def Facts.unread? (f : Facts) (i : Input) : Option (Name × Name) :=
  match f.claimedConstants.filter (!f.shown ·) with
  | [] => none
  | unshown =>
    let t := i.tables
    (unshown.find? fun x => !fitsUnshown t x.2.1 x.2.2).map fun x => (x.1, x.2.1)

/-- The closed input of the environment that `f` describes, under the profile `profile`. It refuses
a module of `roots`, the default targets, that `f` does not claim, a constant with no module, a
reading that the admission refuses (`Draft.admit`), and a constant that `Facts.unread?` gives. -/
def Facts.input (f : Facts) (roots : List Name) (profile : Profile) : Except String Input :=
  let claimed := f.claimed
  match roots.find? (!claimed.contains ·) with
  | some m => .error s!"the module {m} of a default target has its .olean outside the root \
      package's build"
  | none =>
    let stated := f.stated
    match h : f.env.constants.map₁.toList.mapM (fun x => f.decl x.1 x.2 (stated.getD x.1 [])) with
    | .error why => .error why
    | .ok decls =>
      let draft : Draft :=
        { profile, modules := claimed, decls,
          unique := f.decls_nodup (stated := (stated.getD · [])) h }
      match draft.admit with
      | .error why => .error why
      | .ok i =>
        match f.unread? i with
        | some (m, n) => .error s!"the module {m} holds the constant {n}, which Lean's import \
            replaced with another of that name, and this one is no theorem within the profile or \
            has a recursion helper's name"
        | none => .ok i

/-- Whether `root` is the last workspace library directory before Lake's library in the received
search path. Lake v4.35.0 `Package.lint` runs the driver without changing its directory
(`Lake/CLI/Actions.lean`), and `Workspace.augmentedLeanPath` supplies workspace libraries, then the
collocated Lake library, then inherited entries. The root package is first in Lake's package array,
so `Workspace.leanPath` puts its library last.

Assumes: Lake supplies that composition; its library is not a workspace library; and distinct
packages do not configure a shared library directory. Under those assumptions the theorem below
identifies the dispatching root, whatever search path the caller inherited. -/
def dispatchedFrom (root lakeLib : String) (leanPath : List String) : Bool :=
  decide ((leanPath.takeWhile (· ≠ lakeLib)).getLast? = some root) &&
    decide (lakeLib ∈ leanPath)

/-- The search path that Lake gave this process, or a refusal when no Lake did. -/
def receivedLeanPath : IO (List String) := do
  let some leanPath ← IO.getEnv "LEAN_PATH"
    | refuse "LEAN_PATH is not set, so the workspace that Lake dispatched is not known: run the \
        checker with `lake lint` or `lake exe lint`, which set it"
  return (System.SearchPath.parse leanPath).map toString

/-- Refuse unless the workspace with the library directory `root` is the one Lake dispatched. -/
def requireDispatched (root lakeLib : FilePath) : IO Unit := do
  unless dispatchedFrom root.toString lakeLib.toString (← receivedLeanPath) do
    refuse "the current directory is not the workspace Lake dispatched; run `lake lint` from that \
      workspace's directory"

/-- The closed input of the finished build whose default targets' modules are `roots`, on the search
path `leanPath`, or an error that refuses it. -/
def inputFrom (leanPath : List FilePath) (roots : Array Name) (toolchainDir rootDir : FilePath)
    (profile : Profile) : IO Input := do
  Lean.searchPathRef.set leanPath
  let env ←
    try Lean.importModules (roots.map ({ module := · })) {} (loadExts := false) (level := .private)
    catch e => refuse s!"Lean could not load the modules of the default targets: {e}"
  let f ← Facts.load env toolchainDir rootDir
  match f.input roots.toList profile with
  | .ok input => return input
  | .error why => refuse why

/-- For every search path of Lake's composition, the dispatch check accepts exactly the last
workspace library directory. Inherited entries cannot make a different root pass. -/
theorem dispatchedFrom_iff {root lakeLib : String} {dispatching inherited : List String}
    (h : lakeLib ∉ dispatching) :
    dispatchedFrom root lakeLib (dispatching ++ lakeLib :: inherited) = true ↔
      dispatching.getLast? = some root := by
  have hall : ∀ a ∈ dispatching, decide (a ≠ lakeLib) = true := by
    intro a ha
    simp only [ne_eq, decide_eq_true_eq]
    exact fun hal => h (hal ▸ ha)
  have htake : (dispatching ++ lakeLib :: inherited).takeWhile (fun a => decide (a ≠ lakeLib)) =
      dispatching := by
    rw [List.takeWhile_append_of_pos hall]
    simp
  simp only [dispatchedFrom, htake, Bool.and_eq_true, decide_eq_true_eq]
  simp

end Regula.Load
