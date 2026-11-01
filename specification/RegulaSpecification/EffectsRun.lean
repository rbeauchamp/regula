/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Effects

/-!
# What the reader must have done, and what a whole run must do

`Evidence` is what a reading the check admits rests on: each thing it states was read, by an event of the run.
`Reason` is the closed set of what may keep a project from being admitted: a refusal or a failure to read
that has no such reason is no behaviour of the checker, so a reader that refuses everything is ruled out too.
`FullRun` and `PlainRun` state a whole run in those terms.
-/

namespace RegulaSpecification.Effects

open Lean (Name Syntax Environment Import MessageLog)
open Lean.Parser (InputContext ModuleParserState mkInputContext)
open System (FilePath)
open Regula.Effect
open Regula.Language
open RegulaSpecification.Language

variable {L E : Type}

/-- A key path of a TOML table: each key whose value is neither a table nor an array that holds one, and each
key of each table and array of tables under it. A table with no key is a key path itself. -/
inductive KeyPath : Name → Lake.Toml.Table → Name → Prop where
  /-- A key whose value holds no table. -/
  | leaf {pre k v t} : (k, v) ∈ t.items → (∀ r sub, v ≠ .table r sub) →
      (∀ r xs, v = .array r xs → ∀ r' sub, Lake.Toml.Value.table r' sub ∉ xs) →
      KeyPath pre t (pre ++ k)
  /-- A key whose value is an empty table. -/
  | empty {pre k r sub t} : (k, Lake.Toml.Value.table r sub) ∈ t.items → sub.items.isEmpty = true →
      KeyPath pre t (pre ++ k)
  /-- A key path below a table. -/
  | under {pre k r sub t n} : (k, Lake.Toml.Value.table r sub) ∈ t.items → KeyPath (pre ++ k) sub n →
      KeyPath pre t n
  /-- An empty table in an array. -/
  | emptyIn {pre k r xs r' sub t} : (k, Lake.Toml.Value.array r xs) ∈ t.items →
      Lake.Toml.Value.table r' sub ∈ xs → sub.items.isEmpty = true → KeyPath pre t (pre ++ k)
  /-- A key path below a table in an array. -/
  | underIn {pre k r xs r' sub t n} : (k, Lake.Toml.Value.array r xs) ∈ t.items →
      Lake.Toml.Value.table r' sub ∈ xs → KeyPath (pre ++ k) sub n → KeyPath pre t n

/-- A table with a chain of more than `n` nested tables, which the reader does not follow. -/
inductive Deeper : Nat → Lake.Toml.Table → Prop where
  /-- Any table is deeper than nothing. -/
  | zero {t} : Deeper 0 t
  /-- Through a table that holds a key. -/
  | table {n k r sub t} : (k, Lake.Toml.Value.table r sub) ∈ t.items → sub.items.isEmpty = false →
      Deeper n sub → Deeper (n + 1) t
  /-- Through a table in an array that holds a key. -/
  | array {n k r xs r' sub t} : (k, Lake.Toml.Value.array r xs) ∈ t.items →
      Lake.Toml.Value.table r' sub ∈ xs → sub.items.isEmpty = false → Deeper n sub → Deeper (n + 1) t

/-- A path, or the directory above it, does not lie below the tree by `TreeRelative`. -/
def OutsideTree (tree path : FilePath) : Prop :=
  (∀ rel, ¬ TreeRelative (parts tree) (parts path) rel) ∨
    ∃ d, path.parent = some d ∧ ∀ rel, ¬ TreeRelative (parts tree) (parts d) rel

/-- The file of a module, as Lake's load names it: a root's own, or what Lake's resolution of an import gives. -/
def FileOfModule (root : Root L) (modules : List (Name × FilePath)) (m : Name) (path : FilePath) : Prop :=
  (m, path) ∈ modules ∨ root.resolve m = some path

/-- Neither of two directories lies at or below the other. -/
def Apart (a b : FilePath) : Prop :=
  ¬ (parts a <+: parts b) ∧ ¬ (parts b <+: parts a)

/-- `Sees headers held m n`: an import of `m` lets a file see the toolchain's module `n`, by the rule of
`importModulesCore` for a `module` file (`Lean/Environment.lean:2108-2190` at v4.35.0): a module of the
toolchain's own closes it there, whose own closure Lean follows, and a project's module passes on each of its
`public` imports, as `headers` gives them. -/
inductive Sees (headers : List (Name × Array Import)) (held : List Name) : Name → Name → Prop where
  /-- The toolchain's own module. -/
  | self {n} : n ∈ held → Sees headers held n n
  /-- Through a `public` import of a project's module. -/
  | through {m imports i n} : m ∉ held → headers.lookup m = some imports → i ∈ imports →
      i.isExported = true → Sees headers held i.module n → Sees headers held m n

/-- What a reading of the project at `dir`, in the checker's tree `dirTree`, rests on: for each thing that the
reading states, the events of the run that gave it. So every file Lake would compile for the claim is read,
and so is the configuration. It also states what makes a project one that nothing keeps from being admitted (`Reason`):
that each path Lake's load names lies in the closed domain, each name too, and that the imports stay within the reader's
bound.

`held` says what stands at each place where the build consumes a text, by the components of a path. So the statement that
the text judged is what stands is about that state, and not about a write that some event once made: `Evidence` with
`held` fixed keeps under more events, and `Decided` gives it `written t`, a fold of the run's own requests over its whole
reading, which observes no file (`ReadBack` is the observation). `held` gives each file Lake would compile the text its
commands were parsed from, the configuration the text Lake's parser read, `lean-toolchain` the pinned text, and no other
path a text. -/
structure Evidence (t : List (Event L E)) (dir dirTree : FilePath) (held : List String → Option String)
    (r : Reading) : Prop where
  /-- The project and the tree have real paths, and neither lies in the other. -/
  places : ∃ project tree, (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t ∧
    (⟨.realPath dirTree, .ok tree⟩ : Event L E) ∈ t ∧ Apart project tree ∧
    -- `lean-toolchain`.
    (∃ text real, (⟨.readFile (project / "lean-toolchain"), .ok text⟩ : Event L E) ∈ t ∧
      (⟨.realPath (project / "lean-toolchain"), .ok real⟩ : Event L E) ∈ t ∧
      parts real = parts (project / "lean-toolchain") ∧
      parts project <+: parts (project / "lean-toolchain") ∧
      text.trimAscii.toString = leanToolchain) ∧
    -- `lakefile.lean` is absent, by the name.
    (∃ e, (⟨.symlinkMetadata (project / "lakefile.lean"), .error e⟩ : Event L E) ∈ t ∧
      ∃ name code details, e = .noFileOrDirectory name code details) ∧
    -- `lakefile.toml`: the text read is the text Lake's parser read and the text `held` gives it, and each of
    -- its key paths is in the reading.
    (∃ text real table,
      (⟨.realPath (project / "lakefile.toml"), .ok real⟩ : Event L E) ∈ t ∧
      parts real = parts (project / "lakefile.toml") ∧
      parts project <+: parts (project / "lakefile.toml") ∧
      (⟨.readFile (project / "lakefile.toml"), .ok text⟩ : Event L E) ∈ t ∧
      (⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩ : Event L E) ∈ t ∧
      held (parts (tree / "lakefile.toml")) = some text ∧
      ¬ Deeper 8 table ∧
      ∀ n, KeyPath .anonymous table n → n ∈ r.configKeys) ∧
    -- `held` gives `lean-toolchain` the pinned text.
    held (parts (tree / "lean-toolchain")) = some leanToolchain ∧
    -- The tree's copies lie below it.
    ¬ OutsideTree tree (tree / "lakefile.toml") ∧ ¬ OutsideTree tree (tree / "lean-toolchain") ∧
    -- Each file Lake compiles for the claim is read, as `ReadText` states, and each file read is one of them.
    ∃ sysroot root log modules,
      (⟨.getEnv "LEAN_SYSROOT", some sysroot⟩ : Event L E) ∈ t ∧
      (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ t ∧
      DefaultModules t root root.defaultTargets modules ∧
      r.roots = modules.map (·.1) ∧
      -- What Lake's load names lies in the closed domain.
      (∀ d ∈ root.sourceDirs, ∃ rel, TreeRelative (parts tree) (parts d) rel) ∧
      (∀ lib ∈ root.libraries, ∀ g ∈ lib.2, ∃ n, g = .one n) ∧
      (∀ n ∈ root.targets, ClosedModuleName n) ∧
      -- One name, one file: two paths of one name have one list of components, whatever their spelling.
      (∀ m file other, (m, file) ∈ modules → root.resolve m = some other → parts other = parts file) ∧
      (∀ m file other, (m, file) ∈ modules → (m, other) ∈ modules → parts other = parts file) ∧
      ∃ (headers : List (Name × Array Import)) (toolchain : List Name),
      -- The imports stay within the reader's bound.
      modules.length + (headers.map (·.2.size)).sum ≤ 1000000 ∧
      (headers.map (·.1)).Nodup ∧
      (∀ m path, Compiled headers root modules m path → ¬ OutsideTree tree path ∧
        ∃ f ∈ r.files, f.module = m ∧ ∃ imports mods text, headers.lookup m = some imports ∧
          ReadText t project tree f path imports mods text ∧ held (parts path) = some text) ∧
      (∀ n ∈ toolchain, HeldByToolchain t n) ∧
      (∀ f ∈ r.files, ∃ path imports mods text, FileOfModule root modules f.module path ∧
        ReadText t project tree f path imports mods text ∧ held (parts path) = some text ∧
        headers.lookup f.module = some imports ∧
        (∀ n, n ∈ mods ↔ ∃ m ∈ imports, Sees headers toolchain m.module n) ∧
        -- Each import is read or is the toolchain's, and its name is in the closed domain.
        ∀ i ∈ imports, (i.module ∈ r.reached ∨
          (root.resolve i.module = none ∧ modules.lookup i.module = none ∧
            HeldByToolchain t i.module)) ∧ ClosedModuleName i.module ∧ i.module.getRoot ≠ `Mathlib ∧
          ((modules.lookup i.module).isSome = true → (root.resolve i.module).isSome = true)) ∧
      -- `held` gives no other path a text, unless a file of the reading lies there and was judged from that text.
      ∀ p text, held p = some text → p = parts (tree / "lakefile.toml") ∨ p = parts (tree / "lean-toolchain") ∨
        ∃ f ∈ r.files, ∃ path imports mods, FileOfModule root modules f.module path ∧ parts path = p ∧
          ReadText t project tree f path imports mods text

