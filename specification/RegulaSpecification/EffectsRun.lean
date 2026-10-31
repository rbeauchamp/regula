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

/-- The checker's program lies outside the project and the Lake that started it dispatched from the checker's
own package, by this run's responses. `lakeLib` is the library directory of the Lake beside this Lean. -/
def StartedOutside (t : List (Event L E)) (project lakeLib : FilePath) : Prop :=
  ∃ app real own leanPath,
    (⟨.appPath, .ok app⟩ : Event L E) ∈ t ∧ (⟨.realPath app, .ok real⟩ : Event L E) ∈ t ∧
    (⟨.getEnv "LEAN_PATH", some leanPath⟩ : Event L E) ∈ t ∧
    (real.parent.bind (·.parent)).map (· / "lib" / "lean") = some own ∧
    Regula.Load.below project real = false ∧
    Regula.Load.dispatchedFrom own.toString lakeLib.toString
      ((System.SearchPath.parse leanPath).map toString) = true

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
and so is the configuration. -/
structure Evidence (t : List (Event L E)) (dir dirTree : FilePath) (r : Reading) : Prop where
  /-- The project and the tree have real paths, and neither lies in the other. -/
  places : ∃ project tree, (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t ∧
    (⟨.realPath dirTree, .ok tree⟩ : Event L E) ∈ t ∧ Apart project tree ∧
    -- The start from outside.
    (∃ sysroot program lakeLib, (⟨.lakeInstall sysroot, (program, lakeLib)⟩ : Event L E) ∈ t ∧
      StartedOutside t project lakeLib) ∧
    -- `lean-toolchain`.
    (∃ text real, (⟨.readFile (project / "lean-toolchain"), .ok text⟩ : Event L E) ∈ t ∧
      (⟨.realPath (project / "lean-toolchain"), .ok real⟩ : Event L E) ∈ t ∧
      parts real = parts (project / "lean-toolchain") ∧
      parts project <+: parts (project / "lean-toolchain") ∧
      text.trimAscii.toString = leanToolchain) ∧
    -- `lakefile.lean` is absent, by the name.
    (∃ e, (⟨.symlinkMetadata (project / "lakefile.lean"), .error e⟩ : Event L E) ∈ t ∧
      ∃ name code details, e = .noFileOrDirectory name code details) ∧
    -- `lakefile.toml`: the text read is the text Lake's parser read and the text in the tree, and each of
    -- its key paths is in the reading.
    (∃ text real table,
      (⟨.realPath (project / "lakefile.toml"), .ok real⟩ : Event L E) ∈ t ∧
      parts real = parts (project / "lakefile.toml") ∧
      parts project <+: parts (project / "lakefile.toml") ∧
      (⟨.readFile (project / "lakefile.toml"), .ok text⟩ : Event L E) ∈ t ∧
      (⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩ : Event L E) ∈ t ∧
      (⟨.writeFile (tree / "lakefile.toml") text, .ok ()⟩ : Event L E) ∈ t ∧
      ∀ n, KeyPath .anonymous table n → n ∈ r.configKeys) ∧
    -- Each file Lake compiles for the claim is read, as `ReadAs` states, and each file read is one of them.
    ∃ sysroot root log modules,
      (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ t ∧
      DefaultModules t root root.defaultTargets modules ∧
      r.roots = modules.map (·.1) ∧
      (∀ m path, Compiled t project tree root modules r m path →
        ∃ f ∈ r.files, f.module = m ∧ ∃ imports mods, ReadAs t project tree f path imports mods) ∧
      ∃ (headers : List (Name × Array Import)) (held : List Name),
      (∀ n ∈ held, HeldByToolchain t root n) ∧
      (∀ f ∈ r.files, ∃ path imports mods, ReadAs t project tree f path imports mods ∧
        headers.lookup f.module = some imports ∧
        (∀ n, n ∈ mods ↔ ∃ m ∈ imports, Sees headers held m.module n) ∧
        Compiled t project tree root modules r f.module path ∧
        -- Each import is read or is the toolchain's.
        ∀ i ∈ imports, i.module ∈ r.reached ∨
          (root.resolve i.module = none ∧ modules.lookup i.module = none ∧
            HeldByToolchain t root i.module))

