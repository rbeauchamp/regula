module

public import RegulaSpecification.Effects

@[expose] public section

namespace RegulaSpecification.Effects

open Lean (Name Syntax Environment Import MessageLog)
open Lean.Parser (InputContext ModuleParserState mkInputContext)
open System (FilePath)
open Regula.Effect
open Regula.Language
open RegulaSpecification.Language

variable {L E : Type}

inductive KeyPath : Name → Lake.Toml.Table → Name → Prop where
  | leaf {pre k v t} : (k, v) ∈ t.items → (∀ r sub, v ≠ .table r sub) →
      (∀ r xs, v = .array r xs → ∀ r' sub, Lake.Toml.Value.table r' sub ∉ xs) →
      KeyPath pre t (pre ++ k)
  | empty {pre k r sub t} : (k, Lake.Toml.Value.table r sub) ∈ t.items → sub.items.isEmpty = true →
      KeyPath pre t (pre ++ k)
  | under {pre k r sub t n} : (k, Lake.Toml.Value.table r sub) ∈ t.items → KeyPath (pre ++ k) sub n →
      KeyPath pre t n
  | emptyIn {pre k r xs r' sub t} : (k, Lake.Toml.Value.array r xs) ∈ t.items →
      Lake.Toml.Value.table r' sub ∈ xs → sub.items.isEmpty = true → KeyPath pre t (pre ++ k)
  | underIn {pre k r xs r' sub t n} : (k, Lake.Toml.Value.array r xs) ∈ t.items →
      Lake.Toml.Value.table r' sub ∈ xs → KeyPath (pre ++ k) sub n → KeyPath pre t n

inductive Deeper : Nat → Lake.Toml.Table → Prop where
  | zero {t} : Deeper 0 t
  | table {n k r sub t} : (k, Lake.Toml.Value.table r sub) ∈ t.items → sub.items.isEmpty = false →
      Deeper n sub → Deeper (n + 1) t
  | array {n k r xs r' sub t} : (k, Lake.Toml.Value.array r xs) ∈ t.items →
      Lake.Toml.Value.table r' sub ∈ xs → sub.items.isEmpty = false → Deeper n sub → Deeper (n + 1) t

def OutsideTree (tree path : FilePath) : Prop :=
  (∀ rel, ¬ TreeRelative (parts tree) (parts path) rel) ∨
    ∃ d, path.parent = some d ∧ ∀ rel, ¬ TreeRelative (parts tree) (parts d) rel

def FileOfModule (root : Root L) (modules : List (Name × FilePath)) (m : Name) (path : FilePath) : Prop :=
  (m, path) ∈ modules ∨ root.resolve m = some path

def Apart (a b : FilePath) : Prop :=
  ¬ (parts a <+: parts b) ∧ ¬ (parts b <+: parts a)

inductive Sees (headers : List (Name × Array Import)) (held : List Name) : Name → Name → Prop where
  | self {n} : n ∈ held → Sees headers held n n
  | through {m imports i n} : m ∉ held → headers.lookup m = some imports → i ∈ imports →
      i.isExported = true → Sees headers held i.module n → Sees headers held m n

structure Evidence (t : List (Event L E)) (dir dirTree : FilePath) (held : List String → Option String)
    (r : Reading) : Prop where
  places : ∃ project tree, (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t ∧
    (⟨.realPath dirTree, .ok tree⟩ : Event L E) ∈ t ∧ Apart project tree ∧
    (∃ text real, (⟨.readFile (project / "lean-toolchain"), .ok text⟩ : Event L E) ∈ t ∧
      (⟨.realPath (project / "lean-toolchain"), .ok real⟩ : Event L E) ∈ t ∧
      parts real = parts (project / "lean-toolchain") ∧
      parts project <+: parts (project / "lean-toolchain") ∧
      text.trimAscii.toString = leanToolchain) ∧
    (∃ e, (⟨.symlinkMetadata (project / "lakefile.lean"), .error e⟩ : Event L E) ∈ t ∧
      ∃ name code details, e = .noFileOrDirectory name code details) ∧
    (∃ text real table,
      (⟨.realPath (project / "lakefile.toml"), .ok real⟩ : Event L E) ∈ t ∧
      parts real = parts (project / "lakefile.toml") ∧
      parts project <+: parts (project / "lakefile.toml") ∧
      (⟨.readFile (project / "lakefile.toml"), .ok text⟩ : Event L E) ∈ t ∧
      (⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩ : Event L E) ∈ t ∧
      held (parts (tree / "lakefile.toml")) = some text ∧
      ¬ Deeper 8 table ∧
      ∀ n, KeyPath .anonymous table n → n ∈ r.configKeys) ∧
    held (parts (tree / "lean-toolchain")) = some leanToolchain ∧
    ¬ OutsideTree tree (tree / "lakefile.toml") ∧ ¬ OutsideTree tree (tree / "lean-toolchain") ∧
    ∃ sysroot root log modules,
      (⟨.getEnv "LEAN_SYSROOT", some sysroot⟩ : Event L E) ∈ t ∧
      (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ t ∧
      DefaultModules t root root.defaultTargets modules ∧
      r.roots = modules.map (·.1) ∧
      (∀ d ∈ root.sourceDirs, ∃ rel, TreeRelative (parts tree) (parts d) rel ∧ ∀ c ∈ rel, ClosedComponent c) ∧
      (∀ lib ∈ root.libraries, ∀ g ∈ lib.2, ∃ n, g = .one n) ∧
      (∀ n ∈ root.targets, ClosedModuleName n) ∧
      (∀ m file, (m, file) ∈ modules → ∃ other, root.resolve m = some other ∧ parts other = parts file) ∧
      (∀ target ∈ root.defaultTargets, (root.findLib target).isSome = true) ∧
      ∃ (headers : List (Name × Array Import)) (toolchain : List Name),
      modules.length + (headers.map (·.2.size)).sum ≤ 1000000 ∧
      (headers.map (·.1)).Nodup ∧
      (∀ m path, Compiled headers root modules m path → ¬ OutsideTree tree path ∧
        ∃ f ∈ r.files, f.module = m ∧ ∃ imports mods text, headers.lookup m = some imports ∧
          ReadText t root project tree f path imports mods text ∧ held (parts path) = some text) ∧
      (∀ n ∈ toolchain, HeldByToolchain t root n) ∧
      (∀ f ∈ r.files, ∃ path imports mods text, FileOfModule root modules f.module path ∧
        ReadText t root project tree f path imports mods text ∧ held (parts path) = some text ∧
        headers.lookup f.module = some imports ∧
        (∀ n, n ∈ mods ↔ ∃ m ∈ imports, Sees headers toolchain m.module n) ∧
        ∀ i ∈ imports, (i.module ∈ r.reached ∨
          (root.resolve i.module = none ∧ modules.lookup i.module = none ∧
            HeldByToolchain t root i.module)) ∧ ClosedModuleName i.module ∧ i.module.getRoot ≠ `Mathlib) ∧
      ∀ p text, held p = some text → p = parts (tree / "lakefile.toml") ∨ p = parts (tree / "lean-toolchain") ∨
        ∃ f ∈ r.files, ∃ path imports mods, FileOfModule root modules f.module path ∧ parts path = p ∧
          ReadText t root project tree f path imports mods text

