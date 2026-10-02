module

public import RegulaPolicy.Compiler

/-! # Development compiler qualification decisions

The driver executes these recipes and this completion decision. Completion means that
all named commands returned zero for unchanged observed inputs. It grants no admission
authority and proves nothing about the processes, compiler executable, or filesystem. -/

@[expose] public section

namespace Regula.Toolchain

/-- A compiler's self-reported version and full source commit. -/
structure Identity where
  /-- The complete version string, including a prerelease suffix. -/
  version : String
  /-- The full forty-character Git commit. -/
  commit : String
  deriving BEq, DecidableEq, Repr

/-- A nonempty version and a complete lowercase hexadecimal source commit. -/
def Identity.valid (i : Identity) : Bool :=
  !i.version.isEmpty && i.commit.length == 40 &&
    i.commit.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

/-- Admit the compiler probe's exact two-line output, including its final newline. -/
def parseIdentity (output : String) : Except String Identity :=
  match output.splitOn "\n" with
  | [v, h, ""] =>
    let i := Identity.mk v h
    if i.valid then .ok i else .error "compiler identity is incomplete"
  | _ => .error "compiler probe did not return exactly a version and full commit"

/-- Parsing cannot replace a malformed or incomplete identity with a default. -/
theorem parseIdentity_valid {output : String} {i : Identity}
    (h : parseIdentity output = .ok i) : i.valid = true := by
  unfold parseIdentity at h
  split at h
  · dsimp only at h
    split at h
    · cases h; assumption
    · cases h
  · cases h

/-- One existing build or detector campaign, in dependency order. -/
structure Campaign where
  /-- A stable receipt/log name. -/
  name : String
  /-- Arguments to the selected toolchain's Lake executable. -/
  args : List String
  deriving BEq, DecidableEq, Repr

/-- Core checker qualification; Mathlib, Verso and the website corpus are separate claims. -/
def campaigns : List Campaign := [
  ⟨"build", ["build", "axiomGate", "checkerSelftest", "qualify", "lint", "regula"]⟩,
  ⟨"fixtures", ["exe", "checkerSelftest", "--build-bound", "--partition", "fixtures"]⟩,
  ⟨"producers", ["exe", "qualify", "--under-deadline", "producers"]⟩,
  ⟨"history", ["exe", "qualify", "--under-deadline", "history"]⟩,
  ⟨"structural", ["exe", "checkerSelftest", "--build-bound", "--partition", "structural"]⟩,
  ⟨"execution", ["exe", "checkerSelftest", "--build-bound", "--partition", "execution"]⟩,
  ⟨"lint-driver", ["exe", "checkerSelftest", "--build-bound", "--partition", "lint-driver"]⟩,
  ⟨"self-audit", ["exe", "qualify", "--under-deadline", "self-audit"]⟩]

/-- Recorded exit observations in the exact required order, without omitted commands. -/
def complete (results : List (Campaign × UInt32)) : Bool :=
  decide (results.map Prod.fst = campaigns) && results.all (fun r => r.2 == 0)

/-- Completion requires all recipes, in order, with a zero observed exit for every one. -/
theorem complete_iff (results : List (Campaign × UInt32)) : complete results = true ↔
    results.map Prod.fst = campaigns ∧ ∀ r ∈ results, r.2 = 0 := by
  simp [complete, List.all_eq_true]

end Regula.Toolchain
