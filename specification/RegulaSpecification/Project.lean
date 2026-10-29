import RegulaSpecification.RuleRecord

/-!
# The claim, coverage and the closed subset: RG2002, RG2004, RG2006 and the new RG2007

These rules read Lake's targets, the claim, and each loaded module's imports and extension names.
RG2006 and RG2007 take an allowlist as a parameter: the closed set of option names, and of
environment extensions, that a claimed target or module may use. The specification fixes what
each allowlist may contain (no option that can stop a default warning or a check, and no
extension that registers code Lean runs while it elaborates); #484 fixes their members from an
observation of the pinned toolchain.
-/

namespace RegulaSpecification

open Lean (Name)

namespace Input

variable (i : Input)

/-- The library targets that contain module `m`. -/
def librariesOf (m : Name) : List Target :=
  i.targets.filter fun t => t.kind == .library && t.modules.contains m

/-- Module `m` is covered: it is in exactly one library, or in none and the root of an
executable. -/
def Covered (m : Name) : Prop :=
  (i.librariesOf m).length = 1 ∨
    ((i.librariesOf m) = [] ∧ ∃ t ∈ i.targets, t.kind = .executable ∧ m ∈ t.modules)

/-- The number of claim entries that name target `t`. -/
def entriesFor (t : Name) : Nat := (i.manifest.filter (·.target == t)).length

/-- Target `t` is claimed. -/
def ClaimedTarget (t : Name) : Prop := ∃ p e, (⟨t, .claimed p e⟩ : Entry) ∈ i.manifest

end Input

/-- RG2002: the claim does not classify target `t` exactly once, names a target Lake does not
have, classifies an executable differently from a library that contains its root, or claims a
target that is not a default target, whose modules `lake check` would not check. -/
def Violates2002 (i : Input) (t : Name) : Prop :=
  ((∃ tg ∈ i.targets, tg.name = t) ∧ i.entriesFor t ≠ 1) ∨
    ((∃ e ∈ i.manifest, e.target = t) ∧ ¬ ∃ tg ∈ i.targets, tg.name = t) ∨
    (∃ x ∈ i.targets, x.name = t ∧ x.kind = .executable ∧ ∃ l ∈ i.targets, l.kind = .library ∧
      (∃ m ∈ x.modules, m ∈ l.modules) ∧
      ∃ cx cl, (⟨x.name, cx⟩ : Entry) ∈ i.manifest ∧ (⟨l.name, cl⟩ : Entry) ∈ i.manifest ∧ cx ≠ cl) ∨
    (∃ x ∈ i.targets, x.name = t ∧ i.ClaimedTarget t ∧ x.isDefault = false)

/-- RG2004: a root-package module that Lake builds is not covered, or a claimed module imports a
module of an excluded target. -/
def Violates2004 (i : Input) (m : Name) : Prop :=
  ∃ r ∈ i.modules, r.name = m ∧
    (¬ i.Covered m ∨ (i.ClaimedModule m ∧ ∃ n ∈ r.imports, i.ExcludedModule n))

/-- RG2006: a claimed target does not turn automatic implicits off, gives either option of
automatic implicits a value other than `false` at any position of its options, sets an option
outside the allowlist `allowed`, or changes Lean's process another way (a plugin, a dynamic
library or an extra argument). -/
def Violates2006 (allowed : Name → Prop) (i : Input) (t : Name) : Prop :=
  ∃ tg ∈ i.targets, tg.name = t ∧ i.ClaimedTarget t ∧
    ((`autoImplicit, "false") ∉ tg.options ∨ (`relaxedAutoImplicit, "false") ∉ tg.options ∨
      (∃ o ∈ tg.options, (o.1 = `autoImplicit ∨ o.1 = `relaxedAutoImplicit) ∧ o.2 ≠ "false") ∨
      (∃ o ∈ tg.options, ¬ allowed o.1) ∨ tg.extras ≠ [])

/-- RG2007, new: a claimed module has entries of an environment extension outside the allowlist
`declarative`. -/
def Violates2007 (declarative : Name → Prop) (i : Input) (m : Name) : Prop :=
  i.ClaimedModule m ∧ ∃ r ∈ i.modules, r.name = m ∧ ∃ x ∈ r.extensions, ¬ declarative x

/-- The intent record of RG2002. -/
def rg2002 := ruleRecord "RG2002" Violates2002
/-- The intent record of RG2004. -/
def rg2004 := ruleRecord "RG2004" Violates2004
/-- The intent record of RG2006, for the option allowlist `allowed`. -/
def rg2006 (allowed : Name → Prop) := ruleRecord "RG2006" (Violates2006 allowed)
/-- The intent record of RG2007, for the extension allowlist `declarative`. -/
def rg2007 (declarative : Name → Prop) := ruleRecord "RG2007" (Violates2007 declarative)

/-- Extensions whose entries register code that Lean runs while it elaborates a later command or
module: macros, elaborators, syntax, initializers and `meta` declarations. Five names come from the
observation recorded in the specification; the command and tactic elaborator extensions and
`Lean.builtinInitAttr` carry their declaration names in the pinned toolchain's source. -/
def metaExtensions : List Name :=
  [`Lean.Elab.macroAttribute, `Lean.Elab.Term.termElabAttribute,
    `Lean.Elab.Command.commandElabAttribute, `Lean.Elab.Tactic.tacticElabAttribute,
    `Lean.Parser.parserExtension, `Lean.regularInitAttr, `Lean.builtinInitAttr,
    Name.str (Name.str (Name.num `_private.Lean.Compiler.MetaAttr 0) "Lean") "metaExt"]

/-- What the specification requires of RG2007's allowlist: it admits none of `metaExtensions`. -/
def ClosedAllowlist (declarative : Name → Prop) : Prop := ∀ x ∈ metaExtensions, ¬ declarative x

/-- Under a closed allowlist, a claimed module with a macro, an elaborator, syntax, an initializer
or a `meta` declaration violates RG2007. -/
theorem rg2007_refuses_meta {declarative : Name → Prop} (h : ClosedAllowlist declarative)
    {i : Input} {m : Name} {r : ModuleRecord} (hm : i.ClaimedModule m) (hr : r ∈ i.modules)
    (hn : r.name = m) {x : Name} (hx : x ∈ r.extensions) (hmeta : x ∈ metaExtensions) :
    Violates2007 declarative i m :=
  ⟨hm, r, hr, hn, x, hx, h x hmeta⟩

end RegulaSpecification
