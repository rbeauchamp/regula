# CONTEXT

Vocabulary version: 1
Standard: ASD-STE100 Issue 9

## Shared technical nouns

| Term | Category | Definition | Replaces | Source |
| --- | --- | --- | --- | --- |
| declaration | 19 | An item with a name in a Lean module, for example a definition or a theorem. | - | `website/RegulaStandard/CodeOrganization.lean` |
| definition | 7 | A declaration that gives a name to a value or to a function. | - | `website/RegulaStandard/CorePrinciples.lean` |
| docstring | 19 | A comment that Lean attaches to a declaration or to a module. | doc comment | `website/RegulaStandard/DocumentationStandards.lean` |
| Lake | 19 | The program that builds Lean projects. | - | `lakefile.lean` |
| Lean | 19 | The Lean 4 language and its programs. | Lean4 | `lean-toolchain` |
| module | 19 | One Lean source file that a different source file can import. | - | `website/RegulaStandard/CodeOrganization.lean` |
| proof | 7 | A Lean expression that Lean accepts and that shows that a statement is correct. | - | `website/RegulaStandard/PreciseClaims.lean` |
| theorem | 7 | A declaration that gives a name to a statement and to its proof. | - | `website/RegulaStandard/PreciseClaims.lean` |

## Shared technical verbs

| Term | Category | Definition | Replaces | Source |
| --- | --- | --- | --- | --- |
| build | 2c | To make the output files of a project with Lake. | - | `lakefile.lean` |
| compile | 2c | To change source text into a program that a computer can operate. | - | `website/RegulaStandard/PreciseClaims.lean` |
| import | 2c | To make the items of a different module available in a module. | - | `website/RegulaStandard/CodeOrganization.lean` |
| prove | 3a | To show, with a proof that Lean accepts, that a statement is correct. | - | `website/RegulaStandard/PreciseClaims.lean` |

## Project technical nouns

| Term | Category | Definition | Replaces | Source |
| --- | --- | --- | --- | --- |
| baseline | 19 | The file that gives the permitted findings of each document that has findings. | - | `prose-baseline.json` |
| checker | 19 | The Regula program that reads a Lake project and gives findings. | - | `docs/guides/architecture.md` |
| control | 7 | An input for a check, with the result that the check must give for it. | - | `docs/guides/contributing.md` |
| decision contract | 7 | A theorem that tells which inputs a decision function accepts, in relation to a specification. | - | `lean/Regula/Contract.lean` |
| finding | 19 | One report of a check that a rule is not obeyed or that the check did not complete. | - | `lean/RegulaCore/Rule.lean` (`Regula.Impact`) |
| honest code | 19 | Code that does not make a change that the security policy excludes, for example a direct write to the state of an environment extension. | - | `SECURITY.md` |
| requirement | 15 | A part of the standard that a project must obey. | - | `website/RegulaStandard.lean` |
| rule-reference site | 15 | The site that has the standard and one page for each rule. | rule-reference website | `docs/guides/website.md` |
| standard | 15 | The Regula document that gives the requirements for proofs and programs in Lean. | - | `website/RegulaStandard.lean` |
| vocabulary | 15 | The technical nouns, the technical verbs and the replaced words of a project, in the file `CONTEXT.md`. | - | `lean/RegulaCore/Vocabulary.lean` (`Regula.Controlled.Vocabulary`) |

## Replaced words

| Do not write | Write |
| --- | --- |
| another | a different, one more |
| both | the two |
| ensure | make sure |
| every | each, all |
| however | but |
| need | necessary |
| needs | necessary |
| never | do not |
| once | one time, when |
| per | for each |
| should | must |
| whether | if |
| whose | a different construction |
| within | in |
