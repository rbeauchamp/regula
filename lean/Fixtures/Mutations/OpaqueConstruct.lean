/-
Negative fixture for the abstract-data API (standard §1.3, L-03): direct
construction contrary to the documented package operation must fail. The
abstract carrier is not definitionally equal to its implementation type.
-/
import Audit.DocPrelude

def fixtures_forged : Glossary.OpaqueData := "attacker"
