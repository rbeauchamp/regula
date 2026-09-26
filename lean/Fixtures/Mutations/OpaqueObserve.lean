/-
Negative fixture for the abstract-data API (standard §1.3, L-03): payload
recovery contrary to the documented API must fail. The abstract carrier has
no coercion, constructor, projection, eliminator, or exported observer that
identifies it with `String`.
-/
import Audit.DocPrelude

def fixtures_steal (x : Glossary.OpaqueData) : String := x
