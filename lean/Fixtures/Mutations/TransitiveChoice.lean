/-
Mutation: a declaration claimed as choice-free whose choice dependence is
*transitive* — it is proved with core's `String.length_append`, whose proof goes
through classical reasoning in core's `String` internals. Importing a library
lemma is not itself disqualifying; the transitive axiom set decides the label.
-/
theorem fixtures_transitive_choice (s t : String) :
    (s ++ t).length = s.length + t.length :=
  String.length_append s t
