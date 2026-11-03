Parameter D : Type.
Parameters R T S : D -> Prop.

Lemma lemma6 :
  (exists x : D, ~ R x) ->
  (forall y : D, ~~ R y).

Proof.