Parameter D : Type.
Parameters R T S : D -> Prop.

Lemma lemma1:
  (forall x : D, R x -> S x ) -> 
  (forall y : D, R y) -> 
  (forall z : D, S z).

Proof.
  intro.
  intro.
  intro z.
  apply H.
  apply H0.
Qed.