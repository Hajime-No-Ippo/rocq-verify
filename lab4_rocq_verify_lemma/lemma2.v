Parameter D : Type.
Parameters R T S : D -> Prop.

Lemma lemma2 :
  (forall x : D, R x -> S x) ->
  (forall y : D, S y -> T y) ->
  (forall z : D, R z -> T z).

Proof.
  intros.
  apply H0.
  apply H.
  exact H1.
Qed.