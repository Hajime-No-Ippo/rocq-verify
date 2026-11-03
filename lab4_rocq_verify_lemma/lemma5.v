Parameter D : Type.
Parameters R T S : D -> Prop.

Lemma lemma5 :
  (exists x : D, R x \/ S x) ->
  (exists y : D, R y) \/ (exists z : D, S z).

Proof.
  intros.
  destruct H as [x Hx].
  destruct Hx as [R | S].
  - left.
    exists x.
    exact R.
  - right.
    exists x.
    exact S.
Qed.
  
