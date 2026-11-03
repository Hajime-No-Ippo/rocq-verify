Parameter D : Type.
Parameters R T S : D -> Prop.

Lemma lemma4 :
  (exists x : D, R x /\ S x) -> 
  (exists y : D, R y) /\ (exists z : D, S z).
  
Proof.
  intros.
  split.
  - destruct H as [x Hx].
    exists x.
    destruct Hx as[R S].
    exact R.
  - destruct H as [x Hx].
    exists x.
    destruct Hx as[R S].
    exact S.
Qed.