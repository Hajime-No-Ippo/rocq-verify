Parameter D : Type.
Parameters R T S : D -> Prop.

Lemma lemma7 :
  (exists y : D, ~ R y) -> 
  ~ (forall z : D, R z).

Proof.
  intros.
  destruct H as [y Hy].
  intro H.
  apply Hy.
  apply H.
Qed.