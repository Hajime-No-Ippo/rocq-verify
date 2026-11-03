Parameter D : Type.
Parameters R T S : D -> Prop.

Lemma lemma8 :
  (forall x : D, R x) ->
  ~ (exists y : D, ~ R y).

Proof.
  intros.
  intro HF.
  destruct HF as [y Hy].
  apply Hy.
  apply H.
Qed.