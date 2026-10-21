Parameter A B C: Prop.
Lemma q5: (~A \/ B) -> (A -> B).
Proof.
  intros.
  destruct H.
  contradiction.
  exact H.
Qed.

