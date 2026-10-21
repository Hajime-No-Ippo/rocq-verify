Parameter A: Prop.
Lemma q7: ~(A /\ ~A).
Proof.
  red.
  intro H0.
  destruct  H0. 
  apply H0.
  exact H.
Qed.
