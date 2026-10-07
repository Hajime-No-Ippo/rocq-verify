Parameter A B : Prop.
Lemma q4: (A->A->B)->A->B.
Proof.
  intros.
  apply H.
  - apply H0.
  - apply H0.
Qed.
