Parameter A B C D: Prop.

Lemma q6: (A->B)->(A->C)->(B->C->D)->A->D.
Proof.
  intros.
  apply H1.
  - apply H. apply H2.
  - apply H0. apply H2.
Qed.
    

