Parameter A B C: Prop.
Lemma q3: (A->B->C)->B->A->C.
Proof.
  intro.
  intro.
  intro.
  apply H.
  - apply H1.
  - apply H0.
Qed.

