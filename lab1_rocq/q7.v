Parameter A B: Prop.
Lemma q7: ((((A->B)->A)->A)->B)->B.
Proof.
  intros.
  apply H.
  intros.
  apply H0.
  intros.
  apply H.
  intro.
  apply H1.
Qed.

