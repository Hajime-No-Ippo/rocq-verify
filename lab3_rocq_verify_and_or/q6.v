Parameter A B: Prop.
Lemma q6: (A -> B) -> (~B -> ~A).
Proof.
  intro.
  red.
  intro H0.
  intro H1.
  apply H0.
  apply H.
  exact H1.
Qed.
