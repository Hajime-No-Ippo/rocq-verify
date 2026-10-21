Parameter E F: Prop.
Lemma q9:  (~E /\ ~F) -> ~(E \/ F).
Proof.
  intros [Hne Hnf].
  intro H_or.
  elim H_or.
  - exact(Hne).
  - exact(Hnf).
Qed.

  
