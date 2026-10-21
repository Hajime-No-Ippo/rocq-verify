Parameter A B C: Prop.
Lemma q2: ((A /\ B) -> C) -> (A -> (B -> C)).
Proof.
  intros.
  apply H.
  split.
  - exact H0.
  - exact H1.
Qed.
