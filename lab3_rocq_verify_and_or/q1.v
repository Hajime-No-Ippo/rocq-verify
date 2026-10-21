Parameter A B C: Prop.
Lemma q1: ((A /\ B) /\ C) -> (A /\ (B /\ C)).
Proof.
  intros.
  destruct H as [H0  H1].
  destruct H0 as [HA HB].
  split.
  - exact HA.
  - split.
    + exact HB.
    + exact H1.
Qed.

