
Parameter A B C: Prop.
Lemma q3: ((A \/ B) \/ C) -> (A \/ (B \/ C)).
Proof.
  intros H.
  destruct H as [[HA | HB] | HC].
  - left. exact HA.
  - right. left. exact HB.
  - right. right. exact HC.
Qed.


