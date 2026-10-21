Parameter A B C: Prop.
Lemma q4: ((A \/ B) ->C) -> (A -> (B -> C)). 
Proof.
  intros.
  apply H.
  - left. exact H0.
Qed.
