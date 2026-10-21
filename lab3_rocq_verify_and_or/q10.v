Parameter E F: Prop.
Lemma q10: (~E \/ ~F) -> ~(E /\ F).
Proof.
  intro HE.
  intro HF.
  destruct HF.
  destruct HE.
  - apply H1.
    exact H.
  - apply H1.
    exact H0.
Qed.


