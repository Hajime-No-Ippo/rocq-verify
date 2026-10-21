Parameter E F: Prop.
Axiom LEM: forall P: Prop, P \/ ~P.
Lemma q11: ~(E /\ F) -> (~E \/ ~F).
Proof.
  intro HE.
  destruct (LEM E).
  destruct (LEM F).
  - left.
    intro.
    apply HE.
    split.
    + exact H.
    + exact H0.
  - right.
    + exact H0.
  - left.
    exact H.
Qed.
