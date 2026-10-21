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


Parameter A B C: Prop.
Lemma q2: ((A /\ B) -> C) -> (A -> (B -> C)).
Proof.
  intros.
  apply H.
  split.
  - exact H0.
  - exact H1.
Qed.

Parameter A B C: Prop.
Lemma q3: ((A \/ B) \/ C) -> (A \/ (B \/ C)).
Proof.
  intros H.
  destruct H as [[HA | HB] | HC].
  - left. exact HA.
  - right. left. exact HB.
  - right. right. exact HC.
Qed.

Parameter A B C: Prop.
Lemma q4: ((A \/ B) ->C) -> (A -> (B -> C)). 
Proof.
  intros.
  apply H.
  - left. exact H0.
Qed.

Parameter A B C: Prop.
Lemma q5: (~A \/ B) -> (A -> B).
Proof.
  intros.
  destruct H.
  contradiction.
  exact H.
Qed.

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

Parameter A: Prop.
Lemma q7: ~(A /\ ~A).
Proof.
  red.
  intro H0.
  destruct  H0. 
  apply H0.
  exact H.
Qed.

Parameter E F: Prop.
Lemma q8:  ~(E \/ F) -> (~E /\ ~F).
Proof.
  intro H0.
  split.
  - intro HE.
    apply H0.
    left.
    exact HE.
  - intro HF.
    apply H0.
    right.
    exact HF.
Qed.

Parameter E F: Prop.
Lemma q9:  (~E /\ ~F) -> ~(E \/ F).
Proof.
  intros [Hne Hnf].
  intro H_or.
  elim H_or.
  - exact(Hne).
  - exact(Hnf).
Qed.

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
