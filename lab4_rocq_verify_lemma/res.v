Parameter D : Type.
Parameter R S T: D -> Prop.

Lemma lemma1:
  (forall x : D, R x -> S x ) -> 
  (forall y : D, R y) -> 
  (forall z : D, S z)
Proof.
  intro.
  intro.
  intro z.
  apply H.
  apply H0.
Qed.

Lemma lemma2 :
  (forall x : D, R x -> S x) ->
  (forall y : D, S y -> T y) ->
  (forall z : D, R z -> T z).
Proof.
  intros.
  apply H0.
  apply H.
  exact H1.
Qed.

Lemma lemma3 :
  (exists y : D, R y) ->
  (forall x : D, R x -> S x) ->
  (exists y : D, S y).
Proof.
  intros [y HR] H.
  exists y.
  apply H.
  exact HR.
Qed.

Lemma lemma4 :
  (exists x : D, R x /\ S x) -> 
  (exists y : D, R y) /\ (exists z : D, S z).
Proof.
  intros.
  split.
  - destruct H as [x Hx].
    exists x.
    destruct Hx as[R S].
    exact R.
  - destruct H as [x Hx].
    exists x.
    destruct Hx as[R S].
    exact S.
Qed.

Lemma lemma5 :
  (exists x : D, R x \/ S x) ->
  (exists y : D, R y) \/ (exists z : D, S z).
Proof.
  intros.
  destruct H as [x Hx].
  destruct Hx as [R | S].
  - left.
    exists x.
    exact R.
  - right.
    exists x.
    exact S.
Qed.

Lemma lemma6 :
  (exists x : D, ~ R x) ->
  (forall y : D, ~~ R y).
Proof:

Lemma lemma7 :
  (exists y : D, ~ R y) -> 
  ~ (forall z : D, R z).
Proof.
  intros.
  destruct H as [y Hy].
  intro H.
  apply Hy.
  apply H.
Qed.

Lemma lemma8 :
  (forall x : D, R x) ->
  ~ (exists y : D, ~ R y).
Proof.
  intros.
  intro HF.
  destruct HF as [y Hy].
  apply Hy.
  apply H.
Qed.