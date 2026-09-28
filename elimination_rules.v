Parameter A B C:Prop.

Lemma l1: A -> ( A -> B ) -> ( B -> C ) -> C.
intro.
intro.
intro.
apply H1.
apply H0.
exact H.
Qed.

