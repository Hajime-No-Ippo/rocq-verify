Parameter D : Type.
Parameters R T S : D -> Prop.

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
