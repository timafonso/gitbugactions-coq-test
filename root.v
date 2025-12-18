Require Import List.
Import ListNotations.

Lemma exists_tail : forall (xs : list nat),
  xs <> [] ->
  exists x ys, xs = x :: ys.
Proof.
  intros xs H.
  destruct xs as [| x xs'].
  - contradiction.
  - exists 0, xs'.
