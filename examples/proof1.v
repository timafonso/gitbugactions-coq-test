Lemma rev_snoc_cons A :
  forall (x : A) (l : list A), rev (l ++ [x]) = x :: rev l.
Proof.
  induction l.
  - reflexivity.
  - simpl. rewrite IHl. simpl. reflexivity.
Qed.

Lemma assoc_rev A :
  forall (l1 l2 : list A), rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  induction l1.
  - simpl. rewrite rev_nil. reflexivity.
  - simpl. rewrite IHl1. simpl. rewrite app_assoc. reflexivity.
Qed.