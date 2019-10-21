Require Export List_Type_more.

Lemma nth_In_Type {A} : forall n l (d:A), n < length l ->
  In_Type (nth n l d) l.
Proof.
  unfold lt; induction n as [| n hn]; simpl; destruct l; simpl; intros d ie;
    try (now inversion ie).
  - left; reflexivity.
  - right; apply hn; auto with arith.
Qed.

Lemma In_nth_Type {A} l (x:A) d : In_Type x l ->
  { n : _ & n < length l & nth n l d = x }.
Proof.
  induction l as [|a l IH]; intros Hin.
  - inversion Hin.
  - destruct Hin as [Hin|Hin].
    + subst; exists 0; simpl; auto with arith.
    + destruct (IH Hin) as [n Hn Hn'].
      exists (S n); simpl; auto with arith.
Qed.