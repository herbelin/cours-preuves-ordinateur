Require Export Regular ListUtils MSetRBT MSetProperties MSetInterface.
Import ListNotations.

(** * Technicalities about regexps

    - RE : decidable comparisons
    - REs : finite sets of regexps
    - and also: remove in a list, sorted lists, merge of lists, etc
*)

Module RegOrd (Letter : FiniteOrderedType).
 Include Regexps(Letter).

 (** Properties about the comparisons on Letter *)
 Module LetterF := OrderedTypeFacts Letter.

 (** Regexps : decidable comparisons *)
 Module RE <: UsualOrderedType.

 Definition t := re.

 Definition eq := @eq re.
 Definition eq_equiv : Equivalence eq := @eq_equivalence re.

 Fixpoint compare r r' :=
 match r, r' with
 | Void, Void
 | Epsilon, Epsilon => Eq
 | Letter a, Letter b => Letter.compare a b
 | Cat r1 r2, Cat r1' r2'
 | Or r1 r2, Or r1' r2'
 | And r1 r2, And r1' r2' =>
    match compare r1 r1' with
    | Eq => compare r2 r2'
    | c => c
    end
 | Star r, Star r'
 | Not r, Not r' => compare r r'
 | Void, _ => Lt | _, Void => Gt
 | Epsilon, _ => Lt | _, Epsilon => Gt
 | Letter _, _ => Lt | _, Letter _ => Gt
 | Cat _ _, _ => Lt | _, Cat _ _ => Gt
 | Star _, _ => Lt | _, Star _ => Gt
 | Or _ _, _ => Lt | _, Or _ _ => Gt
 | And _ _, _ => Lt | _, And _ _ => Gt
 end.

 Definition lt r r' := compare r r' = Lt.

 Lemma compare_refl r : compare r r = Eq.
 Proof.
 induction r; simpl; auto using LetterF.compare_refl;
  now rewrite IHr1, IHr2.
 Qed.

 Lemma compare_eq r r' : compare r r' = Eq <-> r = r'.
 Proof.
 revert r'; induction r; destruct r'; simpl; auto;
 rewrite ?IHr, ?LetterF.compare_eq_iff; try (split; congruence);
 destruct compare eqn:?; auto;
 rewrite ?IHr1, ?IHr2 in *; split; try congruence;
 intros [= <- <-]; now rewrite compare_refl in *.
 Qed.

 Lemma compare_antisym r r' : compare r' r = CompOpp (compare r r').
 Proof.
 revert r'. induction r; destruct r'; simpl; auto;
 apply LetterF.compare_antisym ||
 (rewrite IHr1; destruct compare; simpl; auto).
 Qed.

 Lemma compare_spec r r' :
  CompareSpec (r = r') (lt r r') (lt r' r) (compare r r').
 Proof.
 unfold lt.
 rewrite (compare_antisym r r').
 generalize (compare_eq r r').
 destruct compare; constructor; intuition.
 Qed.

 Lemma lt_irrefl r : ~lt r r.
 Proof.
 unfold complement, lt.
 induction r; simpl; try easy;
  rewrite ?LetterF.compare_lt_iff; try LetterF.order;
  now destruct compare.
 Qed.

 Lemma lt_trans : Transitive lt.
 Proof.
  unfold lt. intro r.
  induction r; intros [ ] [ ]; simpl; eauto; try easy;
  rewrite ?LetterF.compare_lt_iff; try LetterF.order;
  destruct compare eqn:E; auto; try easy;
  rewrite ?compare_eq in *; subst;
  destruct (compare r) eqn:E'; eauto; try easy;
  rewrite ?compare_eq in *; subst; intro; rewrite ?E; try easy;
  now rewrite (IHr1 _ _ E E').
 Qed.

 Lemma lt_strorder : StrictOrder lt.
 Proof.
 split. exact lt_irrefl. exact lt_trans.
 Qed.

 Lemma lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
 Proof. intuition auto with *. Qed.

 Definition eq_dec (r r' : re) : {r = r'} + { r <> r' }.
 Proof.
 destruct (compare r r') eqn:E; [left|right|right].
 - now apply compare_eq.
 - intros <-. now rewrite compare_refl in *.
 - intros <-. now rewrite compare_refl in *.
 Qed.

 Definition eqb r r' :=
  match compare r r' with Eq => true | _ => false end.

 Lemma eqb_eq r r' : eqb r r' = true <-> r = r'.
 Proof.
 rewrite <- compare_eq. unfold eqb. now destruct compare.
 Qed.

 Lemma eqb_spec r r' : reflect (r = r') (eqb r r').
 Proof.
 apply iff_reflect. symmetry. apply eqb_eq.
 Qed.

 Lemma eqb_neq r r' : eqb r r' = false <-> r <> r'.
 Proof.
 rewrite <- eqb_eq. now destruct eqb.
 Qed.

 Lemma eqb_refl r : eqb r r = true.
 Proof.
 unfold eqb. now rewrite compare_refl.
 Qed.

 End RE.

 (** Finite sets of regexps *)

 Set Inline Level 30.
 Module REs := MSetRBT.Make RE.
 Module REsP := MSetProperties.WProperties REs.
 Ltac REsdec := REsP.Dec.fsetdec.

 Lemma REs_elements_spec x set :
  In x (REs.elements set) <-> REs.In x set.
 Proof.
 rewrite <- REs.elements_spec1, InA_alt. firstorder; subst; auto.
 Qed.

 (** From a list of regexps to a set of regexps *)

 Fixpoint list2set l : REs.t :=
  match l with
  | [] => REs.empty
  | r::l => REs.add r (list2set l)
  end.

 Lemma list2set_in x l : REs.In x (list2set l) <-> In x l.
 Proof.
 induction l; simpl; rewrite <- ?IHl; REsdec.
 Qed.

 (** Results on lists of regexps, using the boolean equality
     [RE.eqb] or the decidable equality [RE.eq_dec]. *)

 (** First, we can decide whether a regexp is in a list or not *)

 Lemma in_or_not r (l:list re) : In r l \/ ~In r l.
 Proof.
 Admitted.

 (** [remove] : similar to Coq standard [List.remove], but with [RE.eqb]
     instead of a generic [eq_dec] argument. *)

 Fixpoint remove x l :=
  match l with
  | [] => []
  | y :: tl => if RE.eqb x y then remove x tl else y :: remove x tl
  end.

 Lemma in_remove x a l : In x (remove a l) <-> In x l /\ a<>x.
 Proof.
 Admitted.

 Lemma remove_id a l : ~In a l -> remove a l = l.
 Proof.
 Admitted.

 Lemma remove_eqlist a l :
  In a l -> eqlist l (a::remove a l).
 Proof.
 Admitted.

 Lemma eqlist_remove a l l' :
  eqlist (a::l) l' -> ~In a l -> eqlist l (remove a l').
 Proof.
 Admitted.

 Lemma remove_nil a l :
  eqlist l [a] -> remove a l = nil.
 Proof.
 Admitted.

 Lemma remove_subset a l l' :
  Subset l (a::l') -> Subset (remove a l) l'.
 Proof.
 Admitted.

 (** Thanks to [remove], we can turn a [subset] list into
     an equivalent [Incl] one. Tricky *)

 Lemma subset_eqlist_Incl (u v : list re) :
  Subset u v -> exists u', eqlist u u' /\ Incl u' v.
 Proof.
 Admitted.

 (** From two [Incl] sublists, we can find a third one equivalent
     to the concatenation of the first two. *)

 Lemma Incl_app (l1 l2 l : list re) :
  Incl l1 l -> Incl l2 l ->
  exists l', eqlist (l1++l2) l' /\ Incl l' l.
 Proof.
 Admitted.

 (** Sorted lists of regexps *)

 Definition Sorted := Sorted.Sorted RE.lt. (* See Coq stdlib *)
 Global Hint Constructors Sorted.Sorted NoDup : core.
 Global Hint Unfold Sorted : core.

 Lemma Sorted_in_lt l x y : Sorted (x::l) -> In y l -> RE.lt x y.
 Proof.
 Admitted.

 Lemma Sorted_not_in l x : Sorted (x::l) -> ~In x l.
 Proof.
 Admitted.

 Lemma Sorted_NoDup l : Sorted l -> NoDup l.
 Proof.
 Admitted.

 (** Two equivalent strictly sorted lists are actually equal. Tricky. *)

 Lemma sorted_unique l l' :
  eqlist l l' -> Sorted l -> Sorted l' -> l = l'.
 Proof.
 Admitted.

 (** Merge lists of regexp. Since we implement this via finite sets,
     we obtain a sorted result for free :-). *)

 Definition merge l1 l2 :=
  REs.elements (REs.union (list2set l1) (list2set l2)).

 Lemma merge_eqlist l l' : eqlist (merge l l') (l++l').
 Proof.
 Admitted.

 Lemma merge_nonnil l l' : l <> [] -> merge l l' <> [].
 Proof.
 Admitted.

 Lemma merge_sorted l l' : Sorted (merge l l').
 Proof.
 Admitted.

 Lemma merge_idem l : Sorted l -> merge l l = l.
 Proof.
 Admitted.

 Lemma merge_sym l l' : merge l l' = merge l' l.
 Proof.
 Admitted.

 Lemma merge_assoc l1 l2 l3 :
  merge l1 (merge l2 l3) = merge (merge l1 l2) l3.
 Proof.
 Admitted.

End RegOrd.
