Require Export RegOrder.
Import ListNotations.

(** * A Similarity relation on regexps *)

(** We include here associativity/commutativity/idempotence of Or,
    plus simplifications of Void and Epsilon for convenience. *)

Reserved Notation "r =~= s" (at level 70).

Module RegSim (Letter : FiniteOrderedType).
Include RegOrd(Letter).

Inductive sim : re -> re -> Prop :=
 | SimRefl r : r =~= r
 | SimSym r s : r =~= s -> s =~= r
 | SimTrans r s t : r =~= s -> s =~= t -> r =~= t

 | And_compat r r' s s' : r =~= r' -> s =~= s' -> And r s =~= And r' s'
 | Or_compat r r' s s' : r =~= r' -> s =~= s' -> Or r s =~= Or r' s'
 | Cat_compat r r' s s' : r =~= r' -> s =~= s' -> Cat r s =~= Cat r' s'
 | Star_compat r r' : r =~= r' -> Star r =~= Star r'
 | Not_compat r r' : r =~= r' -> Not r =~= Not r'

 | Or_idem r : Or r r =~= r
 | Or_comm r s : Or r s =~= Or s r
 | Or_assoc r s t : Or (Or r s) t =~= Or r (Or s t)

 | Or_void r : Or Void r =~= r
 | And_void_l r : And Void r =~= Void
 | And_void_r r : And r Void =~= Void
 | Cat_void_l r : Cat Void r =~= Void
 | Cat_void_r r : Cat r Void =~= Void
 | Cat_eps_l r : Cat Epsilon r =~= r
 | Cat_eps_r r : Cat r Epsilon =~= r
 | Star_void : Star Void =~= Epsilon
 | Star_eps : Star Epsilon =~= Epsilon

where "r =~= s" := (sim r s).

Global Hint Constructors sim : core.

(** This similarity relation is an approximation of
    the general regexp equivalence : two similar regexps
    will have the same underlying language. *)

Lemma sim_equiv r r' : r =~= r' -> r === r'.
Proof.
Admitted.

(** Stuff for rewrite *)
Global Instance sim_equivalence : Equivalence sim.
Proof. split; eauto. Qed.
Global Instance : subrelation sim equiv.
Proof. exact sim_equiv. Qed.
Global Instance : Proper (sim ==> sim ==> sim) Or.
Proof. repeat red; intros. eapply Or_compat; eauto. Qed.
Global Instance : Proper (sim ==> sim ==> sim) And.
Proof. repeat red; intros. eapply And_compat; eauto. Qed.
Global Instance : Proper (sim ==> sim ==> sim) Cat.
Proof. repeat red; intros. eapply Cat_compat; eauto. Qed.
Global Instance : Proper (sim ==> sim) Not.
Proof. repeat red; intros. eapply Not_compat; eauto. Qed.
Global Instance : Proper (sim ==> sim) Star.
Proof. repeat red; intros. eapply Star_compat; eauto. Qed.

Lemma Or_void_r r : Or r Void =~= r.
Proof.
 now rewrite Or_comm, Or_void.
Qed.

Definition is_or r := match r with Or _ _ => true | _ => false end.
Definition leftish_or r := match r with Or r _ => r | _ => r end.

(** Canonical form of a regexp :
    smallest Or arguments should come first, no Void or Epsilon
    should remain at simplifiable positions.
    Here this is only a specification of what is a regexp in
    canonical form, we'll see later how to convert a regexp into
    the corresponding canonical form (cf function [canon]). *)

Fixpoint Canonical r :=
 match r with
 | Void | Epsilon | Letter _ => True
 | And r s => r<>Void /\ s<>Void /\ Canonical r /\ Canonical s
 | Cat r s => r<>Void /\ s<>Void /\ r<>Epsilon /\ s<>Epsilon /\
              Canonical r /\ Canonical s
 | Or r s => r<>Void /\ s<>Void /\
             Canonical r /\ Canonical s /\ is_or r = false /\
             RE.lt r (leftish_or s)
 | Star r => r<>Void /\ r<>Epsilon /\ Canonical r
 | Not r => Canonical r
 end.

Module OR. (* Collecting or rebuilding repeated Or's *)

Fixpoint collect r :=
 match r with
 | Or r1 r2 => r1 :: collect r2
 | _ => [r]
 end.

Fixpoint mk l :=
 match l with
 | [] => Void
 | [r] => r
 | r :: l => Or r (mk l)
 end.

Lemma collect_nonnil r : collect r <> [].
Proof.
 now destruct r.
Qed.

Lemma mk_eqn r l : l<>[] -> mk (r::l) = Or r (mk l).
Proof.
 now destruct l.
Qed.

Lemma mk_collect r : mk (collect r) = r.
Proof.
 induction r; simpl; auto.
 assert (NE := collect_nonnil r2).
 destruct (collect r2); try easy. now f_equal.
Qed.

Lemma collect_mk l :
 l<>[] -> existsb is_or l = false -> collect (mk l) = l.
Proof.
 induction l as [|r [|s l] IH]; auto.
 - easy.
 - intros _ E. simpl in E. rewrite orb_false_r in E.
   simpl.
   now destruct r.
 - intros _ E.
   rewrite mk_eqn by easy.
   remember (s::l) as l'. simpl. f_equal; apply IH. now subst.
   simpl in *; rewrite orb_false_iff in *. intuition.
Qed.

Lemma mk_cons r l : OR.mk (r::l) =~= Or r (OR.mk l).
Proof.
 simpl. destruct l; simpl; auto. symmetry. apply Or_void_r.
Qed.

Lemma mk_in r l : In r l -> mk (r::l) =~= mk l.
Proof.
 induction l as [|r' l IH].
 - inversion 1.
 - simpl. intros [->|IN].
   + destruct l; auto. now rewrite <- Or_assoc, Or_idem.
   + destruct l.
     inversion IN.
     rewrite <- Or_assoc, (Or_comm r r'), Or_assoc.
     f_equiv. now apply IH.
Qed.

Lemma mk_remove r l : mk (r::l) =~= mk (r::remove r l).
Proof.
 induction l.
 - auto.
 - rewrite !mk_cons in *. simpl remove.
   case RE.eqb_spec; intros; subst.
   + now rewrite <- Or_assoc, Or_idem.
   + rewrite mk_cons, <-!Or_assoc, !(Or_comm r a), !Or_assoc.
     now f_equiv.
Qed.

Global Instance mk_sim : Proper (eqlist ==> sim) mk.
Proof.
 intros l. induction l as [|r l IH]; intros l'.
 - intros H. symmetry in H. apply eqlist_nil in H. now subst.
 - intros E.
   destruct (in_or_not r l).
   + rewrite mk_in; auto. apply IH. eapply eqlist_undup; eauto.
   + rewrite <-(mk_in r l') by firstorder.
     rewrite (mk_remove r l'), !mk_cons. f_equiv.
     apply IH. apply eqlist_remove; auto.
Qed.

Lemma mk_app l l' :
 mk (l ++ l') =~= Or (mk l) (mk l').
Proof.
 induction l as [|r [|r' l] IH]; auto; try easy.
 - apply mk_cons.
 - simpl app in *. rewrite !mk_cons in *. rewrite IH.
   now rewrite <- Or_assoc.
Qed.

Lemma mk_can l :
 Sorted l -> Forall Canonical l -> existsb is_or l = false ->
 (In Void l -> l = [Void]) -> Canonical (mk l).
Proof.
 rewrite Forall_forall.
 induction 1; simpl; auto.
 destruct l as [|r' l]; auto.
 remember (r'::l) as l'.
 simpl.
 rewrite orb_false_iff.
 intros C (Oa,Ol') V.
 assert (Va : a<>Void) by (intuition; congruence).
 assert (Vl' : ~In Void l') by (intuition; congruence).
 clear V. repeat split; auto.
 - subst l'. simpl. destruct l; try easy. intros ->; intuition auto with *.
 - apply IHSorted; intuition auto with *.
 - replace (leftish_or (mk l')) with r'.
   + apply Sorted_in_lt with l'; auto.
     subst l'. simpl. auto.
   + subst l'. simpl. destruct l; simpl; auto. now destruct r'.
Qed.

Lemma mk_void l : mk l = Void -> l <> [] -> l = [Void].
Proof.
 destruct l as [|r [|r' l]]; simpl; try easy. intuition congruence.
Qed.

Lemma collect_can r :
  Canonical r -> Forall Canonical (collect r).
Proof.
 rewrite Forall_forall.
 induction r; simpl; intuition; now subst.
Qed.

Lemma collect_void r :
  Canonical r -> In Void (collect r) -> r = Void.
Proof.
 induction r; simpl; intuition.
Qed.

Lemma collect_ltlist r s :
 Canonical s ->
 RE.lt r (leftish_or s) -> Forall (RE.lt r) (collect s).
Proof.
 rewrite Forall_forall.
 revert r.
 induction s; simpl; auto; try (intros r _ LT x [<-|[ ]]; easy).
 intros r (V1 & V2 & Hs1 & Hs2 & NO & LT) LT' x [<-|IN]; auto.
 eapply RE.lt_strorder with s1; eauto.
Qed.

Lemma collect_sorted r : Canonical r -> Sorted (collect r).
Proof.
 induction r; simpl; intuition.
 constructor; auto.
 assert (Hr2 := collect_ltlist _ _ H2 H5).
 inversion Hr2; subst; auto.
Qed.

Lemma merge_can l l' :
 Forall Canonical l -> Forall Canonical l' ->
 Forall Canonical (merge l l').
Proof.
 rewrite !Forall_forall. intros H1 H2 x.
 rewrite (merge_eqlist _ _ x), in_app_iff. intuition.
Qed.

Lemma collect_no_or r :
 Canonical r -> existsb is_or (collect r) = false.
Proof.
 induction r; simpl; auto; try now intros ->.
 rewrite !orb_false_iff. intuition.
Qed.

Lemma merge_no_or l l' :
 existsb is_or l = false -> existsb is_or l' = false ->
 existsb is_or (merge l l') = false.
Proof.
 rewrite !existsb_forall. intros H1 H2 x.
 rewrite (merge_eqlist _ _ x), in_app_iff. intuition.
Qed.

End OR.

(* Smart constructor : sOr *)

Definition sOr r s :=
  if RE.eqb r Void then s
  else if RE.eqb s Void then r
  else OR.mk (merge (OR.collect r) (OR.collect s)).

Lemma sOr_sim r s : sOr r s =~= Or r s.
Proof.
 unfold sOr.
 do 2 (case RE.eqb_spec; simpl; intros; subst; auto).
 rewrite Or_comm; auto.
 now rewrite merge_eqlist, OR.mk_app, !OR.mk_collect.
Qed.

Lemma sOr_can r s :
 Canonical r -> Canonical s -> Canonical (sOr r s).
Proof.
 unfold sOr.
 intros Hr Hs.
 do 2 (case RE.eqb_spec; simpl; intros; subst; auto).
 apply OR.mk_can.
 - apply merge_sorted; apply OR.collect_sorted; auto.
 - apply OR.merge_can; apply OR.collect_can; auto.
 - apply OR.merge_no_or; apply OR.collect_no_or; auto.
 - rewrite (merge_eqlist _ _ Void), in_app_iff.
   intros [IN|IN]; now apply OR.collect_void in IN.
Qed.

Lemma sOr_nop r s :
 Canonical (Or r s) -> sOr r s = Or r s.
Proof.
 simpl. intros (Vr & Vs & Hr & Hs & E & LT).
 unfold sOr.
 rewrite <- RE.eqb_neq in Vr, Vs. rewrite Vr, Vs.
 replace (OR.collect r) with [r] by now destruct r.
 replace (merge [r] (OR.collect s)) with (r :: OR.collect s).
 simpl.
 rewrite OR.mk_collect.
 generalize (OR.collect_nonnil s). now destruct (OR.collect s).
 apply sorted_unique.
 now rewrite merge_eqlist.
 constructor. now apply OR.collect_sorted.
 destruct s; simpl; auto.
 apply merge_sorted.
Qed.

Lemma sOr_idem r :
 Canonical r -> sOr r r = r.
Proof.
 intros.
 unfold sOr.
 case RE.eqb_spec; auto. intros _.
 rewrite merge_idem.
 - apply OR.mk_collect.
 - apply OR.collect_sorted; auto.
Qed.

Lemma sOr_sym r s :
 Canonical r -> Canonical s -> sOr r s = sOr s r.
Proof.
 intros.
 unfold sOr.
 repeat case RE.eqb_spec; intros; subst; auto.
 f_equal.
 apply merge_sym.
Qed.

Lemma sOr_void_l r : sOr Void r = r.
Proof.
 reflexivity.
Qed.

Lemma sOr_void_r r : sOr r Void = r.
Proof.
 unfold sOr. case RE.eqb_spec; auto.
Qed.

Lemma sOr_void r s :
  Canonical r -> Canonical s ->
  sOr r s = Void <-> r = Void /\ s = Void.
Proof.
 intros Hr Hs. unfold sOr.
 case RE.eqb_spec; intros. intuition.
 case RE.eqb_spec; intros. intuition.
 split.
 - intros H.
   apply OR.mk_void in H.
   2: apply merge_nonnil; apply OR.collect_nonnil.
   assert (E : eqlist (OR.collect r ++ OR.collect s) [Void]).
   { now rewrite <- merge_eqlist, H. }
   clear H.
   split.
   + apply OR.collect_void; auto.
     assert (Nr := OR.collect_nonnil r).
     destruct (OR.collect r) as [|x l]; try easy.
     destruct (E x). simpl in *; intuition.
   + apply OR.collect_void; auto.
     assert (Ns := OR.collect_nonnil s).
     destruct (OR.collect s) as [|x l]; try easy.
     destruct (E x). rewrite in_app_iff in *; simpl in *; intuition.
 - now intros (->,->).
Qed.

Lemma sOr_assoc r s t :
  Canonical r -> Canonical s -> Canonical t ->
  sOr (sOr r s) t = sOr r (sOr s t).
Proof.
 intros Cr Cs Ct.
 generalize (sOr_void r s Cr Cs) (sOr_void s t Cs Ct).
 unfold sOr in *.
 case (RE.eqb_spec r Void); simpl; auto. intro Hr.
 case (RE.eqb_spec s Void); simpl; auto.
 + intros ->. rewrite <- RE.eqb_neq in Hr. rewrite Hr; auto.
 + intros Hs.
   case (RE.eqb_spec t Void); simpl; auto.
   * intros ->. intros (E,_) _.
     case RE.eqb_spec. intuition.
     case (RE.eqb_spec s Void); simpl; auto. easy.
   * intros Ht.
     intros (E,_) (E',_).
     case RE.eqb_spec. intuition.
     case RE.eqb_spec. intuition. intros _ _.
     f_equal.
     rewrite !OR.collect_mk;
       auto using merge_nonnil, OR.collect_nonnil,
       OR.merge_no_or, OR.collect_no_or.
     now rewrite merge_assoc.
Qed.

(** The other smart constructors *)

Definition sStar r :=
  if RE.eqb r Void || RE.eqb r Epsilon then Epsilon else Star r.

Definition sCat r s :=
  if RE.eqb r Void || RE.eqb s Void then Void
  else if RE.eqb r Epsilon then s
  else if RE.eqb s Epsilon then r
  else Cat r s.

Definition sAnd r s :=
  if RE.eqb r Void || RE.eqb s Void then Void else And r s.

Lemma sStar_sim r : sStar r =~= Star r.
Proof.
 unfold sStar.
 do 2 (case RE.eqb_spec; simpl; intros; subst; auto).
Qed.

Lemma sCat_sim r s : sCat r s =~= Cat r s.
Proof.
 unfold sCat.
 do 4 (case RE.eqb_spec; simpl; intros; subst; auto).
Qed.

Lemma sAnd_sim r s : sAnd r s =~= And r s.
Proof.
 unfold sAnd.
 do 2 (case RE.eqb_spec; simpl; intros; subst; auto).
Qed.

Lemma sStar_can r : Canonical r -> Canonical (sStar r).
Proof.
 unfold sStar.
 do 2 (case RE.eqb_spec; simpl; intros; subst; auto).
Qed.

Lemma sCat_can r s : Canonical r -> Canonical s -> Canonical (sCat r s).
Proof.
 unfold sCat.
 do 4 (case RE.eqb_spec; simpl; intros; subst; auto). intuition.
Qed.

Lemma sAnd_can r s : Canonical r -> Canonical s -> Canonical (sAnd r s).
Proof.
 unfold sAnd.
 do 2 (case RE.eqb_spec; simpl; intros; subst; auto).
Qed.

(** The canonical form of a regexp : *)

Fixpoint canon r :=
  match r with
  | Void | Epsilon | Letter _ => r
  | Not r => Not (canon r)
  | Star r => sStar (canon r)
  | Cat r s => sCat (canon r) (canon s)
  | And r s => sAnd (canon r) (canon s)
  | Or r s => sOr (canon r) (canon s)
  end.

Lemma canon_or r s : canon (Or r s) = sOr (canon r) (canon s).
Proof.
 reflexivity.
Qed.

Lemma canon_sim r : canon r =~= r.
Proof.
Admitted.

Lemma canon_can r : Canonical (canon r).
Proof.
Admitted.

Lemma canon_spec r s : r =~= s <-> canon r = canon s.
Proof.
Admitted.

Global Instance : Proper (sim ==> eq) canon.
Proof. intros r r' Hr. now apply canon_spec. Qed.

Lemma can_canon_id r : Canonical r -> canon r = r.
Proof.
Admitted.

Lemma canon_canon r : canon (canon r) = canon r.
Proof.
Admitted.

Lemma can_sim_eq r s :
  Canonical r -> Canonical s -> r =~= s -> r = s.
Proof.
Admitted.

(** Decidable test for similarity *)

Definition is_sim r s := RE.eqb (canon r) (canon s).

Definition is_sim_spec r s : is_sim r s = true <-> r =~= s.
Proof.
Admitted.

(** Properties of [sim] *)

Global Instance : Proper (sim ==> eq) is_nullable.
Proof.
 intros r1 r2 Hr.
Admitted.

Global Instance : Proper (sim ==> eq ==> sim) deriv1.
Proof.
 intros r r' Hr a a' <-.
Admitted.

Lemma canon_deriv1 r a : canon r / a =~= r / a.
Proof.
Admitted.

Lemma canon_deriv1_canon r a : canon (canon r / a) = canon (r / a).
Proof.
Admitted.

Global Instance : Proper (sim ==> eq ==> sim) deriv.
Proof.
 intros r r' Hr w w' <-.
Admitted.

Global Instance : Proper (sim ==> eq ==> eq) matching.
Proof.
 intros r r' Hr w w' <-.
Admitted.

End RegSim.
