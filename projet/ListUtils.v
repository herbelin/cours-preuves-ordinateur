Require Export List Setoid Morphisms SetoidList Sorted.
Require Export Orders OrdersFacts.
Require Export Bool Arith Lia.
Import ListNotations.

Lemma app_nil {A} (l l' : list A) : l ++ l' = [] <-> l = [] /\ l' = [].
Proof.
Admitted.

(** Cartesian product *)

Definition product {A B} (l : list A) (l' : list B) : list (A * B) :=
 List.flat_map (fun e => map (pair e) l') l.

Lemma product_ok {A B} (l : list A) (l' : list B) x y :
  List.In (x, y) (product l l') <-> List.In x l /\ List.In y l'.
Proof.
Admitted.

Lemma product_length {A B} (l:list A)(l':list B) :
  length (product l l') = length l * length l'.
Proof.
Admitted.

(** Equivalence of lists *)

Definition eqlist {A} (l l' : list A) := forall n,
  List.In n l <-> List.In n l'.

(** For rewriting with eqlist : *)
Global Instance : forall A, Equivalence (@eqlist A).
Proof. firstorder. Qed.
Global Instance : forall {A}, Proper (eq ==> eqlist ==> eqlist) (@cons A).
Proof. intros A a a' <-. firstorder. Qed.
Global Instance : forall {A}, Proper (eqlist ==> eqlist ==> eqlist) (@app A).
Proof.
 intros A l1 l1' H1 l2 l2' H2 x.
 rewrite !in_app_iff. now rewrite (H1 x), (H2 x).
Qed.
Global Instance : forall {A B}, Proper (eq ==> eqlist ==> eqlist) (@map A B).
Proof.
 intros A B f f' <- l l' H x. rewrite !in_map_iff.
 split; intros (y & E & IN); exists y; split; auto; now apply H.
Qed.

Lemma eqlist_nil {A} (l : list A) : eqlist l [] -> l = [].
Proof.
Admitted.

Lemma eqlist_comm {A} (l l' : list A) : eqlist l l' -> eqlist l' l.
Proof.
Admitted.

Lemma eqlist_undup {A} (a:A) l l' :
 eqlist (a::l) l' -> In a l -> eqlist l l'.
Proof.
Admitted.

Lemma eqlist_uncons {A} (a:A) l l' :
 eqlist (a::l) (a::l') -> ~In a l -> ~In a l' -> eqlist l l'.
Proof.
Admitted.

(** [Incl] : inclusion of lists.

    For this predicate, the positions are important : a list is included
    in another if we can obtain the second one by putting some more
    elements in the first one. *)

Inductive Incl {A} : list A -> list A -> Prop :=
| InclNil : Incl [] []
| InclSkip x l l' : Incl l l' -> Incl l (x::l')
| InclSame x l l' : Incl l l' -> Incl (x::l) (x::l').
Global Hint Constructors Incl : core.

Lemma Incl_nil {A} (l:list A) : Incl [] l.
Proof.
Admitted.
Global Hint Resolve Incl_nil : core.

Lemma Incl_len {A} (l l' : list A) : Incl l l' -> length l <= length l'.
Proof.
Admitted.

Global Instance Incl_PreOrder {A} : PreOrder (@Incl A).
Proof.
 split.
 - red. intro l. induction l; auto.
 - red. intros l1 l2 l3 H12 H23. revert l1 H12.
   induction H23; intros; auto. inversion H12; subst; auto.
Qed.

Global Instance Incl_Order {A} : PartialOrder eq (@Incl A).
Proof.
 intros l l'; split.
 - now intros <-.
 - intros (H,H'). red in H'.
   induction H.
   + inversion H'; subst; auto.
   + apply Incl_len in H; apply Incl_len in H'. simpl in *. lia.
   + f_equal. inversion H'; subst; auto.
     apply Incl_len in H; apply Incl_len in H2. simpl in *. lia.
Qed.

Lemma Incl_Forall {A}(P:A->Prop) l l' :
  Incl l l' -> Forall P l' -> Forall P l.
Proof.
 induction 1; auto; inversion 1; subst; auto.
Qed.

Lemma Incl_singleton {A} (a:A) l : In a l -> Incl [a] l.
Proof.
Admitted.

(** [sublists] generates all lists included in a first one *)

Fixpoint sublists {A} (l : list A) :=
  match l with
  | [] => [[]]
  | a :: l' =>
    let s := sublists l' in
    s ++ List.map (cons a) s
  end.

Lemma sublists_spec {A} (l l' :list A) :
 In l' (sublists l) <-> Incl l' l.
Proof.
Admitted.

Lemma sublists_length {A} (l:list A) :
 length (sublists l) = 2^length l.
Proof.
Admitted.

(** [Subset] : another inclusion predicate, but this time we ignore
   the positions and the repetitions. It is enough for all elements
   of the left list to appear at least somewhere in the right list. *)

Definition Subset {A} (l l' : list A) :=
  forall n, List.In n l -> List.In n l'.

Lemma subset_notin {A} (l l' : list A) a :
 Subset l (a::l') -> ~In a l -> Subset l l'.
Proof.
Admitted.

Lemma subset_nil {A} (l : list A) : Subset l [] -> l = [].
Proof.
Admitted.

Lemma incl_subset {A} (l l':list A) : Incl l l' -> Subset l l'.
Proof.
Admitted.

(** A tricky lemma : a subset without duplicates has a smaller length.
    See Coq standard library for [NoDup]. This proof might be done
    via [List.in_split]. *)

Lemma subset_nodup_length {A} (l l' : list A) :
 Subset l l' -> NoDup l -> length l <= length l'.
Proof.
Admitted.

(** More on [Incl] and [Subset] in RegOrder.v, where we will be able to
    test whether two list elements are equal or not. *)

Lemma existsb_forall {A} (f:A -> bool) l :
 existsb f l = false <-> forall x, In x l -> f x = false.
Proof.
Admitted.

(** Being in a list, modulo an equivalence [R] *)

Section SomeEquivalence.
Context {A}(R:A->A->Prop){HR:Equivalence R}.

Definition InModulo a l := exists a', R a a' /\ In a' l.

Global Instance : Proper (R ==> eqlist ==> iff) InModulo.
Proof.
 intros x x' Hx l l' Hl. unfold InModulo; split;
 intros (a' & IN & E); exists a'; split; eauto; firstorder.
Qed.

(** Equivalence with another such definition (from Coq stdlib) *)

Lemma InModulo_InA a l : InModulo a l <-> InA R a l.
Proof.
 symmetry. apply InA_alt.
Qed.

(** Similar to [subset_nodup_length], but here elements are taken up
    to the equivalence R. See Coq stdlib for [NoDupA]. *)

Lemma subset_nodupA_length l l' :
 (forall x, In x l -> InModulo x l') -> NoDupA R l ->
 length l <= length l'.
Proof using HR.
Admitted.

(** Removing redundancy with respect to some decidable equivalence.
    Quadratic complexity. *)

Variable (f:A->A->bool).
Variable (Hf:forall a b, f a b = true <-> R a b).

Fixpoint removedup l :=
  match l with
  | [] => []
  | x::l =>
    let l' := removedup l in
    if existsb (f x) l' then l' else x::l'
  end.

Lemma removedup_nodup l : NoDupA R (removedup l).
Proof using Hf.
Admitted.

Lemma removedup_incl l : Incl (removedup l) l.
Proof using f.
Admitted.

Lemma removedup_in l x : In x l -> InModulo x (removedup l).
Proof using Hf HR.
Admitted.

End SomeEquivalence.
