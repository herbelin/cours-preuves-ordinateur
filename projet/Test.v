Require Import EquivDec.
Import ListNotations.

(** Alphabet of two letters a b *)

Module BiLetters <: FiniteOrderedType.
 Inductive letter := a | b.
 Definition enumeration := [a;b].
 Lemma enumeration_spec : forall (x:letter), In x enumeration.
 Proof.
  intros [ ]; compute; intuition.
 Qed.
 Definition t := letter.
 Definition eq := @eq letter.
 Definition compare x y :=
   match x, y with
   | a,a | b,b => Eq
   | a,b => Lt
   | b,a => Gt
   end.
 Definition lt x y := compare x y = Lt.
 Definition eq_equiv := @eq_equivalence letter.
 Lemma lt_compat : Proper (eq==>eq==>iff) lt.
 Proof. now intros ? ? -> ? ? ->. Qed.
 Global Instance lt_strorder : StrictOrder lt.
 Proof. split; red. now intros [ ]. now intros [ ] [ ] [ ]. Qed.
 Lemma compare_spec (x y : letter) :
  CompareSpec (x=y) (lt x y) (lt y x) (compare x y).
 Proof. destruct x, y; now constructor. Qed.
 Definition eq_dec (x y : letter) : { x = y } + { x <> y }.
 Proof. destruct x, y; auto; now right. Qed.
 Definition eqb x y :=
   match x,y with a,a | b,b => true | _,_ => false end.
 Lemma eqb_eq (x y:t) : eqb x y = true <-> x = y.
 Proof. now destruct x,y. Qed.
End BiLetters.
Import BiLetters.

Module Import Regexp := RegEquivDec(BiLetters).

Coercion Letter : letter >-> re.

Bind Scope re_scope with re.
Delimit Scope re_scope with re.
Open Scope re.

(* Cat · \cdot
   Star ★ \bigstar
   Not ¬ \neg
*)

Local Infix "·" := Cat (at level 40, left associativity) : re_scope.
Local Infix "+" := Or : re_scope.
Local Notation "r ★" := (Star r) (at level 30, right associativity) : re_scope.
Local Notation "0" := Void : re_scope.
Local Notation "1" := Epsilon : re_scope.
Local Notation "¬ r" := (Not r) (at level 35, no associativity) : re_scope.

Definition a_regexp := a★·b★.

Compute matching a_regexp [a;a;b;b;b].
Compute matching a_regexp [a;a;a;b;b;b;a].

(* The bound on the derivative number is quickly huge *)
Compute derivs_bound a_regexp. (* 4608 *)
(* In fact, there's lots of redundancy in [over_derivs] : *)
Compute REs.cardinal (list2set (over_derivs a_regexp)).
(* ... only 16 distincts possible derivatives *)

(* Only 3 are really derivatives *)
Compute REs.elements (exact_derivs a_regexp).

Compute is_empty a_regexp. (* false : a_regexp isn't equivalent to Void *)

Compute is_equiv (a★·a★) (a★). (* true *)
Compute is_equiv (a·a★) (a★). (* false *)

(* all the 3 previous derivatives are distinct up to equiv,
   hence the minimal automata reckognizing a*.b* will have 3 states
   (including a sink state) *)
Compute minimal_derivs a_regexp.

(* You can try you own regexps ...
   If a alphabet with only two letters isn't enough, you could
   adapt to use Coq's Ascii type ! *)
