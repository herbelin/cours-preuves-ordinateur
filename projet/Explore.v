Require Export Finiteness.
Import ListNotations.

(** * Generating the exact set of derivatives of a regexp *)

(** In Finiteness.v, we've built an over-approximation of these
    derivatives. Now, let's be exact. *)

Module RegExplore (Letter : FiniteOrderedType).
Include FiniteDerivs(Letter).

Implicit Type a : Letter.t.

(** From a given regexp r, the set of all [canon (r/a)] for all
    possible letters a. *)

Definition allderiv1 r :=
  list2set (List.map (fun a => canon (r/a)) Letter.enumeration).

Lemma allderiv1_in r x :
  REs.In x (allderiv1 r) <-> exists a, x = canon (r/a).
Proof.
Admitted.

(** We proceed via a graph exploration. Nodes are regexps, edges are
    letters, there is an edge [a] from [r] to [s] if [canon (r/a) = s].
    We start with our initial regexp, and we stop when nothing new could
    be reached. Note: this graph is actually the automata recognizing
    our regexp, but we do not build it explicitely here.

    - [n] is the depth of our search, to convince Coq we'll stop someday
    - [explored] is a set of derivatives we've finished visiting :
      all their derivatives by a letter are in [explored] or [seen]
    - [seen] is a set of derivatives we still have to handle :
      we haven't checked yet whether their own derivatives are new or not.
*)

Fixpoint explore n explored seen :=
  match n with
  | 0 => REs.empty (* abort *)
  | S n =>
    let seen' := REs.diff seen explored in
    match REs.choose seen' with
    | None => explored (* finished *)
    | Some x =>
      explore n (REs.add x explored)
                (REs.union (allderiv1 x) (REs.remove x seen'))
    end
  end.

Definition try_exact_derivs r n :=
  explore n REs.empty (REs.singleton (canon r)).

(** Normally, we launch explore with [derivs_bound], to be sure to
    converges. But this bound could be horribly slow to compute... *)

Definition slow_exact_derivs r :=
  try_exact_derivs r (S (derivs_bound r)).

(** Pragmatic approach : 100 loops are usually enough.
    If not, we restart with the full bound and wait... *)

Definition exact_derivs r :=
  let s := try_exact_derivs r 100 in
  if REs.is_empty s then slow_exact_derivs r (* 100 wasn't enough *)
  else s.

Definition Deriv r r' := exists w, r' = canon (r//w).
Definition DerivSet r set := forall r', REs.In r' set -> Deriv r r'.
Definition ExactDerivSet r set := forall r', REs.In r' set <-> Deriv r r'.
Definition Hereditary set1 set2 :=
  forall r a, REs.In r set1 -> REs.In (canon (r/a)) set2.

Global Instance : Proper (eq ==> REs.Equal ==> iff) DerivSet.
Proof.
 intros r r' <- set set' E. unfold DerivSet. now setoid_rewrite E.
Qed.

Global Instance : Proper (REs.Equal ==> REs.Equal ==> iff) Hereditary.
Proof.
 intros set1 set1' E1 set2 set2' E2. unfold Hereditary.
 setoid_rewrite E1; setoid_rewrite E2; easy.
Qed.

Lemma a_set_equation x explored seen :
  REs.Equal
    (REs.union (REs.add x explored)
               (REs.union (allderiv1 x)
                          (REs.remove x (REs.diff seen explored))))
    (REs.union (allderiv1 x) (REs.add x (REs.union explored seen))).
Proof.
 intro y. generalize (allderiv1_in x y). REsdec.
Qed.

Definition PreCondition r explored seen :=
  let all := REs.union explored seen in
  REs.In (canon r) all /\
  DerivSet r all /\
  Hereditary explored all.

Lemma PreCondition_init r :
  PreCondition r REs.empty (REs.singleton (canon r)).
Proof.
Admitted.

Lemma PreCondition_next r explored seen x :
  let seen' := REs.diff seen explored in
  REs.In x seen' ->
  PreCondition r explored seen ->
  PreCondition r (REs.add x explored)
                 (REs.union (allderiv1 x) (REs.remove x seen')).
Proof.
Admitted.

(** Here it could help to proceed by induction over the [rev] of some word.
    Feel free to add any intermediate lemmas that might help you. *)

Lemma hereditary_all_derivs r s set :
  REs.In (canon r) set ->
  Hereditary set set ->
  Deriv r s -> REs.In s set.
Proof.
Admitted.

Lemma explore_partial_spec r n explored seen :
 PreCondition r explored seen ->
 let out := explore n explored seen in
 REs.Empty out \/ ExactDerivSet r out.
Proof.
Admitted.

Lemma explore_converges r n explored seen :
 derivs_bound r < n + REs.cardinal explored ->
 PreCondition r explored seen ->
 ~REs.Empty (explore n explored seen).
Proof.
Admitted.

Lemma explore_spec r n explored seen :
 derivs_bound r < n + REs.cardinal explored ->
 PreCondition r explored seen ->
 ExactDerivSet r (explore n explored seen).
Proof.
Admitted.

Lemma slow_exact_derivs_spec r :
  ExactDerivSet r (slow_exact_derivs r).
Proof.
Admitted.

Lemma exact_derivs_spec r :
  ExactDerivSet r (exact_derivs r).
Proof.
Admitted.

Lemma exact_derivs_alt r :
  REs.Equal (exact_derivs r) (slow_exact_derivs r).
Proof.
Admitted.

Lemma exact_derivs_init r : REs.In (canon r) (exact_derivs r).
Proof.
Admitted.

(** The exact count of derivatives of [r] not identified by [=~=] *)

Definition derivs_sim_nb r := REs.cardinal (exact_derivs r).

Lemma derivs_sim_nb_nz r : derivs_sim_nb r <> 0.
Proof.
Admitted.

(** Any list of derivatives without duplicates
    is smaller than [exact_derivs]. *)

Definition DerivList r l := forall r', In r' l -> Deriv r r'.

Lemma derivs_smaller r l :
  NoDup l -> DerivList r l -> length l <= derivs_sim_nb r.
Proof.
Admitted.

(** Any complete list of derivatives is larger than [exact_derivs]. *)

Lemma derivs_larger r l :
  AllDerivsIn r l -> derivs_sim_nb r <= length l.
Proof.
Admitted.

(** In particular, the first bound on derivatives is (way) larger
    than [derivs_sim_nb]. *)

Lemma exact_below_bound r : derivs_sim_nb r <= derivs_bound r.
Proof.
Admitted.

(** Same results using [sim] instead of [canon]. *)

Lemma NoDupA_sim_canon l : NoDupA sim l -> NoDup (map canon l).
Proof.
Admitted.

Lemma derivs_sim_smaller r l :
 NoDupA sim l -> (forall r', In r' l -> exists w, r' =~= r//w) ->
 length l <= derivs_sim_nb r.
Proof.
Admitted.

Lemma derivs_sim_larger r l :
 AllDerivsInMod sim r l -> derivs_sim_nb r <= length l.
Proof.
Admitted.

End RegExplore.
