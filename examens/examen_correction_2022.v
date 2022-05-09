Unset Elimination Schemes.
Inductive tree :=
| Leaf : nat -> tree
| Node : (nat -> tree) -> tree.

Axiom tree_iter : forall B:Type, (nat -> B) ->
            ((nat -> B) -> B) ->
            tree -> B.

Definition tree_rec (B:Type) (f : nat -> B) (f' : (nat -> tree) -> (nat -> B) -> B) (t : tree) : B :=
  snd (tree_iter (tree * B)
        (fun n => (Leaf n, f n))
        (fun g => (Node (fun n => fst (g n)), f' (fun n => fst (g n)) (fun n => snd (g n))))
        t).

Definition tree_case (B:Type) (f : nat -> B) (f' : (nat -> tree) -> B) (t : tree) : B :=
  tree_rec B f (fun g _ => f' g) t.

Inductive form (I:Type) :=
| Atom : I -> form I          (* un atome de la forme X_i pour i∈I *)
| True : form I               (* proposition tout le temps vraie *)
| False : form I              (* proposition tout le temps fausse *)
| Or : form I -> form I -> form I   (* disjonction *)
| And : form I -> form I -> form I  (* conjonction *)
| Imp : form I -> form I -> form I. (* implication *)

Arguments Atom {I} i.
Arguments True {I}.
Arguments False {I}.
Arguments Or {I} F G.
Arguments And {I} F G.
Arguments Imp {I} F G.

Definition form_closed := form Empty_set.

Fixpoint truth_closed (F : form_closed) : bool :=
  match F with
  | Atom i => Empty_set_rect _ i
  | True => true
  | False => false
  | Or F G => truth_closed F || truth_closed G
  | And F G => truth_closed F && truth_closed G
  | Imp F G => negb (truth_closed F) || truth_closed G
  end.

Eval compute in truth_closed (Imp (And False True) False).
Eval compute in truth_closed (Or (And True False) False).

Fixpoint truth {I:Type} (sigma : I -> bool) (F : form I) : bool :=
  match F with
  | Atom i => sigma i
  | True => true
  | False => false
  | Or F G => truth sigma F || truth sigma G
  | And F G => truth sigma F && truth sigma G
  | Imp F G => negb (truth sigma F) || truth sigma G
  end.

Definition sigma1 n := match n with 1 => false | _ => true end.
Eval compute in truth sigma1 (Imp (And (Atom 0) (Atom 1)) (Atom 2)).
Definition sigma2 n := match n with 0 => false | _ => true end.
Eval compute in truth sigma2 (Imp (And (Atom 0) (Atom 1)) (Atom 2)).
Definition form_one_atom := form unit.
Definition context (I:Type) := list (form I).

Definition valid_one_atom (F : form_one_atom) : Prop :=
  truth (fun _ =>  true) F = true /\ truth (fun _ =>  false) F = true.

Fixpoint truth_context {I:Type} (sigma : I -> bool) (Γ : context I) : bool :=
  match Γ with
  | nil => true
  | cons F Γ => truth sigma F && truth_context sigma Γ
  end.

Require Import List.

Inductive provable {I:Type} : list (form I) -> form I -> Prop :=
| Ax : forall F Γ, In F Γ -> provable Γ F
| TrueI : forall Γ, provable Γ True
| FalseE : forall Γ F, provable Γ False -> provable Γ F
| ImpI : forall Γ F G, provable (F::Γ) G -> provable Γ (Imp F G)
| ImpE : forall Γ F G, provable Γ (Imp F G) -> provable Γ F -> provable Γ G
| OrI1 : forall Γ F G, provable Γ F -> provable Γ (Or F G)
| OrI2 : forall Γ F G, provable Γ G -> provable Γ (Or F G)
| OrE : forall Γ F G H, provable Γ (Or F G) ->
          provable (F::Γ) H -> provable (G::Γ) H -> provable Γ H
| AndI : forall Γ F G, provable Γ F -> provable Γ G -> provable Γ (And F G)
| AndI1 : forall Γ F G, provable Γ (And F G) -> provable Γ F
| AndI2 : forall Γ F G, provable Γ (And F G) -> provable Γ G
| ExcludedMiddle : forall Γ F, provable Γ (Or F (Imp F False)).

Require Import Bool.

Lemma axiom (Γ:context unit) (σ : unit->bool) (F:form unit) :
  In F Γ -> truth_context σ Γ = true -> truth σ F = true.
Proof.
induction Γ as [|H Γ IHΓ]; intros HIn HΓ.
- now exfalso.
- destruct HIn as [->|H'].
  + now apply andb_true_iff in HΓ as (HF,_).
  + apply andb_true_iff in HΓ as (_,HΓ).
    now apply IHΓ.
Defined.

Import EqNotations.

Theorem soundness_one_atom {Γ:context unit} {F:form unit}
  (p : provable Γ F) (σ:unit->bool) : truth_context σ Γ = true -> truth σ F = true.
Admitted.

Theorem completeness_one_atom :
  forall (Γ:context unit) (F:form unit),
  (forall σ:unit->bool, truth_context σ Γ = true -> truth σ F = true) ->
  provable Γ F.
Admitted.

Theorem soundness_completeness :
  forall (F:form unit), valid_one_atom F <-> provable nil F.
Admitted.
