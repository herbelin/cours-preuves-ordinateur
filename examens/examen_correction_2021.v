Inductive expr :=
| Cst : nat -> expr               (* Constante numérique:  n       *)
| Add : expr -> expr -> expr      (* Expression somme:     e1 + e2 *)
| Mul : expr -> expr -> expr.     (* Expression produit:   e1 * e2 *)

Fixpoint value e :=
  match e with
  | Cst n => n
  | Add e1 e2 => value e1 + value e2
  | Mul e1 e2 => value e1 * value e2
  end.

Inductive cont :=
| End : cont                    (* Fin du calcul *)
| AddL : expr -> cont -> cont   (* dit d'évaluer le 2e arg d'une addition *)
| AddR : nat -> cont -> cont    (* dit de finaliser le calcul d'une addition *)
| MulL : expr -> cont -> cont   (* dit d'évaluer le 2e arg d'une multiplication *)
| MulR : nat -> cont -> cont.   (* dit de finaliser le calcul d'une multiplication *)

Inductive sum (A:Type) (B:Type) :=
| inl : A -> sum A B
| inr : B -> sum A B.

Arguments inl {A B} a.
Arguments inr {A B} b.

Definition reduce ek :=
  match ek with
  | (Cst n, End) => inl n
  | (Add e1 e2, k) => inr (e1, AddL e2 k)
  | (Mul e1 e2, k) => inr (e1, MulL e2 k)
  | (Cst n, AddL e k) => inr (e, AddR n k)
  | (Cst n, AddR m k) => inr (Cst(m+n), k)
  | (Cst n, MulL e k) => inr (e, MulR n k)
  | (Cst n, MulR m k) => inr (Cst(m*n), k)
  end.

CoInductive trace :=
| result : nat -> trace         (* La machine a atteint un état final <Cst n|End> *)
| reduction : (expr * cont) -> trace -> trace.  (* La machine continue de réduire *)

CoFixpoint exec' ek :=
  match reduce ek with
  | inl n => result n
  | inr ek' => reduction ek' (exec' ek')
  end.

Definition exec e := exec' (e, End).

Inductive option (A:Type) :=
| Some : A -> option A
| None : option A.
Arguments Some {A} a.
Arguments None {A}.

Fixpoint tail trace n :=
  match trace with
  | result n => Some n
  | reduction _ trace' =>
    match n with
    | 0 => None
    | S n' => tail trace' n'
    end
  end.

Definition compute e n := tail (exec e) n.

Inductive multireduce : expr * cont -> expr * cont -> Prop :=
| start : forall ek, multireduce ek ek
| step1 : forall e1 e2 k ek, multireduce (e1, AddL e2 k) ek -> multireduce (Add e1 e2, k) ek
| step2 : forall e1 e2 k ek, multireduce (e1, MulL e2 k) ek -> multireduce (Mul e1 e2, k) ek
| step3 : forall n e k ek, multireduce (e, AddR n k) ek -> multireduce (Cst n, AddL e k) ek
| step4 : forall n m k ek, multireduce (Cst(m+n), k) ek -> multireduce (Cst n, AddR m k) ek
| step5 : forall n e k ek, multireduce (e, MulR n k) ek -> multireduce (Cst n, MulL e k) ek
| step6 : forall n m k ek, multireduce (Cst(m*n), k) ek -> multireduce (Cst n, MulR m k) ek.

Theorem spec : forall e, exists n, compute e n = Some (value e).
Admitted.

Theorem spec' : forall e, exists v, multireduce (e, End) (Cst v, End).
Admitted.

Definition value_cont : nat -> cont -> nat.
Admitted.

Definition phi : expr * cont -> nat.
Admitted.

Lemma gen_spec : forall e k, tail (exec' (e, k)) (phi (e, k)) = Some (value_cont (value e) k).
Admitted.

Lemma gen_spec' : forall ek, exists v, multireduce ek (Cst v, End).
Admitted.
