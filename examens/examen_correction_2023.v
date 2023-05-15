(** Exercice 1 *)

(** 1 *)

(** On donne par exemple les preuves comme lambda-termes

(** a *)

a : (A∧B)∧C ⊢ ((π₂(π₁(a)),π₂(a)),Π₁(π₁(a))) : (B∧C)∧A

(** b *)

b : (A⇒B⇒C) ⊢ λd.(b (π₁(d)) (π₂(d))) : (A∧B)⇒C

(** c *)

c : (∃xA(x)) ⇒ B ⊢ λx.λa.(c (x,a)) : ∀x(A(x) ⇒ B)

(** d *)

((A∧B)∨C) ⊢ A∧C n'est pas prouvable : il faut prouver une conjonction
donc on peut se ramener à prouver indépendamment les deux côtés de la
conjonction, c'est-à-dire ((A∧B)∨C) ⊢ A et ((A∧B)∨C) ⊢ C.

On va alors montrer que le premier n'est pas prouvable.

En effet, quand on a une hypothèse disjonctive, on peut se ramener à
supposer indépendamment chaque côté de la disjonction, c'est-à-dire
(A∧B) ⊢ A et C ⊢ A.

Il n'y a plus de connecteur dans C ⊢ A, donc ce devrait être un
axiome, mais C est différent de A, donc ce n'est pas prouvable.

Note : une autre manière de montrer la non-prouvabilité est d'assigner
la valeur vraie à C et la valeur faux à A. On obtiendrait alors Vrai ⊢
Faux ce qui n'est pas prouvable.

(** e *)

d : (A∨B)∧C ⊢ match π₁(d) with inl(a) => inl a | inr b => (b,π₂(d)) : (A∨(B∧C)

(** 2 *)

La preuve normale de (H 1) est (0,ax 0).

La preuve normale de (H 0) est (1,refl 1).

*)

(** Exercice 2 *)

Inductive bool_list :=
| Nil : bool_list
| Cons_true : bool_list -> bool_list
| Cons_false : bool_list -> bool_list.

Check bool_list_rect.
(*
bool_list_rec : forall B:bool_list -> Type, B Nil ->
            (forall l:bool_list, B l -> B (Cons_true l)) ->
            (forall l:bool_list, B l -> B (Cons_false l)) ->
            forall l:bool_list, B l
*)

(** 1 *)

Definition bool_list_rect_no_dep :
  forall B:Type, B ->
                 (bool_list -> B -> B) ->
                 (bool_list -> B -> B) ->
                 bool_list -> B
  := fun B b ft ff l => bool_list_rect (fun _ => B) b ft ff l.

(** 2 *)

Definition bool_list_case_no_dep :
  forall B:Type, B ->
                 (bool_list -> B) ->
                 (bool_list -> B) ->
                 bool_list -> B
  := fun B b ft ff l => bool_list_rect_no_dep B b (fun l _ => ft l) (fun l _ => ff l) l.

(** 3 *)

Definition bool_list_iter :
  forall B:Type, B ->
                 (B -> B) ->
                 (B -> B) ->
                 bool_list -> B
  := fun B b ft ff l => bool_list_rect_no_dep B b (fun _ b => ft b) (fun _ b => ff b) l.

(** Exercice 3 *)

(** A *)

Inductive expr :=
| Constant : nat -> expr      (* une constante entière *)
| Mul : expr -> expr -> expr  (* le produit formel de deux expressions *)
| IfZero : expr -> expr -> expr -> expr (* évalue la 2e expr si 1e égale 0, la 3e sinon *).

(** 1 *)

Fixpoint interp e :=
  match e with
  | Constant n => n
  | Mul e1 e2 => Nat.mul (interp e1) (interp e2)
  | IfZero e1 e2 e3 =>
      match interp e1 with
      | 0 => interp e2
      | S _ => interp e3
      end
  end.

(** B *)

Module Implicit.

Inductive expr :=
| Constant : nat -> expr
| Mul : expr -> expr -> expr
| IfZero : expr -> expr -> expr -> expr
| Div : expr -> expr -> expr  (* la division de deux expressions *).

Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
  match a with
  | None => None
  | Some a => f a
  end.

(** 2 *)

Fixpoint interp E : option nat :=
  match E with
  | Constant n => Some n
  | Mul E1 E2 => bind (interp E1) (fun n1 => bind (interp E2) (fun n2 => Some (Nat.mul n1 n2)))
  | IfZero E1 E2 E3 =>
      bind (interp E1) (fun n1 =>
      match  n1 with
      | 0 => interp E2
      | S _ => interp E3
      end)
  | Div E1 E2 =>
      bind (interp E1) (fun n1 =>
      bind (interp E2) (fun n2 =>
      match n2 with
      | 0 => None
      | S _ => Some (Nat.div n1 n2)
      end))
  end.

End Implicit.

(** C *)

Module Explicit.

Inductive expr : Type -> Type :=
| Constant : nat -> expr nat
| Mul : expr nat -> expr nat -> expr nat
| IfZero : expr nat -> expr (option nat) -> expr (option nat) -> expr (option nat)
| SafeDiv : expr nat -> expr nat -> expr nat
| DivByZero : expr (option nat)
| Return : expr nat -> expr (option nat)
| Bind : expr (option nat) -> (nat -> expr (option nat)) -> expr (option nat).

(** 3 *)

Fixpoint interp {T} (E : expr T) : T :=
  match E with
  | Constant n => n
  | Mul E1 E2 => Nat.mul (interp E1) (interp E2)
  | IfZero E1 E2 E3 =>
      match (interp E1) with
      | 0 => interp E2
      | S _ => interp E3
      end
  | SafeDiv E1 E2 => Nat.div (interp E1) (interp E2)
  | DivByZero => None
  | Return E => Some (interp E)
  | Bind E f =>
      match interp E with
      | None => None
      | Some n => interp (f n)
      end
  end.

(** 4 *)

Fixpoint trad (E : Implicit.expr) : Explicit.expr (option nat) :=
  match E with
  | Implicit.Constant n => Return (Constant n)
  | Implicit.Mul E1 E2 =>
      Bind (trad E1) (fun n1 =>
      Bind (trad E2) (fun n2 =>
      Return (Mul (Constant n1) (Constant n2))))
  | Implicit.IfZero E1 E2 E3 =>
      Bind (trad E1) (fun n1 =>
      IfZero (Constant n1) (trad E2) (trad E3))
  | Implicit.Div E1 E2 =>
      Bind (trad E1) (fun n1 =>
      Bind (trad E2) (fun n2 =>
      IfZero (Constant n2) DivByZero (Return (SafeDiv (Constant n1) (Constant n2)))))
  end.

(** 5 *)

Theorem correction : forall E:Implicit.expr, Implicit.interp E = Explicit.interp (trad E).
Proof.
  (* Mostly by induction and computation *)
  induction E; simpl; unfold Implicit.bind.
  - trivial.
  - rewrite IHE1, IHE2. trivial.
  - rewrite IHE1, IHE2, IHE3. trivial.
  - rewrite IHE1, IHE2. trivial.
Qed.

End Explicit.

(** 6 *)

Module Explicit'.

Inductive expr : Type -> Type :=
| Constant : nat -> expr nat
| Mul : expr nat -> expr nat -> expr nat
| IfZero : expr nat -> expr (option nat) -> expr (option nat) -> expr (option nat)
| SafeDiv : expr nat -> expr nat -> expr nat
| DivByZero : expr (option nat)
| Return : expr nat -> expr (option nat)
| Bind : expr (option nat) -> (nat -> expr (option nat)) -> expr (option nat)
| CatchDivByZero : expr (option nat) -> expr nat -> expr nat.

Fixpoint interp {T} (E : expr T) : T :=
  match E with
  | Constant n => n
  | Mul E1 E2 => Nat.mul (interp E1) (interp E2)
  | IfZero E1 E2 E3 =>
      match (interp E1) with
      | 0 => interp E2
      | S _ => interp E3
      end
  | SafeDiv E1 E2 => Nat.div (interp E1) (interp E2)
  | DivByZero => None
  | Return E => Some (interp E)
  | Bind E f =>
      match interp E with
      | None => None
      | Some n => interp (f n)
      end
  | CatchDivByZero e1 e2 =>
      match interp e1 with
      | None => interp e2
      | Some n => n
      end
  end.

End Explicit'.

(** D *)

Definition T A := option A.
Definition ret {A} (a : A) : T A := Some a.
Definition bind {A B : Type} (a : T A) (f : A -> T B) : T B :=
  match a with None => None | Some a => f a end.

(** 7 *)

Theorem bind_return : forall {A B} (t : A) (f : A -> T B), bind (ret t) f = f t.
Proof.
reflexivity.
Qed.

Theorem return_bind : forall {A B} (t : T A) (f : A -> T B), bind t ret = t.
Proof.
destruct t; reflexivity.
Qed.

Theorem bind_bind : forall {A B C} (t : T A) (f : A -> T B) (g : B -> T C),
  bind (bind t f) g = bind t (fun a => bind (f a) g).
Proof.
destruct t; reflexivity.
Qed.

(** 8 *)

Module State.

Parameter B : Type.

Definition State A := B -> (A * B)%type.

(** 8 *)

Definition bind {A B : Type} (a : State A) (f : A -> State B) : State B :=
  fun b => let (a',b) := a b in f a' b.

Definition ret {A : Type} (a : A) : State A := fun b => (a,b).

(** 9 *)

Definition write (b:B) : State unit := fun b => (tt,b).

Definition read (_:unit) : State B := fun b => (b,b).

End State.
