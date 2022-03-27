(*****************************************************************)
(******       M1 Preuves Assistées par Ordinateur          *******)
(****** Projet : compilation d'expressions avec sommations *******)
(******               Pierre Letouzey                      *******)
(*****************************************************************)

Require Import String Datatypes Arith NPeano List Lia.
Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

(** Travail demandé :
    a) Enlever l'axiome TODO et remplacer ses usages par du code
       convenable.
    b) Remplacer tous les Admitted par de véritables preuves. *)
Axiom TODO : forall {A:Type}, A.


(** I) Bibliotheque *)

(** Comparaisons d'entiers

    En Coq, la comparaison a <= b est une affirmation logique
    (dans Prop). On ne peut pas s'en servir pour un test dans
    un programme. Pour cela il faut utiliser la comparaison
    booléenne a <=? b (correspondant à la constante Nat.leb,
    définie dans le module NPeano). Voici le lien entre ces
    deux notions. *)

Lemma leb_le x y : (x <=? y) = true <-> x <= y.
Proof.
 apply Nat.leb_le.
Qed.

Lemma leb_gt x y : (x <=? y) = false <-> y < x.
Proof.
 rewrite Nat.lt_nge, <- leb_le. destruct (x <=? y); intuition.
Qed.

(** Une soustraction sans arrondi.

    Sur les entiers naturels, la soustraction usuelle de Coq
    est tronquée : lorsque a < b, alors a - b = 0.
    Ici on utilise None pour signaler ce cas, et Some pour
    indiquer une soustraction "réussie". *)

Fixpoint safe_minus a b : option nat :=
 match b, a with
   | 0, _ => Some a
   | S b, 0 => None
   | S b, S a => safe_minus a b
 end.

Lemma safe_minus_spec a b :
 match safe_minus a b with
 | Some c => a = b + c
 | None => a < b
 end.
Proof.
 revert b; induction a; destruct b; simpl; auto with arith.
 specialize (IHa b). destruct (safe_minus a b); auto with arith.
Qed.

(** Accès au n-ieme élement d'une liste

   NB: list_get existe aussi dans la bibliothèque standard,
   c'est List.nth_error. *)

Fixpoint list_get {A} (l:list A) i : option A :=
  match i,l with
    | 0,   x::_ => Some x
    | S j, _::l => list_get l j
    | _, _ => None
  end.

Definition option_map {A B} (f:A->B) (o:option A) :=
  match o with
    | Some a => Some (f a)
    | None => None
  end.

Fixpoint list_set {A} (l:list A) i x : option (list A) :=
  match i,l with
    | 0, _::l => Some (x::l)
    | S j, a::l => option_map (cons a) (list_set l j x)
    | _, _ => None
  end.

Lemma get_app_l {A} (l l':list A)(n:nat) : n < length l ->
  list_get (l++l') n = list_get l n.
Proof.
 revert l.
 induction n; destruct l; simpl; auto with arith; inversion 1.
Qed.

Lemma get_app_r {A} (l l':list A)(n:nat) :
  list_get (l++l') (length l + n) = list_get l' n.
Proof.
 induction l; auto.
Qed.

Lemma get_app_r0 {A} (l l':list A)(n:nat) : n = length l ->
  list_get (l++l') n = list_get l' 0.
Proof.
  intros. rewrite <- (get_app_r l l'). f_equal. lia.
Qed.

Lemma get_app_r' {A} (l l':list A)(n:nat) : length l <= n ->
  list_get (l++l') n = list_get l' (n-length l).
Proof.
 intros. rewrite <- (get_app_r l l'). f_equal. lia.
Qed.

Lemma get_None {A} (l:list A) n :
 list_get l n = None <-> length l <= n.
Proof.
 revert n. induction l; destruct n; simpl; rewrite ?IHl; split;
  auto with arith; inversion 1.
Qed.

Lemma get_Some {A} (l:list A) n x :
 list_get l n = Some x -> n < length l.
Proof.
 revert n. induction l; destruct n; simpl; try discriminate.
  - auto with arith.
  - intros. apply IHl in H. auto with arith.
Qed.

(** Equivalent de List.assoc, spécialisé aux string *)

Fixpoint lookup {A}(s:string)(l:list (string*A))(default:A) :=
  match l with
    | nil => default
    | (x,d)::l => if string_dec s x then d else lookup s l default
  end.

(** Index d'un element dans une liste, spécialisé aux string *)

Fixpoint index (s:string)(l:list string) :=
  match l with
    | nil => 0
    | x::l => if string_dec s x then 0 else S (index s l)
  end.

(** Opérateur de sommation : sum f x n = f x + ... + f (x+n).
    Attention, il y a (n+1) termes dans cette somme.
    En particulier sum f 0 n = f 0 + ... + f n. *)

Fixpoint sum f x k :=
  match k with
    | 0 => f x
    | S n' => f x + sum f (S x) n'
  end.

Compute sum (fun _ => 1) 0 10. (* 11 *)
Compute sum (fun x => x) 0 10. (* 0 + 1 + ... + 10 = 55 *)

(** II) Expressions arithmétiques avec sommations *)

(** Les expressions *)

Definition var := string.

Inductive op := Plus | Minus | Mult.

Inductive expr :=
  | EInt : nat -> expr
  | EVar : var -> expr
  | EOp  : op -> expr -> expr -> expr
  | ESum : var -> expr -> expr -> expr.

(** (ESum var max body) est la somme des valeurs de body
    lorsque var prend successivement les valeurs de 0 jusqu'à max
    (inclus). Par exemple, voici la somme des carrés de 0 à 10,
    ce qu'on écrit sum(x^2,x=0..10) en Maple ou encore
    $\sum_{x=0}^{10}{x^2}$ en LaTeX. *)

Definition test1 :=
  ESum "x" (EInt 10) (EOp Mult (EVar "x") (EVar "x")).

(** Un peu plus complexe, une double sommation:
    sum(sum(x*y,y=0..x),x=0..10) *)

Definition test2 :=
  ESum "x" (EInt 10)
   (ESum "y" (EVar "x")
     (EOp Mult (EVar "x") (EVar "y"))).


(** Evaluation d'expression *)

Definition eval_op o :=
  match o with
    | Plus => plus
    | Minus => minus
    | Mult => mult
  end.

Fixpoint eval (env:list (string*nat)) e :=
  match e with
    | EInt n => n
    | EVar v => TODO
    | EOp o e1 e2 => TODO
    | ESum v efin ecorps => TODO
  end.

Compute (eval nil test1). (* 385 attendu: n(n+1)(2n+1)/6 pour n=10 *)
Compute (eval nil test2). (* 1705 attendu *)


(** III) Machine à pile *)

(** Notre machine est composée de deux piles : une pile principale
    (pour les calculs) et une pile de variables. Les instructions
    sont stockées à part. *)

Record machine :=
  Mach {
      (** Pointeur de code *)
      pc : nat;
      (** Pile principale *)
      stack : list nat;
      (** Pile de variables *)
      vars : list nat
    }.

Definition initial_machine := Mach 0 nil nil.

Inductive instr :=
  (** Pousse une valeur entière sur la pile. *)
  | Push : nat -> instr
  (** Enleve la valeur au sommet de la pile. *)
  | Pop : instr
  (** Dépile deux valeurs et empile le resultat de l'operation binaire. *)
  | Op : op -> instr
  (** Crée une nouvelle variable en haut de la pile des variables,
      contenant initialement 0. *)
  | NewVar : instr
  (** Enleve la variable en haut de la pile des variables.
      Sa valeur actuelle est perdue. *)
  | DelVar : instr
  (** Pousse la valeur de la i-eme variable sur la pile. *)
  | GetVar : nat -> instr
  (** Enlève la valeur au sommet de la pile et donne-la à la i-eme variable. *)
  | SetVar : nat -> instr
  (** Jump offset: retire offset au pointeur de code si la première
      variable est inférieure ou égale au sommet de pile.
      Pile et variables sont gardées à l'identique. *)
  | Jump : nat -> instr.

(* NB: il n'y a pas d'instruction Halt, on s'arrête quand
   pc arrive au delà du code. *)

(* Sémantique de référence des instructions,
   définie via une relation inductive *)

Inductive Stepi : instr -> machine -> machine -> Prop :=
| SPush pc stk vs n :
    Stepi (Push n) (Mach pc stk vs) (Mach (S pc) (n::stk) vs)
| SPop pc stk vs x :
    Stepi Pop (Mach pc (x::stk) vs) (Mach (S pc) stk vs)
| SOp pc stk vs o y x :
    Stepi (Op o) (Mach pc (y::x::stk) vs)
                 (Mach (S pc) (eval_op o x y :: stk) vs)
| SNewVar pc stk vs :
    Stepi NewVar (Mach pc stk vs) (Mach (S pc) stk (0::vs))
| SDelVar pc stk vs x :
    Stepi DelVar (Mach pc stk (x::vs)) (Mach (S pc) stk vs)
| SGetVar pc stk vs i x :
    list_get vs i = Some x ->
    Stepi (GetVar i) (Mach pc stk vs) (Mach (S pc) (x::stk) vs)
| SSetVar pc stk vs vs' i x :
    list_set vs i x = Some vs' ->
    Stepi (SetVar i) (Mach pc (x::stk) vs)
                     (Mach (S pc) stk vs')
| SJumpYes pc stk vs v x off : off <= pc -> v <= x ->
    Stepi (Jump off) (Mach pc (x::stk) (v::vs))
                     (Mach (pc-off) (x::stk) (v::vs))
| SJumpNo pc stk vs v x off : x < v ->
    Stepi (Jump off) (Mach pc (x::stk) (v::vs))
                     (Mach (S pc) (x::stk) (v::vs)).

Definition Step (code:list instr) (m m' : machine) : Prop :=
 match list_get code m.(pc) with
  | Some instr => Stepi instr m m'
  | None => False
 end.

Inductive Steps (code:list instr) : machine -> machine -> Prop :=
 | NoStep m : Steps code m m
 | SomeSteps m1 m2 m3 :
     Step code m1 m2 -> Steps code m2 m3 -> Steps code m1 m3.

(** state : état d'une machine, c'est à dire sa pile de calcul
    et sa pile de variables, mais pas son pc. *)

Definition state := (list nat * list nat)%type.

(** Une execution complète va de pc=0 à pc=(length code) *)

Definition Exec code '(stk, vs) '(stk', vs') :=
  Steps code (Mach 0 stk vs) (Mach (length code) stk' vs').

(** Run : relation entre un code et le résultat de son exécution. *)

Definition Run code res := Exec code (nil,nil) (res::nil,nil).

(** Petit exemple d'usage de cette sémantique *)

Lemma Run_example :
  Run (Push 7 :: Push 3 :: Op Minus :: nil) 4.
Proof.
 repeat econstructor.
Qed.

(** Propriétés basiques de Steps : transitivité, ... *)

Hint Constructors Steps.

Lemma Steps_trans code m1 m2 m3 :
 Steps code m1 m2 -> Steps code m2 m3 -> Steps code m1 m3.
Proof.
Admitted.

Lemma OneStep code st st' : Step code st st' -> Steps code st st'.
Proof.
Admitted.

(** Décalage de pc dans une machine *)

Definition shift_pc k (p:machine) :=
 let '(Mach pc vars stk) := p in
 (Mach (k+pc) vars stk).

Lemma pc_shift n m : (shift_pc n m).(pc) = n + m.(pc).
Proof.
 now destruct m.
Qed.

(** Ajout de code devant / derriere la zone intéressante *)

Hint Resolve get_Some.

Lemma Step_extend code code' m m' :
 Step code m m' -> Step (code++code') m m'.
Proof.
Admitted.

Lemma Steps_extend code code' m m' :
 Steps code m m' -> Steps (code++code') m m'.
Proof.
Admitted.

Hint Constructors Stepi.

Lemma Stepi_shift instr n m m' :
 Stepi instr m m' ->
 Stepi instr (shift_pc n m) (shift_pc n m').
Proof.
Admitted.

Lemma Step_shift code0 code m m' (n := List.length code0) :
 Step code m m' ->
 Step (code0 ++ code) (shift_pc n m) (shift_pc n m').
Proof.
Admitted.

Lemma Steps_shift code0 code  m m' (n := List.length code0) :
 Steps code m m' ->
 Steps (code0 ++ code) (shift_pc n m) (shift_pc n m').
Proof.
Admitted.

(** Composition d'exécutions complètes *)

Lemma Exec_trans code1 code2 stk1 vars1 stk2 vars2 stk3 vars3 :
 Exec code1 (stk1, vars1) (stk2, vars2) ->
 Exec code2 (stk2, vars2) (stk3, vars3) ->
 Exec (code1 ++ code2) (stk1, vars1) (stk3, vars3).
Proof.
Admitted.


(** Correction des sauts lors d'une boucle

    - La variable 0 est la variable de boucle a,
    - La variable 1 est l'accumulateur acc
    - Le haut de pile est la limite haute b de la variable de boucle

    On montre d'abord que si un code ajoute f(a) à acc et
    incrémente a, alors la répétition de ce code (via un Jump
    ultérieur) ajoutera (sum f a (b-a)) à acc.
    La variable N (valant b-a) est le nombre de tours à faire.
*)

(* Ce lemme est difficile. N'hésitez pas à le sauter et à y revenir
   après avoir fini la partie IV. *)

Hint Resolve le_n_S le_plus_r.

Lemma Steps_jump code n (f:nat->nat) stk vars b :
  length code = n ->
  (forall a acc,
   Steps code
         (Mach 0 (b::stk) (a::acc::vars))
         (Mach n (b::stk) ((S a)::(acc + f a)::vars)))
  ->
  forall N a acc,
    b = N + a ->
    Steps (code++(Jump n)::nil)
          (Mach 0 (b::stk) (a::acc::vars))
          (Mach (S n) (b::stk) ((S b)::(acc + sum f a N)::vars)).
Proof.
Admitted.

(** Version spécialisée du résultat précédent, avec des
    Exec au lieu de Step, et 0 comme valeur initiale des variables
    de boucle et d'accumulateurs. *)

Lemma Exec_jump code (f:nat->nat) stk vars b :
  (forall a acc,
     Exec code (b::stk, a::acc::vars)
               (b::stk, (S a)::(acc + f a)::vars))
  ->
  Exec (code++(Jump (length code))::nil)
      (b::stk, 0::0::vars)
      (b::stk, (S b)::(sum f 0 b)::vars).
Proof.
Admitted.


(** IV) Le compilateur

    On transforme une expression en instructions pour
    notre machine à pile.

    Conventions:
     - à chaque entrée dans une boucle, on crée deux variables,
       la variable de boucle et l'accumulateur.
     - on s'arrange pour que les variables de boucles aient
       des indices pairs dans la pile des variables
     - l'environnement de compilation cenv ne contient que les
       variables de boucles.
    Voir également l'invariant EnvsOk ci-dessous. *)

Fixpoint comp (cenv:list string) e :=
  match e with
    | EInt n => Push n :: nil
    | EVar v => TODO
    | EOp o e1 e2 => TODO
    | ESum v efin ecorps =>
      let prologue := TODO in
      let corps := TODO in
      let boucle := corps ++ Jump TODO :: nil in
      let epilogue := TODO in
      prologue ++ boucle ++ epilogue
  end.

Definition compile e := comp nil e.

(** Variables libres d'une expression *)

Inductive FV (v:var) : expr -> Prop :=
| FVVar : FV v (EVar v).
(* TODO : ajouter les règles manquantes... *)

Hint Constructors FV.

Definition Closed e := forall v, ~ FV v e.

(** Invariants sur les environnements.
    env : environnement d'evaluation (list (string*nat))
    cenv : environnement de compilation (list string)
    vars : pile de variables pour nos machines *)

Definition EnvsOk e env cenv vars :=
 forall v, FV v e ->
   In v cenv /\
   list_get vars (index v cenv * 2) = Some (lookup v env 0).

Hint Unfold EnvsOk.

Lemma EnvsOk_ESum v e1 e2 env cenv vars a b :
  EnvsOk (ESum v e1 e2) env cenv vars ->
  EnvsOk e2 ((v,a)::env) (v::cenv) (a::b::vars).
Proof.
Admitted.


(** Correction du compilateur *)

Ltac basic_exec :=
  (* Cette tactique prouve des buts (Exec code m m')
     quand le code et la machine m sont connus en détail. *)
  unfold Exec; repeat (eapply SomeSteps; [constructor|]);
   try apply NoStep; try reflexivity.

(* Si vous avez l'impression de prouver quelque chose d'impossible,
   peut-être est-ce le signe que vous vous êtes trompé dans la définition
   de comp. *)

Theorem comp_ok e env cenv vars stk :
 EnvsOk e env cenv vars ->
 Exec (comp cenv e) (stk,vars) (eval env e :: stk, vars).
Proof.
Admitted.

Theorem compile_ok e : Closed e -> Run (compile e) (eval nil e).
Proof.
Admitted.

(** V) Sémantique exécutable

    A la place des relations précédentes (Step*, Exec, Run...),
    on cherche maintenant à obtenir une fonction calculant
    le résultat de l'exécution d'une machine à pile. *)

(* Cette partie est nettement plus difficile que les précédentes
   et est complètement optionnelle. *)

Inductive step_result : Type :=
  | More : machine -> step_result (* calcul en cours *)
  | Stop : machine -> step_result (* calcul fini (pc hors code) *)
  | Bug : step_result. (* situation illégale, machine plantée *)

(** Pour la fonction [step] ci-dessous, ces deux opérateurs
    monadiques peuvent aider (même si c'est essentiellement
    une affaire de goût). *)

Definition option_bind {A} (o:option A) (f : A -> step_result) :=
  match o with
    | None => Bug
    | Some x => f x
  end.

Infix ">>=" := option_bind (at level 20, left associativity).

Definition list_bind {A} (l:list A) (f:A->list A->step_result) :=
 match l with
  | nil => Bug
  | x::l => f x l
 end.

Infix "::>" := list_bind (at level 20, left associativity).

(** Un pas de calcul *)

Definition step code (m:machine) : step_result :=
  let '(Mach pc stk vars) := m in
  (** réponse usuelle: *)
  let more := fun stk vars => More (Mach (S pc) stk vars) in
  match list_get code pc with
    | None => Stop m
    | Some instr => match instr with
      | Push n => more (n::stk) vars
      | Pop => TODO
      | Op o => TODO
      | NewVar => TODO
      | DelVar => TODO
      | GetVar i => TODO
      | SetVar i => TODO
      | Jump off => TODO
      end
    end.

(** La fonction [steps] itère [step] un nombre [count] de fois
    (ou moins si [Stop _] ou [Bug] sont atteints). *)

Fixpoint steps count (code:list instr)(m:machine) :=
  match count with
    | 0 => More m
    | S count' => TODO
  end.

(** La function [run] exécute un certain code à partir
    de la machine initiale, puis extrait le résultat obtenu.
    On répond [None] si le calcul n'est pas fini au bout
    des [count] étapes indiquées, ou bien en cas d'anomalies
    lors de l'exécution ou à la fin (p.ex. pile finale vide,
    variables finales non vides, etc). *)

Definition run (count:nat)(code : list instr) : option nat :=
  TODO.

Compute (run 1000 (compile test1)). (* attendu: Some 385 *)
Compute (run 1000 (compile test2)). (* attendu: Some 1705 *)

(** Equivalence entre sémantiques *)

(** TODO: dans cette partie, à vous de formuler les
    lemmes intermédiaires. *)

Lemma run_equiv code res :
 Run code res <-> exists count, run count code = Some res.
Proof.
Admitted.

(** Le theorème principal, formulé pour run *)

Theorem run_compile e :
 Closed e ->
 exists count, run count (compile e) = Some (eval nil e).
Proof.
Admitted.
