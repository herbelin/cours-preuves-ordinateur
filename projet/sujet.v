Require Import Bool Arith Lia Btauto Morphisms Setoid RelationClasses.
Require  List.
Import List.ListNotations.
Open Scope list_scope.

(* Axiome à supprimer quand vous avez fini. *)

Axiom TODO : forall A, A.

(* Première partie : listes *)

(* Équivalence de listes *)

Definition eqlist {A} (l l' : list A) := forall n, List.In n l <-> List.In n l'.

Infix "==" := eqlist (at level 70).

(* Permet d'utiliser les tactiques reflexivity, symmetry, transitivity,
 * congruence, etc.
 *)

Instance eqlist_equiv {A} : Equivalence (@eqlist A).
Proof.
 firstorder.
Qed.

(* Permet de réécrire une liste en une liste équivalente à l'intérieur
 * d'un [List.in x].
 *)

Instance eqlist_In {A} (x : A) : Proper (eqlist ==> iff) (List.In x).
Proof.
  firstorder.
Qed.

Lemma eqlist_swap {A} (l l' : list A) (a : A) :
  l ++ a :: l' == a :: l ++ l'.
Proof.
Admitted.

Lemma eqlist_uncons {A} (l l' : list A) (x : A) :
  ~ List.In x l -> ~ List.In x l' -> x :: l == x :: l' -> l == l'.
Proof.
Admitted.

(* Définir la fonction produit cartésien de deux listes.
 * Le produit cartésien d'un couple de listes (l1,l2) est la liste des
 * couples d'éléments (x,y) avec [x] dans [l1] et [y] dans [l2].
 *)

Fixpoint product {A} (l1 l2 : list A) : list (A * A) :=
  match l1 with
  | [] => TODO _
  | h1 :: t1 => TODO _
  end.

Lemma product_correct {A} (l1 l2 : list A) :
  forall x y, (List.In x l1 /\ List.In y l2) <-> List.In (x, y) (product l1 l2).
Proof.
Admitted.

Lemma NoDup_app {A} (l l' : list A):
  List.NoDup (l ++ l') <->
  List.NoDup l /\ List.NoDup l' /\ (forall x, ~ (List.In x l /\ List.In x l')).
Proof.
Admitted.

(* Maintenant, on considère des listes d'entiers naturels, qui ont
 * l'avantage d'avoir une égalité décidable.
 *)

Definition mem (x : nat) : list nat -> bool := List.existsb (Nat.eqb x).

Lemma mem_In x l : mem x l = true <-> List.In x l.
Proof.
Admitted.

(* Une égalité entre deux booléens, c'est comme un si-et-seulement-si.
 * Parfois il est utile de considérer le cas "vrai" et le cas "faux"
 * séparément le plus tôt possible car les preuves seront très différentes.
 * Parfois il est utile, de séparer les deux cas le plus tard possible car
 * les preuves seront presques identiques. Parfois, on peut s'abstenir
 * entièrement de séparer les deux cas, et procéder par réécriture.
 *)

Lemma mem_app (x : nat) (l1 l2 : list nat) :
  mem x l1 || mem x l2 = mem x (l1 ++ l2).
Proof.
Admitted.

(* Deuxième partie : coarbres *)

(* Definition des coarbres.
 * Un coarbre est un arbre binaire dont les noeuds internes sont marqués
 * comme connectés ou non-connectés et les feuilles sont étiquettés par
 * des identifiants (on utilisera les entiers naturels).
 * L'intérêt de cette définition viendra lorsque nous associerons un
 * graphe (appelé cographe) à chaque coarbre.
 *)

Inductive cotree :=
| Leaf (ident : nat)
| Node (connected : bool) (l r : cotree).

Module Cotree.

(* Compléter la définition suivante de sorte à ce que [In x t] est vrai si
 * et seulement si [x] est une étiquette d'une feuille de [t].
 *)

Inductive In (x : nat) : cotree -> Prop :=
.

Global Hint Constructors In : core.

Lemma In_Node (connected : bool) (t1 t2 : cotree) (x : nat) :
  Cotree.In x (Node connected t1 t2) <-> Cotree.In x t1 \/ Cotree.In x t2.
Proof.
Admitted.

(* Définir une fonction donnant la liste des feuilles d'un coarbre et
 * montrer que [Cotree.In] pouvait également s'exprimer comme une
 * combinaison de [List.In] et [Cotree.leaves].
 *)

Fixpoint leaves (t : cotree) : list nat :=
  match t with
  | Leaf ident => TODO _
  | Node connected l r => TODO _
  end.

Lemma In_leaves (x : nat) (t : cotree) :
  Cotree.In x t <-> List.In x (Cotree.leaves t).
Proof.
Admitted.

(* Par construction, un coarbre n'est pas vide (il a toujours au moins
 * une feuille).
 *)

Lemma nonempty (t : cotree) : exists x : nat, Cotree.In x t.
Proof.
Admitted.

(* Dit autrement la liste des feuilles d'un coarbre n'est pas la liste vide. *)

Lemma leaves_nonnil (t : cotree) : Cotree.leaves t <> [].
Proof.
Admitted.

(* Un prédicat inductif définissant le fait d'être bien-formé pour
 * un coarbre. Un coarbre est bien formé si toutes ses étiquettes aux
 * feuilles sont distinctes.
 *)

Inductive Wf : cotree -> Prop :=
| WfLeaf x : Wf (Leaf x)
| WfNode connected l r :
    Wf l -> Wf r -> (forall x, ~(In x l /\ In x r)) -> Wf (Node connected l r).

Global Hint Constructors Wf : core.

Lemma Wf_not_In_l (connected : bool) (l r : cotree) :
  let t := Node connected l r in
  Wf t ->
  forall (x : nat), Cotree.In x r -> not (Cotree.In x l).
Proof.
Admitted.

Lemma Wf_not_In_r (connected : bool) (l r : cotree) :
  let t := Node connected l r in
  Wf t ->
  forall (x : nat), Cotree.In x l -> not (Cotree.In x r).
Proof.
Admitted.

Lemma Wf_leaves t : Wf t <-> List.NoDup (leaves t).
Proof.
Admitted.

End Cotree.

(* Troisième partie : graphes *)

(* Une définition compacte des graphes par listes d'adjacence.
 * Deux noeuds sont connectés si la liste d'adjacence contient un
 * couple de listes, dont l'une contient le premier noeud, et
 * l'autre contient le second. Par exemple, la liste d'adjacence
 * [([0;1;2],[3;4])] est équivalente à la version non-compacte
 * [(0,3);(0,4);(1,3);(1,4);(2,3);(2,4)].
 * Par définition, on ne donne pas d'orientation aux arêtes.
 *)

Record graph :=
  { edges : list (list nat * list nat);
    vertices : list nat
  }.

Module Graph.

Definition has_edge (g : graph) (n m : nat) : bool :=
  List.existsb
    (fun '(l1, l2) => mem n l1 && mem m l2 || mem n l2 && mem m l1)
    g.(edges).

Lemma has_edge_sym (g : graph) (n m : nat) :
  Graph.has_edge g n m = Graph.has_edge g m n.
Proof.
Admitted.

(* Un graphe est bien formé si tous les noeuds qui apparaissent dans
 * les listes d'adjacence apparaissent aussi dans la liste des
 * noeuds, et que les deux extrémités d'une arête sont différentes.
 *)

Definition Wf (g: graph) : Prop := TODO _.

(* Chemins dans les graphes et connexité. *)

(* On définit un prédicat inductif représentant l'existence d'un chemin
 * (possiblement de taille 0) entre deux noeuds dans un graphe.
 *)

 Inductive has_path (g : graph) : nat -> nat -> Prop :=
 | refl_path :
     forall x : nat, List.In x g.(vertices) -> has_path g x x
 | step_path :
     forall x y z : nat, has_path g x y -> Graph.has_edge g y z = true -> has_path g x z.

Global Hint Constructors has_path : core.

Lemma has_edge_path (g : graph) (n m : nat) :
  Graph.Wf g -> Graph.has_edge g n m = true -> Graph.has_path g n m.
Proof.
Admitted.

Lemma has_path_trans (g : graph) (n m p : nat) :
  Graph.has_path g n m -> Graph.has_path g m p -> Graph.has_path g n p.
Proof.
Admitted.

Lemma has_path_sym (g : graph) (n m : nat) :
  Graph.Wf g -> Graph.has_path g n m -> Graph.has_path g m n.
Proof.
Admitted.

Definition connected (g : graph) :=
  forall n m : nat,
    List.In n g.(vertices) -> List.In m g.(vertices) -> Graph.has_path g n m.

(* Le graphe composé du seul chemin 0--1--2--...--(length-1) est
 * un graphe connecté.
 *)

Lemma path_connected (g : graph) (length : nat) :
  Graph.Wf g ->
  (forall n : nat, List.In n g.(vertices) -> n < length) ->
  (forall n : nat, S n < length -> Graph.has_edge g n (S n) = true) ->
  Graph.connected g.
Proof.
Admitted.

(* On définit une relation d'équivalence pour les graphes.
 * On n'utilise pas l'égalité car on veut considérer comme identiques
 * deux graphes qui ont les mêmes noeuds et les mêmes arêtes, mais dont
 * les noeuds ou les arêtes ne sont pas présentés dans le même ordre ou
 * de la même manière.
 *)

Definition eq (g1 g2 : graph) :=
  g1.(vertices) == g2.(vertices) /\
  (forall (n m : nat), Graph.has_edge g1 n m = Graph.has_edge g2 n m).

(* Permet d'utiliser les tactiques reflexivity, symmetry, transitivity,
 * congruence, etc.
 *)

Instance eq_equiv : Equivalence Graph.eq.
Proof.
  firstorder congruence.
Qed.

Lemma eq_Wf (g1 g2 : graph) : Graph.eq g1 g2 -> Graph.Wf g1 -> Graph.Wf g2.
Proof.
Admitted.

Definition complement (g1 g2 : graph) :=
  Graph.Wf g1 /\ Graph.Wf g2 /\ g1.(vertices) == g2.(vertices) /\
  (forall (n m : nat), List.In n g1.(vertices) -> List.In m g1.(vertices) -> n <> m ->
                Graph.has_edge g1 n m <> Graph.has_edge g2 n m).

Lemma complement_sym (g1 g2 : graph) : complement g1 g2 -> complement g2 g1.
Proof.
  intros (? & ? & H__vertices & H__edges).
  setoid_rewrite H__vertices in H__edges.
  firstorder.
Qed.

End Graph.

(* Quatrième partie : cographes *)

(* Écrire la fonction qui produit le (co)graphe associé à un coarbre.
 * Par définition, ce sera le graphe dont les noeuds sont étiquettés
 * par les étiquettes se trouvant aux feuilles du coarbre et qui
 * possède une arête entre deux noeuds [x] et [y] (distinct) si le
 * plus proche parent de [x] et [y] dans le coarbre est marqué comme
 * connecté.
 *)

Module Cograph.

Fixpoint of_cotree (t : cotree) : graph :=
  match t with
  | Leaf ident => TODO _
  | Node connected l r => TODO _
  end.

Lemma vertices_leaves (t : cotree) :
  (Cograph.of_cotree t).(vertices) = Cotree.leaves t.
Proof.
Admitted.

Lemma vertices_In_cotree (x : nat) (t : cotree) :
  Cotree.In x t <-> List.In x (Cograph.of_cotree t).(vertices).
Proof.
Admitted.

Lemma Wf (t : cotree) : Cotree.Wf t -> Graph.Wf (Cograph.of_cotree t).
Proof.
Admitted.

(* Attention à ne pas se laisser entraîner dans une preuve excessivement
 * longue. Un cas sur deux devrait être raisonnablement bref.
 *)

Lemma of_cotree_correct (connected : bool) (t1 t2 : cotree) :
  let t := Node connected t1 t2 in
  Cotree.Wf t ->
  forall n m : nat,
    Cotree.In n t1 -> Cotree.In m t2 ->
    Graph.has_edge (Cograph.of_cotree t) n m = connected.
Proof.
Admitted.

Lemma of_cotree_rec_l (connected : bool) (t1 t2 : cotree) :
  let t := Node connected t1 t2 in
  Cotree.Wf t ->
  forall n m : nat,
    Cotree.In n t1 -> Cotree.In m t1 ->
    Graph.has_edge (Cograph.of_cotree t) n m = Graph.has_edge (Cograph.of_cotree t1) n m.
Proof.
Admitted.

Lemma of_cotree_rec_r (connected : bool) (t1 t2 : cotree) :
  let t := Node connected t1 t2 in
  Cotree.Wf t ->
  forall n m : nat,
    Cotree.In n t2 -> Cotree.In m t2 ->
    Graph.has_edge (Cograph.of_cotree t) n m = Graph.has_edge (Cograph.of_cotree t2) n m.
Proof.
Admitted.

Lemma of_cotree_correct_path (connected : bool) (t1 t2 : cotree) :
  let t := Node connected t1 t2 in
  Cotree.Wf t ->
  forall n m : nat,
    Cotree.In n t1 -> Cotree.In m t2 ->
    Graph.has_path (Cograph.of_cotree t) n m <-> connected = true.
Proof.
Admitted.

Lemma connected (connected : bool) (t1 t2 : cotree) :
  let t := Node connected t1 t2 in
  Cotree.Wf t -> Graph.connected (Cograph.of_cotree t) <-> connected = true.
Proof.
Admitted.

Definition yes (g : graph) :=
  exists (t : cotree), Cotree.Wf t /\ Graph.eq (Cograph.of_cotree t) g.

End Cograph.

(* La suite du projet est entièrement facultative. *)

(* Cinquième partie : être ou ne pas être un cographe. *)

(* Vous êtes fortement encouragés à recourir à des définitions et des
 * lemmes intermédiaires.
 *)

Theorem complement_cograph (g1 g2 : graph) :
  Graph.complement g1 g2 -> Cograph.yes g1 <-> Cograph.yes g2.
Proof.
Admitted.

(* Tous les graphes ne sont pas des cographes et en voici un exemple.
 * Il s'agit du graphe 0--1--2--3 (quatre noeuds et trois arêtes qui en
 * font un graphe connexe).
 * Preuve difficile : commencer par une preuve informelle avec les grandes
 * étapes. Utiliser assert pour marquer ces étapes intermédiaires.
 *)

Theorem not_all_graphs_are_cographs :
  not (Cograph.yes {| edges := [([0],[1]);([1],[2]);([2],[3])]; vertices := [0;1;2;3] |}).
Proof.
Admitted.

(* Sixième partie : caractérisation des cographes *)

(* La page wikipédia sur les cographes <https://en.wikipedia.org/wiki/Cograph>
 * présente une définition équivalente (qui n'est pas celle que nous avons
 * choisie dans ce projet) et de nombreuses caractérisations des cographes.
 * Vous pouvez si vous le souhaiter en formaliser une.
 * Par exemple, l'une des caractérisation est l'absence de corde de longueur
 * 3. Une corde de longueur 3 est un sous-graphe isomorphe à celui que nous
 * venons de voir : il comporte quatre noeuds et seulement trois arêtes qui
 * les relient tous ensemble, mais il ne comporte aucune arête
 * supplémentaire, qui donnerait naissance à un chemin plus court entre
 * deux noeuds qui ne se suivent pas.
 *)
