TD6 : Les listes en Coq
=======================

M1 Informatique - Preuves Assistées par Ordinateur

Pierre Letouzey (d'après A. Miquel)

## Définition des listes en Coq ##

En Coq, on peut charger via les commandes suivantes la définition
standard des listes, leurs notations, ainsi que des fonctions
usuelles sur les listes et leur propriétés:
```
Require Import List.
Import ListNotations.
```
Dans la bibliothèque Coq, ces *listes polymorphes* sont définies à l'aide de
la définition inductive suivante (ne pas la retaper):
```
Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.
```
Cette déclaration ajoute dans l'environnement courant un constructeur
de type `list : Type->Type`, qui à chaque type `A:Type` associe le type
correspondant `(list A) : Type` des listes à éléments dans `A`.
Cette déclaration fournit également deux constructeurs polymorphes:
```
nil   :  forall A : Type, list A
cons  :  forall A : Type, A -> list A -> list A
```
ainsi qu'un principe de récurrence `list_ind` permettant de raisonner
sur les listes (par exemple via la tactique `induction ...`). Essayer de
formuler ce principe de récurrence sur les listes, puis vérifier la
réponse avec `Check list_ind`.

*Nota*: en Coq, la quantification universelle
`forall x : T, U(x)` introduit un *type fonctionnel*
qui généralise le type flèche `T -> U`, et qu'on appelle
*produit dépendant*.

#### Arguments implicites ####

Normalement, des types de la forme `forall A : Type,...` pour
`nil` et `cons` font donc que ces derniers attendent un premier argument
correspondant à ce `A`, ce qui donnerait par exemple pour une liste d'entier
`(cons nat 3 (nil nat)) : list nat`. Heureusement, il est possible
en Coq de rendre *implicite* ces arguments de type, et donc d'écrire
seulement `cons 3 nil`, tout en laissant Coq *inférer*
en interne les arguments non écrits. La bibliothèque standard de Coq
fournit `nil` et `cons` qui sont déjà en mode implicite, idem pour
toutes les fonctions standards sur les listes. Pour vos propres définitions,
vous pouvez activer globalement ce mode implicite via la commande
suivante en tête de votre fichier:
```
Set Implicit Arguments.
```
Sinon, une autre approche possible est d'utiliser la syntaxe
`{A:Type}` au lieu de `(A:Type)` pour les arguments de fonctions que
l'on souhaite rendre implicites (cf. la définition de `app` ci-dessous).

#### Notations ####

En plus des implicites, Coq fournit également un système de notations
permettant d'alléger l'écriture. Pour les listes, des notations
similaires à OCaml sont disponibles (cf. la commande `Import ListNotations`):

  * `[]` pour `nil`
  * `x :: l` pour `cons x l`
  * `[x;y;z]` pour `x :: y :: z :: nil`, qui est lui-même
    `cons x (cons y (cons z nil))`

## Concaténation de listes ##

L'opération (polymorphe) de concaténation de listes est définie en Coq par:
```
Fixpoint app {A:Type} (l1 l2 : list A) : list A :=
 match l1 with
 | [] => l2
 | x :: tl => x :: (app tl l2)
 end.
```
Là encore, ne pas retaper cette définition, mais utiliser plutôt
la version fournie par la bibliothèque standard, qui vient avec la
notation `l1 ++ l2` pour `app l1 l2`.

  1. Quel est le type de `app` ?
  2. Montrer que pour toute liste `l`, on a `nil ++ l = l` ainsi
     que `l ++ nil = l`.
     Laquelle de ces deux propositions correspond à une égalité
     définitionnelle?
  3. Montrer que l'opération de concaténation est associative.

## Longueur ##

  1. Définir une fonction `length : forall {A:Type}, list A -> nat`
     telle que `length l` retourne la longueur de la liste `l`.
     Vérifier que vous avez bien retrouvé la définition standard de
     `length` fournie par le système.
  2. Montrer que `length (l1 ++ l2) = length l1 + length l2`
     pour toutes listes `l1` et `l2`.

## Retournement ##

  1. Définir une fonction `rev : forall {A}, list A -> list A`
    renversant la liste qu'elle reçoit. On pourra pour
    cela introduire une fonction auxiliaire
    `rev_append : forall {A}, list A -> list A -> list A`
    qui renverse la première liste reçue et la concatène
    avec la seconde.
  2. Montrer que `length (rev l) = length l`.
  3. Montrer que `rev (l1 ++ l2) = (rev l2) ++ (rev l1)`.

*Remarque*: Pour résoudre ces questions, il est utile d'énoncer
des lemmes intermédiaires!
