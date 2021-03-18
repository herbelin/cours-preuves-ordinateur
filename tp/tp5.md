TP5 : Définitions inductives de prédicats
=========================================

M1 Informatique - Preuves Assistées par Ordinateur

Pierre Letouzey (d'après A. Miquel)


### Clôture réflexive-transitive, version 1 ###

Commençons par considérer un type de données particulier:

```coq
Parameter T:Type.
```

Sur ce type `T`, on cherche à définir la clôture
réflexive-transitive d'une relation `R:T->T->Prop`, à savoir la plus
petite relation réflexive et transitive `R*` contenant `R`. Il est
naturel de définir inductivement cette relation à partir des trois
règles suivantes:

  * Inclusion : Si `R(x,y)` alors `R*(x,y)`
  * Réflexivité : On a toujours `R*(x,x)`
  * Transitivité : Si `R*(x,y)` et `R*(y,z)` alors `R*(x,z)`

  1. Comment exprime-t-on ensuite le fait que `R*` est la plus petite
     relation satisfaisant ces trois propriétés ?

En Coq, cette définition inductive s'effectue de la manière suivante:

```coq
Inductive clos1 (R : T -> T -> Prop) : T -> T -> Prop :=
| cl1_base : forall x y, R x y -> clos1 R x y
| cl1_refl : forall x, clos1 R x x
| cl1_trans : forall x y z, clos1 R x y -> clos1 R y z -> clos1 R x z.
```

La définition Coq ci-dessus, qui est paramétrée par la relation `R`,
engendre en réalité:

  * un *transformateur de relation* `clos1 : (T -> T -> Prop) -> (T -> T -> Prop)`
    qui à chaque relation binaire `R` associe sa clôture
    réflexive-transitive `clos1 R`
  * trois constantes `cl1_base`, `cl1_refl` et `cl1_trans`
    correspondant aux trois règles de constructions de `clos1 R`
    (on parle aussi de *constructeurs* pour ces constantes).
  * un principe d'induction `clos1_ind` exprimant que `clos1 R`
    est bien la plus petite relation réflexive et transitive contenant `R`.

  2. Comparer le principe d'induction `clos1_ind` obtenu avec celui formulé à
     la question précédente.

  3. Montrer que si `R` est symétrique, alors `clos1 R` l'est aussi.

     *Remarque* : comme toujours on peut prouver par récurrence une propriété
     en utilisant la tactique `induction` qu'on appelle sur un élément d'un
     type inductif.
     Dans les TP précédents, on faisait donc des récurrences sur des entiers
     naturels ou des listes. Dans ce TP, on fait des récurrences sur des
     propositions (`induction H`).

  4. Montrer que l'opération de clôture réflexive-transitive est idempotente:
     `clos1 (clos1 R) x y -> clos1 R x y` pour tous `x y:T`.

### Clôture réflexive-transitive, version 2 ###
  
Dans les démonstrations cependant, il est souvent plus commode
de définir la clôture réflexive-transitive d'une manière un peu
différente, à savoir comme la relation `R*` engendrée par les
deux règles suivantes:

  - Réflexivité : `R*(x,x)`
  - Transitivité-Inclusion : si `R*(x,y)` et `R(y,z)` alors `R*(x,z)`

Notez l'usage de `R` (et non `R*`) au milieu de la règle précédente.
Cette définition alternative se modélise en Coq au moyen de la
définition inductive suivante:

```coq
Inductive clos2 (R : T -> T -> Prop) : T -> T -> Prop :=
| cl2_refl : forall x, clos2 R x x
| cl2_next : forall x y z, clos2 R x y -> R y z -> clos2 R x z.
```

Nous allons montrer ici l'équivalence des deux définitions `clos1`
et `clos2`, en suivant les étapes intermédiaires suivantes:

  1. Montrer que `clos2 R x y` entraîne `clos1 R x y` (pour tous `x y:T`).
  2. Montrer que `R x y` entraîne `clos2 R x y` (pour tous `x y:T`).
  3. Montrer que `clos2 R` est une relation transitive.
  4. En déduire que `clos1 R x y` entraîne `clos2 R x y` (pour tous `x y:T`).

### Clôture réflexive-transitive, version 3 ###

En Coq, on peut également profiter de la récursivité pour définir des
prédicats.

  1. Définir la relation identité `id:T->T->Prop` ainsi que
     l'opérateur de composition de relations
     `comp:(T->T->Prop)->(T->T->Prop)->(T->T->Prop`.
  2. Définir une fonction
     `puiss:(T->T->Prop)->nat->(T->T->Prop)`
    telle que `puiss R n` calcule la puissance n-ième de
    la relation (par l'opération de composition).

Une troisième définition de la clôture réflexive-transitive d'une
relation `R` est alors donnée par la réunion des puissances successives de
`R`, c'est-à-dire par:

```coq
Definition clos3 (R : T -> T -> Prop) (x y : T) := exists n, puiss R n x y.
```

  3. Montrer que cette définition est équivalente aux deux
     précédentes `clos1` et `clos2`.
