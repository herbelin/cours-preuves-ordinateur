TP2 : Mathématiques élémentaires en Coq
=======================================

M1 Informatique - Preuves Assistées par Ordinateur

Pierre Letouzey (d'après A. Miquel)

### Tactiques du jour ###

En Coq, une définition `d` peut être remplacé par son corps à l'aide
de la tactique `unfold d` (en anglais, unfold signifie déplier).
Attention `unfold` ne déplie une définition que dans le but. Utiliser
une clause `in H` (ou `in H1, H2` ou `in *`) pour déplier dans les
hypothèses.

L'égalité se traite à l'aide des tactiques `reflexivity`, `symmetry`,
`transitivity ...` (donner le terme intermédiaire) et `rewrite ...`
(donner l'égalité à utiliser comme règle de réécriture, par exemple un
nom d'hypothèse ou de lemme) ou `rewrite <- ...` (réécriture de droite
à gauche). 

### Exercice 1 : Relations d'ordre ###

Considérons un type `E:Type` muni d'une relation binaire `R`
dont on suppose qu'elle satisfait aux axiomes des relations d'ordre:

```coq
Parameter E : Type.
Parameter R : E -> E -> Prop.
Axiom refl : forall x : E, R x x.
Axiom trans : forall x y z : E, R x y -> R y z -> R x z.
Axiom antisym : forall x y : E, R x y -> R y x -> x = y.
```

On définit les notions de plus petit élément et d'élément minimal de la façon suivante:

```coq
Definition smallest (x0 : E) := forall x : E, R x0 x.
Definition minimal (x0 : E) := forall x : E, R x x0 -> x = x0.
```

Quels sont les types des objets `smallest` et `minimal` (vérifier
votre réponse avec la commande `Check`) ?

Énoncer en Coq puis démontrer les lemmes suivants:

  1. Si `R` admet un plus petit élément, alors celui-ci est unique.
  2. Le plus petit élément, s'il existe, est un élément minimal.
  3. Si `R` admet un plus petit élément, alors il n'y a pas d'autre élément minimal que celui-ci.

### Exercice 2 : Logique classique ###

Quelques tactiques supplémentaires qui peuvent être utiles :
- `exfalso` remplace le but par `False` (similaire à la règle `⊥E` de la déduction naturelle) ;
- `contradiction` conclue n'importe quel but si le contexte contient `A` et `~A` ;
- `assert (H : ...)` introduit une proposition intermédiaire à prouver (une coupure).

Dans cet exercice, on suppose la règle de raisonnement par
l'absurde, que l'on déclare en Coq de la manière suivante :

```coq
Axiom not_not_elim : forall A : Prop, ~~A -> A.
```

  1. Montrer en Coq que cet axiome entraîne le tiers-exclus : `forall A : Prop, A \/ ~ A`.

On se propose maintenant de formaliser le paradoxe des buveurs, dû à Smullyan:

> Dans toute pièce non vide on peut trouver une personne ayant la
> propriété suivante: Si cette personne boit, alors tout le monde
> dans la pièce boit.

  2. Déclarer en Coq les divers éléments du problème (en s'inspirant de l'exercice précédent).
  
  3. Énoncer le paradoxe et en effectuer la preuve (laquelle repose sur le tiers-exclus).

### Exercice 3 : Sous-ensembles ###

Étant donné un type `E:Type` dans Coq, on s'intéresse aux
sous-ensembles de `E`, qu'il est commode de représenter par des
prédicats unaires sur `E`, c'est-à-dire par des objets de type
`E->Prop`.
  
  1. Définir en Coq un prédicat binaire `subset : (E->Prop)->(E->Prop)->Prop`
     exprimant l'inclusion entre deux sous-ensembles. Montrer que cette
     relation est reflexive et transitive. Est-elle antisymétrique?

  2. Définir en Coq un prédicat binaire `eq : (E->Prop)->(E->Prop)->Prop`
     exprimant l'égalité extensionnelle de deux ensembles.  Montrer
     qu'il s'agit d'une relation d'équivalence.
     Montrer que `subset` est antisymétrique vis-à-vis de `eq`.

  3. Définir en Coq les opérateurs d'union et d'intersection
     binaire sur les sous-ensembles de `E`.  Montrer que ces deux
     opérations sont associatives, commutatives, idempotentes, et
     distributives l'une par rapport à l'autre.
