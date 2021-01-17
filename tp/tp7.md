Le Damier de Cachan
===================

M1 Informatique - Preuves Assistées par Ordinateur

Pierre Letouzey (d'après C. Paulin)

## Le Damier ##

On considère un damier de dimensions 3x3. Sur chaque case se trouve un
jeton bicolore : blanc sur une face et noir sur l'autre (une seule des
deux faces est visible). À chaque étape il est possible de retourner
une rangée ou une colonne du damier. On cherche ici à examiner les
configurations qu'il est possible d'atteindre à partir d'une
configuration donnée. Voici par exemple deux configurations possibles
(où `Wh` marque une case blanche et `Bl` une case noire) :

```
start =
 Wh Wh Bl
 Bl Wh Wh
 Bl Bl Bl

target =
 Bl Bl Bl
 Wh Bl Wh
 Bl Bl Wh
```

Montrer informellement qu'on peut bien aller de la configuration
`start` à la configuration `target`.

## Modélisation du damier ##

Il est conseillé d'utiliser la commande `Set Implicit Arguments` pour
éviter de taper certains arguments de type dans ce qui suit.

 1. Définir un type `color` à deux valeurs `Bl` et `Wh`.
 2. Définir une fonction `inv_color : color -> color` qui échange les deux couleurs.
 3. Ouvrir une section avec la commande `Section Triple`, et
    déclarer une variable locale `X : Type` à l'intérieur de cette section à
    l'aide de la commande `Variable X : Type`.
 4. Définir un type `triple : Type` des triplets `(x, y, z)` d'éléments de `X`.
 5. Définir une fonction `triple_x : X -> triple` qui à tout
    `x : X` associe le triplet `(x, x, x)`.
 6. Définir une fonction `triple_map : (X -> X) -> triple -> triple` qui à une fonction `f` et à
    un triplet `(x, y, z)` associe le triplet `(f (x), f (y), f (z))`.
 7. Définir un type des positions `pos` à trois valeurs `A`, `B` et `C`.
 8. Définir une fonction `triple_proj : pos -> triple -> X` qui extrait une composante d'un
    triplet donnée par sa position.
 9. Définir une fonction `triple_map_select : (X -> X) -> pos -> triple -> triple` qui
    applique une fonction à une composante d'un triplet donnée par sa position.
 10. Fermer la section avec la commande `End Triple`. Quel est
     maintenant le type des objets définis dans la section ?
 11. Définir le type `board` des configurations comme le type des triplets de triplets de couleurs,
     ainsi qu'un objet `white_board` qui modélise la configuration blanche partout.
 12. Définir en Coq les deux configurations `start` et `target`
     données en préambule.

## Manipulation des configurations ##

 1. Définir la fonction `board_proj : board -> pos -> pos -> color` qui extrait le contenu d'une
      case d'une configuration donnée.
 2. Définir les fonctions `inv_row, inv_col : board -> pos -> board` qui inversent respectivement
      une rangée et une colonne d'une configuration donnée.
 3. Définir une relation `move : board -> board -> Prop`
      telle que `move b1 b2` exprime que `b2`
      s'obtient à partir de `b1` en inversant une rangée ou une colonne.
 4. Montrer que cette relation `move` est symétrique.
 5. Définir inductivement la relation `moves : board -> board -> Prop`
    à partir des deux règles suivantes :
      - Pour tout `b`, on a `moves b b`
      - Si `moves b1 b2` et `move b2 b3` alors `moves b1 b3` (pour tout `b1`, `b2`, `b3`)
 6. Montrer que la relation `moves` est réflexive, symétrique et transitive.
 7. Vérifier que `moves start target`.
 8. Peut-on aisément montrer que `~(moves white_board start)`
    par une preuve directe ?

## L'invariant de normalisation ##

 1. Définir une fonction `force_white : board -> board` qui inverse certaines rangées et/ou
    certaines colonnes d'une configuration donnée de manière à ce que la première rangée et
    la première colonne de la configuration retournée par cette fonction soient entièrement
    blanches. Vérifier que pour toute configuration `b` on a `moves b (force_white b)`.
 2. Montrer que `move b1 b2 -> force_white b1 = force_white b2`.
 3. Montrer que `moves b1 b2 <-> force_white b1 = force_white b2`.
 4. En déduire que `~(moves white_board start)`, ainsi qu'une preuve
    simplifiée de `moves start target`.

## Décidabilité de la relation moves ##

En Coq, on exprime qu'une relation `R` (définie sur un type de données `X`) est décidable par la
proposition :
```
forall x y : X, {R x y}+{~R x y}
```
où `{...}+{...}` désigne la disjonction calculatoire (définie dans
`Type`). Notez que cette forme de tiers-exclu calculatoire ne peut pas être déduite du
tiers-exclu sur les propositions.

 1. Montrer que l'égalité `x = y` est décidable sur le type `color`.
 2. Montrer que si l'égalité est décidable sur un type `X`, alors elle est décidable sur `triple X`.
    En déduire qu'elle est décidable sur le type `board`.
 3. À l'aide de tout ce qui précède, montrer que la relation `moves` est décidable.
 4. Extraire le programme OCaml correspondant et tester.
