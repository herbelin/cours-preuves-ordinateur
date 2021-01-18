TP6 : Définitions inductives de prédicats et analyse par cas
============================================================

M1 Informatique - Preuves Assistées par Ordinateur

Pierre Letouzey (d'après A. Miquel)

## L'énigme de MU (Hofstadter 1986) ##

Sur l'alphabet à trois lettres `{M;I;U}`, on considère le
langage `L` défini à partir de l'axiome et des règles suivantes:

  - Axiome: `MI ∈ L`
  - Règle 1: Si `xI ∈ L`, alors `xIU ∈ L` (avec `x ∈ {M;I;U}*`)
  - Règle 2: Si `Mx ∈ L`, alors `Mxx ∈ L` (avec `x ∈ {M;I;U}*`)
  - Règle 3: Si `xIIIy ∈ L`, alors `xUy ∈ L` (avec `x,y ∈ {M;I;U}*`)
  - Règle 4: Si `xUUy ∈ L`, alors `xy ∈ L` (avec `x,y ∈ {M;I;U}*`)

La question est alors de savoir si le mot `MU` fait partie du langage
`L` ou non.

## Modélisation en Coq ##

On se propose de formaliser ce problème en Coq. Pour cela, on
introduit les définitions suivantes :
```
Require Import List.
Import ListNotations.

Inductive alpha := M | I | U.

Definition word := list alpha.

Inductive lang : word -> Prop :=
| axiom : lang [M;I]
| rule1 x : lang (x ++ [I]) -> lang (x ++ [I;U])
| rule2 x : lang ([M] ++ x) -> lang ([M] ++ x ++ x)
| rule3 x y : lang (x ++ [I;I;I] ++ y) -> lang (x ++ [U] ++ y)
| rule4 x y : lang (x ++ [U;U] ++ y) -> lang (x ++ y).
```

Un mot sur l'alphabet `{M;U;I}` est donc représenté en Coq par une
liste de lettres. Par exemple, le mot `MI` correspond ainsi à la liste
`[M;I]`, cette syntaxe étant un raccourci pour `M::I::nil`, lui même
correspondant à `cons M (cons I nil)`. Et la concaténation de
mots est ici la concaténation de listes `++` (nommée `app` en
Coq). Pour plus d'explications sur le type des listes, revoir le TD6.
Enfin, l'appartenance au langage `L` est modélisé en Coq
sous la forme du prédicat `lang : word->Prop`.

 1. Comme échauffement, montrer en Coq que tous les mots du langage `L`
    commencent par la lettre `M`. Attention, il y a au moins deux
    formulations Coq possibles possibles pour cet énoncé (en utilisant
    `exists` ou `match`), prouver la plus facile, puis l'autre par
    équivalence.
    
## Arithmétique ternaire ##

On cherche maintenant à établir que tous les mots du langage ont un
nombre d'occurrences de la lettre `I` qui n'est pas un multiple de
trois. Pour cela, on formalise d'abord l'arithmétique modulo 3 en
Coq à partir de la définition inductive suivante:

```
Inductive Z3 := Z0 | Z1 | Z2.
```
 
  1. Définir les fonctions `succ:Z3->Z3` et
    `add:Z3->Z3->Z3` qui implémentent le successeur et
    l'addition modulo 3. Ajouter une notation pour `add` via
    `Infix "+" := add`.
  2. Montrer que `add` est commutative,
     associative, et qu'elle admet `Z0` pour élément neutre.
  3. Montrer que pour tout `z:Z3`, on a `z<>Z0 -> z+z <> Z0`
  4. Définir une fonction `occurI3 : word -> Z3` qui
    à chaque mot `w:word` associe le nombre d'occurrences de la
    lettre `I` modulo 3 dans `w`.
  5. Montrer que pour tous mots `v` et `w` on a 
    `occurI3 (v ++ w) = (occurI3 v)+(occurI3 w)`.
  6. Montrer que pour tout mot `w` dans le langage `L`, on a
     `occurI3 w <> Z0`.
  7. En déduire que `~(lang [M;U])`.

**Tactiques utiles**: `induction`, `inversion`, `destruct`, `discriminate`, `injection`.


