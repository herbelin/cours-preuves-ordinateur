TP3 : Les entiers naturels en Coq
=================================

M1 Informatique - Preuves Assistées par Ordinateur 

Pierre Letouzey (d'après A. Miquel)

### Le type inductif des entiers ###

En Coq, l'introduction d'un nouveau type de données s'effectue à
l'aide d'un mécanisme de *définition inductive* qui ressemble beaucoup
à la définition d'un type concret en OCaml.  Ainsi, le type `nat` des
entiers naturels est introduit dans la bibliothèque standard de Coq
(cf. fichier
[Init/Datatypes.v](https://coq.inria.fr/stdlib/Coq.Init.Datatypes.html))
à l'aide de la définition inductive suivante:

```coq
Inductive nat : Set :=
| O : nat
| S : nat -> nat.
```

Cette définition ajoute à l'environnement courant trois nouvelles
constantes:
  - le type `nat : Set` (sachant que `Set` est le type des petits types de données);
  - le constructeur `O : nat`
  - le constructeur `S : nat -> nat`
Attention, le constructeur du zéro s'appelle `O` à la base (la lettre O), même si le système accepte ensuite aussi des notations à bases de chiffres : `0` pour `O`, `1` pour `(S O)`, `2` pour `(S (S O))`, etc.

La définition inductive ci-dessus engendre automatiquement un certain nombre de principes d'induction, dont le plus utilisé en pratique est le schéma de récurrence :

```coq
nat_ind :
  forall P : nat -> Prop,
    P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
```

utilisé en interne par la tactique `induction` (preuve par récurrence).

Autres tactiques utiles :
- `simpl` (simplifie le but lorsqu'il peut être réduit par calcul)
- `rewrite H` (réécrit avec un lemme ou une hypothèse `H` dont la conclusion est une égalité)
- `discriminate` (permet de conclure une preuve si elle contient une hypothèse d'égalité entre deux constructeurs différents, par exemple `1 = 0`, c'est-à-dire `S O = O`)
- `injection H as H` (permet de transformer une hypothèse `H : S x = S y` en `H : x = y`)
- `f_equal` (permet de transformer un but `f x = f y` en `x = y`).

Une différence importante à noter entre `f_equal` et `injection`:
`f_equal` fonctionne avec n'importe quelle fonction (on peut toujours
prouver que `f x = f y` si on arrive à montrer que `x = y`, quelle que
soit la fonction `f`) ; en revanche, `injection` ne fonctionne qu'avec
des constructeurs de type inductifs (comme `S`) car on sait que ces
derniers sont *injectifs* (d'où le nom de la tactique).

### Exercice 1 : Addition ###

En Coq, l'addition est définie au moyen de la construction `Fixpoint`, qui est l'équivalent du `let rec` d'OCaml (cf [Init/Nat.v](https://coq.inria.fr/stdlib/Coq.Init.Nat.html)) :

```coq
Fixpoint add (n m:nat) : nat :=
  match n with
   | O => m
   | S p => S (add p m)
  end.
```

Il est important de noter que les appels récursifs se font ici sur un premier argument `n` de plus en plus petit. Il s'agit en fait de *décroissance structurelle*. Coq refuse les définitions pour lesquelles il n'est pas en mesure de vérifier cette propriété, et qui risquent donc de ne pas forcément terminer.

Le système utilise la notation `n + m` pour désigner le terme `Nat.add n m`.

Attention: pour les définitions *non-récursives* on continuera à
utiliser la commande `Definition` (vue au TP précédent, et avec
laquelle on peut utiliser `unfold`) plutôt que `Fixpoint` (qui est
spécifiquement dédié aux fonctions récursives).

Montrer les lemmes suivants sur l'addition (égalités de base, puis associativité et commutativité). Déterminer quelles sont les égalités définitionnelles, c'est-à-dire prouvable par calcul et reflexivité (tactiques `simpl` et `reflexivity`). Pour les autres égalités, procédez par récurrence sur `n`, à l'aide de la tactique `induction`.

```coq
Lemma add_0_l : forall n, 0 + n = n.
Lemma add_succ_l : forall n m, S n + m = S (n + m).
Lemma add_0_r : forall n, n + 0 = n.
Lemma add_succ_r : forall n m, n + S m = S (n + m).
Lemma add_assoc : forall n m p, (n + m) + p = n + (m + p).
Lemma add_comm : forall n m, n + m = m + n.
```

### Exercice 2 : Multiplication ###

En Coq, la multiplication est définie par

```coq
Fixpoint mul (n m:nat) : nat :=
  match n with
   | O => O
   | S p => m + mul p m
  end.
```

Le système utilise ensuite le sucre syntaxique `n * m` pour désigner le terme `mul n m`.

Comme pour l'addition, montrer les lemmes suivants:

```coq
Lemma mul_0_l : forall n, 0 * n = 0.
Lemma mul_succ_l : forall n m, S n * m = m + n * m.
Lemma mul_0_r : forall n, n * 0 = 0.
Lemma mul_succ_r : forall n m, n * S m = n + n * m.
Lemma mul_distr : forall n m p, (n + m) * p = n * p + m * p.
Lemma mul_assoc : forall n m p, (n * m) * p = n * (m * p).
Lemma mul_comm : forall n m, n * m = m * n.
```

### Exercice 3 : Un ordre sur les entiers ###

On peut définir l'ordre large sur les entiers ainsi:

```coq
Definition le (n m : nat) := exists p, n + p = m.
Infix "<=" := le.
```

Notez que cette définition n'est pas celle de la libraire standard de Coq (cf. [Init/Peano.v](https://coq.inria.fr/stdlib/Coq.Init.Peano.html)), basée elle sur un prédicat inductif. Mais vous
pourrez montrer par la suite que ces deux définitions sont bien équivalentes.

Montrer que notre prédicat `le` est bien une relation d'ordre:

```coq
Lemma le_refl : forall n, n <= n.
Lemma le_trans : forall n m p, n <= m -> m <= p -> n <= p.
Lemma le_antisym : forall n m, n <= m -> m <= n -> n = m.
```

### Epilogue ###

Au lancement de Coq, la définition des entiers `nat` est directement
disponible, ainsi que les opérations correspondante, en version
*qualifiées*, par exemple `Nat.add` qui correspond au signe `+`. Il
existe aussi d'anciens noms pour ces opérations : `plus`, `mult`, mais
ils sont considérés comme obsolètes. Les preuves concernant les
entiers et leurs opérations ne sont pas toutes disponibles
initialement, elles sont à charger via `Require Import Arith`. Ceci
donnera accès par exemple à `Nat.add_assoc` et à la plupart des lemmes
de ce TP. La commande `Search` permettra d'en savoir plus sur les
résultats disponibles. Enfin, d'autres tactiques plus puissantes
aideront grandement par la suite, par exemple `auto`, `lia` et
`ring`.
