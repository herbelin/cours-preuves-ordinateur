# Projet #

Ce projet porte sur les expressions régulières ([regexps][]) et les [dérivées][] de Brzozowski

[regexps]: https://fr.wikipedia.org/wiki/Expression_rationnelle
[dérivées]: https://fr.wikipedia.org/wiki/D%C3%A9riv%C3%A9e_de_Brzozowski

Ce projet peut se faire par binôme d'au plus deux étudiants.

Les dates de soutenance seront fixés ultérieurement.

**Attention** : faire l'intégralité des preuves de ce projet serait vraiment
**très** long, mais il forme une unité que nous avons tenu à vous fournir malgré
tout. Par contre plusieurs fichiers sont **optionnels**. La partie obligatoire
de ce projet consiste en :

  - Les deux fichiers de la partie 1 : [Languages.v](Languages.v) et [Regular.v](Regular.v). **À rendre pour le 5 mai.**
  
  - Deux fichiers au choix dans la partie 2 parmi [ListUtils.v](ListUtils.v), [Finiteness.v](Finiteness.v), [Explore.v](Explore.v) et [EquivDec.v](EquivDec.v). **À rendre pour le jour des soutenances, qui pourraient avoir lieu à partir du 22 mai.**

Pour chacun de ces fichiers, le travail consiste à remplacer autant que possible
les `Admitted` par des preuves Coq sans axiomes. Il se peut que certaines preuves
soient déjà fournies. Vous pouvez ajouter librement des lemmes intermédiaires
ou toutes commandes facilitant vos preuves (p.ex. des `Hint`). Par contre ne modifiez
pas les enoncés et les définitions fournies (`Definition`, `Fixpoint`, ...) sans
notre autorisation.

Les fichiers optionnels [RegOrder.v](RegOrder.v) et [Similar.v](Similar.v) sont à lire
malgré tout, vu que les notions qui y sont définies et les résultats qui y sont enoncés
vont resservir dans la suite. Mais il ne vous est pas demandé de prouver les `Admitted`
qui sont dans ces fichiers. Ceci dit, ce n'est pas interdit non plus...

Les preuves peuvent être abordées dans l'ordre de votre choix. Simplement, avant
de travailler sur un fichier il faut juste avoir compilé ceux qui précèdent,
tout simplement via `make` (ou à défaut utiliser `coqc` sur chacun des fichiers,
dans le bon ordre, mais ce n'est pas recommandé).

A tout moment, s'il vous semble qu'il vous manque de l'outillage technique pour
avancer dans une preuve, ou si certaines notions restent obscures même
après consultation de la documention de Coq, ne pas hésiter à nous contacter.

## Partie 1 : Définitions des notions et premières propriétés

  - [Languages.v](Languages.v) : notion générale de langages sur un alphabet donné via des prédicats Coq
  
  - [Regular.v](Regular.v) : structure de regexp, langage d'une regexp, dérivée d'une regexp, etc.

Pour donner un ordre de grandeur, toutes les preuves de cette partie
sont faisables en une quinzaine de lignes au plus et souvent beaucoup
moins (dans un style assez compact il est vrai).

## Partie 2 : Finitude des dérivées de Brzozowski

  Dans cette partie, il vous est demander de traiter **deux** fichiers parmi les non-optionnels ci-dessous:

  - [ListUtils.v](ListUtils.v) : quelques notions complémentaires sur les listes, par exemple une equivalence, des inclusions, etc.
  
  - [RegOrder.v](RegOrder.v) : **optionnel**, comparaison et test d'egalité sur les regexps, ensembles finis de regexp, compléments sur les listes de regexps.

  - [Similar.v](Similar.v) : **optionnel** une relation `sim` (noté `=~=`) de similitude entre regexp, qui approxime l'equivalence `===`. Fonction `canon` donnant en pratique la forme canonique d'une regexp vis-à-vis de `sim`.

  - [Finiteness.v](Finiteness.v) (attention, particulièrement difficile) : théorème de Brzozowski affirmant qu'une regexp a un nombre fini de dérivées en forme canonique. On donne ici une liste contenant au moins ces dérivées (mais en pratique beaucoup plus).

  - [Explore.v](Explore.v) : recherche efficace des dérivées d'une regexp, par des techniques de parcours de graphe. La borne trouvée dans le fichier précédent permet de prouver l'arrêt de cette recherche.

  - [EquivDec.v](EquivDec.v) : à partir de ce qui précède, on peut maintenant fournir un algorithme testant l'équivalence `===` de deux regexps, et du coup donnant les dérivées distinctes vis-à-vis de `===`. 


## Quelques tactiques automatiques utiles ##

- [`tauto`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.tauto)
  pour résoudre les tautologies en logique intuitionniste
  propositionnelle (i.e. par succession de `apply` sans instantiation
  de quantificateurs).
- [`firstorder`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.firstorder)
  peut parfois résoudre des buts nécessitant l'instantiation
  d'hypothèses quantifiées du contexte.
- [`btauto`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.btauto)
  résout des égalités booléennes tautologiques (requiert `Require Import Btauto`).
- [`congruence`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.congruence)
  résout le but par raisonnement équationnel (utile si le contexte
  contient, par exemple `H0: x = 0` et `H1: x = 1`).
- [`lia`](https://coq.inria.fr/refman/addendum/micromega.html#coq:tacn.lia)
  résout des buts arithmétiques (requiert `Require Import Lia`).
- [`intuition`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.intuition)
  à utiliser en combinaison avec une tactique qui prouve les buts
  restant comme `btauto` ou `congruence` (i.e. `intuition btauto`,
  `intuition congruence`, `intuition lia`, etc.)
- [`eauto`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.eauto)
  permet d'aller plus loin que
  [`auto`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.auto)
  dans ce que Coq tente de deviner, comme par exemple le point
  intermédiaire d'une transitivité.  Cette tactique peut être à
  utiliser en combinaison avec d'autres tactiques dites
  "existentielles" comme
  [`eapply`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacv.eapply)
  ou
  [`eexists`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacv.eexists),
  avec lesquelles Coq pose des `?` aux endroits qui lui manque, en
  attendant qu'un `eauto` les devine.
- `f_equiv` est la tactique analogue à `f_equal` utilisable avec une equivalence
  au lieu de l'égalité standard de Coq. Par exemple, si l'on utilise `f_equiv`
  sur le but `Or r s =~= Or r' s'`, il nous restera à prouver `r =~= r'`
  et `s =~= s'`. Cela ne marche évidemment qu'avec les fonctions connues comme
  compatibles pour l'equivalence en question (cf. les commandes `Instance` fournies).

## Quelques lemmes utiles ##

### sur les booléens ###

- `eq_true_iff_eq : forall b1 b2 : bool, b1 = true <-> b2 = true -> b1 = b2`
- `orb_true_iff : forall b1 b2 : bool, b1 || b2 = true <-> b1 = true \/ b2 = true`
- `andb_true_iff : forall b1 b2 : bool, b1 && b2 = true <-> b1 = true /\ b2 = true`
- `List.existsb_exists : forall (A : Type) (f : A -> bool) (l : list A),
  List.existsb f l = true <-> (exists x : A, List.In x l /\ f x = true)`

### sur les listes ###

```
List.app_nil_r : forall (A : Type) (l : list A), l ++ [] = l
```

De nombreux autres lemmes sont disponibles, vous pouvez les chercher
avec la commande `Search`. Par exemple, `Search "++" List.In`.

## Quelques conseils par fichiers : Langages.v ##

### Prouver des égalités ###

L'égalité `==` sur les langages est définie comme une équivalence,
vous pouvez donc généralement commencer vos preuves de `==` par `split`,
à moins qu'il soit possible de réécrire une partie avec une égalité
déjà établie.

### Simplifier des expressions ###

Forcer à simplifier quand des langages sont appliqués à des mots:
`simpl` ne marche pas, vous pouvez utiliser la tactique
[`red`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.red). Comme
`simpl`, `red` accepte une clause `in` qui permet de réduire dans une
hypothèse, voire partout avec `in *`.

### Récurrences ###

Quelques preuves nécessitent des récurrences. Dans ce cas, il est
utile de généraliser le plus possible le résultat à prouver par
récurrence, à l'aide de la tactique
[`revert`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.revert).

## Quelques conseils par fichiers : Regular.v ##

On utilise ici plusieurs fonctions booléennes, telle que
 - `Letter.eqb` (le test d'égalité entre deux lettres)
 - `is_nullable` (le test detectant si une regexp accepte le mot vide)

Lors des preuves ultérieures, face à un `if f arg ...` où `f` est une de
ces fonctions booléennes, on utilise normalement `destruct (f arg) eqn:H`
pour raisonner par cas. L'option `eqn:H` permet d'enregistrer dans une
hypothèse `H` l'équation `f arg = true` ou bien `f arg = false`, afin de
pouvoir savoir dans quel cas on est. Mieux encore, si vous disposez
d'un lemme décrivant `f` via le prédicat `reflect`, nommons-le `f_spec`,
alors vous pouvez directement utiliser `case f_spec` (sans donner les
arguments), et les deux cas proposeront automatiquement des hypothèses
appropriées.

Par exemple, pour `Letter.eqb`, un `case LetterB.eqb_spec` va briser un
`if Letter.eqb .. .. then .. else ..`, et proposer soit une hypothèse
`.. = ..`, soit une hypothèse `.. <> ..`, selon le cas.

Et pour `is_nullable`, un `case nullable_spec` brisera un
`if is_nullable ..`, et proposera soit une hypothèse `Lang .. []`, soit
une hypothèse `~Lang .. []`.

## Quelques conseils par fichiers : Explore.v ##

Les ensembles finis `REs.t` que l'on manipule dans `Explore.v` sont une instance de la bibliothèque [MSets](https://coq.inria.fr/distrib/current/stdlib/Coq.MSets.MSetInterface.html), qui est proche de la bibliothèque `Set` d'OCaml. Voici quelques conseils les concernant :

 - On peut retrouver la liste des opérations ensemblistes disponibles via `Print Module REs`.
   Les principales opérations sont `REs.add`, `REs.union`, `REs.elements`, `REs.cardinal`.
   
 - Chaque opération vient avec un lemme donnant sa spécification principale, par exemple `REs.add_spec` pour `REs.add`.
 
 - Pour `REs.elements`, la conversion d'ensemble en liste, utiliser plutôt le lemme maison `REs_elements_spec` que `REs.elements_spec1`.
 
 - Une large classe de problèmes ensemblistes est automatiquement résoluble par la tactique automatique `REsdec`, plus d'information dans le long cmomentaire initial du fichier [MSetDecide.v](https://coq.inria.fr/distrib/current/stdlib/Coq.MSets.MSetDecide.html).
 
 - `REsP` est un module contenant des propriétés complémentaires de ces ensembles finis.
   A priori les seuls lemmes nécessaires ici sont ceux concernant `REs.cardinal`, en particulier
   `REsP.add_cardinal_2`. Là encore `Search REs.cardinal` vous en dira plus.
   
 - La tactique `REsP.FM.set_iff` peut aussi être intéressante pour réécrire autant que possible les spécifications des opérations ensemblistes.
   
 - Ne pas chercher à descendre dans les implémentations des opérations de `REs`.
   Si vous voyez apparaître `REs.Raw` quelque part dans vos preuves, quelque chose ne va pas
   (trop de `unfold` ou similaire). De même dans Test.v, ne pas faire `Compute` directement
   sur un `REs.t` (résultat illisible), mais plutôt afficher la liste correspondante : `Compute REs.elements ...`.
