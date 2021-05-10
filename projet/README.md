# Projet #

Le sujet du projet parle de coarbres et de [cographes][].

[cographes]: https://en.wikipedia.org/wiki/Cograph

## Quelques tactiques automatiques utiles ##

Voir aussi le petit rappel des tactiques de base tout en bas.

- [`tauto`](https://coq.inria.fr/refman/proofs/automatic-tactics/logic.html#coq:tacn.tauto)
  pour résoudre les tautologies en logique intuitionniste
  propositionnelle (i.e. par succession de `apply` sans instantiation
  de quantificateurs).
- [`firstorder`](https://coq.inria.fr/refman/proofs/automatic-tactics/logic.html#coq:tacn.firstorder)
  peut parfois résoudre des buts nécessitant l'instantiation
  d'hypothèses quantifiées du contexte.
- [`btauto`](https://coq.inria.fr/refman/proofs/automatic-tactics/logic.html#coq:tacn.btauto)
  résout des égalités booléennes tautologiques.
- [`congruence`](https://coq.inria.fr/refman/proofs/automatic-tactics/logic.html#coq:tacn.congruence)
  résout le but par raisonnement équationnel (utile si le contexte
  contient, par exemple `H0: x = 0` et `H1: x = 1`).
- [`lia`](https://coq.inria.fr/refman/addendum/micromega.html#coq:tacn.lia)
  résout des buts arithmétiques.
- [`intuition`](https://coq.inria.fr/refman/proofs/automatic-tactics/logic.html#coq:tacn.intuition)
  essaye le même genre de stratégie que `tauto` mais peut s'utiliser en combinaison avec une tactique qui prouve les buts
  restant comme `btauto` ou `congruence` (i.e. `intuition btauto`,
  `intuition congruence`, `intuition lia`, etc.). À noter : `firstorder` peut aussi prendre une tactique en argument pour
  finir les buts restants.

## Quelques lemmes utiles ##

### sur les booléens ###

- `eq_true_iff_eq : forall b1 b2 : bool, b1 = true <-> b2 = true -> b1 = b2`
- `orb_true_iff : forall b1 b2 : bool, b1 || b2 = true <-> b1 = true \/ b2 = true`
- `andb_true_iff : forall b1 b2 : bool, b1 && b2 = true <-> b1 = true /\ b2 = true`
- `List.existsb_exists : forall (A : Type) (f : A -> bool) (l : list A),
  List.existsb f l = true <-> (exists x : A, List.In x l /\ f x = true)`
- `Nat.eqb_eq: forall n m : nat, (n =? m) = true <-> n = m`

### sur les listes ###

Cherchez les avec la commande `Search`. Par exemple, `Search "++" List.In`.

## Petit rappel des tactiques de bases ##

- [`intro` / `intros`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.intro)
  pour introduire des variables et des hypothèses dans le contexte.
- [`revert`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.revert)
  pour annuler l'effet d'`intro` et regénéralisant le but (peut être utile avant un appel à `induction`).
- [`clear`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.clear)
  pour effacer des hypothèses devenues inutiles du contexte.
- [`easy`](https://coq.inria.fr/refman/proofs/automatic-tactics/auto.html#coq:tacn.easy)
  une tactique qui résout le but courant en combinant les effets de :
  - [`assumption`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.assumption)
    lorsque le but se trouve parmi les hypothèses.
  - [`contradiction`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.contradiction)
    lorsqu'une hypothèse et sa négation sont présentes dans le contexte.
  - [`discriminate`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.discriminate)
    lorsqu'une hypothèse est une égalité entre deux constructeurs différents.
  - [`reflexivity`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.reflexivity)
    lorsque le but est une égalité entre deux éléments qui sont égaux (à réduction près).
- [`assert (nom : enonce)`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.assert)
  pour introduire un but intermédiare.
- [`apply`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.apply)
  pour appliquer un lemme ou une hypothèse
  (variants utiles à connaître : `apply ... with`, `eapply`, `apply ... in`).
- [`specialize (nom arguments) as nom`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacv.specialize)
  pour spécialiser une hypothèse du contexte ou un lemme.
- [`rewrite`](https://coq.inria.fr/refman/proofs/writing-proofs/rewriting.html#coq:tacn.rewrite)
  à ne pas confondre avec `apply`. S'utilise pour réécrire avec un lemme ou une hypothèse dont
  la conclusion est une égalité (ou une équivalence). Variant utile à connaître : `rewrite ... with`.
- [`simpl`](https://coq.inria.fr/refman/proofs/writing-proofs/rewriting.html#coq:tacn.simpl)
  pour simplifier le but lorsque c'est possible par calcul.
- [`unfold`](https://coq.inria.fr/refman/proofs/writing-proofs/rewriting.html#coq:tacn.unfold)
  pour remplacer un nom par sa définition.
- [`split`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacv.split)
  lorsque le but est un type inductif à un seul constructeur (typiquement `/\`),
  crée un sous-but par argument du constructeur (par exemple, la gauche et la droite de `/\`).
- [`destruct`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.destruct)
  pour destructurer un élément d'un type inductif.
  Si le type inductif n'a qu'un seul constructeur (cas du `/\` et du `exists`), alors on
  récupère les arguments du contructeur (composantes gauche et droite du `/\` par exemple).
  Si le type inductif a plusieurs constructeurs, alors un sous-but est généré par constructeur.
- [`induction`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.induction)
  pour faire une preuve par récurrence sur un élément d'un type inductif.
  Le comportement est similaire à celui de `destruct` mais on récupère en plus une (ou plusieurs)
  hypothèses de récurrence.
- [`injection`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.injection)
  lorsqu'une hypothèse est une égalité entre deux constructeurs identiques, on peut récupérer
  une égalité entre les arguments de ces constructeurs (car les constructeurs sont toujours
  des fonctions injectives).
- [`inversion`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.inversion)
  à utiliser sur une hypothèse dont le type est un prédicat inductif pour déterminer comment
  cette hypothèse a été construite et récupérer les hypothèses correspondant à chacun des cas
  possibles pour la construire.
- [`f_equal`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.f_equal)
  pour transformer un but de la forme `f x = f y` en `x = y`. Peut s'utiliser quelle que soit
  la fonction `f` mais attention, parfois ce n'est pas la bonne manière de montrer le but.
- [`symmetry`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.symmetry)
  inverse une égalité (ou une équivalence).
- [`transitivity x`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.transitivity)
  prouve une égalité (ou une équivalence) par transitivité.
