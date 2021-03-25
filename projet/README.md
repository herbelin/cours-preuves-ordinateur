# Projet #

Le sujet du projet parle de coarbres et de [cographes][].

[cographes]: https://en.wikipedia.org/wiki/Cograph

## Quelques tactiques automatiques utiles ##

- [`tauto`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.tauto)
  pour résoudre les tautologies en logique intuitionniste
  propositionnelle (i.e. par succession de `apply` sans instantiation
  de quantificateurs).
- [`firstorder`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.firstorder)
  peut parfois résoudre des buts nécessitant l'instantiation
  d'hypothèses quantifiées du contexte.
- [`btauto`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.btauto)
  résout des égalités booléennes tautologiques.
- [`congruence`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.congruence)
  résout le but par raisonnement équationnel (utile si le contexte
  contient, par exemple `H0: x = 0` et `H1: x = 1`).
- [`lia`](https://coq.inria.fr/refman/addendum/micromega.html#coq:tacn.lia)
  résout des buts arithmétiques.
- [`intuition`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.intuition)
  à utiliser en combinaison avec une tactique qui prouve les buts
  restant comme `btauto` ou `congruence` (i.e. `intuition btauto`,
  `intuition congruence`, `intuition lia`, etc.)

## Quelques lemmes utiles ##

### sur les booléens ###

- `eq_true_iff_eq : forall b1 b2 : bool, b1 = true <-> b2 = true -> b1 = b2`
- `orb_true_iff : forall b1 b2 : bool, b1 || b2 = true <-> b1 = true \/ b2 = true`
- `andb_true_iff : forall b1 b2 : bool, b1 && b2 = true <-> b1 = true /\ b2 = true`
- `List.existsb_exists : forall (A : Type) (f : A -> bool) (l : list A),
  List.existsb f l = true <-> (exists x : A, List.In x l /\ f x = true)`

### sur les listes ###

Cherchez les avec la commande `Search`. Par exemple, `Search "++" List.In`.
