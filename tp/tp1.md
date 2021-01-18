TP1 : Premiers pas en Coq
=========================

M1 Informatique - Preuves Assistées par Ordinateur 

Pierre Letouzey (d'après A. Miquel)

> La documentation du système Coq est consultable en ligne:
> https://coq.inria.fr/documentation

### Démarrage du système ###

Pour utiliser Coq, vous aurez besoin d'installer le logiciel ainsi
qu'une interface utilisateur.  Les options sont :

- [JsCoq](https://x80.org/collacoq) (Coq directement dans un
  navigateur web)
- [CoqIDE](https://coq.inria.fr/refman/practical-tools/coqide.html)
  (généralement distribué avec Coq)
- [VsCoq](https://github.com/coq-community/vscoq) (support Coq pour
  l'éditeur VsCode)
- [Proof General](https://proofgeneral.github.io/) éventuellement
  complété par Company-Coq (support Coq pour l'éditeur Emacs)
- [Coqtail](https://github.com/whonore/Coqtail) (support Coq pour
  l'éditeur Vim)

Les différentes interfaces proposent une disposition assez similaire :
le fichier en cours d'édition est à gauche, tandis que les preuves en
cours seront affichées en haut à droite, et les messages du système en
bas à droite (réponses de Coq ou messages d'erreurs).

### Commandes Coq ###

En Coq, une commande est formée d'un nom de commande (commençant par
une majuscule), éventuellement suivie d'un ou plusieurs arguments, et
terminée par un point.  Exemples:

```
  Check 0.
  Check S.
  Check nat.
  Print nat.
  Search nat.
  Check 2 + 2 = 5.
  Check forall x, exists y, x = 2 * y \/ x = 2 * y + 1.
  Definition id := fun (A : Set) (x : A) => x.
  Check id.
  Check id nat 7.
```

Après avoir tapé quelques commandes, soumettez-les à Coq, en utilisant
l'un des moyens de navigation (icônes, menus ou raccourcis
clavier). Observez le déplacement de la zone colorée marquant la
partie du fichier déjà exécutée.

### Passage au mode preuve ###

L'utilisateur déclare son intention d'effectuer une preuve avec une
commande de la forme :

```
Lemma and_commut :
 forall A B : Prop, A /\ B <-> B /\ A.
```

On notera que cette commande donne un nom (ici: `and_commut`) au
lemme, ce qui permettra de le référencer par la suite. On peut
éventuellement remplacer `Lemma` par `Theorem` ou quelques autres
mots-clés équivalents comme `Proposition` ou `Fact`. On marquera le
début de la preuve par la commmande `Proof` (très fortement
recommandée même si facultative).

### Sous-buts et tactiques ###

Une fois le mode preuve lancé, la zone supérieure gauche affiche en
permanence un ou plusieurs sous-buts (**subgoals**) qu'il s'agit de
démontrer. Ces sous-buts sont essentiellement des séquents de la
déduction naturelle écrits verticalement: les hypothèses (nommées)
sont en haut, et la conclusion figure en bas sous un trait. Dans la
partie haute figurent également des déclarations de variables.

La preuve se fait à l'aide de **tactiques** (distinguées des commandes
par une minuscule initiale), qui effectuent des transformations plus
ou moins complexes sur le but courant.  Par exemple, la tactique
`intro` effectuée sur un but de la forme `A -> B` introduit une
hypothèse `H : A` dans le contexte, et remplace la conclusion par
`B`. À chaque règle d'inférence de la déduction naturelle correspond
une ou plusieurs tactiques, mais certaines tactiques permettent
également d'effectuer des morceaux de preuve plus complexes, comme par
exemple la résolution de contraintes linéaires en arithmétique de
Presburger (tactique `lia`).

Les tactiques sont susceptibles d'engendrer de nouveaux sous-buts
(correspondant aux prémisses), ou au contraire de faire disparaître le
but courant (lorsque celui-ci est résolu).  La preuve est terminée
lorsqu'il n'y a plus de sous-but à démontrer. On doit alors utiliser
la commande `Qed` (d'après *Quod erat demonstrandum*, le CQFD latin)
pour conclure la preuve et repasser au mode *commande*. Voici par
exemple une preuve complète pour l'énoncé précédent :

```
Lemma and_commut :
  forall A B : Prop, A /\ B <-> B /\ A.
Proof.
 intros. split.
 - intros. destruct H. split. assumption. assumption.
 - intros. destruct H. split; assumption.
Qed.
```

Lorsque les tactiques sont séparées par des points, Coq va alors les
exécuter pas-à-pas. On peut aussi utiliser le `;` pour **chaîner** des
tactiques. Ainsi `split;assumption` fait agir `assumption` sur les
deux sous-buts créés par `split`.

Devant des tactiques, on peut éventuellement placer une **puce**,
c'est-à-dire un des marqueurs `-` ou `+` ou `*`. Ces puces sont
optionnelles mais aident grandement à hiérarchiser la preuve en cours
en délimitant chaque sous-partie.

Un tel *script de preuve*, une fois sauvé dans un fichier tel que
`mes_preuves.v`, peut ensuite être *compilé* via la commande unix
`coqc mes_preuves.v`.  Si les preuves que contient ce fichier sont
correctes, un fichier compilé `mes_preuves.vo` est alors produit, qui
permettra de recharger ces preuves rapidement par la suite (cf. la
commande `Require Import`).

### Exercice 1 : Calcul propositionnel ###

Poser l'existence de variables propositionnelles `A`, `B` et `C` via
la commande:

```
Parameters A B C : Prop.
```

Puis prouver en Coq les formules suivantes :

```
Lemma E1F1 : A -> A.
Lemma E1F2 : (A -> B) -> (B -> C) -> A -> C.
Lemma E1F3 : A /\ B <-> B /\ A.
Lemma E1F4 : A \/ B <-> B \/ A.
Lemma E1F5 : (A /\ B) /\ C <-> A /\ (B /\ C).
Lemma E1F6 : (A \/ B) \/ C <-> A \/ (B \/ C).
Lemma E1F7 : A -> ~~A.
Lemma E1F8 : (A -> B) -> ~B -> ~A.
Lemma E1F9 : ~~(A \/ ~A).
```

### Exercice 2 :  Calcul des prédicats ###

Après avoir effectué les déclarations suivantes:

```
Parameter X Y : Set.
Parameter A B : X -> Prop.
Parameter R : X -> Y -> Prop.
```

Prouver en Coq les formules suivantes:

```
Lemma E2F1 : (forall x, A x /\ B x) <-> (forall x, A x) /\ (forall x, B x).
Lemma E2F2 : (exists x, A x \/ B x) <-> (exists x, A x) \/ (exists x, B x).
Lemma E2F3 : (exists y, forall x, R x y) -> forall x, exists y, R x y.
```

### Exercice 3 : Reprise ! ###

Refaire en Coq les exercices 1 et 4 de la feuille de TD 1. Pour
simuler la règle de raisonnement par l'absurde, on pourra déclarer
l'axiome suivant:

```
Axiom not_not_elim : forall A : Prop, ~~A -> A.
```
