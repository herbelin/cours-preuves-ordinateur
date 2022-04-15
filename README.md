# Cours Preuves assistées par ordinateur (hiver 2022)

#### Horaires

12 semaines à partir du 17 janvier 2022 (à partir du 28 janvier pour les TD / TP).

- Cours : lundi 8h30-10h30 en visio sur [Big Blue Button](https://bbb-front.math.univ-paris-diderot.fr/recherche/hug-cu1-eym-m5i) jusqu'à nouvel ordre (Hugo Herbelin)
- TP/TD : vendredi 14h-16h en présentiel, salle 2031 (Théo Zimmermann)

Contacter les enseignants pour obtenir les liens

#### Notes de cours

- [Introduction à la logique du 1er ordre](logique-premier-ordre.pdf) (notes d'Alexandre Miquel pour la version initialle du cours en 2008)
- [Notes de cours sur la correspondance preuve-programme, notamment en logique classique](proofs-and-programs.pdf) (en anglais)
- [Un petit guide de survie pour Coq](https://www.irif.fr/~letouzey//preuves/guide.html)

#### Plan prospectif

- Cours 1 : [Contexte historique](cours1.pdf), règles d'inférence de la déduction naturelle ([section 2.1 du poly PP](proofs-and-programs.pdf))
- Cours 2 : Règles d'inférence de la déduction naturelle (suite), élimination des coupures, lambda-calcul simplement typé, correspondance preuves-programmes ([section 3.1 du poly PP](proofs-and-programs.pdf))
- Cours 3 : Lambda-calcul simplement typé, correspondance preuves-programmes, élimination des coupures, β-réduction, coupures commutatives, propriété de la sous-formule ([Théorème 5 du poly PP](proofs-and-programs.pdf)), inversibilité de l'introduction des connecteurs négatifs, contextes d'évaluation
- Cours 4 : Correspondance preuves-programmes, règles η, inversibilité de l'élimination des connecteurs positifs, ...
- Cours 5 : Quantificateurs
- Cours 6 et 7 : Types inductifs, itérateur / récurseur / analyse de cas / point fixe, Coq's `match`/fix`
- Cours 8 : Récursion bien fondée, récursion gardée et non gardée
- Cours 9 et 10 : Une hiérarchie de force logique et d'expressivité calculatoire (PRA, PA, PA₂, ZF)
- Cours 11 : Système F, coinduction
- Cours 12 : Familles inductives
- Cours 12 : Synthèse

#### Séances TP / TD

- Séance 1 (28 janvier) : [TD 1](td/td1.pdf) ([quelques questions corrigées](td/correction-td1-seance1.pdf))
- Séance 2 (4 février) : [TP 1](tp/tp1.md)
- Séance 3 (11 février) : Suite du [TD 1](td/td1.pdf)
- Séance 4 (18 février) : [TP 2](tp/tp2.md)
- Séance 5 (25 février) : Suite du [TD 1](td/td1.pdf) et début du [TD 2](td/td2.pdf)
- Séance 6 (11 mars) : [TP 3](tp/tp3.md)
- Séance 7 (18 mars) : [TP 4](tp/tp4.md)
- Séance 8 (25 mars) : [TP 5](tp/tp5.md)
- Séance 9 (1er avril) : [TP 6](tp/tp6.md)
- Séance 10 (8 avril) : Suite du [TD 2](td/td2.pdf)
- Séance 11 (15 avril) : [TD 3](td/td3.pdf)
- Séance 12 (22 avril) : [TP 7](tp/tp7.md)

#### Projet

Sujet : [projet.v](projet.v).

- Vous pouvez le faire seul ou en binôme.
- Le but est de remplacer les `TODO` et les `Admitted`.
- Vous pouvez vous servir de toutes les tactiques vues en cours / TP, mais aussi de toute autre tactique et de tout lemme disponible dans la bibliothèque de Coq (sans oublier les lemmes mis à disposition dans la partie I du projet). Notamment :
  - `lia` (apès `Require Import Lia`) : tactique automatique pour les buts purement arithmétiques.
  - `auto` / `eauto` : tactiques permettant d'exploiter les déclarations de `Hint` dispersées à travers le projet.
- Le sujet comporte des indications dans les commentaires : lisez-les.
- Il est possible de sauter des preuves et de se servir des lemmes néanmoins dans la suite.
- Ne restez pas bloqués sans solliciter de l'aide (notamment par mail). N'hésitez pas non plus à demander des conseils en tout genre.
- La partie V est entièrement optionnelle.
- Le projet sera à rendre au moment de la période d'examen et sera accompagné de soutenances.

#### Examens

- [examen 2021](examens/examen-2021.pdf)
