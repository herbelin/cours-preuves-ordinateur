# Cours Preuves assistées par ordinateur (hiver 2023)

#### Horaires

12 semaines à partir du 18 janvier 2023 (à partir du 20 janvier pour les TD / TP).

- Cours : mercredi 10h45-12h45, salle Condorcet 86A (Hugo Herbelin)
- TP/TD : vendredi 11h-13h, salle 2001 (Théo Zimmermann)

#### Objectifs du cours

Dans une société toujours plus dépendante du bon fonctionnement des
programmes informatiques, le cours combinera une introduction aux
principes de base de la preuve des programmes (la logique) et une
introduction à l'utilisation du logiciel Coq pour la
preuve de correction effective des programmes.

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

- Séance 1 (20 janvier) : [TD 1](td/td1.pdf) ([quelques questions corrigées](td/correction-td1-seance1.pdf))
- Séance 2 (27 février) : [TP 1](tp/tp1.md)
- Séance 3 (3 février) : Suite du [TD 1](td/td1.pdf)
- Séance 4 (10 février) : [TP 2](tp/tp2.md)
- Séance 5 (17 février) : Suite du [TD 1](td/td1.pdf) et début du [TD 2](td/td2.pdf)
- Séance 6 (3 mars) : [TP 3](tp/tp3.md)
- Séance 7 (10 mars) : [TP 4](tp/tp4.md)
- Séance 8 (17 mars) : [TP 5](tp/tp5.md)
- Séance 9 (24 mars) : [TP 6](tp/tp6.md)
- Séance 10 (31 mars) : Suite du [TD 2](td/td2.pdf)
- Séance 11 (7 avril) : [TD 3](td/td3.pdf)
- Séance 12 (14 avril) : [TP 7](tp/tp7.md)

#### Projet

Sujet 2022 : [projet.v](projet.v).

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

- [examen 2021](examens/examen-2021.pdf) avec sa [correction](examens/examen-correction-2021.pdf) et le [code Coq](examens/examen_correction_2021.v) correspondant

- [examen 2022](examens/examen-2022.pdf) avec sa [correction partielle](examens/examen-correction-2022.pdf) et le [code Coq](examens/examen_correction_2022.v) correspondant
