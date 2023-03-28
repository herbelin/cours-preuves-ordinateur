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
- Cours 2 : Règles d'inférence de la déduction naturelle (suite), lambda-calcul simplement typé, β-réduction, correspondance preuves-programmes ([section 3.1 du poly PP](proofs-and-programs.pdf)), quantificateurs
- Cours 3 : Lambda-calcul simplement typé, correspondance preuves-programmes, élimination des coupures, propriété de la sous-formule ([Théorème 5 du poly PP](proofs-and-programs.pdf)), formes normales, normalisation
- Cours 4 : Règles η, inversibilité de l'introduction des connecteurs négatifs et de l'élimination des connecteurs positifs, admissibilité de la contractione et de l'affaiblissement
- Cours 5 : Coupures commutatives, logique classique et opérateurs de contrôle, contextes d'évaluation
- Cours 6 et 7 et 8 : Types inductifs, itérateur / récurseur / analyse de cas / point fixe / récurrence / analyse de cas dépendante
- Cours 9 : Coq's `match`/`fix`, récursion gardée, système F, codage de Church
- Cours 10 : Une hiérarchie de force logique et d'expressivité calculatoire (PRA, PA, PA₂, ZF)
- Cours 11 : coinduction
- Cours 12 : Familles inductives
- Cours 12 : Synthèse

#### Séances TP / TD

- Séance 1 (20 janvier) : [TD 1](td/td1.pdf) ([correction](td/correction-td1-seance1.pdf))
- Séance 2 (27 janvier) : Suite du [TD 1](td/td1.pdf)
- Séance 3 (3 février) : [TP 1](tp/tp1.md)
- Séance 4 (10 février) : Suite du [TD 1](td/td1.pdf)
- Séance 5 (17 février) : [TP 2](tp/tp2.md)
- Séance 6 (24 février) : [TD 2](td/td2.pdf)
- Séance 7 (10 mars) : [TP 3](tp/tp3.md)
- Séance 8 (17 mars) : [TP 4](tp/tp4.md)
- Séance 9 (24 mars) : [TP 5](tp/tp5.md)

#### Projet

Cf. [projet/README.md](projet/README.md)

#### Examens

- [examen 2021](examens/examen-2021.pdf) avec sa [correction](examens/examen-correction-2021.pdf) et le [code Coq](examens/examen_correction_2021.v) correspondant

- [examen 2022](examens/examen-2022.pdf) avec sa [correction partielle](examens/examen-correction-2022.pdf) et le [code Coq](examens/examen_correction_2022.v) correspondant
