Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
Require Import fintype finfun bigop ssralg ssrnum poly.
Import GRing.Theory Num.Theory.
Require Import ssrint.

Fail Check idomain_axiomz.
Locate idomain_axiomz.
Check intUnitRing.idomain_axiomz.
Import intUnitRing.
Check idomain_axiomz.

Locate horner_int.
Check horner_int.
