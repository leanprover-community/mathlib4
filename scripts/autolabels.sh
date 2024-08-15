#!/usr/bin/env bash

 : <<'BASH_MODULE_DOCS'

This file contains the dictionary for converting a modified dir into a github label,
as well as the script to perform the conversion.

Rules:
* only lines starting with `|t-` are considered;
* repeated spaces, commas and pipes (|) are ignored;
* `Mathlib` is added by default to each `Root folder`.

Exception: `Tactic/Linter` is converted into `Tactic-Linter` internally, to simplify separating it from
`Tactic/anything_other_than_linter`.

|Label                   |Root folders                                                                       |
|-                       |-                                                                                  |
|t-algebra               | Algebra, FieldTheory, RingTheory, GroupTheory, RepresentationTheory, LinearAlgebra|
|t-algebraic-geometry    | AlgebraicGeometry, Geometry/RingedSpace                                           |
|t-euclidean-geometry    | Geometry.Euclidean                                                                |
|t-differential-geometry | Geometry/Manifold                                                                 |
|t-analysis              | Analysis                                                                          |
|t-category-theory       | CategoryTheory                                                                    |
|t-combinatorics         | Combinatorics                                                                     |
|t-computability         | Computability                                                                     |
|t-condensed             | Condensed                                                                         |
|t-data                  | Data                                                                              |
|t-dynamics              | Dynamics                                                                          |
|t-linter                | Tactic/Linter                                                                     |
|t-logic                 | Logic, ModelTheory                                                                |
|t-measure-probability   | MeasureTheory, Probability, InformationTheory                                     |
|t-meta                  | Tactic, Lean, Init, Util, Mathport, Control, Testing                              |
|t-number-theory         | NumberTheory                                                                      |
|t-order                 | Order                                                                             |
|t-topology              | Topology, AlgebraicTopology                                                       |
|t-set-theory            | SetTheory                                                                         |

BASH_MODULE_DOCS

mdToSpaces () { tr -s '|, ' ' ' < scripts/autolabels.sh | sed -n 's=^ *t-=t-=p; /^BASH_MODULE_DOCS$/Q' ; }

(
  mdToSpaces
  git diff --name-only origin/master
) |
awk -v long="${1}" '
    gsub(/Tactic\/Linter/, "Tactic-Linter")
    (2 <= NF) {
      for(i=2; i<=NF; i++) {
        dir="Mathlib/"$i"/"
        dirToLabel[dir]=$1
      }
    }
    (1 == NF) { gitDiffs[$1]++ }
  END{
    for(fil in gitDiffs) {
      fd=0
      for(dir in dirToLabel) {
        if (fil ~ dir) {
          fd++
          labelFor[dirToLabel[dir]]=labelFor[dirToLabel[dir]]"\n* "fil
        }
      }
      if(fd == 0) { unlabeled[fil]=0 }
    }
    if (!(long == "long")){
      labCount=0
      for(l in labelFor) { labCount++ }
      for(l in labelFor) {
        labCount--
        printf("%s%s", l, (labCount == 0)? "" : ",")
      }
    }
    if (long == "long"){
      print "applicable labels:"
      for(l in labelFor) {
        printf("* %s\n", l)
      }
      for(l in labelFor) {
        printf("\nfound label %s for %s\n", l, labelFor[l])
      }
      print("\nno label found for")
      for(fil in unlabeled) {
        printf("* %s\n", fil)
      }
    }
  }'
