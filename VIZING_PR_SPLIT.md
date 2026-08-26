# Suggested Vizing theorem PR split

These PRs are ordered so each one builds on the previous one and stays reviewable.

## PR 1: Edge coloring and local color sets

**Scope**
- Introduce edge colorings as colorings of the line graph.
- Define local incident edge/color sets and missing colors.
- Prove the basic degree/cardinality lemmas used later.

**Files**
- `Mathlib/Combinatorics/SimpleGraph/Coloring/EdgeColoring.lean`
- `Mathlib/Combinatorics/SimpleGraph/Coloring/KempeChain/Basic.lean` up through the incident/missing-color API and basic Kempe subgraph definitions
- re-export from `Mathlib/Combinatorics/SimpleGraph/Coloring/KempeChain.lean`

**Sample title**
`feat(SimpleGraph/Coloring): add edge colorings and missing colors`

**Sample description**
Adds the edge-coloring API used for Vizing's theorem. Edge colorings are implemented as vertex colorings of the line graph, with definitions for colors incident to a vertex and colors missing at a vertex. Also proves the basic cardinality estimates relating incident colors to degree.

## PR 2: Kempe chain swapping and recoloring

**Scope**
- Add the two-color Kempe subgraph infrastructure.
- Define color swaps on a Kempe component.
- Prove the recoloring and one-edge extension lemmas.

**Files**
- `Mathlib/Combinatorics/SimpleGraph/Coloring/KempeChain/Basic.lean`
- `Mathlib/Combinatorics/SimpleGraph/Coloring/KempeChain/Swap.lean`
- `Mathlib/Combinatorics/SimpleGraph/Coloring/KempeChain/Recolor.lean`
- `Mathlib/Combinatorics/SimpleGraph/Coloring/KempeChain.lean`

**Sample title**
`feat(SimpleGraph/Coloring): add Kempe chain recoloring lemmas`

**Sample description**
Develops the Kempe-chain machinery needed by the Vizing fan argument. This includes the two-color subgraph, connected Kempe components, swapping colors on a component, and extending a partial edge coloring across one edge when a color is missing at both endpoints.

## PR 3: Vizing fan basics and rotation

**Scope**
- Define Vizing fans and fan extensions.
- Prove missing-color cardinality bounds for fans.
- Prove the Term-A fan rotation lemma.

**Files**
- `Mathlib/Combinatorics/SimpleGraph/Coloring/VizingFan/Basic.lean`
- `Mathlib/Combinatorics/SimpleGraph/Coloring/VizingFan/Rotation.lean`
- `Mathlib/Combinatorics/SimpleGraph/Coloring/VizingFan.lean`

**Sample title**
`feat(SimpleGraph/Coloring): define Vizing fans and rotation`

**Sample description**
Introduces Vizing fans for partial edge colorings and proves the fan-rotation step. This PR isolates the main combinatorial mechanism used later by the adjacency lemma, without yet proving the full maximal-fan argument.

## PR 4: Vizing adjacency lemma

**Scope**
- Prove existence of maximal fans.
- Prove the maximal fan dichotomy.
- Prove the public `vizingAdjacencyLemma` used by the final theorem.

**Files**
- `Mathlib/Combinatorics/SimpleGraph/Coloring/VizingFan/Adjacency.lean`
- `Mathlib/Combinatorics/SimpleGraph/Coloring/VizingFan.lean`

**Sample title**
`feat(SimpleGraph/Coloring): prove the Vizing adjacency lemma`

**Sample description**
Completes the fan argument by extending a fan to a maximal fan and applying the Term-A/Term-B dichotomy. The resulting adjacency lemma is the bridge from local Kempe-chain recoloring to the global upper bound in Vizing's theorem.

## PR 5: Vizing's theorem

**Scope**
- Prove the lower bound `Δ ≤ χ'`.
- Prove the induction-on-edges upper bound `χ' ≤ Δ + 1`.
- State the final theorem that the chromatic index is either `Δ` or `Δ + 1`.

**Files**
- `Mathlib/Combinatorics/SimpleGraph/Coloring/VizingTheorem/Basic.lean`
- `Mathlib/Combinatorics/SimpleGraph/Coloring/VizingTheorem/UpperBound.lean`
- `Mathlib/Combinatorics/SimpleGraph/Coloring/VizingTheorem.lean`

**Sample title**
`feat(SimpleGraph/Coloring): prove Vizing's theorem`

**Sample description**
Uses the Vizing adjacency lemma to prove the classical upper bound on the chromatic index of a finite simple graph. Together with the clique lower bound for the line graph, this gives Vizing's theorem: the chromatic index is either the maximum degree or one more.
