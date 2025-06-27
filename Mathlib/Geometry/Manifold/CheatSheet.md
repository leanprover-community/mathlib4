## Differential geometry cheat sheet

How do I say certain basic things in Lean?
For each of them, include a variable block. Can verso do this already?


Let M be a C^k manifold.
```
variable {𝕜 E M H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace M] {k : ℕ} -- more general: take k : WithTop ℕ∞, allows smooth and analytic; remove WithTop to exclude analyticity
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M] [IsManifold I k M]
```

Let M be a smooth manifold
```
variable {𝕜 E M H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace M]
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M] [IsManifold I ∞ M]
```

Let M be a smooth real manifold.
```
variable {E M H : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [TopologicalSpace H] [TopologicalSpace M]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M] -- test, needs open scoped Manifold??
```

Let M be an analytic manifold
```
open scoped Manifold -- test, necessary?

variable {𝕜 E M H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace M]
  {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M] [IsManifold I ω M]
```

Let f : M \to N be smooth.
Let f : M \to E (a normed space) be smooth.

Consider the product manifold M \times N.


Let \phi be the preferred chart at x\in M.

Let \phi be any (compatible) chart on M.

--------

Let E\to M be a topological vector bundle.

Let E\to M be a smooth vector bundle.

Let s be a section of E.
Let s be a C^k section of E. / The section s of E is C^k.


Let \phi be the preferred local trivialisation at x\in E.
Let \phi be any compatible trivialisation on M.

Consider the tangent bundle TM of M.

Let X be a C^k vector field on M.


explain TotalSpace.mk' somewhere in here...



**Basic API lemmas**
- testing smoothness of a map in charts: the standard charts; any charts

- testing smoothness of a section in trivialisations: the standard charts; any charts


**constructions**
- product manifold (tricky!)
- disjoint union

- product bundle (how difficult?)
- Lie bracket of vector fields
