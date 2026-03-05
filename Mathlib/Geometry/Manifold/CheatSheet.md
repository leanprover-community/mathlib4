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

Differentiability of functions between manifolds
```
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Defs

variable
  -- Given a non-trivially normed field 𝕜
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- A manifold M over 𝕜
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- A manifold M' over 𝕜
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  -- A function from M to M' and x in M
  (f : M → M') (x : M)

variable (x : M) in
-- f is differentiable at x
#check MDifferentiableAt I I' f x

variable (n : WithTop ℕ∞) in -- A natural number or ∞ or ω
#check ContMDiff I I' n f


variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (g : M → F) in
open scoped Manifold in
#check ContMDiff I 𝓘(𝕜, F) n g  -- g is n times continuously differentiable
```

Consider the product manifold M \times N.


Let \phi be the preferred chart at x\in M.

Let \phi be any (compatible) chart on M.

--------

Let E\to M be a topological vector bundle.

Let E\to M be a smooth vector bundle.

Let s be a section of E.
```
variable (s : Π x : M, V x)
```
Let X be a vector field on `M`
```
(X : Π x : M, TangentSpace I x)
```

Let s be a C^k section of E. / The section s of E is C^k.
```
ContMDiff I (I.prod 𝓘(𝕜, F)) (k + 1) (fun x ↦ TotalSpace.mk' F x (σ x))
```

Let `X` be a C^k vector field on M.
```
variable {X : Π x : M, TangentSpace I x}
-- TODO: this doesn't work!
-- variable (___hX: ContMDiff I I.tangent 2 (fun x ↦ (X x : TangentBundle I M)))
```

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
