import Mathlib

/-!
# Orientations playground: let's try different definitions of orientations of manifolds

-/
open Bundle Filter Function Topology
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/- Observe that
- orientability is a property of an atlas: {id, -id} is not an orientable atlas of R,
  but R is orientable with the orientable atlas {id}

Can we
- have the definition be a choice of `Module.Orientation` of each `TangentSpace I x`?
  Well, how do you say "the orientation is locally constant"?
- and talking about choices of orientations might be not as nice. Can we do this more directly?

-/

section

/-
intuition/textbook definition: an orientation on a manifold `M` (with an implicitly given atlas `𝓐`)
is a choice of basis of each tangent space `T_pM` such that, for each chart `(φ, U)` in the atlas,
each induced basis of T_x M (for `x ∈ U`) has the same sign
(i.e., either matches our chosen standard basis, or dismatches it)
-/

def iota : Type _ := sorry
instance : Fintype iota := sorry
instance : DecidableEq iota := sorry

variable (𝕜 E) in
def basis : Module.Basis iota 𝕜 E := sorry

variable [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]

noncomputable def referenceOrientation := Module.Basis.orientation (basis 𝕜 E)

/- variable (I M) in
structure Orientation1 where
  -- Choice of basis of each tangent space.
  basis : Π x : M, Module.Basis iota 𝕜 (TangentSpace I x)
  --or : Π x : M, Module.Basis.orientation (basis x)
  compat : ∀ (φ : OpenPartialHomeomorph M H), ∀ x : M, φ ∈ atlas H M → x ∈ φ.source →
    -- doesn't even typecheck
    (basis x).orientation = referenceOrientation -/

/-
Annoying about this definition:
- cannot easily "choose a basis for E"; need an indexing type somewhere
- this doesn't typecheck, even!
- needs additional hypotheses on 𝕜 (is ℂ one? not sure... but perhaps only R is fine here!)
- needs finite-dimensionality; also seems annoying (but perhaps is true in general)

-/

end

/-

We could probably make that a Lean definition also. I'm not convinced it's as nice: eventually, we
would like to talk about a manifold being *orientable*, and phrasing that directly in terms of an
atlas is quite nice!
Instead, let's try things more abstractly: choose a sign `ε x` at each `x : M`.
(Intuition: we assume all charts have been shrunk to give a single consistent orientation,
e.g. by having connected domains; then the sign specifies whether `chartAt x` preserves or reverses
orientation.
More formally, fix a global choice of orientation on `E`; then `ε x` is positive iff `chartAt x` )


-/

variable {p q : M} [Module ℝ E]

/- Intuition: M has been endowed with an oriented atlas --- in particular, each preferred chart
has a sign such that changes of coordinates have positive determinant iff these maps have the same
sign.
-/
structure Orientation2a where
  -- The "sign"
  sign : M → SignType
  -- compatibility condition
  -- up to minor tweaks (such as, we probably want two conditions
  -- "signs are equal => det is positive" and "signs are different => det is negative" instead;
  -- currently different signs could have determinant zero)
  compat : ∀ x y, y ∈ (chartAt H x).source →
    sign y = sign x ↔ 0 < (fderiv ℝ ((extChartAt I y).symm ≫ extChartAt I x) (extChartAt I x x)).det

-- In fact, the above condition could be generalised to the whole atlas: we can give a sign to
-- each chart in that atlas, not just the preferred charts.
structure Orientation2b where
  -- The "sign" of each chart in the atlas
  sign : atlas H M → SignType
  -- the corresponding compatibility condition
  compat : ∀ φ ψ x, (hφ : φ ∈ atlas H M) → (hψ : ψ ∈ atlas H M) →
      x ∈ ((ψ.extend I).symm ≫ (φ.extend I)).source →
    sign ⟨φ, hφ⟩ = sign ⟨ψ, hψ⟩ ↔ 0 < (fderiv ℝ ((ψ.extend I).symm ≫ (φ.extend I)) x).det

----- another idea, after taking a walk


















#exit

orientable manifold: choice of sign and the compability property!

A given manifold M may be orientation for some atlas and not others: that's just what we said above.



OrientedManifold

OrientableManifold
