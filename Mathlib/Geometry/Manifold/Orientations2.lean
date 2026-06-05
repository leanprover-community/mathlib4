module

public import Mathlib

/-!
# Orientations playground: let's try different definitions of orientations of manifolds

-/
open Bundle Filter Function Topology
open scoped Manifold

-- Let M be a real manifold
variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-
Another bunch of thoughts while taking a walk

- in the end, we want to have all the different definitions
- we want to able to say "a volume form induces an orientation"
  (which is equivalent to a section of the exterior power bundle),
- the "oriented atlas" definition is nicer to check in some cases, including intervals, products,
  and e.g. "a complex manifold (as a real manifold) is oriented"

*details about the latter* the key lemma in that proof is
"a complex-linear map, seen as real linear map, has positive determinant"
(because changes of coordinates are complex-linear in a complex manifold, hence real linear)

xxx generalise to different spaces?
why is that? say f : E → E is complex linear,
let J : E → E denote the endomorphism which is
multiplication by i.
Then f ∘ J = J ∘ f and J² = -id, i.e. J ∘ f ∘ J = -f and f = 1/2 (f - J ∘ f ∘ J).

Choose an ordered C-basis B=(b_i) of E, then (b1, J b1, ..., bn, J bn) is an R-basis of E.
Note that f - J ∘ f ∘ J has some property <...> (it commutes with J!).
The matrix of f in the real basis consists of blocks a&b\\-b&a, which has determinant a²+b²>0.
Or so... therefore, is positive.

*Note* we don't need the f = 1/2 (f - J ∘ f ∘ J) step; commuting with j resp J suffices.
*Guess* the same argument works with distinct domain and co-domain.


For expressing statements "let M be an oriented manifold", "the Mobius strip is not oriented" or
"an oriented surface is isomorphic to one of the following", either definition is useful.

Propose to go ahead with the current definition for now, leaving ample TODOs about the other
equivalent definitions. But will both unlock new results in mathlib and projects for new
contributors. Painting ourselves in a corner like this does not seem wise.

-/


/-
Design idea


-/

/- A set of open partial homeomorphisms is *orientable* if it admits an orientation:
intuitively speaking, if all transition maps between any two charts have positive Jacobian
determinant. This definition needs a modification to be correct in dimension 1 (each chart also
carries a sign, and the Jacobian determinant shall be positive iff the corresponding signs are
positive, and negative otherwise).

An orientation of this system is a choice of such signs.
An orientation of a manifold is an orientation of its atlas. -/

/- An *orientation* of a set of open partial homomeomorphisms is, morally speaking,is oriented-/
variable (I) in
private structure OrientationFoo (S : Set (OpenPartialHomeomorph M H)) where
  sign : S → SignType
  compatible : ∀ φ ψ : S, ∀ x ∈ ((ψ.1.extend I).symm ≫ (φ.1.extend I)).source,
    sign φ = sign ψ ↔ 0 < (fderiv ℝ ((ψ.1.extend I).symm ≫ (φ.1.extend I)) x).det

variable (I M) in
/-- A manifold `M` is orientable if its atlas admits an orientation. -/
def IsOrientable : Prop := Nonempty (OrientationFoo I (atlas H M))

open scoped ContDiff Manifold
open Set

variable (I M) in
@[no_expose] def IsManifold.Orientation := OrientationFoo I ({ chartAt H x | x : M}) -- atlas H M

variable (I M) in
structure OrientationBar where
  -- The "sign"
  sign : M → SignType
  -- compatibility condition
  -- up to minor tweaks (such as, we probably want two conditions
  -- "signs are equal => det is positive" and "signs are different => det is negative" instead;
  -- currently different signs could have determinant zero)
  compat1 : ∀ x y, y ∈ (chartAt H x).source →
    sign y = sign x → 0 < (fderiv ℝ ((extChartAt I y).symm ≫ extChartAt I x) (extChartAt I x x)).det
  compat2 : ∀ x y, y ∈ (chartAt H x).source →
    sign y ≠ sign x → (fderiv ℝ ((extChartAt I y).symm ≫ extChartAt I x) (extChartAt I x x)).det < 0

-- the rewrites of the chart's definitions are all very painful; not good ergonomics!
/- def orientationIcc : OrientationFoo (𝓡∂ 1) (({ chartAt _ x | x : Icc (0 : ℝ) 1})) where
  sign := by
    intro ⟨φ, hφ⟩
    simp at hφ
    choose z hz hφ using hφ
    by_cases hz' : z < 1
    · simp_all
      simp [hz'] at hφ
      simp [hz] at hφ
    --simp at hφ

    --by_cases :
    have : (φ = IccLeftChart 0 1) ∨ (φ = IccRightChart 0 1) := sorry
    obtain (hφ' | rfl) := this
    simp at hφ
    sorry
  compatible := sorry -/

noncomputable
def orientation2a : OrientationBar (𝓡∂ 1) (Icc (0 : ℝ) 1) where
  sign x := if x.val < 1 then SignType.pos else SignType.neg
  compat1 x y hy := by
    intro hsign
    by_cases hx' : x.val < 1 <;> by_cases hy' : y.val < 1 <;> simp [hx', hy'] at hsign ⊢
    · -- side computation: IccLeftChart ∘ IccLeftChart.symm = id everywhere? on source?,
      -- so argument of fderiv is id on the source, hence det = 1 > 0
      sorry
    · -- analogous computation for right charts
      sorry
  compat2 x y hy hsign := by
    by_cases hx' : x.val < 1 <;> by_cases hy' : y.val < 1 <;> simp [hx', hy'] at hsign ⊢
    · sorry -- compute IccLeftChart ∘ IccRightChart.symm, then fderiv and determinant
    · sorry -- analogous

-- Reversing an orientation.
def OrientationBar.reverse (φ : OrientationBar I M) : OrientationBar I M where
  sign x := - φ.sign x
  compat1 x y hy hsign := φ.compat1 _ _ hy (by simp_all)
  compat2 x y hy hsign := φ.compat2 _ _ hy (by simp_all)

-- open subset of orientable is orientable
-- product of orientable is orientable

lemma isOrientable_Icc {n : ℕ∞ω} : IsOrientable (𝓡∂ 1) (Icc (0 : ℝ) 1) := by
  refine ⟨?_⟩

  sorry

/-
def? pullback orientation --- sign defined by pullback; compatibility might be automatic
  actually, might want to only demand the sign change near x, but that could be fine...

f is orientation-preserving if f*O' = O holds!

lemma: f between normed-spaces is (manifold) orientation-preserving iff it has positive Jacobian
compute: id is orientation-preserving; -id iff odd-dimensional, composition
some interesting example that's bad?

(Caution: cannot do)

What do we want a definition of orientations for?
- to orient boundary components (for bordism theory and Stokes): tell us "this component points inward" and "this one outward"
  e.g., for an annulus, or a circle (outwards)
  def. given pos. oriented basis B for boundary M at x and an outward-pointing normal vector X,
  we say boundary component at x is pos. oriented if (i*B, X) is a pos oriented basis for T_xM

-/
