/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Smooth monoid
A smooth monoid is a monoid that is also a smooth manifold, in which multiplication is a smooth map
of the product manifold `G` × `G` into `G`.

In this file we define the basic structures to talk about smooth monoids: `SmoothMul` and its
additive counterpart `SmoothAdd`. These structures are general enough to also talk about smooth
semigroups.
-/


open scoped Manifold
/- Next line is necessary while the manifold smoothness class is not extended to `ω`.
Later, replace with `open scoped ContDiff`. -/
local notation "∞" => (⊤ : ℕ∞)

library_note "Design choices about smooth algebraic structures"/--
1. All smooth algebraic structures on `G` are `Prop`-valued classes that extend
`SmoothManifoldWithCorners I G`. This way we save users from adding both
`[SmoothManifoldWithCorners I G]` and `[SmoothMul I G]` to the assumptions. While many API
lemmas hold true without the `SmoothManifoldWithCorners I G` assumption, we're not aware of a
mathematically interesting monoid on a topological manifold such that (a) the space is not a
`SmoothManifoldWithCorners`; (b) the multiplication is smooth at `(a, b)` in the charts
`extChartAt I a`, `extChartAt I b`, `extChartAt I (a * b)`.

2. Because of `ModelProd` we can't assume, e.g., that a `LieGroup` is modelled on `𝓘(𝕜, E)`. So,
we formulate the definitions and lemmas for any model.

3. While smoothness of an operation implies its continuity, lemmas like
`continuousMul_of_smooth` can't be instances becausen otherwise Lean would have to search for
`SmoothMul I G` with unknown `𝕜`, `E`, `H`, and `I : ModelWithCorners 𝕜 E H`. If users needs
`[ContinuousMul G]` in a proof about a smooth monoid, then they need to either add
`[ContinuousMul G]` as an assumption (worse) or use `haveI` in the proof (better). -/

-- See note [Design choices about smooth algebraic structures]
/-- Basic hypothesis to talk about a smooth (Lie) additive monoid or a smooth additive
semigroup. A smooth additive monoid over `α`, for example, is obtained by requiring both the
instances `AddMonoid α` and `SmoothAdd α`. -/
class SmoothAdd {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (G : Type*)
    [Add G] [TopologicalSpace G] [ChartedSpace H G] extends SmoothManifoldWithCorners I G :
    Prop where
  smooth_add : ContMDiff (I.prod I) I ⊤ fun p : G × G => p.1 + p.2

-- See note [Design choices about smooth algebraic structures]
/-- Basic hypothesis to talk about a smooth (Lie) monoid or a smooth semigroup.
A smooth monoid over `G`, for example, is obtained by requiring both the instances `Monoid G`
and `SmoothMul I G`. -/
@[to_additive]
class SmoothMul {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (G : Type*)
    [Mul G] [TopologicalSpace G] [ChartedSpace H G] extends SmoothManifoldWithCorners I G :
    Prop where
  smooth_mul : ContMDiff (I.prod I) I ⊤ fun p : G × G => p.1 * p.2

section SmoothMul

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*} [Mul G]
  [TopologicalSpace G] [ChartedSpace H G] [SmoothMul I G] {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

section

variable (I)

@[to_additive]
theorem contMDiff_mul : ContMDiff (I.prod I) I ⊤ fun p : G × G => p.1 * p.2 :=
  SmoothMul.smooth_mul

@[deprecated (since := "2024-11-20")] alias smooth_mul := contMDiff_mul
@[deprecated (since := "2024-11-20")] alias smooth_add := contMDiff_add

include I in
/-- If the multiplication is smooth, then it is continuous. This is not an instance for technical
reasons, see note [Design choices about smooth algebraic structures]. -/
@[to_additive "If the addition is smooth, then it is continuous. This is not an instance for
technical reasons, see note [Design choices about smooth algebraic structures]."]
theorem continuousMul_of_smooth : ContinuousMul G :=
  ⟨(contMDiff_mul I).continuous⟩

end

section

variable {f g : M → G} {s : Set M} {x : M} {n : ℕ∞}

@[to_additive]
theorem ContMDiffWithinAt.mul (hf : ContMDiffWithinAt I' I n f s x)
    (hg : ContMDiffWithinAt I' I n g s x) : ContMDiffWithinAt I' I n (f * g) s x :=
  ((contMDiff_mul I).contMDiffAt.of_le le_top).comp_contMDiffWithinAt x (hf.prod_mk hg)

@[to_additive]
nonrec theorem ContMDiffAt.mul (hf : ContMDiffAt I' I n f x) (hg : ContMDiffAt I' I n g x) :
    ContMDiffAt I' I n (f * g) x :=
  hf.mul hg

@[to_additive]
theorem ContMDiffOn.mul (hf : ContMDiffOn I' I n f s) (hg : ContMDiffOn I' I n g s) :
    ContMDiffOn I' I n (f * g) s := fun x hx => (hf x hx).mul (hg x hx)

@[to_additive]
theorem ContMDiff.mul (hf : ContMDiff I' I n f) (hg : ContMDiff I' I n g) :
    ContMDiff I' I n (f * g) := fun x => (hf x).mul (hg x)

@[deprecated (since := "2024-11-21")] alias SmoothWithinAt.mul := ContMDiffWithinAt.mul
@[deprecated (since := "2024-11-21")] alias SmoothAt.mul := ContMDiffAt.mul
@[deprecated (since := "2024-11-21")] alias SmoothOn.mul := ContMDiffOn.mul
@[deprecated (since := "2024-11-21")] alias Smooth.mul := ContMDiff.mul

@[deprecated (since := "2024-11-21")] alias SmoothWithinAt.add := ContMDiffWithinAt.add
@[deprecated (since := "2024-11-21")] alias SmoothAt.add := ContMDiffAt.add
@[deprecated (since := "2024-11-21")] alias SmoothOn.add := ContMDiffOn.add
@[deprecated (since := "2024-11-21")] alias Smooth.add := ContMDiff.add

@[to_additive]
theorem contMDiff_mul_left {a : G} : ContMDiff I I n (a * ·) :=
  contMDiff_const.mul contMDiff_id

@[deprecated (since := "2024-11-21")] alias smooth_mul_left := contMDiff_mul_left
@[deprecated (since := "2024-11-21")] alias smooth_add_left := contMDiff_add_left

@[to_additive]
theorem contMDiffAt_mul_left {a b : G} : ContMDiffAt I I n (a * ·) b :=
  contMDiff_mul_left.contMDiffAt

@[to_additive]
theorem mdifferentiable_mul_left {a : G} : MDifferentiable I I (a * ·) :=
  contMDiff_mul_left.mdifferentiable le_rfl

@[to_additive]
theorem mdifferentiableAt_mul_left {a b : G} : MDifferentiableAt I I (a * ·) b :=
  contMDiffAt_mul_left.mdifferentiableAt le_rfl

@[to_additive]
theorem contMDiff_mul_right {a : G} : ContMDiff I I n (· * a) :=
  contMDiff_id.mul contMDiff_const

@[deprecated (since := "2024-11-21")] alias smooth_mul_right := contMDiff_mul_right
@[deprecated (since := "2024-11-21")] alias smooth_add_right := contMDiff_add_right

@[to_additive]
theorem contMDiffAt_mul_right {a b : G} : ContMDiffAt I I n (· * a) b :=
  contMDiff_mul_right.contMDiffAt

@[to_additive]
theorem mdifferentiable_mul_right {a : G} : MDifferentiable I I (· * a) :=
  contMDiff_mul_right.mdifferentiable le_rfl

@[to_additive]
theorem mdifferentiableAt_mul_right {a b : G} : MDifferentiableAt I I (· * a) b :=
  contMDiffAt_mul_right.mdifferentiableAt le_rfl

end

variable (I) (g h : G)

/-- Left multiplication by `g`. It is meant to mimic the usual notation in Lie groups.
Lemmas involving `smoothLeftMul` with the notation `𝑳` usually use `L` instead of `𝑳` in the
names. -/
def smoothLeftMul : C^∞⟮I, G; I, G⟯ :=
  ⟨leftMul g, contMDiff_mul_left⟩

/-- Right multiplication by `g`. It is meant to mimic the usual notation in Lie groups.
Lemmas involving `smoothRightMul` with the notation `𝑹` usually use `R` instead of `𝑹` in the
names. -/
def smoothRightMul : C^∞⟮I, G; I, G⟯ :=
  ⟨rightMul g, contMDiff_mul_right⟩

-- Left multiplication. The abbreviation is `MIL`.
scoped[LieGroup] notation "𝑳" => smoothLeftMul

-- Right multiplication. The abbreviation is `MIR`.
scoped[LieGroup] notation "𝑹" => smoothRightMul

open scoped LieGroup

@[simp]
theorem L_apply : (𝑳 I g) h = g * h :=
  rfl

@[simp]
theorem R_apply : (𝑹 I g) h = h * g :=
  rfl

@[simp]
theorem L_mul {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H G] [SmoothMul I G]
    (g h : G) : 𝑳 I (g * h) = (𝑳 I g).comp (𝑳 I h) := by
  ext
  simp only [ContMDiffMap.comp_apply, L_apply, mul_assoc]

@[simp]
theorem R_mul {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H G] [SmoothMul I G]
    (g h : G) : 𝑹 I (g * h) = (𝑹 I h).comp (𝑹 I g) := by
  ext
  simp only [ContMDiffMap.comp_apply, R_apply, mul_assoc]

section

variable {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ChartedSpace H G'] [SmoothMul I G']
  (g' : G')

theorem smoothLeftMul_one : (𝑳 I g') 1 = g' :=
  mul_one g'

theorem smoothRightMul_one : (𝑹 I g') 1 = g' :=
  one_mul g'

end

-- Instance of product
@[to_additive]
instance SmoothMul.prod {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [Mul G]
    [SmoothMul I G] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*}
    [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') (G' : Type*) [TopologicalSpace G']
    [ChartedSpace H' G'] [Mul G'] [SmoothMul I' G'] : SmoothMul (I.prod I') (G × G') :=
  { SmoothManifoldWithCorners.prod G G' with
    smooth_mul :=
      ((contMDiff_fst.comp contMDiff_fst).mul (contMDiff_fst.comp contMDiff_snd)).prod_mk
        ((contMDiff_snd.comp contMDiff_fst).mul (contMDiff_snd.comp contMDiff_snd)) }

end SmoothMul

section Monoid

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*} [Monoid G]
  [TopologicalSpace G] [ChartedSpace H G] [SmoothMul I G] {H' : Type*} [TopologicalSpace H']
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {I' : ModelWithCorners 𝕜 E' H'}
  {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ChartedSpace H' G'] [SmoothMul I' G']

@[to_additive]
theorem contMDiff_pow : ∀ n : ℕ, ContMDiff I I ⊤ fun a : G => a ^ n
  | 0 => by simp only [pow_zero]; exact contMDiff_const
  | k + 1 => by simpa [pow_succ] using (contMDiff_pow _).mul contMDiff_id

@[deprecated (since := "2024-11-21")] alias smooth_pow := contMDiff_pow
@[deprecated (since := "2024-11-21")] alias smooth_nsmul := contMDiff_nsmul

/-- Morphism of additive smooth monoids. -/
structure SmoothAddMonoidMorphism (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [AddMonoid G] [SmoothAdd I G]
    (G' : Type*) [TopologicalSpace G'] [ChartedSpace H' G'] [AddMonoid G']
    [SmoothAdd I' G'] extends G →+ G' where
  smooth_toFun : ContMDiff I I' ⊤ toFun

/-- Morphism of smooth monoids. -/
@[to_additive]
structure SmoothMonoidMorphism (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [Monoid G] [SmoothMul I G] (G' : Type*)
    [TopologicalSpace G'] [ChartedSpace H' G'] [Monoid G'] [SmoothMul I' G'] extends
    G →* G' where
  smooth_toFun : ContMDiff I I' ⊤ toFun

@[to_additive]
instance : One (SmoothMonoidMorphism I I' G G') :=
  ⟨{  smooth_toFun := contMDiff_const
      toMonoidHom := 1 }⟩

@[to_additive]
instance : Inhabited (SmoothMonoidMorphism I I' G G') :=
  ⟨1⟩

@[to_additive]
instance : FunLike (SmoothMonoidMorphism I I' G G') G G' where
  coe a := a.toFun
  coe_injective' f g h := by cases f; cases g; congr; exact DFunLike.ext' h

@[to_additive]
instance : MonoidHomClass (SmoothMonoidMorphism I I' G G') G G' where
  map_one f := f.map_one
  map_mul f := f.map_mul

@[to_additive]
instance : ContinuousMapClass (SmoothMonoidMorphism I I' G G') G G' where
  map_continuous f := f.smooth_toFun.continuous

end Monoid

/-! ### Differentiability of finite point-wise sums and products

  Finite point-wise products (resp. sums) of differentiable/smooth functions `M → G` (at `x`/on `s`)
  into a commutative monoid `G` are differentiable/smooth at `x`/on `s`. -/
section CommMonoid

open Function

variable {ι 𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [CommMonoid G] [TopologicalSpace G] [ChartedSpace H G] [SmoothMul I G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {s : Set M} {x x₀ : M} {t : Finset ι} {f : ι → M → G} {n : ℕ∞} {p : ι → Prop}

@[to_additive]
theorem ContMDiffWithinAt.prod (h : ∀ i ∈ t, ContMDiffWithinAt I' I n (f i) s x₀) :
    ContMDiffWithinAt I' I n (fun x ↦ ∏ i ∈ t, f i x) s x₀ := by
  classical
  induction' t using Finset.induction_on with i K iK IH
  · simp [contMDiffWithinAt_const]
  · simp only [iK, Finset.prod_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i K)).mul (IH fun j hj ↦ h _ <| Finset.mem_insert_of_mem hj)

@[to_additive]
theorem contMDiffWithinAt_finprod (lf : LocallyFinite fun i ↦ mulSupport <| f i) {x₀ : M}
    (h : ∀ i, ContMDiffWithinAt I' I n (f i) s x₀) :
    ContMDiffWithinAt I' I n (fun x ↦ ∏ᶠ i, f i x) s x₀ :=
  let ⟨_I, hI⟩ := finprod_eventually_eq_prod lf x₀
  (ContMDiffWithinAt.prod fun i _hi ↦ h i).congr_of_eventuallyEq
    (eventually_nhdsWithin_of_eventually_nhds hI) hI.self_of_nhds

@[to_additive]
theorem contMDiffWithinAt_finset_prod' (h : ∀ i ∈ t, ContMDiffWithinAt I' I n (f i) s x) :
    ContMDiffWithinAt I' I n (∏ i ∈ t, f i) s x :=
  Finset.prod_induction f (fun f => ContMDiffWithinAt I' I n f s x) (fun _ _ hf hg => hf.mul hg)
    (contMDiffWithinAt_const (c := 1)) h

@[to_additive]
theorem contMDiffWithinAt_finset_prod (h : ∀ i ∈ t, ContMDiffWithinAt I' I n (f i) s x) :
    ContMDiffWithinAt I' I n (fun x => ∏ i ∈ t, f i x) s x := by
  simp only [← Finset.prod_apply]
  exact contMDiffWithinAt_finset_prod' h

@[to_additive]
theorem ContMDiffAt.prod (h : ∀ i ∈ t, ContMDiffAt I' I n (f i) x₀) :
    ContMDiffAt I' I n (fun x ↦ ∏ i ∈ t, f i x) x₀ := by
  simp only [← contMDiffWithinAt_univ] at *
  exact ContMDiffWithinAt.prod h

@[to_additive]
theorem contMDiffAt_finprod
    (lf : LocallyFinite fun i ↦ mulSupport <| f i) (h : ∀ i, ContMDiffAt I' I n (f i) x₀) :
    ContMDiffAt I' I n (fun x ↦ ∏ᶠ i, f i x) x₀ :=
  contMDiffWithinAt_finprod lf h

@[to_additive]
theorem contMDiffAt_finset_prod' (h : ∀ i ∈ t, ContMDiffAt I' I n (f i) x) :
    ContMDiffAt I' I n (∏ i ∈ t, f i) x :=
  contMDiffWithinAt_finset_prod' h

@[to_additive]
theorem contMDiffAt_finset_prod (h : ∀ i ∈ t, ContMDiffAt I' I n (f i) x) :
    ContMDiffAt I' I n (fun x => ∏ i ∈ t, f i x) x :=
  contMDiffWithinAt_finset_prod h

@[to_additive]
theorem contMDiffOn_finprod
    (lf : LocallyFinite fun i ↦ Function.mulSupport <| f i) (h : ∀ i, ContMDiffOn I' I n (f i) s) :
    ContMDiffOn I' I n (fun x ↦ ∏ᶠ i, f i x) s := fun x hx ↦
  contMDiffWithinAt_finprod lf fun i ↦ h i x hx

@[to_additive]
theorem contMDiffOn_finset_prod' (h : ∀ i ∈ t, ContMDiffOn I' I n (f i) s) :
    ContMDiffOn I' I n (∏ i ∈ t, f i) s := fun x hx =>
  contMDiffWithinAt_finset_prod' fun i hi => h i hi x hx

@[to_additive]
theorem contMDiffOn_finset_prod (h : ∀ i ∈ t, ContMDiffOn I' I n (f i) s) :
    ContMDiffOn I' I n (fun x => ∏ i ∈ t, f i x) s := fun x hx =>
  contMDiffWithinAt_finset_prod fun i hi => h i hi x hx

@[to_additive]
theorem ContMDiff.prod (h : ∀ i ∈ t, ContMDiff I' I n (f i)) :
    ContMDiff I' I n fun x ↦ ∏ i ∈ t, f i x :=
  fun x ↦ ContMDiffAt.prod fun j hj ↦ h j hj x

@[to_additive]
theorem contMDiff_finset_prod' (h : ∀ i ∈ t, ContMDiff I' I n (f i)) :
    ContMDiff I' I n (∏ i ∈ t, f i) := fun x => contMDiffAt_finset_prod' fun i hi => h i hi x

@[to_additive]
theorem contMDiff_finset_prod (h : ∀ i ∈ t, ContMDiff I' I n (f i)) :
    ContMDiff I' I n fun x => ∏ i ∈ t, f i x := fun x =>
  contMDiffAt_finset_prod fun i hi => h i hi x

@[to_additive]
theorem contMDiff_finprod (h : ∀ i, ContMDiff I' I n (f i))
    (hfin : LocallyFinite fun i => mulSupport (f i)) : ContMDiff I' I n fun x => ∏ᶠ i, f i x :=
  fun x ↦ contMDiffAt_finprod hfin fun i ↦ h i x

@[to_additive]
theorem contMDiff_finprod_cond (hc : ∀ i, p i → ContMDiff I' I n (f i))
    (hf : LocallyFinite fun i => mulSupport (f i)) :
    ContMDiff I' I n fun x => ∏ᶠ (i) (_ : p i), f i x := by
  simp only [← finprod_subtype_eq_finprod_cond]
  exact contMDiff_finprod (fun i => hc i i.2) (hf.comp_injective Subtype.coe_injective)

@[deprecated (since := "2024-11-21")] alias smoothAt_finprod := contMDiffAt_finprod
@[deprecated (since := "2024-11-21")] alias smoothAt_finsum := contMDiffAt_finsum

@[deprecated (since := "2024-11-21")]
alias smoothWithinAt_finset_prod' := contMDiffWithinAt_finset_prod'
@[deprecated (since := "2024-11-21")]
alias smoothWithinAt_finset_sum' := contMDiffWithinAt_finset_sum'


@[deprecated (since := "2024-11-21")]
alias smoothWithinAt_finset_prod := contMDiffWithinAt_finset_prod
@[deprecated (since := "2024-11-21")]
alias smoothWithinAt_finset_sum := contMDiffWithinAt_finset_sum

@[deprecated (since := "2024-11-21")] alias smoothAt_finset_prod' := contMDiffAt_finset_prod'
@[deprecated (since := "2024-11-21")] alias smoothAt_finset_sum' := contMDiffAt_finset_sum'

@[deprecated (since := "2024-11-21")] alias smoothAt_finset_prod := contMDiffAt_finset_prod
@[deprecated (since := "2024-11-21")] alias smoothAt_finset_sum := contMDiffAt_finset_sum

@[deprecated (since := "2024-11-21")] alias smoothOn_finset_prod' := contMDiffOn_finset_prod'
@[deprecated (since := "2024-11-21")] alias smoothOn_finset_sum' := contMDiffOn_finset_sum'

@[deprecated (since := "2024-11-21")] alias smoothOn_finset_prod := contMDiffOn_finset_prod
@[deprecated (since := "2024-11-21")] alias smoothOn_finset_sum := contMDiffOn_finset_sum

@[deprecated (since := "2024-11-21")] alias smooth_finset_prod' := contMDiffOn_finset_prod'
@[deprecated (since := "2024-11-21")] alias smooth_finset_sum' := contMDiffOn_finset_sum'

@[deprecated (since := "2024-11-21")] alias smooth_finset_prod := contMDiff_finset_prod
@[deprecated (since := "2024-11-21")] alias smooth_finset_sum := contMDiff_finset_sum

@[deprecated (since := "2024-11-21")] alias smooth_finprod := contMDiff_finprod
@[deprecated (since := "2024-11-21")] alias smooth_finsum := contMDiff_finsum

@[deprecated (since := "2024-11-21")] alias smooth_finprod_cond := contMDiff_finprod_cond
@[deprecated (since := "2024-11-21")] alias smooth_finsum_cond := contMDiff_finsum_cond

end CommMonoid

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

instance hasSmoothAddSelf : SmoothAdd 𝓘(𝕜, E) E := by
  constructor
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact contDiff_add.contMDiff

end

section DivConst

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [DivInvMonoid G] [TopologicalSpace G] [ChartedSpace H G] [SmoothMul I G]
  {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

variable {f : M → G} {s : Set M} {x : M} {n : ℕ∞} (c : G)

@[to_additive]
theorem ContMDiffWithinAt.div_const (hf : ContMDiffWithinAt I' I n f s x) :
    ContMDiffWithinAt I' I n (fun x ↦ f x / c) s x := by
  simpa only [div_eq_mul_inv] using hf.mul contMDiffWithinAt_const

@[to_additive]
nonrec theorem ContMDiffAt.div_const (hf : ContMDiffAt I' I n f x) :
    ContMDiffAt I' I n (fun x ↦ f x / c) x :=
  hf.div_const c

@[to_additive]
theorem ContMDiffOn.div_const (hf : ContMDiffOn I' I n f s) :
    ContMDiffOn I' I n (fun x ↦ f x / c) s := fun x hx => (hf x hx).div_const c

@[to_additive]
theorem ContMDiff.div_const (hf : ContMDiff I' I n f) :
    ContMDiff I' I n (fun x ↦ f x / c) := fun x => (hf x).div_const c

@[deprecated (since := "2024-11-21")] alias SmoothWithinAt.div_const := ContMDiffWithinAt.div_const
@[deprecated (since := "2024-11-21")] alias SmoothAt.div_const := ContMDiffAt.div_const
@[deprecated (since := "2024-11-21")] alias SmoothOn.div_const := ContMDiffOn.div_const
@[deprecated (since := "2024-11-21")] alias Smooth.div_const := ContMDiff.div_const

end DivConst
