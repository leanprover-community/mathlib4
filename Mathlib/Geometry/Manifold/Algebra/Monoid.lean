/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathlib.Geometry.Manifold.ContMDiffMap

#align_import geometry.manifold.algebra.monoid from "leanprover-community/mathlib"@"e354e865255654389cc46e6032160238df2e0f40"

/-!
# Smooth monoid
A smooth monoid is a monoid that is also a smooth manifold, in which multiplication is a smooth map
of the product manifold `G` × `G` into `G`.

In this file we define the basic structures to talk about smooth monoids: `SmoothMul` and its
additive counterpart `SmoothAdd`. These structures are general enough to also talk about smooth
semigroups.
-/


open scoped Manifold

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
  smooth_add : Smooth (I.prod I) I fun p : G × G => p.1 + p.2
#align has_smooth_add SmoothAdd

-- See note [Design choices about smooth algebraic structures]
/-- Basic hypothesis to talk about a smooth (Lie) monoid or a smooth semigroup.
A smooth monoid over `G`, for example, is obtained by requiring both the instances `Monoid G`
and `SmoothMul I G`. -/
@[to_additive]
class SmoothMul {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (G : Type*)
    [Mul G] [TopologicalSpace G] [ChartedSpace H G] extends SmoothManifoldWithCorners I G :
    Prop where
  smooth_mul : Smooth (I.prod I) I fun p : G × G => p.1 * p.2
#align has_smooth_mul SmoothMul

section SmoothMul

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*} [Mul G]
  [TopologicalSpace G] [ChartedSpace H G] [SmoothMul I G] {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

section

variable (I)

@[to_additive]
theorem smooth_mul : Smooth (I.prod I) I fun p : G × G => p.1 * p.2 :=
  SmoothMul.smooth_mul
#align smooth_mul smooth_mul
#align smooth_add smooth_add

/-- If the multiplication is smooth, then it is continuous. This is not an instance for technical
reasons, see note [Design choices about smooth algebraic structures]. -/
@[to_additive "If the addition is smooth, then it is continuous. This is not an instance for
technical reasons, see note [Design choices about smooth algebraic structures]."]
theorem continuousMul_of_smooth : ContinuousMul G :=
  ⟨(smooth_mul I).continuous⟩
#align has_continuous_mul_of_smooth continuousMul_of_smooth
#align has_continuous_add_of_smooth continuousAdd_of_smooth

end

section

variable {f g : M → G} {s : Set M} {x : M} {n : ℕ∞}

@[to_additive]
theorem ContMDiffWithinAt.mul (hf : ContMDiffWithinAt I' I n f s x)
    (hg : ContMDiffWithinAt I' I n g s x) : ContMDiffWithinAt I' I n (f * g) s x :=
  ((smooth_mul I).smoothAt.of_le le_top).comp_contMDiffWithinAt x (hf.prod_mk hg)
#align cont_mdiff_within_at.mul ContMDiffWithinAt.mul
#align cont_mdiff_within_at.add ContMDiffWithinAt.add

@[to_additive]
nonrec theorem ContMDiffAt.mul (hf : ContMDiffAt I' I n f x) (hg : ContMDiffAt I' I n g x) :
    ContMDiffAt I' I n (f * g) x :=
  hf.mul hg
#align cont_mdiff_at.mul ContMDiffAt.mul
#align cont_mdiff_at.add ContMDiffAt.add

@[to_additive]
theorem ContMDiffOn.mul (hf : ContMDiffOn I' I n f s) (hg : ContMDiffOn I' I n g s) :
    ContMDiffOn I' I n (f * g) s := fun x hx => (hf x hx).mul (hg x hx)
#align cont_mdiff_on.mul ContMDiffOn.mul
#align cont_mdiff_on.add ContMDiffOn.add

@[to_additive]
theorem ContMDiff.mul (hf : ContMDiff I' I n f) (hg : ContMDiff I' I n g) :
    ContMDiff I' I n (f * g) := fun x => (hf x).mul (hg x)
#align cont_mdiff.mul ContMDiff.mul
#align cont_mdiff.add ContMDiff.add

@[to_additive]
nonrec theorem SmoothWithinAt.mul (hf : SmoothWithinAt I' I f s x)
    (hg : SmoothWithinAt I' I g s x) : SmoothWithinAt I' I (f * g) s x :=
  hf.mul hg
#align smooth_within_at.mul SmoothWithinAt.mul
#align smooth_within_at.add SmoothWithinAt.add

@[to_additive]
nonrec theorem SmoothAt.mul (hf : SmoothAt I' I f x) (hg : SmoothAt I' I g x) :
    SmoothAt I' I (f * g) x :=
  hf.mul hg
#align smooth_at.mul SmoothAt.mul
#align smooth_at.add SmoothAt.add

@[to_additive]
nonrec theorem SmoothOn.mul (hf : SmoothOn I' I f s) (hg : SmoothOn I' I g s) :
    SmoothOn I' I (f * g) s :=
  hf.mul hg
#align smooth_on.mul SmoothOn.mul
#align smooth_on.add SmoothOn.add

@[to_additive]
nonrec theorem Smooth.mul (hf : Smooth I' I f) (hg : Smooth I' I g) : Smooth I' I (f * g) :=
  hf.mul hg
#align smooth.mul Smooth.mul
#align smooth.add Smooth.add

@[to_additive]
theorem smooth_mul_left {a : G} : Smooth I I fun b : G => a * b :=
  smooth_const.mul smooth_id
#align smooth_mul_left smooth_mul_left
#align smooth_add_left smooth_add_left

@[to_additive]
theorem smooth_mul_right {a : G} : Smooth I I fun b : G => b * a :=
  smooth_id.mul smooth_const
#align smooth_mul_right smooth_mul_right
#align smooth_add_right smooth_add_right

end

variable (I) (g h : G)

/-- Left multiplication by `g`. It is meant to mimic the usual notation in Lie groups.
Lemmas involving `smoothLeftMul` with the notation `𝑳` usually use `L` instead of `𝑳` in the
names. -/
def smoothLeftMul : C^∞⟮I, G; I, G⟯ :=
  ⟨leftMul g, smooth_mul_left⟩
#align smooth_left_mul smoothLeftMul

/-- Right multiplication by `g`. It is meant to mimic the usual notation in Lie groups.
Lemmas involving `smoothRightMul` with the notation `𝑹` usually use `R` instead of `𝑹` in the
names. -/
def smoothRightMul : C^∞⟮I, G; I, G⟯ :=
  ⟨rightMul g, smooth_mul_right⟩
#align smooth_right_mul smoothRightMul

-- Left multiplication. The abbreviation is `MIL`.
scoped[LieGroup] notation "𝑳" => smoothLeftMul

-- Right multiplication. The abbreviation is `MIR`.
scoped[LieGroup] notation "𝑹" => smoothRightMul

open scoped LieGroup

@[simp]
theorem L_apply : (𝑳 I g) h = g * h :=
  rfl
set_option linter.uppercaseLean3 false in
#align L_apply L_apply

@[simp]
theorem R_apply : (𝑹 I g) h = h * g :=
  rfl
set_option linter.uppercaseLean3 false in
#align R_apply R_apply

@[simp]
theorem L_mul {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H G] [SmoothMul I G]
    (g h : G) : 𝑳 I (g * h) = (𝑳 I g).comp (𝑳 I h) := by
  ext
  simp only [ContMDiffMap.comp_apply, L_apply, mul_assoc]
set_option linter.uppercaseLean3 false in
#align L_mul L_mul

@[simp]
theorem R_mul {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H G] [SmoothMul I G]
    (g h : G) : 𝑹 I (g * h) = (𝑹 I h).comp (𝑹 I g) := by
  ext
  simp only [ContMDiffMap.comp_apply, R_apply, mul_assoc]
set_option linter.uppercaseLean3 false in
#align R_mul R_mul

section

variable {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ChartedSpace H G'] [SmoothMul I G']
  (g' : G')

theorem smoothLeftMul_one : (𝑳 I g') 1 = g' :=
  mul_one g'
#align smooth_left_mul_one smoothLeftMul_one

theorem smoothRightMul_one : (𝑹 I g') 1 = g' :=
  one_mul g'
#align smooth_right_mul_one smoothRightMul_one

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
      ((smooth_fst.comp smooth_fst).smooth.mul (smooth_fst.comp smooth_snd)).prod_mk
        ((smooth_snd.comp smooth_fst).smooth.mul (smooth_snd.comp smooth_snd)) }
#align has_smooth_mul.prod SmoothMul.prod
#align has_smooth_add.sum SmoothAdd.sum

end SmoothMul

section Monoid

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*} [Monoid G]
  [TopologicalSpace G] [ChartedSpace H G] [SmoothMul I G] {H' : Type*} [TopologicalSpace H']
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {I' : ModelWithCorners 𝕜 E' H'}
  {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ChartedSpace H' G'] [SmoothMul I' G']

@[to_additive]
theorem smooth_pow : ∀ n : ℕ, Smooth I I fun a : G => a ^ n
  | 0 => by simp only [pow_zero]; exact smooth_const
  | k + 1 => by simpa [pow_succ] using smooth_id.mul (smooth_pow _)
#align smooth_pow smooth_pow

/-- Morphism of additive smooth monoids. -/
structure SmoothAddMonoidMorphism (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [AddMonoid G] [SmoothAdd I G]
    (G' : Type*) [TopologicalSpace G'] [ChartedSpace H' G'] [AddMonoid G']
    [SmoothAdd I' G'] extends G →+ G' where
  smooth_toFun : Smooth I I' toFun
#align smooth_add_monoid_morphism SmoothAddMonoidMorphism

/-- Morphism of smooth monoids. -/
@[to_additive]
structure SmoothMonoidMorphism (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [Monoid G] [SmoothMul I G] (G' : Type*)
    [TopologicalSpace G'] [ChartedSpace H' G'] [Monoid G'] [SmoothMul I' G'] extends
    G →* G' where
  smooth_toFun : Smooth I I' toFun
#align smooth_monoid_morphism SmoothMonoidMorphism

@[to_additive]
instance : One (SmoothMonoidMorphism I I' G G') :=
  ⟨{  smooth_toFun := smooth_const
      toMonoidHom := 1 }⟩

@[to_additive]
instance : Inhabited (SmoothMonoidMorphism I I' G G') :=
  ⟨1⟩

@[to_additive]
instance : NDFunLike (SmoothMonoidMorphism I I' G G') G G' where
  coe a := a.toFun
  coe_injective' f g h := by cases f; cases g; congr; exact FunLike.ext' h

@[to_additive]
instance : MonoidHomClass (SmoothMonoidMorphism I I' G G') G G' where
  map_one f := f.map_one
  map_mul f := f.map_mul

@[to_additive]
instance : ContinuousMapClass (SmoothMonoidMorphism I I' G G') G G' where
  map_continuous f := f.smooth_toFun.continuous

end Monoid

section CommMonoid

open scoped BigOperators

variable {ι 𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*} [CommMonoid G]
  [TopologicalSpace G] [ChartedSpace H G] [SmoothMul I G] {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] {s : Set M} {x : M} {t : Finset ι}
  {f : ι → M → G} {n : ℕ∞} {p : ι → Prop}

@[to_additive]
theorem contMDiffWithinAt_finset_prod' (h : ∀ i ∈ t, ContMDiffWithinAt I' I n (f i) s x) :
    ContMDiffWithinAt I' I n (∏ i in t, f i) s x :=
  Finset.prod_induction f (fun f => ContMDiffWithinAt I' I n f s x) (fun _ _ hf hg => hf.mul hg)
    contMDiffWithinAt_const h
#align cont_mdiff_within_at_finset_prod' contMDiffWithinAt_finset_prod'
#align cont_mdiff_within_at_finset_sum' contMDiffWithinAt_finset_sum'

@[to_additive]
theorem contMDiffAt_finset_prod' (h : ∀ i ∈ t, ContMDiffAt I' I n (f i) x) :
    ContMDiffAt I' I n (∏ i in t, f i) x :=
  contMDiffWithinAt_finset_prod' h
#align cont_mdiff_at_finset_prod' contMDiffAt_finset_prod'
#align cont_mdiff_at_finset_sum' contMDiffAt_finset_sum'

@[to_additive]
theorem contMDiffOn_finset_prod' (h : ∀ i ∈ t, ContMDiffOn I' I n (f i) s) :
    ContMDiffOn I' I n (∏ i in t, f i) s := fun x hx =>
  contMDiffWithinAt_finset_prod' fun i hi => h i hi x hx
#align cont_mdiff_on_finset_prod' contMDiffOn_finset_prod'
#align cont_mdiff_on_finset_sum' contMDiffOn_finset_sum'

@[to_additive]
theorem contMDiff_finset_prod' (h : ∀ i ∈ t, ContMDiff I' I n (f i)) :
    ContMDiff I' I n (∏ i in t, f i) := fun x => contMDiffAt_finset_prod' fun i hi => h i hi x
#align cont_mdiff_finset_prod' contMDiff_finset_prod'
#align cont_mdiff_finset_sum' contMDiff_finset_sum'

@[to_additive]
theorem contMDiffWithinAt_finset_prod (h : ∀ i ∈ t, ContMDiffWithinAt I' I n (f i) s x) :
    ContMDiffWithinAt I' I n (fun x => ∏ i in t, f i x) s x := by
  simp only [← Finset.prod_apply]
  exact contMDiffWithinAt_finset_prod' h
#align cont_mdiff_within_at_finset_prod contMDiffWithinAt_finset_prod
#align cont_mdiff_within_at_finset_sum contMDiffWithinAt_finset_sum

@[to_additive]
theorem contMDiffAt_finset_prod (h : ∀ i ∈ t, ContMDiffAt I' I n (f i) x) :
    ContMDiffAt I' I n (fun x => ∏ i in t, f i x) x :=
  contMDiffWithinAt_finset_prod h
#align cont_mdiff_at_finset_prod contMDiffAt_finset_prod
#align cont_mdiff_at_finset_sum contMDiffAt_finset_sum

@[to_additive]
theorem contMDiffOn_finset_prod (h : ∀ i ∈ t, ContMDiffOn I' I n (f i) s) :
    ContMDiffOn I' I n (fun x => ∏ i in t, f i x) s := fun x hx =>
  contMDiffWithinAt_finset_prod fun i hi => h i hi x hx
#align cont_mdiff_on_finset_prod contMDiffOn_finset_prod
#align cont_mdiff_on_finset_sum contMDiffOn_finset_sum

@[to_additive]
theorem contMDiff_finset_prod (h : ∀ i ∈ t, ContMDiff I' I n (f i)) :
    ContMDiff I' I n fun x => ∏ i in t, f i x := fun x =>
  contMDiffAt_finset_prod fun i hi => h i hi x
#align cont_mdiff_finset_prod contMDiff_finset_prod
#align cont_mdiff_finset_sum contMDiff_finset_sum

@[to_additive]
theorem smoothWithinAt_finset_prod' (h : ∀ i ∈ t, SmoothWithinAt I' I (f i) s x) :
    SmoothWithinAt I' I (∏ i in t, f i) s x :=
  contMDiffWithinAt_finset_prod' h
#align smooth_within_at_finset_prod' smoothWithinAt_finset_prod'
#align smooth_within_at_finset_sum' smoothWithinAt_finset_sum'

@[to_additive]
theorem smoothAt_finset_prod' (h : ∀ i ∈ t, SmoothAt I' I (f i) x) :
    SmoothAt I' I (∏ i in t, f i) x :=
  contMDiffAt_finset_prod' h
#align smooth_at_finset_prod' smoothAt_finset_prod'
#align smooth_at_finset_sum' smoothAt_finset_sum'

@[to_additive]
theorem smoothOn_finset_prod' (h : ∀ i ∈ t, SmoothOn I' I (f i) s) :
    SmoothOn I' I (∏ i in t, f i) s :=
  contMDiffOn_finset_prod' h
#align smooth_on_finset_prod' smoothOn_finset_prod'
#align smooth_on_finset_sum' smoothOn_finset_sum'

@[to_additive]
theorem smooth_finset_prod' (h : ∀ i ∈ t, Smooth I' I (f i)) : Smooth I' I (∏ i in t, f i) :=
  contMDiff_finset_prod' h
#align smooth_finset_prod' smooth_finset_prod'
#align smooth_finset_sum' smooth_finset_sum'

@[to_additive]
theorem smoothWithinAt_finset_prod (h : ∀ i ∈ t, SmoothWithinAt I' I (f i) s x) :
    SmoothWithinAt I' I (fun x => ∏ i in t, f i x) s x :=
  contMDiffWithinAt_finset_prod h
#align smooth_within_at_finset_prod smoothWithinAt_finset_prod
#align smooth_within_at_finset_sum smoothWithinAt_finset_sum

@[to_additive]
theorem smoothAt_finset_prod (h : ∀ i ∈ t, SmoothAt I' I (f i) x) :
    SmoothAt I' I (fun x => ∏ i in t, f i x) x :=
  contMDiffAt_finset_prod h
#align smooth_at_finset_prod smoothAt_finset_prod
#align smooth_at_finset_sum smoothAt_finset_sum

@[to_additive]
theorem smoothOn_finset_prod (h : ∀ i ∈ t, SmoothOn I' I (f i) s) :
    SmoothOn I' I (fun x => ∏ i in t, f i x) s :=
  contMDiffOn_finset_prod h
#align smooth_on_finset_prod smoothOn_finset_prod
#align smooth_on_finset_sum smoothOn_finset_sum

@[to_additive]
theorem smooth_finset_prod (h : ∀ i ∈ t, Smooth I' I (f i)) :
    Smooth I' I fun x => ∏ i in t, f i x :=
  contMDiff_finset_prod h
#align smooth_finset_prod smooth_finset_prod
#align smooth_finset_sum smooth_finset_sum

open Function Filter

@[to_additive]
theorem contMDiff_finprod (h : ∀ i, ContMDiff I' I n (f i))
    (hfin : LocallyFinite fun i => mulSupport (f i)) : ContMDiff I' I n fun x => ∏ᶠ i, f i x := by
  intro x
  rcases finprod_eventually_eq_prod hfin x with ⟨s, hs⟩
  exact (contMDiff_finset_prod (fun i _ => h i) x).congr_of_eventuallyEq hs
#align cont_mdiff_finprod contMDiff_finprod
#align cont_mdiff_finsum contMDiff_finsum

@[to_additive]
theorem contMDiff_finprod_cond (hc : ∀ i, p i → ContMDiff I' I n (f i))
    (hf : LocallyFinite fun i => mulSupport (f i)) :
    ContMDiff I' I n fun x => ∏ᶠ (i) (_ : p i), f i x := by
  simp only [← finprod_subtype_eq_finprod_cond]
  exact contMDiff_finprod (fun i => hc i i.2) (hf.comp_injective Subtype.coe_injective)
#align cont_mdiff_finprod_cond contMDiff_finprod_cond
#align cont_mdiff_finsum_cond contMDiff_finsum_cond

@[to_additive]
theorem smooth_finprod (h : ∀ i, Smooth I' I (f i))
    (hfin : LocallyFinite fun i => mulSupport (f i)) : Smooth I' I fun x => ∏ᶠ i, f i x :=
  contMDiff_finprod h hfin
#align smooth_finprod smooth_finprod
#align smooth_finsum smooth_finsum

@[to_additive]
theorem smooth_finprod_cond (hc : ∀ i, p i → Smooth I' I (f i))
    (hf : LocallyFinite fun i => mulSupport (f i)) :
    Smooth I' I fun x => ∏ᶠ (i) (_ : p i), f i x :=
  contMDiff_finprod_cond hc hf
#align smooth_finprod_cond smooth_finprod_cond
#align smooth_finsum_cond smooth_finsum_cond

end CommMonoid

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

instance hasSmoothAddSelf : SmoothAdd 𝓘(𝕜, E) E :=
  ⟨by rw [← modelWithCornersSelf_prod]; exact contDiff_add.contMDiff⟩
#align has_smooth_add_self hasSmoothAddSelf

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

@[to_additive]
nonrec theorem SmoothWithinAt.div_const (hf : SmoothWithinAt I' I f s x) :
  SmoothWithinAt I' I (fun x ↦ f x / c) s x :=
  hf.div_const c

@[to_additive]
nonrec theorem SmoothAt.div_const (hf : SmoothAt I' I f x) :
    SmoothAt I' I (fun x ↦ f x / c) x :=
  hf.div_const c

@[to_additive]
nonrec theorem SmoothOn.div_const (hf : SmoothOn I' I f s) :
    SmoothOn I' I (fun x ↦ f x / c) s :=
  hf.div_const c

@[to_additive]
nonrec theorem Smooth.div_const (hf : Smooth I' I f) : Smooth I' I (fun x ↦ f x / c) :=
  hf.div_const c

end DivConst
