/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# `C^n` monoid
A `C^n` monoid is a monoid that is also a `C^n` manifold, in which multiplication is a `C^n` map
of the product manifold `G` × `G` into `G`.

In this file we define the basic structures to talk about `C^n` monoids: `ContMDiffMul` and its
additive counterpart `ContMDiffAdd`. These structures are general enough to also talk about `C^n`
semigroups.
-/

@[expose] public section

open scoped Manifold ContDiff

library_note «Design choices about smooth algebraic structures» /--
1. All `C^n` algebraic structures on `G` are `Prop`-valued classes that extend
   `IsManifold I n G`. This way we save users from adding both
   `[IsManifold I n G]` and `[ContMDiffMul I n G]` to the assumptions. While many API
   lemmas hold true without the `IsManifold I n G` assumption, we're not aware of a
   mathematically interesting monoid on a topological manifold such that (a) the space is not a
   `IsManifold`; (b) the multiplication is `C^n` at `(a, b)` in the charts
   `extChartAt I a`, `extChartAt I b`, `extChartAt I (a * b)`.

2. Because of `ModelProd` we can't assume, e.g., that a `LieGroup` is modelled on `𝓘(𝕜, E)`. So,
   we formulate the definitions and lemmas for any model.

3. While smoothness of an operation implies its continuity, lemmas like
   `continuousMul_of_contMDiffMul` can't be instances because otherwise Lean would have to search
   for `ContMDiffMul I n G` with unknown `𝕜`, `E`, `H`, and `I : ModelWithCorners 𝕜 E H`. If users
   need `[ContinuousMul G]` in a proof about a `C^n` monoid, then they need to either add
   `[ContinuousMul G]` as an assumption (worse) or use `haveI` in the proof (better).
-/

-- See note [Design choices about smooth algebraic structures]
/-- Basic hypothesis to talk about a `C^n` (Lie) additive monoid or a `C^n` additive
semigroup. A `C^n` additive monoid over `G`, for example, is obtained by requiring both the
instances `AddMonoid G` and `ContMDiffAdd I n G`. -/
class ContMDiffAdd {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    (G : Type*) [Add G] [TopologicalSpace G] [ChartedSpace H G] : Prop
    extends IsManifold I n G where
  contMDiff_add : CMDiff n fun p : G × G ↦ p.1 + p.2

-- See note [Design choices about smooth algebraic structures]
/-- Basic hypothesis to talk about a `C^n` (Lie) monoid or a `C^n` semigroup.
A `C^n` monoid over `G`, for example, is obtained by requiring both the instances `Monoid G`
and `ContMDiffMul I n G`. -/
@[to_additive]
class ContMDiffMul {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    (G : Type*) [Mul G] [TopologicalSpace G] [ChartedSpace H G] : Prop
    extends IsManifold I n G where
  contMDiff_mul : CMDiff n fun p : G × G ↦ p.1 * p.2

section ContMDiffMul

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
  {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H G] {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

@[to_additive]
protected theorem ContMDiffMul.of_le {m n : WithTop ℕ∞} (hmn : m ≤ n)
    [h : ContMDiffMul I n G] : ContMDiffMul I m G := by
  have : IsManifold I m G := IsManifold.of_le hmn
  exact ⟨h.contMDiff_mul.of_le hmn⟩

@[to_additive]
instance {a : WithTop ℕ∞} [ContMDiffMul I ∞ G] [h : ENat.LEInfty a] : ContMDiffMul I a G :=
  ContMDiffMul.of_le h.out

@[to_additive]
instance {a : WithTop ℕ∞} [ContMDiffMul I ω G] : ContMDiffMul I a G :=
  ContMDiffMul.of_le le_top

@[to_additive]
instance [ContinuousMul G] : ContMDiffMul I 0 G := by
  constructor
  rw [contMDiff_zero_iff]
  exact continuous_mul

@[to_additive]
instance [ContMDiffMul I 2 G] : ContMDiffMul I 1 G :=
  ContMDiffMul.of_le one_le_two

section

variable (I n)

@[to_additive]
theorem contMDiff_mul [ContMDiffMul I n G] : CMDiff n fun p : G × G ↦ p.1 * p.2 :=
  ContMDiffMul.contMDiff_mul

include I n in
/-- If the multiplication is `C^n`, then it is continuous. This is not an instance for technical
reasons, see note [Design choices about smooth algebraic structures]. -/
@[to_additive /-- If the addition is `C^n`, then it is continuous. This is not an instance for
technical reasons, see note [Design choices about smooth algebraic structures]. -/]
theorem continuousMul_of_contMDiffMul [ContMDiffMul I n G] : ContinuousMul G :=
  ⟨(contMDiff_mul I n).continuous⟩

end

section

variable [ContMDiffMul I n G] {f g : M → G} {s : Set M} {x : M}

@[to_additive]
theorem ContMDiffWithinAt.mul (hf : CMDiffAt[s] n f x) (hg : CMDiffAt[s] n g x) :
    CMDiffAt[s] n (f * g) x :=
  (contMDiff_mul I n).contMDiffAt.comp_contMDiffWithinAt x (hf.prodMk hg)

@[to_additive]
nonrec theorem ContMDiffAt.mul (hf : CMDiffAt n f x) (hg : CMDiffAt n g x) : CMDiffAt n (f * g) x :=
  hf.mul hg

@[to_additive]
theorem ContMDiffOn.mul (hf : CMDiff[s] n f) (hg : CMDiff[s] n g) : CMDiff[s] n (f * g) :=
  fun x hx ↦ (hf x hx).mul (hg x hx)

@[to_additive]
theorem ContMDiff.mul (hf : CMDiff n f) (hg : CMDiff n g) : CMDiff n (f * g) :=
  fun x ↦ (hf x).mul (hg x)

@[to_additive]
theorem contMDiff_mul_left {a : G} : CMDiff n (a * ·) :=
  contMDiff_const.mul contMDiff_id

@[to_additive]
theorem contMDiffAt_mul_left {a b : G} : CMDiffAt n (a * ·) b :=
  contMDiff_mul_left.contMDiffAt

@[to_additive]
theorem contMDiff_mul_right {a : G} : CMDiff n (· * a) :=
  contMDiff_id.mul contMDiff_const

@[to_additive]
theorem contMDiffAt_mul_right {a b : G} : CMDiffAt n (· * a) b :=
  contMDiff_mul_right.contMDiffAt

end

section

variable [ContMDiffMul I 1 G]

@[to_additive]
theorem mdifferentiable_mul_left {a : G} : MDiff (a * ·) :=
  contMDiff_mul_left.mdifferentiable one_ne_zero

@[to_additive]
theorem mdifferentiableAt_mul_left {a b : G} : MDiffAt (a * ·) b :=
  contMDiffAt_mul_left.mdifferentiableAt one_ne_zero

@[to_additive]
theorem mdifferentiable_mul_right {a : G} : MDiff (· * a) :=
  contMDiff_mul_right.mdifferentiable one_ne_zero

@[to_additive]
theorem mdifferentiableAt_mul_right {a b : G} : MDiffAt (· * a) b :=
  contMDiffAt_mul_right.mdifferentiableAt one_ne_zero

end

variable (I) (g h : G)
variable [ContMDiffMul I ∞ G]

/-- Left multiplication by `g`. It is meant to mimic the usual notation in Lie groups.
Used mostly through the notation `𝑳`.
Lemmas involving `smoothLeftMul` with the notation `𝑳` usually use `L` instead of `𝑳` in the
names. -/
def smoothLeftMul : C^∞⟮I, G; I, G⟯ :=
  ⟨(g * ·), contMDiff_mul_left⟩

/-- Right multiplication by `g`. It is meant to mimic the usual notation in Lie groups.
Used mostly through the notation `𝑹`.
Lemmas involving `smoothRightMul` with the notation `𝑹` usually use `R` instead of `𝑹` in the
names. -/
def smoothRightMul : C^∞⟮I, G; I, G⟯ :=
  ⟨(· * g), contMDiff_mul_right⟩

-- Left multiplication. The abbreviation is `MIL`.
@[inherit_doc] scoped[LieGroup] notation "𝑳" => smoothLeftMul

-- Right multiplication. The abbreviation is `MIR`.
@[inherit_doc] scoped[LieGroup] notation "𝑹" => smoothRightMul

open scoped LieGroup

@[simp]
theorem L_apply : (𝑳 I g) h = g * h :=
  rfl

@[simp]
theorem R_apply : (𝑹 I g) h = h * g :=
  rfl

@[simp]
theorem L_mul {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I ∞ G]
    (g h : G) : 𝑳 I (g * h) = (𝑳 I g).comp (𝑳 I h) := by
  ext
  simp only [ContMDiffMap.comp_apply, L_apply, mul_assoc]

@[simp]
theorem R_mul {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I ∞ G]
    (g h : G) : 𝑹 I (g * h) = (𝑹 I h).comp (𝑹 I g) := by
  ext
  simp only [ContMDiffMap.comp_apply, R_apply, mul_assoc]

section

variable {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ChartedSpace H G'] [ContMDiffMul I ∞ G']
  (g' : G')

theorem smoothLeftMul_one : (𝑳 I g') 1 = g' :=
  mul_one g'

theorem smoothRightMul_one : (𝑹 I g') 1 = g' :=
  one_mul g'

end

-- Instance of product
@[to_additive prod]
instance ContMDiffMul.prod {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [Mul G]
    [ContMDiffMul I n G] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*}
    [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') (G' : Type*) [TopologicalSpace G']
    [ChartedSpace H' G'] [Mul G'] [ContMDiffMul I' n G'] : ContMDiffMul (I.prod I') n (G × G') :=
  { IsManifold.prod G G' with
    contMDiff_mul :=
      ((contMDiff_fst.comp contMDiff_fst).mul (contMDiff_fst.comp contMDiff_snd)).prodMk
        ((contMDiff_snd.comp contMDiff_fst).mul (contMDiff_snd.comp contMDiff_snd)) }

end ContMDiffMul

section Monoid

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*} [Monoid G]
  [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I n G] {H' : Type*} [TopologicalSpace H']
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {I' : ModelWithCorners 𝕜 E' H'}
  {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ChartedSpace H' G'] [ContMDiffMul I' n G']

@[to_additive]
theorem contMDiff_pow : ∀ i : ℕ, CMDiff n fun a : G ↦ a ^ i
  | 0 => by simp only [pow_zero, contMDiff_const]
  | k + 1 => by simpa [pow_succ] using (contMDiff_pow _).mul contMDiff_id

/-- Morphism of additive `C^n` monoids. -/
structure ContMDiffAddMonoidMorphism (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (n : WithTop ℕ∞) (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [AddMonoid G]
    (G' : Type*) [TopologicalSpace G'] [ChartedSpace H' G'] [AddMonoid G']
    extends G →+ G' where
  contMDiff_toFun : CMDiff n toFun

/-- Morphism of `C^n` monoids. -/
@[to_additive]
structure ContMDiffMonoidMorphism (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (n : WithTop ℕ∞) (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [Monoid G] (G' : Type*)
    [TopologicalSpace G'] [ChartedSpace H' G'] [Monoid G'] extends
    G →* G' where
  contMDiff_toFun : CMDiff n toFun

@[to_additive]
instance : One (ContMDiffMonoidMorphism I I' n G G') :=
  ⟨{  contMDiff_toFun := contMDiff_const
      toMonoidHom := 1 }⟩

@[to_additive]
instance : Inhabited (ContMDiffMonoidMorphism I I' n G G') :=
  ⟨1⟩

@[to_additive]
instance : FunLike (ContMDiffMonoidMorphism I I' n G G') G G' where
  coe a := a.toFun
  coe_injective' f g h := by cases f; cases g; congr; exact DFunLike.ext' h

@[to_additive]
instance : MonoidHomClass (ContMDiffMonoidMorphism I I' n G G') G G' where
  map_one f := f.map_one
  map_mul f := f.map_mul

@[to_additive]
instance : ContinuousMapClass (ContMDiffMonoidMorphism I I' n G G') G G' where
  map_continuous f := f.contMDiff_toFun.continuous

end Monoid

/-! ### Differentiability of finite point-wise sums and products, and powers

  Finite point-wise products (resp. sums), and powers, of `C^n` functions `M → G` (at `x`/on `s`)
  into a commutative monoid `G` are `C^n` at `x`/on `s`. -/
section CommMonoid

open Function

variable {ι 𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞} {H : Type*} [TopologicalSpace H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [CommMonoid G] [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I n G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {s : Set M} {x x₀ : M} {t : Finset ι} {f : ι → M → G} {p : ι → Prop}

@[to_additive]
theorem ContMDiffWithinAt.prod (h : ∀ i ∈ t, CMDiffAt[s] n (f i) x₀) :
    CMDiffAt[s] n (fun x ↦ ∏ i ∈ t, f i x) x₀ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [contMDiffWithinAt_const]
  | insert i K iK IH =>
    simp only [iK, Finset.prod_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i K)).mul (IH fun j hj ↦ h _ <| Finset.mem_insert_of_mem hj)

@[to_additive]
theorem contMDiffWithinAt_finprod (lf : LocallyFinite fun i ↦ mulSupport <| f i) {x₀ : M}
    (h : ∀ i, CMDiffAt[s] n (f i) x₀) :
    CMDiffAt[s] n (fun x ↦ ∏ᶠ i, f i x) x₀ :=
  let ⟨_I, hI⟩ := finprod_eventually_eq_prod lf x₀
  (ContMDiffWithinAt.prod fun i _hi ↦ h i).congr_of_eventuallyEq
    (eventually_nhdsWithin_of_eventually_nhds hI) hI.self_of_nhds

@[to_additive]
theorem contMDiffWithinAt_finset_prod' (h : ∀ i ∈ t, CMDiffAt[s] n (f i) x) :
    CMDiffAt[s] n (∏ i ∈ t, f i) x :=
  Finset.prod_induction f (fun f ↦ CMDiffAt[s] n f x) (fun _ _ hf hg ↦ hf.mul hg)
    (contMDiffWithinAt_const (c := 1)) h

@[to_additive]
theorem contMDiffWithinAt_finset_prod (h : ∀ i ∈ t, CMDiffAt[s] n (f i) x) :
    CMDiffAt[s] n (fun x ↦ ∏ i ∈ t, f i x) x := by
  simp only [← Finset.prod_apply]
  exact contMDiffWithinAt_finset_prod' h

@[to_additive]
theorem ContMDiffAt.prod (h : ∀ i ∈ t, CMDiffAt n (f i) x₀) :
    CMDiffAt n (fun x ↦ ∏ i ∈ t, f i x) x₀ := by
  simp only [← contMDiffWithinAt_univ] at *
  exact ContMDiffWithinAt.prod h

@[to_additive]
theorem contMDiffAt_finprod
    (lf : LocallyFinite fun i ↦ mulSupport <| f i) (h : ∀ i, CMDiffAt n (f i) x₀) :
    CMDiffAt n (fun x ↦ ∏ᶠ i, f i x) x₀ :=
  contMDiffWithinAt_finprod lf h

@[to_additive]
theorem contMDiffAt_finset_prod' (h : ∀ i ∈ t, CMDiffAt n (f i) x) :
    CMDiffAt n (∏ i ∈ t, f i) x :=
  contMDiffWithinAt_finset_prod' h

@[to_additive]
theorem contMDiffAt_finset_prod (h : ∀ i ∈ t, CMDiffAt n (f i) x) :
    CMDiffAt n (fun x ↦ ∏ i ∈ t, f i x) x :=
  contMDiffWithinAt_finset_prod h

@[to_additive]
theorem contMDiffOn_finprod
    (lf : LocallyFinite fun i ↦ Function.mulSupport <| f i) (h : ∀ i, CMDiff[s] n (f i)) :
    CMDiff[s] n (fun x ↦ ∏ᶠ i, f i x) := fun x hx ↦
  contMDiffWithinAt_finprod lf fun i ↦ h i x hx

@[to_additive]
theorem contMDiffOn_finset_prod' (h : ∀ i ∈ t, CMDiff[s] n (f i)) :
    CMDiff[s] n (∏ i ∈ t, f i) :=
  fun x hx ↦ contMDiffWithinAt_finset_prod' fun i hi ↦ h i hi x hx

@[to_additive]
theorem contMDiffOn_finset_prod (h : ∀ i ∈ t, CMDiff[s] n (f i)) :
    CMDiff[s] n (fun x ↦ ∏ i ∈ t, f i x) :=
  fun x hx ↦ contMDiffWithinAt_finset_prod fun i hi ↦ h i hi x hx

@[to_additive]
theorem ContMDiff.prod (h : ∀ i ∈ t, CMDiff n (f i)) :
    CMDiff n fun x ↦ ∏ i ∈ t, f i x :=
  fun x ↦ ContMDiffAt.prod fun j hj ↦ h j hj x

@[to_additive]
theorem contMDiff_finset_prod' (h : ∀ i ∈ t, CMDiff n (f i)) :
    CMDiff n (∏ i ∈ t, f i) := fun x ↦ contMDiffAt_finset_prod' fun i hi ↦ h i hi x

@[to_additive]
theorem contMDiff_finset_prod (h : ∀ i ∈ t, CMDiff n (f i)) :
    CMDiff n fun x ↦ ∏ i ∈ t, f i x :=
  fun x ↦ contMDiffAt_finset_prod fun i hi ↦ h i hi x

@[to_additive]
theorem contMDiff_finprod (h : ∀ i, CMDiff n (f i))
    (hfin : LocallyFinite fun i ↦ mulSupport (f i)) : CMDiff n fun x ↦ ∏ᶠ i, f i x :=
  fun x ↦ contMDiffAt_finprod hfin fun i ↦ h i x

@[to_additive]
theorem contMDiff_finprod_cond (hc : ∀ i, p i → CMDiff n (f i))
    (hf : LocallyFinite fun i ↦ mulSupport (f i)) :
    CMDiff n fun x ↦ ∏ᶠ (i) (_ : p i), f i x := by
  simp only [← finprod_subtype_eq_finprod_cond]
  exact contMDiff_finprod (fun i ↦ hc i i.2) (hf.comp_injective Subtype.coe_injective)

variable {g : M → G}

@[to_additive]
theorem ContMDiffWithinAt.pow (hg : CMDiffAt[s] n g x) (m : ℕ) :
    CMDiffAt[s] n (fun x ↦ g x ^ m) x :=
  (contMDiff_pow m).contMDiffAt.comp_contMDiffWithinAt x hg

@[to_additive]
nonrec theorem ContMDiffAt.pow (hg : CMDiffAt n g x) (m : ℕ) :
    CMDiffAt n (fun x ↦ g x ^ m) x :=
  hg.pow m

@[to_additive]
theorem ContMDiffOn.pow (hg : CMDiff[s] n g) (m : ℕ) :
    CMDiff[s] n (fun x ↦ g x ^ m) :=
  fun x hx ↦ (hg x hx).pow m

@[to_additive]
theorem ContMDiff.pow (hg : CMDiff n g) (m : ℕ) :
    CMDiff n (fun x ↦ g x ^ m) :=
  fun x ↦ (hg x).pow m

end CommMonoid

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {n : WithTop ℕ∞}

instance instContMDiffAddSelf : ContMDiffAdd 𝓘(𝕜, E) n E := by
  constructor
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact contDiff_add.contMDiff

end

section DivConst

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [DivInvMonoid G] [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I n G]
  {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

variable {f : M → G} {s : Set M} {x : M} (c : G)

@[to_additive]
theorem ContMDiffWithinAt.div_const (hf : CMDiffAt[s] n f x) :
    CMDiffAt[s] n (fun x ↦ f x / c) x := by
  simpa only [div_eq_mul_inv] using hf.mul contMDiffWithinAt_const

@[to_additive]
nonrec theorem ContMDiffAt.div_const (hf : CMDiffAt n f x) :
    CMDiffAt n (fun x ↦ f x / c) x :=
  hf.div_const c

@[to_additive]
theorem ContMDiffOn.div_const (hf : CMDiff[s] n f) :
    CMDiff[s] n (fun x ↦ f x / c) := fun x hx ↦ (hf x hx).div_const c

@[to_additive]
theorem ContMDiff.div_const (hf : CMDiff n f) :
    CMDiff n (fun x ↦ f x / c) := fun x ↦ (hf x).div_const c

end DivConst
