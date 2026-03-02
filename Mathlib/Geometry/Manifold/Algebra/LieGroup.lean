/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Notation

/-!
# Lie groups

A Lie group is a group that is also a `C^n` manifold, in which the group operations of
multiplication and inversion are `C^n` maps. Regularity of the group multiplication means that
multiplication is a `C^n` mapping of the product manifold `G` × `G` into `G`.

Note that, since a manifold here is not second-countable and Hausdorff, a Lie group here is not
guaranteed to be second-countable (even though it can be proved that it is Hausdorff). Note also
that Lie groups here are not necessarily finite dimensional.

## Main definitions

* `LieAddGroup I G` : a Lie additive group where `G` is a manifold on the model with corners `I`.
* `LieGroup I G` : a Lie multiplicative group where `G` is a manifold on the model with corners `I`.
* `ContMDiffInv₀`: typeclass for `C^n` manifolds with `0` and `Inv` such that inversion is `C^n`
  map at each non-zero point. This includes complete normed fields and (multiplicative) Lie groups.


## Main results
* `ContMDiff.inv`, `ContMDiff.div` and variants: point-wise inversion and division of maps `M → G`
  is `C^n`.
* `ContMDiff.inv₀` and variants: if `ContMDiffInv₀ I n N`, point-wise inversion of `C^n`
  maps `f : M → N` is `C^n` at all points at which `f` doesn't vanish.
* `ContMDiff.div₀` and variants: if also `ContMDiffMul I n N` (i.e., `N` is a Lie group except
  possibly for smoothness of inversion at `0`), similar results hold for point-wise division.
* `instNormedSpaceLieAddGroup` : a normed vector space over a nontrivially normed field
  is an additive Lie group.
* `Instances/UnitsOfNormedAlgebra` shows that the group of units of a complete normed `𝕜`-algebra
  is a multiplicative Lie group.

## Implementation notes

A priori, a Lie group here is a manifold with corners.

The definition of Lie group cannot require `I : ModelWithCorners 𝕜 E E` with the same space as the
model space and as the model vector space, as one might hope, because in the product situation,
the model space is `ModelProd E E'` and the model vector space is `E × E'`, which are not the same,
so the definition does not apply. Hence the definition should be more general, allowing
`I : ModelWithCorners 𝕜 E H`.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff

-- See note [Design choices about smooth algebraic structures]
/-- An additive Lie group is a group and a `C^n` manifold at the same time in which
the addition and negation operations are `C^n`. -/
class LieAddGroup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H)
    (n : WithTop ℕ∞) (G : Type*)
    [AddGroup G] [TopologicalSpace G] [ChartedSpace H G] : Prop extends ContMDiffAdd I n G where
  /-- Negation is smooth in an additive Lie group. -/
  contMDiff_neg : CMDiff n fun a : G => -a

-- See note [Design choices about smooth algebraic structures]
/-- A (multiplicative) Lie group is a group and a `C^n` manifold at the same time in which
the multiplication and inverse operations are `C^n`. -/
@[to_additive]
class LieGroup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H)
    (n : WithTop ℕ∞) (G : Type*)
    [Group G] [TopologicalSpace G] [ChartedSpace H G] : Prop extends ContMDiffMul I n G where
  /-- Inversion is smooth in a Lie group. -/
  contMDiff_inv : CMDiff n fun a : G => a⁻¹

/-!
  ### Smoothness of inversion, negation, division and subtraction

  Let `f : M → G` be a `C^n` function into a Lie group, then `f` is point-wise
  invertible with smooth inverse `f`. If `f` and `g` are two such functions, the quotient
  `f / g` (i.e., the point-wise product of `f` and the point-wise inverse of `g`) is also `C^n`. -/
section PointwiseDivision

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞} {G : Type*}
  [TopologicalSpace G] [ChartedSpace H G] [Group G] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

@[to_additive]
protected theorem LieGroup.of_le {m n : WithTop ℕ∞} (hmn : m ≤ n)
    [h : LieGroup I n G] : LieGroup I m G := by
  have : ContMDiffMul I m G := ContMDiffMul.of_le hmn
  exact ⟨h.contMDiff_inv.of_le hmn⟩

@[to_additive]
instance {a : WithTop ℕ∞} [LieGroup I ∞ G] [h : ENat.LEInfty a] : LieGroup I a G :=
  LieGroup.of_le h.out

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
instance {a : WithTop ℕ∞} [LieGroup I ω G] : LieGroup I a G :=
  LieGroup.of_le le_top

@[to_additive]
instance [IsTopologicalGroup G] : LieGroup I 0 G := by
  constructor
  rw [contMDiff_zero_iff]
  exact continuous_inv

@[to_additive]
instance [LieGroup I 2 G] : LieGroup I 1 G :=
  LieGroup.of_le one_le_two

variable [LieGroup I n G]

section

variable (I n)

/-- In a Lie group, inversion is `C^n`. -/
@[to_additive /-- In an additive Lie group, inversion is a smooth map. -/]
theorem contMDiff_inv : CMDiff n fun x : G => x⁻¹ :=
  LieGroup.contMDiff_inv

include I n in
/-- A Lie group is a topological group. This is not an instance for technical reasons,
see note [Design choices about smooth algebraic structures]. -/
@[to_additive /-- An additive Lie group is an additive topological group. This is not an instance
for technical reasons, see note [Design choices about smooth algebraic structures]. -/]
theorem topologicalGroup_of_lieGroup : IsTopologicalGroup G :=
  { continuousMul_of_contMDiffMul I n with continuous_inv := (contMDiff_inv I n).continuous }

end

@[to_additive]
theorem ContMDiffWithinAt.inv {f : M → G} {s : Set M} {x₀ : M}
    (hf : CMDiffAt[s] n f x₀) : CMDiffAt[s] n (fun x => (f x)⁻¹) x₀ :=
  (contMDiff_inv I n).contMDiffAt.contMDiffWithinAt.comp x₀ hf <| Set.mapsTo_univ _ _

@[to_additive]
theorem ContMDiffAt.inv {f : M → G} {x₀ : M} (hf : CMDiffAt n f x₀) :
    CMDiffAt n (fun x => (f x)⁻¹) x₀ :=
  (contMDiff_inv I n).contMDiffAt.comp x₀ hf

@[to_additive]
theorem ContMDiffOn.inv {f : M → G} {s : Set M} (hf : CMDiff[s] n f) :
    CMDiff[s] n (fun x => (f x)⁻¹) := fun x hx => (hf x hx).inv

@[to_additive]
theorem ContMDiff.inv {f : M → G} (hf : CMDiff n f) : CMDiff n fun x => (f x)⁻¹ :=
  fun x => (hf x).inv

@[to_additive]
theorem ContMDiffWithinAt.div {f g : M → G} {s : Set M} {x₀ : M}
    (hf : CMDiffAt[s] n f x₀) (hg : CMDiffAt[s] n g x₀) :
    CMDiffAt[s] n (fun x => f x / g x) x₀ := by
  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

@[to_additive]
theorem ContMDiffAt.div {f g : M → G} {x₀ : M} (hf : CMDiffAt n f x₀)
    (hg : CMDiffAt n g x₀) : CMDiffAt n (fun x => f x / g x) x₀ := by
  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

@[to_additive]
theorem ContMDiffOn.div {f g : M → G} {s : Set M} (hf : CMDiff[s] n f)
    (hg : CMDiff[s] n g) : CMDiff[s] n (fun x => f x / g x) := by
  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

@[to_additive]
theorem ContMDiff.div {f g : M → G} (hf : CMDiff n f) (hg : CMDiff n g) :
    CMDiff n fun x => f x / g x := by simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

end PointwiseDivision

/-! Binary product of Lie groups -/
section Product

-- Instance of product group
@[to_additive]
instance Prod.instLieGroup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
    {H : Type*} [TopologicalSpace H] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*}
    [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I n G] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners 𝕜 E' H'} {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G']
    [Group G'] [LieGroup I' n G'] : LieGroup (I.prod I') n (G × G') :=
  { ContMDiffMul.prod _ _ _ _ with contMDiff_inv := contMDiff_fst.inv.prodMk contMDiff_snd.inv }

end Product

/-! ### Normed spaces are Lie groups -/

instance instNormedSpaceLieAddGroup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] : LieAddGroup 𝓘(𝕜, E) n E where
  contMDiff_neg := contDiff_neg.contMDiff

/-! ## `C^n` manifolds with `C^n` inversion away from zero

Typeclass for `C^n` manifolds with `0` and `Inv` such that inversion is `C^n` at all non-zero
points. (This includes multiplicative Lie groups, but also complete normed semifields.)
Point-wise inversion is `C^n` when the function/denominator is non-zero. -/
section ContMDiffInv₀

-- See note [Design choices about smooth algebraic structures]
/-- A `C^n` manifold with `0` and `Inv` such that `fun x ↦ x⁻¹` is `C^n` at all nonzero points.
Any complete normed (semi)field has this property. -/
class ContMDiffInv₀ {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H)
    (n : WithTop ℕ∞) (G : Type*)
    [Inv G] [Zero G] [TopologicalSpace G] [ChartedSpace H G] : Prop where
  /-- Inversion is `C^n` away from `0`. -/
  contMDiffAt_inv₀ : ∀ ⦃x : G⦄, x ≠ 0 → CMDiffAt n (fun (y : G) ↦ y⁻¹) x

instance {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞} : ContMDiffInv₀ 𝓘(𝕜) n 𝕜 where
  contMDiffAt_inv₀ x hx := by
    change ContMDiffAt 𝓘(𝕜) 𝓘(𝕜) n Inv.inv x
    rw [contMDiffAt_iff_contDiffAt]
    exact contDiffAt_inv 𝕜 hx

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*}
  [TopologicalSpace G] [ChartedSpace H G] [Inv G] [Zero G] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {f : M → G}

protected theorem ContMDiffInv₀.of_le {m n : WithTop ℕ∞} (hmn : m ≤ n)
    [h : ContMDiffInv₀ I n G] : ContMDiffInv₀ I m G := by
  exact ⟨fun x hx ↦ (h.contMDiffAt_inv₀ hx).of_le hmn⟩

instance {a : WithTop ℕ∞} [ContMDiffInv₀ I ∞ G] [h : ENat.LEInfty a] : ContMDiffInv₀ I a G :=
  ContMDiffInv₀.of_le h.out

set_option backward.isDefEq.respectTransparency false in
instance {a : WithTop ℕ∞} [ContMDiffInv₀ I ω G] : ContMDiffInv₀ I a G :=
  ContMDiffInv₀.of_le le_top

instance [ContinuousInv₀ G] : ContMDiffInv₀ I 0 G := by
  have : T1Space G := I.t1Space G
  constructor
  have A : CMDiff[{0}ᶜ] 0 (fun (x : G) ↦ x⁻¹) := by
    rw [contMDiffOn_zero_iff]
    exact continuousOn_inv₀
  intro x hx
  have : ContMDiffWithinAt I I 0 (fun (x : G) ↦ x⁻¹) {0}ᶜ x := A x hx
  apply ContMDiffWithinAt.contMDiffAt this
  exact IsOpen.mem_nhds isOpen_compl_singleton hx

instance [ContMDiffInv₀ I 2 G] : ContMDiffInv₀ I 1 G :=
  ContMDiffInv₀.of_le one_le_two

variable [ContMDiffInv₀ I n G]

theorem contMDiffAt_inv₀ {x : G} (hx : x ≠ 0) : ContMDiffAt I I n (fun y ↦ y⁻¹) x :=
  ContMDiffInv₀.contMDiffAt_inv₀ hx

include I n in
/-- In a manifold with `C^n` inverse away from `0`, the inverse is continuous away from `0`.
This is not an instance for technical reasons, see
note [Design choices about smooth algebraic structures]. -/
theorem continuousInv₀_of_contMDiffInv₀ : ContinuousInv₀ G :=
  { continuousAt_inv₀ := fun _ hx ↦ (contMDiffAt_inv₀ (I := I) (n := n) hx).continuousAt }

@[deprecated (since := "2025-09-01")] alias hasContinuousInv₀_of_hasContMDiffInv₀ :=
  continuousInv₀_of_contMDiffInv₀

theorem contMDiffOn_inv₀ : CMDiff[{0}ᶜ] n (Inv.inv : G → G) := fun _x hx =>
  (contMDiffAt_inv₀ hx).contMDiffWithinAt

variable {s : Set M} {a : M}

theorem ContMDiffWithinAt.inv₀ (hf : CMDiffAt[s] n f a) (ha : f a ≠ 0) :
    CMDiffAt[s] n (fun x => (f x)⁻¹) a :=
  (contMDiffAt_inv₀ ha).comp_contMDiffWithinAt a hf

theorem ContMDiffAt.inv₀ (hf : CMDiffAt n f a) (ha : f a ≠ 0) : CMDiffAt n (fun x ↦ (f x)⁻¹) a :=
  (contMDiffAt_inv₀ ha).comp a hf

theorem ContMDiff.inv₀ (hf : CMDiff n f) (h0 : ∀ x, f x ≠ 0) :
    CMDiff n (fun x ↦ (f x)⁻¹) :=
  fun x ↦ ContMDiffAt.inv₀ (hf x) (h0 x)

theorem ContMDiffOn.inv₀ (hf : CMDiff[s] n f) (h0 : ∀ x ∈ s, f x ≠ 0) :
    CMDiff[s] n (fun x => (f x)⁻¹) :=
  fun x hx ↦ ContMDiffWithinAt.inv₀ (hf x hx) (h0 x hx)

end ContMDiffInv₀

/-! ### Point-wise division of `C^n` functions

If `[ContMDiffMul I n N]` and `[ContMDiffInv₀ I n N]`, point-wise division of `C^n`
functions `f : M → N` is `C^n` whenever the denominator is non-zero.
(This includes `N` being a completely normed field.)
-/
section Div

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
{H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*}
  [TopologicalSpace G] [ChartedSpace H G] [GroupWithZero G] [ContMDiffInv₀ I n G]
  [ContMDiffMul I n G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {f g : M → G} {s : Set M} {a : M}

theorem ContMDiffWithinAt.div₀
    (hf : CMDiffAt[s] n f a) (hg : CMDiffAt[s] n g a) (h₀ : g a ≠ 0) : CMDiffAt[s] n (f / g) a := by
  simpa [div_eq_mul_inv] using hf.mul (hg.inv₀ h₀)

theorem ContMDiffOn.div₀ (hf : CMDiff[s] n f) (hg : CMDiff[s] n g)
    (h₀ : ∀ x ∈ s, g x ≠ 0) : CMDiff[s] n (f / g) := by
  simpa [div_eq_mul_inv] using hf.mul (hg.inv₀ h₀)

theorem ContMDiffAt.div₀ (hf : CMDiffAt n f a) (hg : CMDiffAt n g a)
    (h₀ : g a ≠ 0) : CMDiffAt n (f / g) a := by
  simpa [div_eq_mul_inv] using hf.mul (hg.inv₀ h₀)

theorem ContMDiff.div₀ (hf : CMDiff n f) (hg : CMDiff n g) (h₀ : ∀ x, g x ≠ 0) :
    CMDiff n (f / g) := by simpa only [div_eq_mul_inv] using hf.mul (hg.inv₀ h₀)

end Div
