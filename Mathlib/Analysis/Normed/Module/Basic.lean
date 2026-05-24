/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.MulAction

/-!
# Normed spaces

In this file we define (semi)normed spaces and algebras. We also prove some theorems
about these definitions.
-/

@[expose] public section

variable {𝕜 𝕜' E F α : Type*}

open Filter Metric Function Set Topology Bornology
open scoped NNReal ENNReal uniformity

section SeminormedAddCommGroup

-- Here, we set a rather high priority for the instance `[NormedSpace 𝕜 E] : Module 𝕜 E`
-- to take precedence over `Semiring.toModule` as this leads to instance paths with better
-- unification properties.
/-- A normed space over a normed field is a vector space endowed with a norm which satisfies the
equality `‖c • x‖ = ‖c‖ ‖x‖`. We require only `‖c • x‖ ≤ ‖c‖ ‖x‖` in the definition, then prove
`‖c • x‖ = ‖c‖ ‖x‖` in `norm_smul`.

Note that since this requires `SeminormedAddCommGroup` and not `NormedAddCommGroup`, this
typeclass can be used for "seminormed spaces" too, just as `Module` can be used for
"semimodules". -/
@[ext]
class NormedSpace (𝕜 : Type*) (E : Type*) [NormedField 𝕜] [NormPseudoMetric E] [AddCommGroup E] [IsNormedAddGroup E]
    extends Module 𝕜 E where
  protected norm_smul_le : ∀ (a : 𝕜) (b : E), ‖a • b‖ ≤ ‖a‖ * ‖b‖

attribute [inherit_doc NormedSpace] NormedSpace.norm_smul_le

variable [NormedField 𝕜] [NormPseudoMetric E] [AddCommGroup E] [IsNormedAddGroup E] [NormPseudoMetric F] [AddCommGroup F] [IsNormedAddGroup F]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

-- see Note [lower instance priority]
instance (priority := 100) NormedSpace.toNormSMulClass : NormSMulClass 𝕜 E :=
  haveI : IsBoundedSMul 𝕜 E := .of_norm_smul_le NormedSpace.norm_smul_le
  NormedDivisionRing.toNormSMulClass

/-- This is a shortcut instance, which was found to help with performance in
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Normed.20modules/near/516757412.

It is implied via `NormedSpace.toNormSMulClass`. -/
instance NormedSpace.toIsBoundedSMul : IsBoundedSMul 𝕜 E := inferInstance

instance NormedField.toNormedSpace : NormedSpace 𝕜 𝕜 where norm_smul_le a b := norm_mul_le a b

variable (𝕜) in
theorem norm_zsmul (n : ℤ) (x : E) : ‖n • x‖ = ‖(n : 𝕜)‖ * ‖x‖ := by
  rw [← norm_smul, ← Int.smul_one_eq_cast, smul_assoc, one_smul]

theorem norm_intCast_eq_abs_mul_norm_one (α) [SeminormedRing α] [NormSMulClass ℤ α] (n : ℤ) :
    ‖(n : α)‖ = |n| * ‖(1 : α)‖ := by
  rw [← zsmul_one, norm_smul, Int.norm_eq_abs, Int.cast_abs]

theorem norm_natCast_eq_mul_norm_one (α) [SeminormedRing α] [NormSMulClass ℤ α] (n : ℕ) :
    ‖(n : α)‖ = n * ‖(1 : α)‖ := by
  simpa using norm_intCast_eq_abs_mul_norm_one α n

@[simp]
lemma norm_natCast {α : Type*} [SeminormedRing α] [NormOneClass α] [NormSMulClass ℤ α]
    (a : ℕ) : ‖(a : α)‖ = a := by
  simpa using norm_natCast_eq_mul_norm_one α a

theorem eventually_nhds_norm_smul_sub_lt (c : 𝕜) (x : E) {ε : ℝ} (h : 0 < ε) :
    ∀ᶠ y in 𝓝 x, ‖c • (y - x)‖ < ε :=
  have : Tendsto (fun y ↦ ‖c • (y - x)‖) (𝓝 x) (𝓝 0) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  this.eventually (gt_mem_nhds h)

theorem Filter.Tendsto.zero_smul_isBoundedUnder_le {f : α → 𝕜} {g : α → E} {l : Filter α}
    (hf : Tendsto f l (𝓝 0)) (hg : IsBoundedUnder (· ≤ ·) l (Norm.norm ∘ g)) :
    Tendsto (fun x => f x • g x) l (𝓝 0) :=
  hf.op_zero_isBoundedUnder_le hg (· • ·) norm_smul_le

theorem Filter.IsBoundedUnder.smul_tendsto_zero {f : α → 𝕜} {g : α → E} {l : Filter α}
    (hf : IsBoundedUnder (· ≤ ·) l (norm ∘ f)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x • g x) l (𝓝 0) :=
  hg.op_zero_isBoundedUnder_le hf (flip (· • ·)) fun x y =>
    (norm_smul_le y x).trans_eq (mul_comm _ _)

instance NormedSpace.discreteTopology_zmultiples
    {E : Type*} [NormMetric E] [AddCommGroup E] [IsNormedAddGroup E] [NormedSpace ℚ E] (e : E) :
    DiscreteTopology <| AddSubgroup.zmultiples e := by
  have : IsAddTorsionFree E := .of_module_rat E
  rcases eq_or_ne e 0 with (rfl | he)
  · rw [AddSubgroup.zmultiples_zero_eq_bot]
    exact Subsingleton.discreteTopology (α := ↑(⊥ : Subspace ℚ E))
  · rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
    refine ⟨Metric.ball 0 ‖e‖, Metric.isOpen_ball, ?_⟩
    ext ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    rw [mem_preimage, mem_ball_zero_iff, AddSubgroup.coe_mk, mem_singleton_iff, Subtype.ext_iff,
      AddSubgroup.coe_mk, AddSubgroup.coe_zero, norm_zsmul ℚ k e, Int.norm_cast_rat,
      Int.norm_eq_abs, mul_lt_iff_lt_one_left (norm_pos_iff.mpr he), ← @Int.cast_one ℝ _,
      ← Int.cast_abs, Int.cast_lt, Int.abs_lt_one_iff, smul_eq_zero, or_iff_left he]

section Real
variable {E : Type*} [NormMetric E] [AddCommGroup E] [IsNormedAddGroup E] [NormedSpace ℝ E] [Nontrivial E]

lemma Metric.diam_sphere_eq (x : E) {r : ℝ} (hr : 0 ≤ r) : diam (sphere x r) = 2 * r := by
  apply le_antisymm
    (diam_mono sphere_subset_closedBall isBounded_closedBall |>.trans <| diam_closedBall hr)
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  calc
    2 * r = dist (x + r • ‖y‖⁻¹ • y) (x - r • ‖y‖⁻¹ • y) := by
      simp [dist_eq_norm, ← two_nsmul, ← smul_assoc, norm_smul, abs_of_nonneg hr, hy, mul_assoc]
    _ ≤ diam (sphere x r) := by
      apply dist_le_diam_of_mem isBounded_sphere <;> simp [norm_smul, hy, abs_of_nonneg hr]

lemma Metric.diam_closedBall_eq (x : E) {r : ℝ} (hr : 0 ≤ r) : diam (closedBall x r) = 2 * r :=
  le_antisymm (diam_closedBall hr) <|
    diam_sphere_eq x hr |>.symm.le.trans <| diam_mono sphere_subset_closedBall isBounded_closedBall

lemma Metric.diam_ball_eq (x : E) {r : ℝ} (hr : 0 ≤ r) : diam (ball x r) = 2 * r := by
  /- This proof could be simplified with `Metric.diam_closure` and `closure_ball`,
  but we opt for this proof to minimize dependencies. -/
  refine le_antisymm (diam_ball hr) <|
    mul_le_of_forall_lt_of_nonneg (by positivity) diam_nonneg fun a ha ha' r' hr' hr'' ↦ ?_
  calc a * r' ≤ 2 * r' := by gcongr
    _ ≤ _ := by simpa only [← Metric.diam_sphere_eq x hr'.le]
      using diam_mono (sphere_subset_ball hr'') isBounded_ball

end Real

open NormedField

instance ULift.normedSpace : NormedSpace 𝕜 (ULift E) :=
  { __ := ULift.instIsNormedAddGroup (E := E),
    __ := ULift.module'
    norm_smul_le := fun s x => (norm_smul_le s x.down :) }

/-- The product of two normed spaces is a normed space, with the sup norm. -/
instance Prod.normedSpace : NormedSpace 𝕜 (E × F) :=
  { Prod.instIsNormedAddGroup (E := E) (F := F), Prod.instModule with
    norm_smul_le := fun s x => by
      simp only [norm_smul, Prod.norm_def, le_rfl] }

/-- The product of finitely many normed spaces is a normed space, with the sup norm. -/
instance Pi.normedSpace {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, NormPseudoMetric (E i)] [∀ i, AddCommGroup (E i)] [∀ i, IsNormedAddGroup (E i)]
    [∀ i, NormedSpace 𝕜 (E i)] : NormedSpace 𝕜 (∀ i, E i) where
  norm_smul_le a f := by
    simp_rw [← coe_nnnorm, ← NNReal.coe_mul, NNReal.coe_le_coe, Pi.nnnorm_def,
      NNReal.mul_finset_sup]
    exact Finset.sup_mono_fun fun _ _ => norm_smul_le a _

instance SeparationQuotient.instNormedSpace : NormedSpace 𝕜 (SeparationQuotient E) where
  norm_smul_le := norm_smul_le

instance MulOpposite.instNormedSpace : NormedSpace 𝕜 Eᵐᵒᵖ where
  norm_smul_le _ x := norm_smul_le _ x.unop

/-- A subspace of a normed space is also a normed space, with the restriction of the norm. -/
instance Submodule.normedSpace {𝕜 R : Type*} [SMul 𝕜 R] [NormedField 𝕜] [Ring R] {E : Type*}
    [NormPseudoMetric E] [AddCommGroup E] [IsNormedAddGroup E] [NormedSpace 𝕜 E] [Module R E] [IsScalarTower 𝕜 R E]
    (s : Submodule R E) : NormedSpace 𝕜 s where
  norm_smul_le c x := norm_smul_le c (x : E)

variable {S 𝕜 R E : Type*} [SMul 𝕜 R] [NormedField 𝕜] [Ring R] [NormPseudoMetric E] [AddCommGroup E] [IsNormedAddGroup E]
variable [NormedSpace 𝕜 E] [Module R E] [IsScalarTower 𝕜 R E] [SetLike S E] [AddSubgroupClass S E]
variable [SMulMemClass S R E] (s : S)

instance (priority := 75) SubmoduleClass.toNormedSpace : NormedSpace 𝕜 s where
  norm_smul_le c x := norm_smul_le c (x : E)

end SeminormedAddCommGroup

/-- A linear map from a `Module` to a `NormedSpace` induces a `NormedSpace` structure on the
domain, using the `SeminormedAddCommGroup.induced` norm.

See note [reducible non-instances] -/
abbrev NormedSpace.induced {F : Type*} (𝕜 E G : Type*) [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [NormPseudoMetric G] [AddCommGroup G] [IsNormedAddGroup G] [NormedSpace 𝕜 G] [FunLike F E G] [LinearMapClass F 𝕜 E G] (f : F) :
    letI := NormPseudoMetric.induced E G f
    letI := IsNormedAddGroup.induced E G f
    NormedSpace 𝕜 E :=
  letI := NormPseudoMetric.induced E G f
  letI := IsNormedAddGroup.induced E G f
  { norm_smul_le a b := by simpa only [← map_smul f a b] using norm_smul_le a (f b) }

section NontriviallyNormedSpace

variable (𝕜 E)
variable [NontriviallyNormedField 𝕜] [NormMetric E] [AddCommGroup E] [IsNormedAddGroup E] [NormedSpace 𝕜 E] [Nontrivial E]
include 𝕜

/-- If `E` is a nontrivial normed space over a nontrivially normed field `𝕜`, then `E` is unbounded:
for any `c : ℝ`, there exists a vector `x : E` with norm strictly greater than `c`. -/
theorem NormedSpace.exists_lt_norm (c : ℝ) : ∃ x : E, c < ‖x‖ := by
  rcases exists_ne (0 : E) with ⟨x, hx⟩
  rcases NormedField.exists_lt_norm 𝕜 (c / ‖x‖) with ⟨r, hr⟩
  use r • x
  rwa [norm_smul, ← div_lt_iff₀]
  rwa [norm_pos_iff]

protected theorem NormedSpace.unbounded_univ : ¬Bornology.IsBounded (univ : Set E) := fun h =>
  let ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 h
  let ⟨x, hx⟩ := NormedSpace.exists_lt_norm 𝕜 E R
  hx.not_ge (hR x trivial)

protected lemma NormedSpace.cobounded_neBot : NeBot (cobounded E) := by
  rw [neBot_iff, Ne, cobounded_eq_bot_iff, ← isBounded_univ]
  exact NormedSpace.unbounded_univ 𝕜 E

instance (priority := 100) NontriviallyNormedField.cobounded_neBot : NeBot (cobounded 𝕜) :=
  NormedSpace.cobounded_neBot 𝕜 𝕜

instance (priority := 80) RealNormedSpace.cobounded_neBot [NormedSpace ℝ E] :
    NeBot (cobounded E) := NormedSpace.cobounded_neBot ℝ E

instance (priority := 80) NontriviallyNormedField.infinite : Infinite 𝕜 :=
  ⟨fun _ ↦ NormedSpace.unbounded_univ 𝕜 𝕜 (Set.toFinite _).isBounded⟩

end NontriviallyNormedSpace

section NormedSpace

variable (𝕜 E)
variable [NormedField 𝕜] [Infinite 𝕜] [NormMetric E] [AddCommGroup E] [IsNormedAddGroup E] [Nontrivial E] [NormedSpace 𝕜 E]
include 𝕜

/-- A normed vector space over an infinite normed field is a noncompact space.
This cannot be an instance because in order to apply it,
Lean would have to search for `NormedSpace 𝕜 E` with unknown `𝕜`.
We register this as an instance in two cases: `𝕜 = E` and `𝕜 = ℝ`. -/
protected theorem NormedSpace.noncompactSpace : NoncompactSpace E := by
  by_cases! H : ∃ c : 𝕜, c ≠ 0 ∧ ‖c‖ ≠ 1
  · letI := NontriviallyNormedField.ofNormNeOne H
    exact ⟨fun h ↦ NormedSpace.unbounded_univ 𝕜 E h.isBounded⟩
  · rcases exists_ne (0 : E) with ⟨x, hx⟩
    suffices IsClosedEmbedding (Infinite.natEmbedding 𝕜 · • x) from this.noncompactSpace
    refine isClosedEmbedding_of_pairwise_le_dist (norm_pos_iff.2 hx) fun k n hne ↦ ?_
    simp only [dist_eq_norm, ← sub_smul, norm_smul]
    rw [H, one_mul]
    rwa [sub_ne_zero, (Embedding.injective _).ne_iff]

instance (priority := 100) NormedField.noncompactSpace : NoncompactSpace 𝕜 :=
  NormedSpace.noncompactSpace 𝕜 𝕜

instance (priority := 100) RealNormedSpace.noncompactSpace [NormedSpace ℝ E] : NoncompactSpace E :=
  NormedSpace.noncompactSpace ℝ E

end NormedSpace

section NormedAlgebra

/-- A normed algebra `𝕜'` over `𝕜` is normed module that is also an algebra.

See the implementation notes for `Algebra` for a discussion about non-unital algebras. Following
the strategy there, a non-unital *normed* algebra can be written as:
```lean
variable [NormedField 𝕜] [NonUnitalSeminormedRing 𝕜']
variable [NormedSpace 𝕜 𝕜'] [SMulCommClass 𝕜 𝕜' 𝕜'] [IsScalarTower 𝕜 𝕜' 𝕜']
```
-/
class NormedAlgebra (𝕜 : Type*) (𝕜' : Type*) [NormedField 𝕜] [SeminormedRing 𝕜'] extends
  Algebra 𝕜 𝕜' where
  norm_smul_le : ∀ (r : 𝕜) (x : 𝕜'), ‖r • x‖ ≤ ‖r‖ * ‖x‖

attribute [inherit_doc NormedAlgebra] NormedAlgebra.norm_smul_le

variable (𝕜')
variable [NormedField 𝕜] [SeminormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜']

instance (priority := 100) NormedAlgebra.toNormedSpace : NormedSpace 𝕜 𝕜' :=
  { NormedAlgebra.toAlgebra.toModule with
  norm_smul_le := NormedAlgebra.norm_smul_le }

theorem norm_algebraMap (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖ * ‖(1 : 𝕜')‖ := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact norm_smul _ _

theorem nnnorm_algebraMap (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖₊ = ‖x‖₊ * ‖(1 : 𝕜')‖₊ :=
  Subtype.ext <| norm_algebraMap 𝕜' x

theorem dist_algebraMap (x y : 𝕜) :
    (dist (algebraMap 𝕜 𝕜' x) (algebraMap 𝕜 𝕜' y)) = dist x y * ‖(1 : 𝕜')‖ := by
  simp only [dist_eq_norm, ← map_sub, norm_algebraMap]

/-- This is a simpler version of `norm_algebraMap` when `‖1‖ = 1` in `𝕜'`. -/
@[simp]
theorem norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖ := by
  rw [norm_algebraMap, norm_one, mul_one]

@[simp]
theorem Algebra.norm_smul_one_eq_norm [NormOneClass 𝕜'] (x : 𝕜) : ‖x • (1 : 𝕜')‖ = ‖x‖ := by
  simp [norm_smul]

/-- This is a simpler version of `nnnorm_algebraMap` when `‖1‖ = 1` in `𝕜'`. -/
@[simp]
theorem nnnorm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖₊ = ‖x‖₊ :=
  Subtype.ext <| norm_algebraMap' _ _

/-- This is a simpler version of `dist_algebraMap` when `‖1‖ = 1` in `𝕜'`. -/
@[simp]
theorem dist_algebraMap' [NormOneClass 𝕜'] (x y : 𝕜) :
    (dist (algebraMap 𝕜 𝕜' x) (algebraMap 𝕜 𝕜' y)) = dist x y := by
  simp only [dist_eq_norm, ← map_sub, norm_algebraMap']

section NNReal

variable [NormOneClass 𝕜'] [NormedAlgebra ℝ 𝕜']

@[simp]
theorem norm_algebraMap_nnreal (x : ℝ≥0) : ‖algebraMap ℝ≥0 𝕜' x‖ = x :=
  (norm_algebraMap' 𝕜' (x : ℝ)).symm ▸ Real.norm_of_nonneg x.prop

@[simp]
theorem nnnorm_algebraMap_nnreal (x : ℝ≥0) : ‖algebraMap ℝ≥0 𝕜' x‖₊ = x :=
  Subtype.ext <| norm_algebraMap_nnreal 𝕜' x

end NNReal

variable (𝕜)

open Filter Bornology in
/-- Preimages of cobounded sets under the algebra map are cobounded. -/
@[simp]
theorem tendsto_algebraMap_cobounded (𝕜 𝕜' : Type*) [NormedField 𝕜] [SeminormedRing 𝕜']
    [NormedAlgebra 𝕜 𝕜'] [NormOneClass 𝕜'] :
    Tendsto (algebraMap 𝕜 𝕜') (cobounded 𝕜) (cobounded 𝕜') := by
  intro c hc
  rw [mem_map]
  rw [← isCobounded_def, ← isBounded_compl_iff, isBounded_iff_forall_norm_le] at hc ⊢
  obtain ⟨s, hs⟩ := hc
  exact ⟨s, fun x hx ↦ by simpa using hs (algebraMap 𝕜 𝕜' x) hx⟩

@[deprecated (since := "2025-11-04")] alias
  algebraMap_cobounded_le_cobounded := tendsto_algebraMap_cobounded

/-- In a normed algebra, the inclusion of the base field in the extended field is an isometry. -/
theorem algebraMap_isometry [NormOneClass 𝕜'] : Isometry (algebraMap 𝕜 𝕜') := by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_algebraMap']

instance NormedAlgebra.id : NormedAlgebra 𝕜 𝕜 :=
  { NormedField.toNormedSpace, Algebra.id 𝕜 with }

/-- Any normed characteristic-zero division ring that is a normed algebra over the reals is also a
normed algebra over the rationals.

Phrased another way, if `𝕜` is a normed algebra over the reals, then `AlgebraRat` respects that
norm. -/
instance normedAlgebraRat {𝕜} [NormedDivisionRing 𝕜] [CharZero 𝕜] [NormedAlgebra ℝ 𝕜] :
    NormedAlgebra ℚ 𝕜 where
  norm_smul_le q x := by
    rw [← smul_one_smul ℝ q x, Rat.smul_one_eq_cast, norm_smul, Rat.norm_cast_real]

instance PUnit.instNormedAlgebra : NormedAlgebra 𝕜 PUnit where
  norm_smul_le q _ := by simp only [norm_eq_zero, mul_zero, le_refl]

instance : NormedAlgebra 𝕜 (ULift 𝕜') :=
  { ULift.normedSpace, ULift.algebra with }

/-- The product of two normed algebras is a normed algebra, with the sup norm. -/
instance Prod.normedAlgebra {E F : Type*} [SeminormedRing E] [SeminormedRing F] [NormedAlgebra 𝕜 E]
    [NormedAlgebra 𝕜 F] : NormedAlgebra 𝕜 (E × F) :=
  { Prod.normedSpace, Prod.algebra 𝕜 E F with }

/-- The product of finitely many normed algebras is a normed algebra, with the sup norm. -/
instance Pi.normedAlgebra {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, SeminormedRing (E i)]
    [∀ i, NormedAlgebra 𝕜 (E i)] : NormedAlgebra 𝕜 (∀ i, E i) :=
  { Pi.normedSpace, Pi.algebra _ E with }

variable [SeminormedRing E] [NormedAlgebra 𝕜 E]

instance SeparationQuotient.instNormedAlgebra : NormedAlgebra 𝕜 (SeparationQuotient E) where
  __ : NormedSpace 𝕜 (SeparationQuotient E) := inferInstance
  __ : Algebra 𝕜 (SeparationQuotient E) := inferInstance

instance MulOpposite.instNormedAlgebra {E : Type*} [SeminormedRing E] [NormedAlgebra 𝕜 E] :
    NormedAlgebra 𝕜 Eᵐᵒᵖ where
  __ := instAlgebra
  __ := instNormedSpace

end NormedAlgebra

/-- A non-unital algebra homomorphism from an `Algebra` to a `NormedAlgebra` induces a
`NormedAlgebra` structure on the domain, using the `SeminormedRing.induced` norm.

See note [reducible non-instances] -/
abbrev NormedAlgebra.induced {F : Type*} (𝕜 R S : Type*) [NormedField 𝕜] [Ring R] [Algebra 𝕜 R]
    [SeminormedRing S] [NormedAlgebra 𝕜 S] [FunLike F R S] [NonUnitalAlgHomClass F 𝕜 R S]
    (f : F) :
    letI := NormPseudoMetric.induced R S f
    letI := IsNormedRing.induced R S f
    NormedAlgebra 𝕜 R :=
  letI := NormPseudoMetric.induced R S f
  letI := IsNormedRing.induced R S f
  ⟨fun a b ↦ show ‖f (a • b)‖ ≤ ‖a‖ * ‖f b‖ from (map_smul f a b).symm ▸ norm_smul_le a (f b)⟩

instance Subalgebra.toNormedAlgebra {𝕜 A : Type*} [SeminormedRing A] [NormedField 𝕜]
    [NormedAlgebra 𝕜 A] (S : Subalgebra 𝕜 A) : NormedAlgebra 𝕜 S :=
  fast_instance% NormedAlgebra.induced 𝕜 S A S.val

section SubalgebraClass

variable {S 𝕜 E : Type*} [NormedField 𝕜] [SeminormedRing E] [NormedAlgebra 𝕜 E]
variable [SetLike S E] [SubringClass S E] [SMulMemClass S 𝕜 E] (s : S)

instance (priority := 75) SubalgebraClass.toNormedAlgebra : NormedAlgebra 𝕜 s where
  norm_smul_le c x := norm_smul_le c (x : E)

end SubalgebraClass

section RestrictScalars

section NormInstances

instance [I : Norm E] : Norm (RestrictScalars 𝕜 𝕜' E) :=
  I

instance [I : PseudoMetricSpace E] : PseudoMetricSpace (RestrictScalars 𝕜 𝕜' E) :=
  I

instance [I : MetricSpace E] : MetricSpace (RestrictScalars 𝕜 𝕜' E) where
  toPseudoMetricSpace := instPseudoMetricSpaceRestrictScalars
  eq_of_dist_eq_zero := I.eq_of_dist_eq_zero

instance [NormPseudoMetric E] : NormPseudoMetric (RestrictScalars 𝕜 𝕜' E) where

instance [NormMetric E] : NormMetric (RestrictScalars 𝕜 𝕜' E) where

instance [NormPseudoMetric E] [AddCommGroup E] [I : IsNormedAddGroup E] :
    IsNormedAddGroup (RestrictScalars 𝕜 𝕜' E) :=
  I

instance [NormPseudoMetric E] [NonUnitalRing E] [I : IsNormedRing E] :
    IsNormedRing (RestrictScalars 𝕜 𝕜' E) :=
  I

example [I : SeminormedAddCommGroup E] :
    SeminormedAddCommGroup (RestrictScalars 𝕜 𝕜' E) :=
  inferInstance

example [I : NonUnitalSeminormedRing E] :
    NonUnitalSeminormedRing (RestrictScalars 𝕜 𝕜' E) :=
  inferInstance

example [I : NonUnitalNormedRing E] :
    NonUnitalNormedRing (RestrictScalars 𝕜 𝕜' E) :=
  inferInstance

example [I : SeminormedRing E] :
    SeminormedRing (RestrictScalars 𝕜 𝕜' E) :=
  inferInstance

example [I : NormedRing E] :
    NormedRing (RestrictScalars 𝕜 𝕜' E) :=
  inferInstance

example [I : NonUnitalSeminormedCommRing E] :
    NonUnitalSeminormedCommRing (RestrictScalars 𝕜 𝕜' E) :=
  inferInstance

example [I : NonUnitalNormedCommRing E] :
    NonUnitalNormedCommRing (RestrictScalars 𝕜 𝕜' E) :=
  inferInstance

example [I : SeminormedCommRing E] :
    SeminormedCommRing (RestrictScalars 𝕜 𝕜' E) :=
  inferInstance

example [I : NormedCommRing E] :
    NormedCommRing (RestrictScalars 𝕜 𝕜' E) :=
  inferInstance

end NormInstances

section NormedSpace

variable (𝕜 𝕜' E)
variable [NormedField 𝕜] [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [NormPseudoMetric E] [AddCommGroup E] [IsNormedAddGroup E] [NormedSpace 𝕜' E]

/-- Warning: This declaration should be used judiciously.
Please consider using `IsScalarTower` instead.

This definition allows the `RestrictScalars.normedSpace` instance to be put directly on `E`
rather on `RestrictScalars 𝕜 𝕜' E`. This would be a very bad instance; both because `𝕜'` cannot be
inferred, and because it is likely to create instance diamonds.

See Note [reducible non-instances].
-/
@[implicit_reducible]
def NormedSpace.restrictScalars : NormedSpace 𝕜 E :=
  { Module.restrictScalars 𝕜 𝕜' E with
    norm_smul_le := fun c x =>
      (norm_smul_le (algebraMap 𝕜 𝕜' c) (_ : E)).trans_eq <| by rw [norm_algebraMap'] }

theorem NormedSpace.restrictScalars_eq {E : Type*} [NormPseudoMetric E] [AddCommGroup E] [IsNormedAddGroup E]
    [h : NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E] :
    NormedSpace.restrictScalars 𝕜 𝕜' E = h := by
  ext
  apply algebraMap_smul

/-- If `E` is a normed space over `𝕜'` and `𝕜` is a normed algebra over `𝕜'`, then
`RestrictScalars.module` is additionally a `NormedSpace`. -/
instance RestrictScalars.normedSpace : NormedSpace 𝕜 (RestrictScalars 𝕜 𝕜' E) :=
  fast_instance% NormedSpace.restrictScalars 𝕜 𝕜' E

-- If you think you need this, consider instead reproducing `RestrictScalars.lsmul`
-- appropriately modified here.
/-- The action of the original `NormedField` on `RestrictScalars 𝕜 𝕜' E`.
This is not an instance as it would be contrary to the purpose of `RestrictScalars`.
-/
@[implicit_reducible]
def Module.RestrictScalars.normedSpaceOrig {𝕜 : Type*} {𝕜' : Type*} {E : Type*} [NormedField 𝕜']
    [NormPseudoMetric E] [AddCommGroup E] [IsNormedAddGroup E] [I : NormedSpace 𝕜' E] : NormedSpace 𝕜' (RestrictScalars 𝕜 𝕜' E) :=
  I

end NormedSpace

section NormedAlgebra

variable (𝕜 𝕜' E)
variable [NormedField 𝕜] [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [SeminormedRing E] [NormedAlgebra 𝕜' E]

/-- Warning: This declaration should be used judiciously.
Please consider using `IsScalarTower` instead.

This definition allows the `RestrictScalars.normedAlgebra` instance to be put directly on `E`
rather on `RestrictScalars 𝕜 𝕜' E`. This would be a very bad instance; both because `𝕜'` cannot be
inferred, and because it is likely to create instance diamonds.

See Note [reducible non-instances].
-/
@[implicit_reducible]
def NormedAlgebra.restrictScalars : NormedAlgebra 𝕜 E :=
  { NormedSpace.restrictScalars 𝕜 𝕜' E, Algebra.restrictScalars 𝕜 𝕜' E with }

set_option backward.isDefEq.respectTransparency false in
/-- If `E` is a normed algebra over `𝕜'` and `𝕜` is a normed algebra over `𝕜'`, then
`RestrictScalars.module` is additionally a `NormedAlgebra`. -/
instance RestrictScalars.normedAlgebra : NormedAlgebra 𝕜 (RestrictScalars 𝕜 𝕜' E) :=
  fast_instance% NormedAlgebra.restrictScalars 𝕜 𝕜' E

-- If you think you need this, consider instead reproducing `RestrictScalars.lsmul`
-- appropriately modified here.
set_option backward.isDefEq.respectTransparency false in
/-- The action of the original `NormedField` on `RestrictScalars 𝕜 𝕜' E`.
This is not an instance as it would be contrary to the purpose of `RestrictScalars`.
-/
@[implicit_reducible]
def Module.RestrictScalars.normedAlgebraOrig {𝕜 : Type*} {𝕜' : Type*} {E : Type*} [NormedField 𝕜']
    [SeminormedRing E] [I : NormedAlgebra 𝕜' E] : NormedAlgebra 𝕜' (RestrictScalars 𝕜 𝕜' E) :=
  I
end NormedAlgebra

end RestrictScalars

section Core
/-!
### Structures for constructing new normed spaces

This section contains tools meant for constructing new normed spaces. These allow one to easily
construct all the relevant instances (distances measures, etc) while proving only a minimal
set of axioms. Furthermore, tools are provided to add a norm structure to a type that already
has a preexisting uniformity or bornology: in such cases, it is necessary to keep the preexisting
instances, while ensuring that the norm induces the same uniformity/bornology.
-/

open scoped Uniformity Bornology

/-- A structure encapsulating minimal axioms needed to defined a seminormed vector space, as found
in textbooks. This is meant to be used to easily define `SeminormedSpace E` instances from
scratch on a type with no preexisting distance or topology. -/
structure SeminormedSpace.Core (𝕜 : Type*) (E : Type*) [NormedField 𝕜] [AddCommGroup E]
    [Norm E] [Module 𝕜 E] : Prop where
  norm_nonneg (x : E) : 0 ≤ ‖x‖
  norm_smul (c : 𝕜) (x : E) : ‖c • x‖ = ‖c‖ * ‖x‖
  norm_triangle (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖

/-- Produces a `PseudoMetricSpace E` instance from a `SeminormedSpace.Core`. Note that
if this is used to define an instance on a type, it also provides a new uniformity and
topology on the type. See note [reducible non-instances]. -/
abbrev PseudoMetricSpace.ofSeminormedSpaceCore {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E]
    [Norm E] [Module 𝕜 E] (core : SeminormedSpace.Core 𝕜 E) :
    PseudoMetricSpace E where
  dist x y := ‖-x + y‖
  dist_self x := by
    show ‖-x + x‖ = 0
    simp only [add_comm, ← sub_eq_add_neg, sub_self]
    have : (0 : E) = (0 : 𝕜) • (0 : E) := by simp
    rw [this, core.norm_smul]
    simp
  dist_comm x y := by
    show ‖-x + y‖ = ‖-y + x‖
    have : -y + x = (-1 : 𝕜) • (-x + y) := by simp; abel
    rw [this, core.norm_smul]
    simp
  dist_triangle x y z := by
    show ‖-x + z‖ ≤ ‖-x + y‖ + ‖-y + z‖
    have : -x + z = (-x + y) + (-y + z) := by abel
    rw [this]
    exact core.norm_triangle _ _
  edist_dist x y := by exact (ENNReal.ofReal_eq_coe_nnreal _).symm

/-- Produces a `PseudoEMetricSpace E` instance from a `SeminormedSpace.Core`. Note that
if this is used to define an instance on a type, it also provides a new uniformity and
topology on the type. See note [reducible non-instances]. -/
abbrev PseudoEMetricSpace.ofSeminormedSpaceCore {𝕜 E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E]
    (core : SeminormedSpace.Core 𝕜 E) : PseudoEMetricSpace E :=
  (PseudoMetricSpace.ofSeminormedSpaceCore core).toPseudoEMetricSpace

/-- Produces a `PseudoMetricSpace E` instance from a `SeminormedSpace.Core` on a type that
already has an existing uniform space structure. This requires a proof that the uniformity induced
by the norm is equal to the preexisting uniformity. See note [reducible non-instances]. -/
abbrev PseudoMetricSpace.ofSeminormedSpaceCoreReplaceUniformity {𝕜 E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E]
    (core : SeminormedSpace.Core 𝕜 E)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
        (self := PseudoEMetricSpace.ofSeminormedSpaceCore core)]) :
    PseudoMetricSpace E :=
  .replaceUniformity (.ofSeminormedSpaceCore core) H

/-- Produces a `PseudoMetricSpace E` instance from a `SeminormedSpace.Core` on a type that
already has an existing topology. This requires a proof that the topology induced
by the norm is equal to the preexisting topology. See note [reducible non-instances]. -/
abbrev PseudoMetricSpace.ofSeminormedSpaceCoreReplaceTopology {𝕜 E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [T : TopologicalSpace E]
    (core : SeminormedSpace.Core 𝕜 E)
    (H : T = (PseudoEMetricSpace.ofSeminormedSpaceCore
      core).toUniformSpace.toTopologicalSpace) :
    PseudoMetricSpace E :=
  .replaceTopology (.ofSeminormedSpaceCore core) H

open Bornology in
/-- Produces a `PseudoMetricSpace E` instance from a `SeminormedSpace.Core` on a type that
already has a preexisting uniform space structure and a preexisting bornology. This requires proofs
that the uniformity induced by the norm is equal to the preexisting uniformity, and likewise for
the bornology. See note [reducible non-instances]. -/
abbrev PseudoMetricSpace.ofSeminormedSpaceCoreReplaceAll {𝕜 E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E] [B : Bornology E]
    (core : SeminormedSpace.Core 𝕜 E)
    (HU : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedSpaceCore core)])
    (HB : ∀ s : Set E, @IsBounded _ B s
      ↔ @IsBounded _ (PseudoMetricSpace.ofSeminormedSpaceCore core).toBornology s) :
    PseudoMetricSpace E :=
  .replaceBornology (.replaceUniformity (.ofSeminormedSpaceCore core) HU) HB

/-- Produces a `NormPseudoMetric E` instance from a `SeminormedSpace.Core`. Note that
if this is used to define an instance on a type, it also provides a new uniformity and
topology on the type. See note [reducible non-instances]. -/
abbrev NormPseudoMetric.ofSeminormedSpaceCore {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E]
    [Norm E] [Module 𝕜 E] (core : SeminormedSpace.Core 𝕜 E) :
    NormPseudoMetric E where
  toPseudoMetricSpace := .ofSeminormedSpaceCore core

/-- Produces a `NormPseudoMetric E` instance from a `SeminormedSpace.Core` on a type that
already has an existing uniform space structure. This requires a proof that the uniformity induced
by the norm is equal to the preexisting uniformity. See note [reducible non-instances]. -/
abbrev NormPseudoMetric.ofSeminormedSpaceCoreReplaceUniformity {𝕜 E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E]
    (core : SeminormedSpace.Core 𝕜 E)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
        (self := PseudoEMetricSpace.ofSeminormedSpaceCore core)]) :
    NormPseudoMetric E where
  toPseudoMetricSpace := .ofSeminormedSpaceCoreReplaceUniformity core H

/-- Produces a `NormPseudoMetric E` instance from a `SeminormedSpace.Core` on a type that
already has an existing topology. This requires a proof that the topology induced
by the norm is equal to the preexisting topology. See note [reducible non-instances]. -/
abbrev NormPseudoMetric.ofSeminormedSpaceCoreReplaceTopology {𝕜 E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [T : TopologicalSpace E]
    (core : SeminormedSpace.Core 𝕜 E)
    (H : T = (PseudoEMetricSpace.ofSeminormedSpaceCore
      core).toUniformSpace.toTopologicalSpace) :
    NormPseudoMetric E where
  toPseudoMetricSpace := .ofSeminormedSpaceCoreReplaceTopology core H

open Bornology in
/-- Produces a `NormPseudoMetric E` instance from a `SeminormedSpace.Core` on a type that
already has a preexisting uniform space structure and a preexisting bornology. This requires proofs
that the uniformity induced by the norm is equal to the preexisting uniformity, and likewise for
the bornology. See note [reducible non-instances]. -/
abbrev NormPseudoMetric.ofSeminormedSpaceCoreReplaceAll {𝕜 E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E] [B : Bornology E]
    (core : SeminormedSpace.Core 𝕜 E)
    (HU : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedSpaceCore core)])
    (HB : ∀ s : Set E, @IsBounded _ B s
      ↔ @IsBounded _ (PseudoMetricSpace.ofSeminormedSpaceCore core).toBornology s) :
    NormPseudoMetric E where
  toPseudoMetricSpace := .ofSeminormedSpaceCoreReplaceAll core HU HB

/-- Produces a `SeminormedAddCommGroup E` instance from a `SeminormedSpace.Core`. Note that
if this is used to define an instance on a type, it also provides a new distance measure from the
norm.  it must therefore not be used on a type with a preexisting distance measure or topology.
See note [reducible non-instances]. -/
abbrev SeminormedAddCommGroup.ofCore {𝕜 : Type*} {E : Type*} [NormedField 𝕜] [AddCommGroup E]
    [Norm E] [Module 𝕜 E] (core : SeminormedSpace.Core 𝕜 E) : SeminormedAddCommGroup E :=
  letI := NormPseudoMetric.ofSeminormedSpaceCore core
  letI : IsNormedAddGroup E := {}
  inferInstance

/-- Produces a `SeminormedAddCommGroup E` instance from a `SeminormedSpace.Core` on a type
that already has an existing uniform space structure. This requires a proof that the uniformity
induced by the norm is equal to the preexisting uniformity. See note [reducible non-instances]. -/
abbrev SeminormedAddCommGroup.ofCoreReplaceUniformity {𝕜 : Type*} {E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E]
    (core : SeminormedSpace.Core 𝕜 E)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedSpaceCore core)]) :
    SeminormedAddCommGroup E :=
  letI := NormPseudoMetric.ofSeminormedSpaceCoreReplaceUniformity core H
  letI : IsNormedAddGroup E := {}
  inferInstance

/-- Produces a `SeminormedAddCommGroup E` instance from a `SeminormedSpace.Core` on a type
that already has an existing topology. This requires a proof that the uniformity
induced by the norm is equal to the preexisting uniformity. See note [reducible non-instances]. -/
abbrev SeminormedAddCommGroup.ofCoreReplaceTopology {𝕜 : Type*} {E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [T : TopologicalSpace E]
    (core : SeminormedSpace.Core 𝕜 E)
    (H : T = (PseudoEMetricSpace.ofSeminormedSpaceCore
      core).toUniformSpace.toTopologicalSpace) :
    SeminormedAddCommGroup E :=
  letI := NormPseudoMetric.ofSeminormedSpaceCoreReplaceTopology core H
  letI : IsNormedAddGroup E := {}
  inferInstance

open Bornology in
/-- Produces a `SeminormedAddCommGroup E` instance from a `SeminormedSpace.Core` on a type
that already has a preexisting uniform space structure and a preexisting bornology. This requires
proofs that the uniformity induced by the norm is equal to the preexisting uniformity, and likewise
for the bornology. See note [reducible non-instances]. -/
abbrev SeminormedAddCommGroup.ofCoreReplaceAll {𝕜 : Type*} {E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E] [B : Bornology E]
    (core : SeminormedSpace.Core 𝕜 E)
    (HU : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedSpaceCore core)])
    (HB : ∀ s : Set E, @IsBounded _ B s
      ↔ @IsBounded _ (PseudoMetricSpace.ofSeminormedSpaceCore core).toBornology s) :
    SeminormedAddCommGroup E :=
  letI := NormPseudoMetric.ofSeminormedSpaceCoreReplaceAll core HU HB
  letI : IsNormedAddGroup E := {}
  inferInstance

/-- A structure encapsulating minimal axioms needed to defined a normed vector space, as found
in textbooks. This is meant to be used to easily define `NormedAddCommGroup E` and `NormedSpace E`
instances from scratch on a type with no preexisting distance or topology. -/
structure NormedSpace.Core (𝕜 : Type*) (E : Type*)
    [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Norm E] : Prop
    extends SeminormedSpace.Core 𝕜 E where
  norm_eq_zero_iff (x : E) : ‖x‖ = 0 ↔ x = 0

variable {𝕜 : Type*} {E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Norm E]

/-- Produces a `NormMetric E` instance from a `NormedSpace.Core`. Note that if this is
used to define an instance on a type, it also provides a new distance measure from the norm.
it must therefore not be used on a type with a preexisting distance measure.
See note [reducible non-instances]. -/
abbrev NormMetric.ofCore (core : NormedSpace.Core 𝕜 E) : NormMetric E :=
  { NormPseudoMetric.ofSeminormedSpaceCore core.toCore with
    eq_of_dist_eq_zero := by
      letI := NormPseudoMetric.ofSeminormedSpaceCore core.toCore
      letI : IsNormedAddGroup E := {}
      intro x y h
      rw [← sub_eq_zero, ← core.norm_eq_zero_iff, ← norm_neg_add]
      exact h }

/-- Produces a `NormMetric E` instance from a `NormedSpace.Core` on a type
that already has an existing uniform space structure. This requires a proof that the uniformity
induced by the norm is equal to the preexisting uniformity. See note [reducible non-instances]. -/
abbrev NormMetric.ofCoreReplaceUniformity [U : UniformSpace E] (core : NormedSpace.Core 𝕜 E)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedSpaceCore core.toCore)]) :
    NormMetric E :=
  { NormPseudoMetric.ofSeminormedSpaceCoreReplaceUniformity core.toCore H with
    eq_of_dist_eq_zero := by
      letI := NormPseudoMetric.ofSeminormedSpaceCore core.toCore
      letI : IsNormedAddGroup E := {}
      intro x y h
      rw [← sub_eq_zero, ← core.norm_eq_zero_iff, ← norm_neg_add]
      exact h }

/-- Produces a `NormMetric E` instance from a `NormedSpace.Core` on a type
that already has an existing topology. This requires a proof that the uniformity
induced by the norm is equal to the preexisting uniformity. See note [reducible non-instances]. -/
abbrev NormMetric.ofCoreReplaceTopology [T : TopologicalSpace E]
    (core : NormedSpace.Core 𝕜 E)
    (H : T = (PseudoEMetricSpace.ofSeminormedSpaceCore
      core.toCore).toUniformSpace.toTopologicalSpace) :
    NormMetric E :=
  { NormPseudoMetric.ofSeminormedSpaceCoreReplaceTopology core.toCore H with
    eq_of_dist_eq_zero := by
      letI := NormPseudoMetric.ofSeminormedSpaceCore core.toCore
      letI : IsNormedAddGroup E := {}
      intro x y h
      rw [← sub_eq_zero, ← core.norm_eq_zero_iff, ← norm_neg_add]
      exact h }

open Bornology in
/-- Produces a `NormMetric E` instance from a `NormedSpace.Core` on a type
that already has a preexisting uniform space structure and a preexisting bornology. This requires
proofs that the uniformity induced by the norm is equal to the preexisting uniformity, and likewise
for the bornology. See note [reducible non-instances]. -/
abbrev NormMetric.ofCoreReplaceAll [U : UniformSpace E] [B : Bornology E]
    (core : NormedSpace.Core 𝕜 E)
    (HU : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedSpaceCore core.toCore)])
    (HB : ∀ s : Set E, @IsBounded _ B s
      ↔ @IsBounded _ (PseudoMetricSpace.ofSeminormedSpaceCore core.toCore).toBornology s) :
    NormMetric E :=
  { NormPseudoMetric.ofSeminormedSpaceCoreReplaceAll core.toCore HU HB with
    eq_of_dist_eq_zero := by
      letI := NormPseudoMetric.ofSeminormedSpaceCore core.toCore
      letI : IsNormedAddGroup E := {}
      intro x y h
      rw [← sub_eq_zero, ← core.norm_eq_zero_iff, ← norm_neg_add]
      exact h }

/-- Produces a `NormedAddCommGroup E` instance from a `NormedSpace.Core`. Note that if this is
used to define an instance on a type, it also provides a new distance measure from the norm.
it must therefore not be used on a type with a preexisting distance measure.
See note [reducible non-instances]. -/
abbrev NormedAddCommGroup.ofCore (core : NormedSpace.Core 𝕜 E) : NormedAddCommGroup E :=
  letI := NormMetric.ofCore core
  letI : IsNormedAddGroup E := {}
  inferInstance

/-- Produces a `NormedAddCommGroup E` instance from a `NormedSpace.Core` on a type
that already has an existing uniform space structure. This requires a proof that the uniformity
induced by the norm is equal to the preexisting uniformity. See note [reducible non-instances]. -/
abbrev NormedAddCommGroup.ofCoreReplaceUniformity [U : UniformSpace E] (core : NormedSpace.Core 𝕜 E)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedSpaceCore core.toCore)]) :
    NormedAddCommGroup E :=
  letI := NormMetric.ofCoreReplaceUniformity core H
  letI : IsNormedAddGroup E := {}
  inferInstance

/-- Produces a `NormedAddCommGroup E` instance from a `NormedSpace.Core` on a type
that already has an existing topology. This requires a proof that the uniformity
induced by the norm is equal to the preexisting uniformity. See note [reducible non-instances]. -/
abbrev NormedAddCommGroup.ofCoreReplaceTopology [T : TopologicalSpace E]
    (core : NormedSpace.Core 𝕜 E)
    (H : T = (PseudoEMetricSpace.ofSeminormedSpaceCore
      core.toCore).toUniformSpace.toTopologicalSpace) :
    NormedAddCommGroup E :=
  letI := NormMetric.ofCoreReplaceTopology core H
  letI : IsNormedAddGroup E := {}
  inferInstance

open Bornology in
/-- Produces a `NormedAddCommGroup E` instance from a `NormedSpace.Core` on a type
that already has a preexisting uniform space structure and a preexisting bornology. This requires
proofs that the uniformity induced by the norm is equal to the preexisting uniformity, and likewise
for the bornology. See note [reducible non-instances]. -/
abbrev NormedAddCommGroup.ofCoreReplaceAll [U : UniformSpace E] [B : Bornology E]
    (core : NormedSpace.Core 𝕜 E)
    (HU : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedSpaceCore core.toCore)])
    (HB : ∀ s : Set E, @IsBounded _ B s
      ↔ @IsBounded _ (PseudoMetricSpace.ofSeminormedSpaceCore core.toCore).toBornology s) :
    NormedAddCommGroup E :=
  letI := NormMetric.ofCoreReplaceAll core HU HB
  letI : IsNormedAddGroup E := {}
  inferInstance

/-- Produces a `NormedSpace 𝕜 E` instance from a `NormedSpace.Core`. This is meant to be used
on types where the `NormedAddCommGroup E` instance has also been defined using `core`.
See note [reducible non-instances]. -/
abbrev NormedSpace.ofCore {𝕜 : Type*} {E : Type*} [NormedField 𝕜] [NormPseudoMetric E] [AddCommGroup E] [IsNormedAddGroup E]
    [Module 𝕜 E] (core : NormedSpace.Core 𝕜 E) : NormedSpace 𝕜 E where
  norm_smul_le r x := by rw [core.norm_smul r x]

end Core

variable {G H : Type*} [NormPseudoMetric G] [AddCommGroup G] [IsNormedAddGroup G] [NormPseudoMetric H] [AddCommGroup H] [IsNormedAddGroup H] [NormedSpace ℝ H]
  {s : Set G}

/-- A group homomorphism from a normed group to a real normed space,
bounded on a neighborhood of `0`, must be continuous. -/
lemma AddMonoidHom.continuous_of_isBounded_nhds_zero (f : G →+ H) (hs : s ∈ 𝓝 (0 : G))
    (hbounded : IsBounded (f '' s)) : Continuous f := by
  obtain ⟨δ, hδ, hUε⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨C, hC⟩ := (isBounded_iff_subset_ball 0).1 (hbounded.subset <| image_mono hUε)
  refine continuous_of_continuousAt_zero _ (continuousAt_iff.2 fun ε (hε : _ < _) => ?_)
  simp only [dist_zero_right, map_zero]
  simp only [subset_def, mem_image, mem_ball, dist_zero_right, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hC
  have hC₀ : 0 < C := (norm_nonneg _).trans_lt <| hC 0 (by simpa)
  obtain ⟨n, hn⟩ := exists_nat_gt (C / ε)
  have hnpos : 0 < (n : ℝ) := (div_pos hC₀ hε).trans hn
  have hn₀ : n ≠ 0 := by rintro rfl; simp at hnpos
  refine ⟨δ / n, div_pos hδ hnpos, fun {x} hxδ => ?_⟩
  calc
    ‖f x‖
    _ = ‖(n : ℝ)⁻¹ • f (n • x)‖ := by simp [← Nat.cast_smul_eq_nsmul ℝ, hn₀]
    _ ≤ ‖(n : ℝ)⁻¹‖ * ‖f (n • x)‖ := norm_smul_le ..
    _ < ‖(n : ℝ)⁻¹‖ * C := by
      gcongr
      · simpa [pos_iff_ne_zero]
      · refine hC _ <| norm_nsmul_le.trans_lt ?_
        simpa only [norm_mul, Real.norm_natCast, lt_div_iff₀ hnpos, mul_comm] using hxδ
    _ = (n : ℝ)⁻¹ * C := by simp
    _ < (C / ε : ℝ)⁻¹ * C := by gcongr
    _ = ε := by simp [hC₀.ne']
