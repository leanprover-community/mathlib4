/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Algebra.Module.Basic

#align_import analysis.normed_space.basic from "leanprover-community/mathlib"@"bc91ed7093bf098d253401e69df601fc33dde156"

/-!
# Normed spaces

In this file we define (semi)normed spaces and algebras. We also prove some theorems
about these definitions.
-/


variable {α : Type*} {β : Type*} {γ : Type*} {ι : Type*}

open Filter Metric Function Set Topology Bornology
open scoped BigOperators NNReal ENNReal uniformity

section SeminormedAddCommGroup

section Prio

-- set_option extends_priority 920 -- Porting note: option unsupported

-- Here, we set a rather high priority for the instance `[NormedSpace α β] : Module α β`
-- to take precedence over `Semiring.toModule` as this leads to instance paths with better
-- unification properties.
/-- A normed space over a normed field is a vector space endowed with a norm which satisfies the
equality `‖c • x‖ = ‖c‖ ‖x‖`. We require only `‖c • x‖ ≤ ‖c‖ ‖x‖` in the definition, then prove
`‖c • x‖ = ‖c‖ ‖x‖` in `norm_smul`.

Note that since this requires `SeminormedAddCommGroup` and not `NormedAddCommGroup`, this
typeclass can be used for "semi normed spaces" too, just as `Module` can be used for
"semi modules". -/
class NormedSpace (α : Type*) (β : Type*) [NormedField α] [SeminormedAddCommGroup β] extends
  Module α β where
  norm_smul_le : ∀ (a : α) (b : β), ‖a • b‖ ≤ ‖a‖ * ‖b‖
#align normed_space NormedSpace

attribute [inherit_doc NormedSpace] NormedSpace.norm_smul_le

end Prio

variable [NormedField α] [SeminormedAddCommGroup β]

-- see Note [lower instance priority]
instance (priority := 100) NormedSpace.boundedSMul [NormedSpace α β] : BoundedSMul α β :=
  BoundedSMul.of_norm_smul_le NormedSpace.norm_smul_le
#align normed_space.has_bounded_smul NormedSpace.boundedSMul

instance NormedField.toNormedSpace : NormedSpace α α where norm_smul_le a b := norm_mul_le a b
#align normed_field.to_normed_space NormedField.toNormedSpace

-- shortcut instance
instance NormedField.to_boundedSMul : BoundedSMul α α :=
  NormedSpace.boundedSMul
#align normed_field.to_has_bounded_smul NormedField.to_boundedSMul

theorem norm_zsmul (α) [NormedField α] [NormedSpace α β] (n : ℤ) (x : β) :
    ‖n • x‖ = ‖(n : α)‖ * ‖x‖ := by rw [← norm_smul, ← Int.smul_one_eq_coe, smul_assoc, one_smul]
#align norm_zsmul norm_zsmul

@[simp]
theorem abs_norm (z : β) : |‖z‖| = ‖z‖ := abs_of_nonneg <| norm_nonneg _
#align abs_norm abs_norm

theorem inv_norm_smul_mem_closed_unit_ball [NormedSpace ℝ β] (x : β) :
    ‖x‖⁻¹ • x ∈ closedBall (0 : β) 1 := by
  simp only [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, ← _root_.div_eq_inv_mul,
    div_self_le_one]
#align inv_norm_smul_mem_closed_unit_ball inv_norm_smul_mem_closed_unit_ball

theorem norm_smul_of_nonneg [NormedSpace ℝ β] {t : ℝ} (ht : 0 ≤ t) (x : β) : ‖t • x‖ = t * ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
#align norm_smul_of_nonneg norm_smul_of_nonneg

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace α E]

variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace α F]

theorem eventually_nhds_norm_smul_sub_lt (c : α) (x : E) {ε : ℝ} (h : 0 < ε) :
    ∀ᶠ y in 𝓝 x, ‖c • (y - x)‖ < ε :=
  have : Tendsto (fun y => ‖c • (y - x)‖) (𝓝 x) (𝓝 0) :=
    ((continuous_id.sub continuous_const).const_smul _).norm.tendsto' _ _ (by simp)
  this.eventually (gt_mem_nhds h)
#align eventually_nhds_norm_smul_sub_lt eventually_nhds_norm_smul_sub_lt

theorem Filter.Tendsto.zero_smul_isBoundedUnder_le {f : ι → α} {g : ι → E} {l : Filter ι}
    (hf : Tendsto f l (𝓝 0)) (hg : IsBoundedUnder (· ≤ ·) l (Norm.norm ∘ g)) :
    Tendsto (fun x => f x • g x) l (𝓝 0) :=
  hf.op_zero_isBoundedUnder_le hg (· • ·) norm_smul_le
#align filter.tendsto.zero_smul_is_bounded_under_le Filter.Tendsto.zero_smul_isBoundedUnder_le

theorem Filter.IsBoundedUnder.smul_tendsto_zero {f : ι → α} {g : ι → E} {l : Filter ι}
    (hf : IsBoundedUnder (· ≤ ·) l (norm ∘ f)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x • g x) l (𝓝 0) :=
  hg.op_zero_isBoundedUnder_le hf (flip (· • ·)) fun x y =>
    (norm_smul_le y x).trans_eq (mul_comm _ _)
#align filter.is_bounded_under.smul_tendsto_zero Filter.IsBoundedUnder.smul_tendsto_zero

theorem closure_ball [NormedSpace ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
    closure (ball x r) = closedBall x r := by
  refine' Subset.antisymm closure_ball_subset_closedBall fun y hy => _
  have : ContinuousWithinAt (fun c : ℝ => c • (y - x) + x) (Ico 0 1) 1 :=
    ((continuous_id.smul continuous_const).add continuous_const).continuousWithinAt
  convert this.mem_closure _ _
  · rw [one_smul, sub_add_cancel]
  · simp [closure_Ico zero_ne_one, zero_le_one]
  · rintro c ⟨hc0, hc1⟩
    rw [mem_ball, dist_eq_norm, add_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0,
      mul_comm, ← mul_one r]
    rw [mem_closedBall, dist_eq_norm] at hy
    replace hr : 0 < r := ((norm_nonneg _).trans hy).lt_of_ne hr.symm
    apply mul_lt_mul' <;> assumption
#align closure_ball closure_ball

theorem frontier_ball [NormedSpace ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
    frontier (ball x r) = sphere x r := by
  rw [frontier, closure_ball x hr, isOpen_ball.interior_eq, closedBall_diff_ball]
#align frontier_ball frontier_ball

theorem interior_closedBall [NormedSpace ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
    interior (closedBall x r) = ball x r := by
  cases' hr.lt_or_lt with hr hr
  · rw [closedBall_eq_empty.2 hr, ball_eq_empty.2 hr.le, interior_empty]
  refine' Subset.antisymm _ ball_subset_interior_closedBall
  intro y hy
  rcases (mem_closedBall.1 <| interior_subset hy).lt_or_eq with (hr | rfl)
  · exact hr
  set f : ℝ → E := fun c : ℝ => c • (y - x) + x
  suffices f ⁻¹' closedBall x (dist y x) ⊆ Icc (-1) 1 by
    have hfc : Continuous f := (continuous_id.smul continuous_const).add continuous_const
    have hf1 : (1 : ℝ) ∈ f ⁻¹' interior (closedBall x <| dist y x) := by simpa
    have h1 : (1 : ℝ) ∈ interior (Icc (-1 : ℝ) 1) :=
      interior_mono this (preimage_interior_subset_interior_preimage hfc hf1)
    contrapose h1
    simp
  intro c hc
  rw [mem_Icc, ← abs_le, ← Real.norm_eq_abs, ← mul_le_mul_right hr]
  simpa [dist_eq_norm, norm_smul] using hc
#align interior_closed_ball interior_closedBall

theorem frontier_closedBall [NormedSpace ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
    frontier (closedBall x r) = sphere x r := by
  rw [frontier, closure_closedBall, interior_closedBall x hr, closedBall_diff_ball]
#align frontier_closed_ball frontier_closedBall

theorem interior_sphere [NormedSpace ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
    interior (sphere x r) = ∅ := by
  rw [← frontier_closedBall x hr, interior_frontier isClosed_ball]
#align interior_sphere interior_sphere

theorem frontier_sphere [NormedSpace ℝ E] (x : E) {r : ℝ} (hr : r ≠ 0) :
    frontier (sphere x r) = sphere x r := by
  rw [isClosed_sphere.frontier_eq, interior_sphere x hr, diff_empty]
#align frontier_sphere frontier_sphere

instance NormedSpace.discreteTopology_zmultiples
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ E] (e : E) :
    DiscreteTopology <| AddSubgroup.zmultiples e := by
  rcases eq_or_ne e 0 with (rfl | he)
  · rw [AddSubgroup.zmultiples_zero_eq_bot]
    refine Subsingleton.discreteTopology (α := ↑(⊥ : Subspace ℚ E))
  · rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
    refine' ⟨Metric.ball 0 ‖e‖, Metric.isOpen_ball, _⟩
    ext ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    rw [mem_preimage, mem_ball_zero_iff, AddSubgroup.coe_mk, mem_singleton_iff, Subtype.ext_iff,
      AddSubgroup.coe_mk, AddSubgroup.coe_zero, norm_zsmul ℚ k e, Int.norm_cast_rat,
      Int.norm_eq_abs, mul_lt_iff_lt_one_left (norm_pos_iff.mpr he), ←
      @Int.cast_one ℝ _, Int.cast_lt, Int.abs_lt_one_iff, smul_eq_zero, or_iff_left he]

open NormedField

instance ULift.normedSpace : NormedSpace α (ULift E) :=
  { ULift.seminormedAddCommGroup (E := E), ULift.module' with
    norm_smul_le := fun s x => (norm_smul_le s x.down : _) }

/-- The product of two normed spaces is a normed space, with the sup norm. -/
instance Prod.normedSpace : NormedSpace α (E × F) :=
  { Prod.seminormedAddCommGroup (E := E) (F := F), Prod.instModule with
    norm_smul_le := fun s x => by
      simp only [norm_smul, Prod.norm_def, Prod.smul_snd, Prod.smul_fst,
        mul_max_of_nonneg, norm_nonneg, le_rfl] }
#align prod.normed_space Prod.normedSpace

/-- The product of finitely many normed spaces is a normed space, with the sup norm. -/
instance Pi.normedSpace {E : ι → Type*} [Fintype ι] [∀ i, SeminormedAddCommGroup (E i)]
    [∀ i, NormedSpace α (E i)] : NormedSpace α (∀ i, E i) where
  norm_smul_le a f := by
    simp_rw [← coe_nnnorm, ← NNReal.coe_mul, NNReal.coe_le_coe, Pi.nnnorm_def,
      NNReal.mul_finset_sup]
    exact Finset.sup_mono_fun fun _ _ => norm_smul_le a _
#align pi.normed_space Pi.normedSpace

instance MulOpposite.normedSpace : NormedSpace α Eᵐᵒᵖ :=
  { MulOpposite.seminormedAddCommGroup (E := Eᵐᵒᵖ), MulOpposite.module _ with
    norm_smul_le := fun s x => norm_smul_le s x.unop }
#align mul_opposite.normed_space MulOpposite.normedSpace

/-- A subspace of a normed space is also a normed space, with the restriction of the norm. -/
instance Submodule.normedSpace {𝕜 R : Type*} [SMul 𝕜 R] [NormedField 𝕜] [Ring R] {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [Module R E] [IsScalarTower 𝕜 R E]
    (s : Submodule R E) : NormedSpace 𝕜 s where norm_smul_le c x := norm_smul_le c (x : E)
#align submodule.normed_space Submodule.normedSpace

end SeminormedAddCommGroup

/-- A linear map from a `Module` to a `NormedSpace` induces a `NormedSpace` structure on the
domain, using the `SeminormedAddCommGroup.induced` norm.

See note [reducible non-instances] -/
@[reducible]
def NormedSpace.induced {F : Type*} (α β γ : Type*) [NormedField α] [AddCommGroup β] [Module α β]
    [SeminormedAddCommGroup γ] [NormedSpace α γ] [LinearMapClass F α β γ] (f : F) :
    @NormedSpace α β _ (SeminormedAddCommGroup.induced β γ f) := by
  -- Porting note: trouble inferring SeminormedAddCommGroup β and Module α β
  -- unfolding the induced semi-norm is fiddly
  refine @NormedSpace.mk (α := α) (β := β) _ ?_ ?_ ?_
  · infer_instance
  · intro a b
    change ‖(⇑f) (a • b)‖ ≤ ‖a‖ * ‖(⇑f) b‖
    exact (map_smul f a b).symm ▸ norm_smul_le a (f b)
#align normed_space.induced NormedSpace.induced

section NormedAddCommGroup

variable [NormedField α]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace α E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace α F]

open NormedField

/-- While this may appear identical to `NormedSpace.toModule`, it contains an implicit argument
involving `NormedAddCommGroup.toSeminormedAddCommGroup` that typeclass inference has trouble
inferring.

Specifically, the following instance cannot be found without this `NormedSpace.toModule'`:
```lean
example
  (𝕜 ι : Type*) (E : ι → Type*)
  [NormedField 𝕜] [Π i, NormedAddCommGroup (E i)] [Π i, NormedSpace 𝕜 (E i)] :
  Π i, Module 𝕜 (E i) := by infer_instance
```

[This Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Typeclass.20resolution.20under.20binders/near/245151099)
gives some more context. -/
instance (priority := 100) NormedSpace.toModule' : Module α F :=
  NormedSpace.toModule
#align normed_space.to_module' NormedSpace.toModule'

section Surj

variable (E)

variable [NormedSpace ℝ E] [Nontrivial E]

theorem exists_norm_eq {c : ℝ} (hc : 0 ≤ c) : ∃ x : E, ‖x‖ = c := by
  rcases exists_ne (0 : E) with ⟨x, hx⟩
  rw [← norm_ne_zero_iff] at hx
  use c • ‖x‖⁻¹ • x
  simp [norm_smul, Real.norm_of_nonneg hc, abs_of_nonneg hc, inv_mul_cancel hx]
#align exists_norm_eq exists_norm_eq

@[simp]
theorem range_norm : range (norm : E → ℝ) = Ici 0 :=
  Subset.antisymm (range_subset_iff.2 norm_nonneg) fun _ => exists_norm_eq E
#align range_norm range_norm

theorem nnnorm_surjective : Surjective (nnnorm : E → ℝ≥0) := fun c =>
  (exists_norm_eq E c.coe_nonneg).imp fun _ h => NNReal.eq h
#align nnnorm_surjective nnnorm_surjective

@[simp]
theorem range_nnnorm : range (nnnorm : E → ℝ≥0) = univ :=
  (nnnorm_surjective E).range_eq
#align range_nnnorm range_nnnorm

end Surj

/-- If `E` is a nontrivial topological module over `ℝ`, then `E` has no isolated points.
This is a particular case of `Module.punctured_nhds_neBot`. -/
instance Real.punctured_nhds_module_neBot {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [ContinuousAdd E] [Nontrivial E] [Module ℝ E] [ContinuousSMul ℝ E] (x : E) : NeBot (𝓝[≠] x) :=
  Module.punctured_nhds_neBot ℝ E x
#align real.punctured_nhds_module_ne_bot Real.punctured_nhds_module_neBot

theorem interior_closedBall' [NormedSpace ℝ E] [Nontrivial E] (x : E) (r : ℝ) :
    interior (closedBall x r) = ball x r := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero, ball_zero, interior_singleton]
  · exact interior_closedBall x hr
#align interior_closed_ball' interior_closedBall'

theorem frontier_closedBall' [NormedSpace ℝ E] [Nontrivial E] (x : E) (r : ℝ) :
    frontier (closedBall x r) = sphere x r := by
  rw [frontier, closure_closedBall, interior_closedBall' x r, closedBall_diff_ball]
#align frontier_closed_ball' frontier_closedBall'

@[simp]
theorem interior_sphere' [NormedSpace ℝ E] [Nontrivial E] (x : E) (r : ℝ) :
    interior (sphere x r) = ∅ := by rw [← frontier_closedBall' x, interior_frontier isClosed_ball]
#align interior_sphere' interior_sphere'

@[simp]
theorem frontier_sphere' [NormedSpace ℝ E] [Nontrivial E] (x : E) (r : ℝ) :
    frontier (sphere x r) = sphere x r := by
  rw [isClosed_sphere.frontier_eq, interior_sphere' x, diff_empty]
#align frontier_sphere' frontier_sphere'

end NormedAddCommGroup

section NontriviallyNormedSpace

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Nontrivial E]

/-- If `E` is a nontrivial normed space over a nontrivially normed field `𝕜`, then `E` is unbounded:
for any `c : ℝ`, there exists a vector `x : E` with norm strictly greater than `c`. -/
theorem NormedSpace.exists_lt_norm (c : ℝ) : ∃ x : E, c < ‖x‖ := by
  rcases exists_ne (0 : E) with ⟨x, hx⟩
  rcases NormedField.exists_lt_norm 𝕜 (c / ‖x‖) with ⟨r, hr⟩
  use r • x
  rwa [norm_smul, ← _root_.div_lt_iff]
  rwa [norm_pos_iff]
#align normed_space.exists_lt_norm NormedSpace.exists_lt_norm

protected theorem NormedSpace.unbounded_univ : ¬Bornology.IsBounded (univ : Set E) := fun h =>
  let ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 h
  let ⟨x, hx⟩ := NormedSpace.exists_lt_norm 𝕜 E R
  hx.not_le (hR x trivial)
#align normed_space.unbounded_univ NormedSpace.unbounded_univ

protected lemma NormedSpace.cobounded_neBot : NeBot (cobounded E) := by
  rw [neBot_iff, Ne.def, cobounded_eq_bot_iff, ← isBounded_univ]
  exact NormedSpace.unbounded_univ 𝕜 E

instance (priority := 100) NontriviallyNormedField.cobounded_neBot : NeBot (cobounded 𝕜) :=
  NormedSpace.cobounded_neBot 𝕜 𝕜

instance (priority := 80) RealNormedSpace.cobounded_neBot [NormedSpace ℝ E] :
    NeBot (cobounded E) := NormedSpace.cobounded_neBot ℝ E

instance (priority := 80) NontriviallyNormedField.infinite : Infinite 𝕜 :=
  ⟨fun _ ↦ NormedSpace.unbounded_univ 𝕜 𝕜 (Set.toFinite _).isBounded⟩

end NontriviallyNormedSpace

section NormedSpace

variable (𝕜 E : Type*) [NormedField 𝕜] [Infinite 𝕜] [NormedAddCommGroup E] [Nontrivial E]
  [NormedSpace 𝕜 E]

/-- A normed vector space over an infinite normed field is a noncompact space.
This cannot be an instance because in order to apply it,
Lean would have to search for `NormedSpace 𝕜 E` with unknown `𝕜`.
We register this as an instance in two cases: `𝕜 = E` and `𝕜 = ℝ`. -/
protected theorem NormedSpace.noncompactSpace : NoncompactSpace E := by
  by_cases H : ∃ c : 𝕜, c ≠ 0 ∧ ‖c‖ ≠ 1
  · letI := NontriviallyNormedField.ofNormNeOne H
    exact ⟨fun h ↦ NormedSpace.unbounded_univ 𝕜 E h.isBounded⟩
  · push_neg at H
    rcases exists_ne (0 : E) with ⟨x, hx⟩
    suffices ClosedEmbedding (Infinite.natEmbedding 𝕜 · • x) from this.noncompactSpace
    refine closedEmbedding_of_pairwise_le_dist (norm_pos_iff.2 hx) fun k n hne ↦ ?_
    simp only [dist_eq_norm, ← sub_smul, norm_smul]
    rw [H, one_mul]
    rwa [sub_ne_zero, (Embedding.injective _).ne_iff]
#align normed_space.noncompact_space NormedSpace.noncompactSpace

instance (priority := 100) NormedField.noncompactSpace : NoncompactSpace 𝕜 :=
  NormedSpace.noncompactSpace 𝕜 𝕜
#align nontrivially_normed_field.noncompact_space NormedField.noncompactSpace

instance (priority := 100) RealNormedSpace.noncompactSpace [NormedSpace ℝ E] : NoncompactSpace E :=
  NormedSpace.noncompactSpace ℝ E
#align real_normed_space.noncompact_space RealNormedSpace.noncompactSpace

end NormedSpace

section NormedAlgebra

/-- A normed algebra `𝕜'` over `𝕜` is normed module that is also an algebra.

See the implementation notes for `Algebra` for a discussion about non-unital algebras. Following
the strategy there, a non-unital *normed* algebra can be written as:
```lean
variables [NormedField 𝕜] [NonUnitalSeminormedRing 𝕜']
variables [NormedSpace 𝕜 𝕜'] [SMulCommClass 𝕜 𝕜' 𝕜'] [IsScalarTower 𝕜 𝕜' 𝕜']
```
-/
class NormedAlgebra (𝕜 : Type*) (𝕜' : Type*) [NormedField 𝕜] [SeminormedRing 𝕜'] extends
  Algebra 𝕜 𝕜' where
  norm_smul_le : ∀ (r : 𝕜) (x : 𝕜'), ‖r • x‖ ≤ ‖r‖ * ‖x‖
#align normed_algebra NormedAlgebra

attribute [inherit_doc NormedAlgebra] NormedAlgebra.norm_smul_le

variable {𝕜 : Type*} (𝕜' : Type*) [NormedField 𝕜] [SeminormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜']

instance (priority := 100) NormedAlgebra.toNormedSpace : NormedSpace 𝕜 𝕜' :=
  -- Porting note: previous Lean could figure out what we were extending
  { NormedAlgebra.toAlgebra.toModule with
  norm_smul_le := NormedAlgebra.norm_smul_le }
#align normed_algebra.to_normed_space NormedAlgebra.toNormedSpace

/-- While this may appear identical to `NormedAlgebra.toNormedSpace`, it contains an implicit
argument involving `NormedRing.toSeminormedRing` that typeclass inference has trouble inferring.

Specifically, the following instance cannot be found without this `NormedSpace.toModule'`:
```lean
example
  (𝕜 ι : Type*) (E : ι → Type*)
  [NormedField 𝕜] [Π i, NormedRing (E i)] [Π i, NormedAlgebra 𝕜 (E i)] :
  Π i, Module 𝕜 (E i) := by infer_instance
```

See `NormedSpace.toModule'` for a similar situation. -/
instance (priority := 100) NormedAlgebra.toNormedSpace' {𝕜'} [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] :
    NormedSpace 𝕜 𝕜' := by infer_instance
#align normed_algebra.to_normed_space' NormedAlgebra.toNormedSpace'

theorem norm_algebraMap (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖ * ‖(1 : 𝕜')‖ := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact norm_smul _ _
#align norm_algebra_map norm_algebraMap

theorem nnnorm_algebraMap (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖₊ = ‖x‖₊ * ‖(1 : 𝕜')‖₊ :=
  Subtype.ext <| norm_algebraMap 𝕜' x
#align nnnorm_algebra_map nnnorm_algebraMap

@[simp]
theorem norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖ := by
  rw [norm_algebraMap, norm_one, mul_one]
#align norm_algebra_map' norm_algebraMap'

@[simp]
theorem nnnorm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖₊ = ‖x‖₊ :=
  Subtype.ext <| norm_algebraMap' _ _
#align nnnorm_algebra_map' nnnorm_algebraMap'

section NNReal

variable [NormOneClass 𝕜'] [NormedAlgebra ℝ 𝕜']

@[simp]
theorem norm_algebraMap_nNReal (x : ℝ≥0) : ‖algebraMap ℝ≥0 𝕜' x‖ = x :=
  (norm_algebraMap' 𝕜' (x : ℝ)).symm ▸ Real.norm_of_nonneg x.prop
#align norm_algebra_map_nnreal norm_algebraMap_nNReal

@[simp]
theorem nnnorm_algebraMap_nNReal (x : ℝ≥0) : ‖algebraMap ℝ≥0 𝕜' x‖₊ = x :=
  Subtype.ext <| norm_algebraMap_nNReal 𝕜' x
#align nnnorm_algebra_map_nnreal nnnorm_algebraMap_nNReal

end NNReal

variable (𝕜)

/-- In a normed algebra, the inclusion of the base field in the extended field is an isometry. -/
theorem algebraMap_isometry [NormOneClass 𝕜'] : Isometry (algebraMap 𝕜 𝕜') := by
  refine' Isometry.of_dist_eq fun x y => _
  rw [dist_eq_norm, dist_eq_norm, ← RingHom.map_sub, norm_algebraMap']
#align algebra_map_isometry algebraMap_isometry

instance NormedAlgebra.id : NormedAlgebra 𝕜 𝕜 :=
  { NormedField.toNormedSpace, Algebra.id 𝕜 with }
#align normed_algebra.id NormedAlgebra.id

-- Porting note: cannot synth scalar tower ℚ ℝ k
/-- Any normed characteristic-zero division ring that is a normed algebra over the reals is also a
normed algebra over the rationals.

Phrased another way, if `𝕜` is a normed algebra over the reals, then `AlgebraRat` respects that
norm. -/
instance normedAlgebraRat {𝕜} [NormedDivisionRing 𝕜] [CharZero 𝕜] [NormedAlgebra ℝ 𝕜] :
    NormedAlgebra ℚ 𝕜 where
  norm_smul_le q x := by
    rw [← smul_one_smul ℝ q x, Rat.smul_one_eq_coe, norm_smul, Rat.norm_cast_real]
#align normed_algebra_rat normedAlgebraRat

instance PUnit.normedAlgebra : NormedAlgebra 𝕜 PUnit where
  norm_smul_le q _ := by simp only [norm_eq_zero, mul_zero, le_refl]
#align punit.normed_algebra PUnit.normedAlgebra

instance : NormedAlgebra 𝕜 (ULift 𝕜') :=
  { ULift.normedSpace, ULift.algebra with }

/-- The product of two normed algebras is a normed algebra, with the sup norm. -/
instance Prod.normedAlgebra {E F : Type*} [SeminormedRing E] [SeminormedRing F] [NormedAlgebra 𝕜 E]
    [NormedAlgebra 𝕜 F] : NormedAlgebra 𝕜 (E × F) :=
  { Prod.normedSpace, Prod.algebra 𝕜 E F with }
#align prod.normed_algebra Prod.normedAlgebra

-- Porting note: Lean 3 could synth the algebra instances for Pi Pr
/-- The product of finitely many normed algebras is a normed algebra, with the sup norm. -/
instance Pi.normedAlgebra {E : ι → Type*} [Fintype ι] [∀ i, SeminormedRing (E i)]
    [∀ i, NormedAlgebra 𝕜 (E i)] : NormedAlgebra 𝕜 (∀ i, E i) :=
  { Pi.normedSpace, Pi.algebra _ E with }
#align pi.normed_algebra Pi.normedAlgebra

variable {E : Type*} [SeminormedRing E] [NormedAlgebra 𝕜 E]

instance MulOpposite.normedAlgebra {E : Type*} [SeminormedRing E] [NormedAlgebra 𝕜 E] :
    NormedAlgebra 𝕜 Eᵐᵒᵖ :=
  { MulOpposite.normedSpace, MulOpposite.instAlgebra with }

#align mul_opposite.normed_algebra MulOpposite.normedAlgebra

end NormedAlgebra

/-- A non-unital algebra homomorphism from an `Algebra` to a `NormedAlgebra` induces a
`NormedAlgebra` structure on the domain, using the `SeminormedRing.induced` norm.

See note [reducible non-instances] -/
@[reducible]
def NormedAlgebra.induced {F : Type*} (α β γ : Type*) [NormedField α] [Ring β] [Algebra α β]
    [SeminormedRing γ] [NormedAlgebra α γ] [NonUnitalAlgHomClass F α β γ] (f : F) :
    @NormedAlgebra α β _ (SeminormedRing.induced β γ f) := by
  -- Porting note: trouble with SeminormedRing β, Algebra α β, and unfolding seminorm
  refine @NormedAlgebra.mk (𝕜 := α) (𝕜' := β) _ ?_ ?_ ?_
  · infer_instance
  · intro a b
    change ‖(⇑f) (a • b)‖ ≤ ‖a‖ * ‖(⇑f) b‖
    exact (map_smul f a b).symm ▸ norm_smul_le a (f b)
#align normed_algebra.induced NormedAlgebra.induced

-- Porting note: failed to synth NonunitalAlgHomClass
instance Subalgebra.toNormedAlgebra {𝕜 A : Type*} [SeminormedRing A] [NormedField 𝕜]
    [NormedAlgebra 𝕜 A] (S : Subalgebra 𝕜 A) : NormedAlgebra 𝕜 S :=
  @NormedAlgebra.induced _ 𝕜 S A _ (SubringClass.toRing S) _ _ _ _ S.val
#align subalgebra.to_normed_algebra Subalgebra.toNormedAlgebra

section RestrictScalars

variable (𝕜 : Type*) (𝕜' : Type*) [NormedField 𝕜] [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  (E : Type*) [SeminormedAddCommGroup E] [NormedSpace 𝕜' E]

instance {𝕜 : Type*} {𝕜' : Type*} {E : Type*} [I : SeminormedAddCommGroup E] :
    SeminormedAddCommGroup (RestrictScalars 𝕜 𝕜' E) :=
  I

instance {𝕜 : Type*} {𝕜' : Type*} {E : Type*} [I : NormedAddCommGroup E] :
    NormedAddCommGroup (RestrictScalars 𝕜 𝕜' E) :=
  I

/-- If `E` is a normed space over `𝕜'` and `𝕜` is a normed algebra over `𝕜'`, then
`RestrictScalars.module` is additionally a `NormedSpace`. -/
instance RestrictScalars.normedSpace : NormedSpace 𝕜 (RestrictScalars 𝕜 𝕜' E) :=
  { RestrictScalars.module 𝕜 𝕜' E with
    norm_smul_le := fun c x =>
      (norm_smul_le (algebraMap 𝕜 𝕜' c) (_ : E)).trans_eq <| by rw [norm_algebraMap'] }

-- If you think you need this, consider instead reproducing `RestrictScalars.lsmul`
-- appropriately modified here.
/-- The action of the original normed_field on `RestrictScalars 𝕜 𝕜' E`.
This is not an instance as it would be contrary to the purpose of `RestrictScalars`.
-/
def Module.RestrictScalars.normedSpaceOrig {𝕜 : Type*} {𝕜' : Type*} {E : Type*} [NormedField 𝕜']
    [SeminormedAddCommGroup E] [I : NormedSpace 𝕜' E] : NormedSpace 𝕜' (RestrictScalars 𝕜 𝕜' E) :=
  I
#align module.restrict_scalars.normed_space_orig Module.RestrictScalars.normedSpaceOrig

/-- Warning: This declaration should be used judiciously.
Please consider using `IsScalarTower` and/or `RestrictScalars 𝕜 𝕜' E` instead.

This definition allows the `RestrictScalars.normedSpace` instance to be put directly on `E`
rather on `RestrictScalars 𝕜 𝕜' E`. This would be a very bad instance; both because `𝕜'` cannot be
inferred, and because it is likely to create instance diamonds.
-/
def NormedSpace.restrictScalars : NormedSpace 𝕜 E :=
  RestrictScalars.normedSpace _ 𝕜' _
#align normed_space.restrict_scalars NormedSpace.restrictScalars

end RestrictScalars
