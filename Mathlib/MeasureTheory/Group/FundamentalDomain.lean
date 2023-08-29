/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Integral.SetIntegral

#align_import measure_theory.group.fundamental_domain from "leanprover-community/mathlib"@"eb810cf549db839dadf13353dbe69bac55acdbbc"

/-!
# Fundamental domain of a group action

A set `s` is said to be a *fundamental domain* of an action of a group `G` on a measurable space `α`
with respect to a measure `μ` if

* `s` is a measurable set;

* the sets `g • s` over all `g : G` cover almost all points of the whole space;

* the sets `g • s`, are pairwise a.e. disjoint, i.e., `μ (g₁ • s ∩ g₂ • s) = 0` whenever `g₁ ≠ g₂`;
  we require this for `g₂ = 1` in the definition, then deduce it for any two `g₁ ≠ g₂`.

In this file we prove that in case of a countable group `G` and a measure preserving action, any two
fundamental domains have the same measure, and for a `G`-invariant function, its integrals over any
two fundamental domains are equal to each other.

We also generate additive versions of all theorems in this file using the `to_additive` attribute.

## Main declarations

* `MeasureTheory.IsFundamentalDomain`: Predicate for a set to be a fundamental domain of the
  action of a group
* `MeasureTheory.fundamentalFrontier`: Fundamental frontier of a set under the action of a group.
  Elements of `s` that belong to some other translate of `s`.
* `MeasureTheory.fundamentalInterior`: Fundamental interior of a set under the action of a group.
  Elements of `s` that do not belong to any other translate of `s`.
-/


open scoped ENNReal Pointwise Topology NNReal ENNReal MeasureTheory

open MeasureTheory MeasureTheory.Measure Set Function TopologicalSpace Filter

namespace MeasureTheory

/-- A measurable set `s` is a *fundamental domain* for an additive action of an additive group `G`
on a measurable space `α` with respect to a measure `α` if the sets `g +ᵥ s`, `g : G`, are pairwise
a.e. disjoint and cover the whole space. -/
structure IsAddFundamentalDomain (G : Type*) {α : Type*} [Zero G] [VAdd G α] [MeasurableSpace α]
    (s : Set α) (μ : Measure α := by volume_tac) : Prop where
  protected nullMeasurableSet : NullMeasurableSet s μ
  protected ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g +ᵥ x ∈ s
  protected aedisjoint : Pairwise <| (AEDisjoint μ on fun g : G => g +ᵥ s)
#align measure_theory.is_add_fundamental_domain MeasureTheory.IsAddFundamentalDomain

/-- A measurable set `s` is a *fundamental domain* for an action of a group `G` on a measurable
space `α` with respect to a measure `α` if the sets `g • s`, `g : G`, are pairwise a.e. disjoint and
cover the whole space. -/
@[to_additive IsAddFundamentalDomain]
structure IsFundamentalDomain (G : Type*) {α : Type*} [One G] [SMul G α] [MeasurableSpace α]
    (s : Set α) (μ : Measure α := by volume_tac) : Prop where
  protected nullMeasurableSet : NullMeasurableSet s μ
  protected ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ s
  protected aedisjoint : Pairwise <| (AEDisjoint μ on fun g : G => g • s)
#align measure_theory.is_fundamental_domain MeasureTheory.IsFundamentalDomain

variable {G H α β E : Type*}

namespace IsFundamentalDomain

variable [Group G] [Group H] [MulAction G α] [MeasurableSpace α] [MulAction H β] [MeasurableSpace β]
  [NormedAddCommGroup E] {s t : Set α} {μ : Measure α}

/-- If for each `x : α`, exactly one of `g • x`, `g : G`, belongs to a measurable set `s`, then `s`
is a fundamental domain for the action of `G` on `α`. -/
@[to_additive "If for each `x : α`, exactly one of `g +ᵥ x`, `g : G`, belongs to a measurable set
`s`, then `s` is a fundamental domain for the additive action of `G` on `α`."]
theorem mk' (h_meas : NullMeasurableSet s μ) (h_exists : ∀ x : α, ∃! g : G, g • x ∈ s) :
    IsFundamentalDomain G s μ where
  nullMeasurableSet := h_meas
  ae_covers := eventually_of_forall fun x => (h_exists x).exists
  aedisjoint a b hab := Disjoint.aedisjoint <| disjoint_left.2 fun x hxa hxb => by
    rw [mem_smul_set_iff_inv_smul_mem] at hxa hxb
    -- ⊢ False
    exact hab (inv_injective <| (h_exists x).unique hxa hxb)
    -- 🎉 no goals
#align measure_theory.is_fundamental_domain.mk' MeasureTheory.IsFundamentalDomain.mk'
#align measure_theory.is_add_fundamental_domain.mk' MeasureTheory.IsAddFundamentalDomain.mk'

/-- For `s` to be a fundamental domain, it's enough to check
`MeasureTheory.AEDisjoint (g • s) s` for `g ≠ 1`. -/
@[to_additive "For `s` to be a fundamental domain, it's enough to check
  `MeasureTheory.AEDisjoint (g +ᵥ s) s` for `g ≠ 0`."]
theorem mk'' (h_meas : NullMeasurableSet s μ) (h_ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ s)
    (h_ae_disjoint : ∀ g, g ≠ (1 : G) → AEDisjoint μ (g • s) s)
    (h_qmp : ∀ g : G, QuasiMeasurePreserving ((g • ·) : α → α) μ μ) :
    IsFundamentalDomain G s μ where
  nullMeasurableSet := h_meas
  ae_covers := h_ae_covers
  aedisjoint := pairwise_aedisjoint_of_aedisjoint_forall_ne_one h_ae_disjoint h_qmp
#align measure_theory.is_fundamental_domain.mk'' MeasureTheory.IsFundamentalDomain.mk''
#align measure_theory.is_add_fundamental_domain.mk'' MeasureTheory.IsAddFundamentalDomain.mk''

/-- If a measurable space has a finite measure `μ` and a countable group `G` acts
quasi-measure-preservingly, then to show that a set `s` is a fundamental domain, it is sufficient
to check that its translates `g • s` are (almost) disjoint and that the sum `∑' g, μ (g • s)` is
sufficiently large. -/
@[to_additive
  "If a measurable space has a finite measure `μ` and a countable additive group `G` acts
  quasi-measure-preservingly, then to show that a set `s` is a fundamental domain, it is sufficient
  to check that its translates `g +ᵥ s` are (almost) disjoint and that the sum `∑' g, μ (g +ᵥ s)` is
  sufficiently large."]
theorem mk_of_measure_univ_le [IsFiniteMeasure μ] [Countable G] (h_meas : NullMeasurableSet s μ)
    (h_ae_disjoint : ∀ (g) (_ : g ≠ (1 : G)), AEDisjoint μ (g • s) s)
    (h_qmp : ∀ g : G, QuasiMeasurePreserving ((· • ·) g : α → α) μ μ)
    (h_measure_univ_le : μ (univ : Set α) ≤ ∑' g : G, μ (g • s)) : IsFundamentalDomain G s μ :=
  have aedisjoint : Pairwise (AEDisjoint μ on fun g : G => g • s) :=
    pairwise_aedisjoint_of_aedisjoint_forall_ne_one h_ae_disjoint h_qmp
  { nullMeasurableSet := h_meas
    aedisjoint
    ae_covers := by
      replace h_meas : ∀ g : G, NullMeasurableSet (g • s) μ := fun g => by
        rw [← inv_inv g, ← preimage_smul]; exact h_meas.preimage (h_qmp g⁻¹)
      have h_meas' : NullMeasurableSet {a | ∃ g : G, g • a ∈ s} μ := by
        rw [← iUnion_smul_eq_setOf_exists]; exact .iUnion h_meas
      rw [ae_iff_measure_eq h_meas', ← iUnion_smul_eq_setOf_exists]
      -- ⊢ ↑↑μ (⋃ (g : G), g • s) = ↑↑μ univ
      refine' le_antisymm (measure_mono <| subset_univ _) _
      -- ⊢ ↑↑μ univ ≤ ↑↑μ (⋃ (g : G), g • s)
      rw [measure_iUnion₀ aedisjoint h_meas]
      -- ⊢ ↑↑μ univ ≤ ∑' (i : G), ↑↑μ (i • s)
      exact h_measure_univ_le }
      -- 🎉 no goals
#align measure_theory.is_fundamental_domain.mk_of_measure_univ_le MeasureTheory.IsFundamentalDomain.mk_of_measure_univ_le
#align measure_theory.is_add_fundamental_domain.mk_of_measure_univ_le MeasureTheory.IsAddFundamentalDomain.mk_of_measure_univ_le

@[to_additive]
theorem iUnion_smul_ae_eq (h : IsFundamentalDomain G s μ) : ⋃ g : G, g • s =ᵐ[μ] univ :=
  eventuallyEq_univ.2 <| h.ae_covers.mono fun _ ⟨g, hg⟩ =>
    mem_iUnion.2 ⟨g⁻¹, _, hg, inv_smul_smul _ _⟩
#align measure_theory.is_fundamental_domain.Union_smul_ae_eq MeasureTheory.IsFundamentalDomain.iUnion_smul_ae_eq
#align measure_theory.is_add_fundamental_domain.Union_vadd_ae_eq MeasureTheory.IsAddFundamentalDomain.iUnion_vadd_ae_eq

@[to_additive]
theorem mono (h : IsFundamentalDomain G s μ) {ν : Measure α} (hle : ν ≪ μ) :
    IsFundamentalDomain G s ν :=
  ⟨h.1.mono_ac hle, hle h.2, h.aedisjoint.mono fun _ _ h => hle h⟩
#align measure_theory.is_fundamental_domain.mono MeasureTheory.IsFundamentalDomain.mono
#align measure_theory.is_add_fundamental_domain.mono MeasureTheory.IsAddFundamentalDomain.mono

@[to_additive]
theorem preimage_of_equiv {ν : Measure β} (h : IsFundamentalDomain G s μ) {f : β → α}
    (hf : QuasiMeasurePreserving f ν μ) {e : G → H} (he : Bijective e)
    (hef : ∀ g, Semiconj f (e g • ·) (g • ·)) : IsFundamentalDomain H (f ⁻¹' s) ν where
  nullMeasurableSet := h.nullMeasurableSet.preimage hf
  ae_covers := (hf.ae h.ae_covers).mono fun x ⟨g, hg⟩ => ⟨e g, by rwa [mem_preimage, hef g x]⟩
                                                                  -- 🎉 no goals
  aedisjoint a b hab := by
    lift e to G ≃ H using he
    -- ⊢ (AEDisjoint ν on fun g => g • f ⁻¹' s) a b
    have : (e.symm a⁻¹)⁻¹ ≠ (e.symm b⁻¹)⁻¹ := by simp [hab]
    -- ⊢ (AEDisjoint ν on fun g => g • f ⁻¹' s) a b
    have := (h.aedisjoint this).preimage hf
    -- ⊢ (AEDisjoint ν on fun g => g • f ⁻¹' s) a b
    simp only [Semiconj] at hef
    -- ⊢ (AEDisjoint ν on fun g => g • f ⁻¹' s) a b
    simpa only [onFun, ← preimage_smul_inv, preimage_preimage, ← hef, e.apply_symm_apply, inv_inv]
      using this
#align measure_theory.is_fundamental_domain.preimage_of_equiv MeasureTheory.IsFundamentalDomain.preimage_of_equiv
#align measure_theory.is_add_fundamental_domain.preimage_of_equiv MeasureTheory.IsAddFundamentalDomain.preimage_of_equiv

@[to_additive]
theorem image_of_equiv {ν : Measure β} (h : IsFundamentalDomain G s μ) (f : α ≃ β)
    (hf : QuasiMeasurePreserving f.symm ν μ) (e : H ≃ G)
    (hef : ∀ g, Semiconj f (e g • ·) (g • ·)) : IsFundamentalDomain H (f '' s) ν := by
  rw [f.image_eq_preimage]
  -- ⊢ IsFundamentalDomain H (↑f.symm ⁻¹' s)
  refine' h.preimage_of_equiv hf e.symm.bijective fun g x => _
  -- ⊢ ↑f.symm ((fun x => ↑e.symm g • x) x) = (fun x => g • x) (↑f.symm x)
  rcases f.surjective x with ⟨x, rfl⟩
  -- ⊢ ↑f.symm ((fun x => ↑e.symm g • x) (↑f x)) = (fun x => g • x) (↑f.symm (↑f x))
  rw [← hef _ _, f.symm_apply_apply, f.symm_apply_apply, e.apply_symm_apply]
  -- 🎉 no goals
#align measure_theory.is_fundamental_domain.image_of_equiv MeasureTheory.IsFundamentalDomain.image_of_equiv
#align measure_theory.is_add_fundamental_domain.image_of_equiv MeasureTheory.IsAddFundamentalDomain.image_of_equiv

@[to_additive]
theorem pairwise_aedisjoint_of_ac {ν} (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) :
    Pairwise fun g₁ g₂ : G => AEDisjoint ν (g₁ • s) (g₂ • s) :=
  h.aedisjoint.mono fun _ _ H => hν H
#align measure_theory.is_fundamental_domain.pairwise_ae_disjoint_of_ac MeasureTheory.IsFundamentalDomain.pairwise_aedisjoint_of_ac
#align measure_theory.is_add_fundamental_domain.pairwise_ae_disjoint_of_ac MeasureTheory.IsAddFundamentalDomain.pairwise_aedisjoint_of_ac

@[to_additive]
theorem smul_of_comm {G' : Type*} [Group G'] [MulAction G' α] [MeasurableSpace G']
    [MeasurableSMul G' α] [SMulInvariantMeasure G' α μ] [SMulCommClass G' G α]
    (h : IsFundamentalDomain G s μ) (g : G') : IsFundamentalDomain G (g • s) μ :=
  h.image_of_equiv (MulAction.toPerm g) (measurePreserving_smul _ _).quasiMeasurePreserving
    (Equiv.refl _) <| smul_comm g
#align measure_theory.is_fundamental_domain.smul_of_comm MeasureTheory.IsFundamentalDomain.smul_of_comm
#align measure_theory.is_add_fundamental_domain.vadd_of_comm MeasureTheory.IsAddFundamentalDomain.vadd_of_comm

variable [MeasurableSpace G] [MeasurableSMul G α] [SMulInvariantMeasure G α μ]

@[to_additive]
theorem nullMeasurableSet_smul (h : IsFundamentalDomain G s μ) (g : G) :
    NullMeasurableSet (g • s) μ :=
  h.nullMeasurableSet.smul g
#align measure_theory.is_fundamental_domain.null_measurable_set_smul MeasureTheory.IsFundamentalDomain.nullMeasurableSet_smul
#align measure_theory.is_add_fundamental_domain.null_measurable_set_vadd MeasureTheory.IsAddFundamentalDomain.nullMeasurableSet_vadd

@[to_additive]
theorem restrict_restrict (h : IsFundamentalDomain G s μ) (g : G) (t : Set α) :
    (μ.restrict t).restrict (g • s) = μ.restrict (g • s ∩ t) :=
  restrict_restrict₀ ((h.nullMeasurableSet_smul g).mono restrict_le_self)
#align measure_theory.is_fundamental_domain.restrict_restrict MeasureTheory.IsFundamentalDomain.restrict_restrict
#align measure_theory.is_add_fundamental_domain.restrict_restrict MeasureTheory.IsAddFundamentalDomain.restrict_restrict

@[to_additive]
theorem smul (h : IsFundamentalDomain G s μ) (g : G) : IsFundamentalDomain G (g • s) μ :=
  h.image_of_equiv (MulAction.toPerm g) (measurePreserving_smul _ _).quasiMeasurePreserving
    ⟨fun g' => g⁻¹ * g' * g, fun g' => g * g' * g⁻¹, fun g' => by simp [mul_assoc], fun g' => by
                                                                  -- 🎉 no goals
      simp [mul_assoc]⟩
      -- 🎉 no goals
    fun g' x => by simp [smul_smul, mul_assoc]
                   -- 🎉 no goals
#align measure_theory.is_fundamental_domain.smul MeasureTheory.IsFundamentalDomain.smul
#align measure_theory.is_add_fundamental_domain.vadd MeasureTheory.IsAddFundamentalDomain.vadd

variable [Countable G] {ν : Measure α}

@[to_additive]
theorem sum_restrict_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) :
    (sum fun g : G => ν.restrict (g • s)) = ν := by
  rw [← restrict_iUnion_ae (h.aedisjoint.mono fun i j h => hν h) fun g =>
      (h.nullMeasurableSet_smul g).mono_ac hν,
    restrict_congr_set (hν h.iUnion_smul_ae_eq), restrict_univ]
#align measure_theory.is_fundamental_domain.sum_restrict_of_ac MeasureTheory.IsFundamentalDomain.sum_restrict_of_ac
#align measure_theory.is_add_fundamental_domain.sum_restrict_of_ac MeasureTheory.IsAddFundamentalDomain.sum_restrict_of_ac

@[to_additive]
theorem lintegral_eq_tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂ν = ∑' g : G, ∫⁻ x in g • s, f x ∂ν := by
  rw [← lintegral_sum_measure, h.sum_restrict_of_ac hν]
  -- 🎉 no goals
#align measure_theory.is_fundamental_domain.lintegral_eq_tsum_of_ac MeasureTheory.IsFundamentalDomain.lintegral_eq_tsum_of_ac
#align measure_theory.is_add_fundamental_domain.lintegral_eq_tsum_of_ac MeasureTheory.IsAddFundamentalDomain.lintegral_eq_tsum_of_ac

@[to_additive]
theorem sum_restrict (h : IsFundamentalDomain G s μ) : (sum fun g : G => μ.restrict (g • s)) = μ :=
  h.sum_restrict_of_ac (refl _)
#align measure_theory.is_fundamental_domain.sum_restrict MeasureTheory.IsFundamentalDomain.sum_restrict
#align measure_theory.is_add_fundamental_domain.sum_restrict MeasureTheory.IsAddFundamentalDomain.sum_restrict

@[to_additive]
theorem lintegral_eq_tsum (h : IsFundamentalDomain G s μ) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ :=
  h.lintegral_eq_tsum_of_ac (refl _) f
#align measure_theory.is_fundamental_domain.lintegral_eq_tsum MeasureTheory.IsFundamentalDomain.lintegral_eq_tsum
#align measure_theory.is_add_fundamental_domain.lintegral_eq_tsum MeasureTheory.IsAddFundamentalDomain.lintegral_eq_tsum

@[to_additive]
theorem lintegral_eq_tsum' (h : IsFundamentalDomain G s μ) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in s, f (g⁻¹ • x) ∂μ :=
  calc
    ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ := h.lintegral_eq_tsum f
    _ = ∑' g : G, ∫⁻ x in g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫⁻ x in s, f (g⁻¹ • x) ∂μ := tsum_congr fun g => Eq.symm <|
      (measurePreserving_smul g⁻¹ μ).set_lintegral_comp_emb (measurableEmbedding_const_smul _) _ _
#align measure_theory.is_fundamental_domain.lintegral_eq_tsum' MeasureTheory.IsFundamentalDomain.lintegral_eq_tsum'
#align measure_theory.is_add_fundamental_domain.lintegral_eq_tsum' MeasureTheory.IsAddFundamentalDomain.lintegral_eq_tsum'

@[to_additive]
theorem set_lintegral_eq_tsum (h : IsFundamentalDomain G s μ) (f : α → ℝ≥0∞) (t : Set α) :
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ :=
  calc
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ.restrict t :=
      h.lintegral_eq_tsum_of_ac restrict_le_self.absolutelyContinuous _
    _ = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ := by simp only [h.restrict_restrict, inter_comm]
                                                  -- 🎉 no goals
#align measure_theory.is_fundamental_domain.set_lintegral_eq_tsum MeasureTheory.IsFundamentalDomain.set_lintegral_eq_tsum
#align measure_theory.is_add_fundamental_domain.set_lintegral_eq_tsum MeasureTheory.IsAddFundamentalDomain.set_lintegral_eq_tsum

@[to_additive]
theorem set_lintegral_eq_tsum' (h : IsFundamentalDomain G s μ) (f : α → ℝ≥0∞) (t : Set α) :
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
  calc
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ := h.set_lintegral_eq_tsum f t
    _ = ∑' g : G, ∫⁻ x in t ∩ g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫⁻ x in g⁻¹ • (g • t ∩ s), f x ∂μ := by simp only [smul_set_inter, inv_smul_smul]
                                                          -- 🎉 no goals
    _ = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ := tsum_congr fun g => Eq.symm <|
      (measurePreserving_smul g⁻¹ μ).set_lintegral_comp_emb (measurableEmbedding_const_smul _) _ _
#align measure_theory.is_fundamental_domain.set_lintegral_eq_tsum' MeasureTheory.IsFundamentalDomain.set_lintegral_eq_tsum'
#align measure_theory.is_add_fundamental_domain.set_lintegral_eq_tsum' MeasureTheory.IsAddFundamentalDomain.set_lintegral_eq_tsum'

@[to_additive]
theorem measure_eq_tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (t : Set α) :
    ν t = ∑' g : G, ν (t ∩ g • s) := by
  have H : ν.restrict t ≪ μ := Measure.restrict_le_self.absolutelyContinuous.trans hν
  -- ⊢ ↑↑ν t = ∑' (g : G), ↑↑ν (t ∩ g • s)
  simpa only [set_lintegral_one, Pi.one_def,
    Measure.restrict_apply₀ ((h.nullMeasurableSet_smul _).mono_ac H), inter_comm] using
    h.lintegral_eq_tsum_of_ac H 1
#align measure_theory.is_fundamental_domain.measure_eq_tsum_of_ac MeasureTheory.IsFundamentalDomain.measure_eq_tsum_of_ac
#align measure_theory.is_add_fundamental_domain.measure_eq_tsum_of_ac MeasureTheory.IsAddFundamentalDomain.measure_eq_tsum_of_ac

@[to_additive]
theorem measure_eq_tsum' (h : IsFundamentalDomain G s μ) (t : Set α) :
    μ t = ∑' g : G, μ (t ∩ g • s) :=
  h.measure_eq_tsum_of_ac AbsolutelyContinuous.rfl t
#align measure_theory.is_fundamental_domain.measure_eq_tsum' MeasureTheory.IsFundamentalDomain.measure_eq_tsum'
#align measure_theory.is_add_fundamental_domain.measure_eq_tsum' MeasureTheory.IsAddFundamentalDomain.measure_eq_tsum'

@[to_additive]
theorem measure_eq_tsum (h : IsFundamentalDomain G s μ) (t : Set α) :
    μ t = ∑' g : G, μ (g • t ∩ s) := by
  simpa only [set_lintegral_one] using h.set_lintegral_eq_tsum' (fun _ => 1) t
  -- 🎉 no goals
#align measure_theory.is_fundamental_domain.measure_eq_tsum MeasureTheory.IsFundamentalDomain.measure_eq_tsum
#align measure_theory.is_add_fundamental_domain.measure_eq_tsum MeasureTheory.IsAddFundamentalDomain.measure_eq_tsum

@[to_additive]
theorem measure_zero_of_invariant (h : IsFundamentalDomain G s μ) (t : Set α)
    (ht : ∀ g : G, g • t = t) (hts : μ (t ∩ s) = 0) : μ t = 0 := by
  rw [measure_eq_tsum h]; simp [ht, hts]
  -- ⊢ ∑' (g : G), ↑↑μ (g • t ∩ s) = 0
                          -- 🎉 no goals
#align measure_theory.is_fundamental_domain.measure_zero_of_invariant MeasureTheory.IsFundamentalDomain.measure_zero_of_invariant
#align measure_theory.is_add_fundamental_domain.measure_zero_of_invariant MeasureTheory.IsAddFundamentalDomain.measure_zero_of_invariant

/-- Given a measure space with an action of a finite group `G`, the measure of any `G`-invariant set
is determined by the measure of its intersection with a fundamental domain for the action of `G`. -/
@[to_additive measure_eq_card_smul_of_vadd_ae_eq_self "Given a measure space with an action of a
  finite additive group `G`, the measure of any `G`-invariant set is determined by the measure of
  its intersection with a fundamental domain for the action of `G`."]
theorem measure_eq_card_smul_of_smul_ae_eq_self [Finite G] (h : IsFundamentalDomain G s μ)
    (t : Set α) (ht : ∀ g : G, (g • t : Set α) =ᵐ[μ] t) : μ t = Nat.card G • μ (t ∩ s) := by
  haveI : Fintype G := Fintype.ofFinite G
  -- ⊢ ↑↑μ t = Nat.card G • ↑↑μ (t ∩ s)
  rw [h.measure_eq_tsum]
  -- ⊢ ∑' (g : G), ↑↑μ (g • t ∩ s) = Nat.card G • ↑↑μ (t ∩ s)
  replace ht : ∀ g : G, (g • t ∩ s : Set α) =ᵐ[μ] (t ∩ s : Set α) := fun g =>
    ae_eq_set_inter (ht g) (ae_eq_refl s)
  simp_rw [measure_congr (ht _), tsum_fintype, Finset.sum_const, Nat.card_eq_fintype_card,
    Finset.card_univ]
#align measure_theory.is_fundamental_domain.measure_eq_card_smul_of_smul_ae_eq_self MeasureTheory.IsFundamentalDomain.measure_eq_card_smul_of_smul_ae_eq_self
#align measure_theory.is_add_fundamental_domain.measure_eq_card_smul_of_vadd_ae_eq_self MeasureTheory.IsAddFundamentalDomain.measure_eq_card_smul_of_vadd_ae_eq_self

@[to_additive]
protected theorem set_lintegral_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
    (f : α → ℝ≥0∞) (hf : ∀ (g : G) (x), f (g • x) = f x) :
    ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ :=
  calc
    ∫⁻ x in s, f x ∂μ = ∑' g : G, ∫⁻ x in s ∩ g • t, f x ∂μ := ht.set_lintegral_eq_tsum _ _
    _ = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ := by simp only [hf, inter_comm]
                                                          -- 🎉 no goals
    _ = ∫⁻ x in t, f x ∂μ := (hs.set_lintegral_eq_tsum' _ _).symm
#align measure_theory.is_fundamental_domain.set_lintegral_eq MeasureTheory.IsFundamentalDomain.set_lintegral_eq
#align measure_theory.is_add_fundamental_domain.set_lintegral_eq MeasureTheory.IsAddFundamentalDomain.set_lintegral_eq

@[to_additive]
theorem measure_set_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ) {A : Set α}
    (hA₀ : MeasurableSet A) (hA : ∀ g : G, (fun x => g • x) ⁻¹' A = A) : μ (A ∩ s) = μ (A ∩ t) := by
  have : ∫⁻ x in s, A.indicator 1 x ∂μ = ∫⁻ x in t, A.indicator 1 x ∂μ := by
    refine hs.set_lintegral_eq ht (Set.indicator A fun _ => 1) fun g x ↦ ?_
    convert (Set.indicator_comp_right (g • · : α → α) (g := fun _ ↦ (1 : ℝ≥0∞))).symm
    rw [hA g]
  simpa [Measure.restrict_apply hA₀, lintegral_indicator _ hA₀] using this
  -- 🎉 no goals
#align measure_theory.is_fundamental_domain.measure_set_eq MeasureTheory.IsFundamentalDomain.measure_set_eq
#align measure_theory.is_add_fundamental_domain.measure_set_eq MeasureTheory.IsAddFundamentalDomain.measure_set_eq

/-- If `s` and `t` are two fundamental domains of the same action, then their measures are equal. -/
@[to_additive "If `s` and `t` are two fundamental domains of the same action, then their measures
  are equal."]
protected theorem measure_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ) :
    μ s = μ t := by
  simpa only [set_lintegral_one] using hs.set_lintegral_eq ht (fun _ => 1) fun _ _ => rfl
  -- 🎉 no goals
#align measure_theory.is_fundamental_domain.measure_eq MeasureTheory.IsFundamentalDomain.measure_eq
#align measure_theory.is_add_fundamental_domain.measure_eq MeasureTheory.IsAddFundamentalDomain.measure_eq

@[to_additive]
protected theorem aEStronglyMeasurable_on_iff {β : Type*} [TopologicalSpace β]
    [PseudoMetrizableSpace β] (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
    {f : α → β} (hf : ∀ (g : G) (x), f (g • x) = f x) :
    AEStronglyMeasurable f (μ.restrict s) ↔ AEStronglyMeasurable f (μ.restrict t) :=
  calc
    AEStronglyMeasurable f (μ.restrict s) ↔
        AEStronglyMeasurable f (Measure.sum fun g : G => μ.restrict (g • t ∩ s)) := by
      simp only [← ht.restrict_restrict,
        ht.sum_restrict_of_ac restrict_le_self.absolutelyContinuous]
    _ ↔ ∀ g : G, AEStronglyMeasurable f (μ.restrict (g • (g⁻¹ • s ∩ t))) := by
      simp only [smul_set_inter, inter_comm, smul_inv_smul, aestronglyMeasurable_sum_measure_iff]
      -- 🎉 no goals
    _ ↔ ∀ g : G, AEStronglyMeasurable f (μ.restrict (g⁻¹ • (g⁻¹⁻¹ • s ∩ t))) :=
      inv_surjective.forall
    _ ↔ ∀ g : G, AEStronglyMeasurable f (μ.restrict (g⁻¹ • (g • s ∩ t))) := by simp only [inv_inv]
                                                                               -- 🎉 no goals
    _ ↔ ∀ g : G, AEStronglyMeasurable f (μ.restrict (g • s ∩ t)) := by
      refine' forall_congr' fun g => _
      -- ⊢ AEStronglyMeasurable f (Measure.restrict μ (g⁻¹ • (g • s ∩ t))) ↔ AEStrongly …
      have he : MeasurableEmbedding ((· • ·) g⁻¹ : α → α) := measurableEmbedding_const_smul _
      -- ⊢ AEStronglyMeasurable f (Measure.restrict μ (g⁻¹ • (g • s ∩ t))) ↔ AEStrongly …
      rw [← image_smul, ← ((measurePreserving_smul g⁻¹ μ).restrict_image_emb he
        _).aestronglyMeasurable_comp_iff he]
      simp only [(· ∘ ·), hf]
      -- 🎉 no goals
    _ ↔ AEStronglyMeasurable f (μ.restrict t) := by
      simp only [← aestronglyMeasurable_sum_measure_iff, ← hs.restrict_restrict,
        hs.sum_restrict_of_ac restrict_le_self.absolutelyContinuous]
#align measure_theory.is_fundamental_domain.ae_strongly_measurable_on_iff MeasureTheory.IsFundamentalDomain.aEStronglyMeasurable_on_iff
#align measure_theory.is_add_fundamental_domain.ae_strongly_measurable_on_iff MeasureTheory.IsAddFundamentalDomain.aEStronglyMeasurable_on_iff

@[to_additive]
protected theorem hasFiniteIntegral_on_iff (hs : IsFundamentalDomain G s μ)
    (ht : IsFundamentalDomain G t μ) {f : α → E} (hf : ∀ (g : G) (x), f (g • x) = f x) :
    HasFiniteIntegral f (μ.restrict s) ↔ HasFiniteIntegral f (μ.restrict t) := by
  dsimp only [HasFiniteIntegral]
  -- ⊢ ∫⁻ (a : α) in s, ↑‖f a‖₊ ∂μ < ⊤ ↔ ∫⁻ (a : α) in t, ↑‖f a‖₊ ∂μ < ⊤
  rw [hs.set_lintegral_eq ht]
  -- ⊢ ∀ (g : G) (x : α), ↑‖f (g • x)‖₊ = ↑‖f x‖₊
  intro g x; rw [hf]
  -- ⊢ ↑‖f (g • x)‖₊ = ↑‖f x‖₊
             -- 🎉 no goals
#align measure_theory.is_fundamental_domain.has_finite_integral_on_iff MeasureTheory.IsFundamentalDomain.hasFiniteIntegral_on_iff
#align measure_theory.is_add_fundamental_domain.has_finite_integral_on_iff MeasureTheory.IsAddFundamentalDomain.hasFiniteIntegral_on_iff

@[to_additive]
protected theorem integrableOn_iff (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
    {f : α → E} (hf : ∀ (g : G) (x), f (g • x) = f x) : IntegrableOn f s μ ↔ IntegrableOn f t μ :=
  and_congr (hs.aEStronglyMeasurable_on_iff ht hf) (hs.hasFiniteIntegral_on_iff ht hf)
#align measure_theory.is_fundamental_domain.integrable_on_iff MeasureTheory.IsFundamentalDomain.integrableOn_iff
#align measure_theory.is_add_fundamental_domain.integrable_on_iff MeasureTheory.IsAddFundamentalDomain.integrableOn_iff

variable [NormedSpace ℝ E] [CompleteSpace E]

@[to_additive]
theorem integral_eq_tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (f : α → E)
    (hf : Integrable f ν) : ∫ x, f x ∂ν = ∑' g : G, ∫ x in g • s, f x ∂ν := by
  rw [← MeasureTheory.integral_sum_measure, h.sum_restrict_of_ac hν]
  -- ⊢ Integrable fun x => f x
  rw [h.sum_restrict_of_ac hν]
  -- ⊢ Integrable fun x => f x
  exact hf
  -- 🎉 no goals
#align measure_theory.is_fundamental_domain.integral_eq_tsum_of_ac MeasureTheory.IsFundamentalDomain.integral_eq_tsum_of_ac
#align measure_theory.is_add_fundamental_domain.integral_eq_tsum_of_ac MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum_of_ac

@[to_additive]
theorem integral_eq_tsum (h : IsFundamentalDomain G s μ) (f : α → E) (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ :=
  integral_eq_tsum_of_ac h (by rfl) f hf
                               -- 🎉 no goals
#align measure_theory.is_fundamental_domain.integral_eq_tsum MeasureTheory.IsFundamentalDomain.integral_eq_tsum
#align measure_theory.is_add_fundamental_domain.integral_eq_tsum MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum

@[to_additive]
theorem integral_eq_tsum' (h : IsFundamentalDomain G s μ) (f : α → E) (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑' g : G, ∫ x in s, f (g⁻¹ • x) ∂μ :=
  calc
    ∫ x, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ := h.integral_eq_tsum f hf
    _ = ∑' g : G, ∫ x in g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫ x in s, f (g⁻¹ • x) ∂μ := tsum_congr fun g =>
      (measurePreserving_smul g⁻¹ μ).set_integral_image_emb (measurableEmbedding_const_smul _) _ _
#align measure_theory.is_fundamental_domain.integral_eq_tsum' MeasureTheory.IsFundamentalDomain.integral_eq_tsum'
#align measure_theory.is_add_fundamental_domain.integral_eq_tsum' MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum'

@[to_additive]
theorem set_integral_eq_tsum (h : IsFundamentalDomain G s μ) {f : α → E} {t : Set α}
    (hf : IntegrableOn f t μ) : ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in t ∩ g • s, f x ∂μ :=
  calc
    ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ.restrict t :=
      h.integral_eq_tsum_of_ac restrict_le_self.absolutelyContinuous f hf
    _ = ∑' g : G, ∫ x in t ∩ g • s, f x ∂μ := by
      simp only [h.restrict_restrict, measure_smul, inter_comm]
      -- 🎉 no goals
#align measure_theory.is_fundamental_domain.set_integral_eq_tsum MeasureTheory.IsFundamentalDomain.set_integral_eq_tsum
#align measure_theory.is_add_fundamental_domain.set_integral_eq_tsum MeasureTheory.IsAddFundamentalDomain.set_integral_eq_tsum

@[to_additive]
theorem set_integral_eq_tsum' (h : IsFundamentalDomain G s μ) {f : α → E} {t : Set α}
    (hf : IntegrableOn f t μ) : ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
  calc
    ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in t ∩ g • s, f x ∂μ := h.set_integral_eq_tsum hf
    _ = ∑' g : G, ∫ x in t ∩ g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫ x in g⁻¹ • (g • t ∩ s), f x ∂μ := by simp only [smul_set_inter, inv_smul_smul]
                                                         -- 🎉 no goals
    _ = ∑' g : G, ∫ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
      tsum_congr fun g =>
        (measurePreserving_smul g⁻¹ μ).set_integral_image_emb (measurableEmbedding_const_smul _) _ _
#align measure_theory.is_fundamental_domain.set_integral_eq_tsum' MeasureTheory.IsFundamentalDomain.set_integral_eq_tsum'
#align measure_theory.is_add_fundamental_domain.set_integral_eq_tsum' MeasureTheory.IsAddFundamentalDomain.set_integral_eq_tsum'

@[to_additive]
protected theorem set_integral_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
    {f : α → E} (hf : ∀ (g : G) (x), f (g • x) = f x) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ := by
  by_cases hfs : IntegrableOn f s μ
  -- ⊢ ∫ (x : α) in s, f x ∂μ = ∫ (x : α) in t, f x ∂μ
  · have hft : IntegrableOn f t μ := by rwa [ht.integrableOn_iff hs hf]
    -- ⊢ ∫ (x : α) in s, f x ∂μ = ∫ (x : α) in t, f x ∂μ
    calc
      ∫ x in s, f x ∂μ = ∑' g : G, ∫ x in s ∩ g • t, f x ∂μ := ht.set_integral_eq_tsum hfs
      _ = ∑' g : G, ∫ x in g • t ∩ s, f (g⁻¹ • x) ∂μ := by simp only [hf, inter_comm]
      _ = ∫ x in t, f x ∂μ := (hs.set_integral_eq_tsum' hft).symm
  · rw [integral_undef hfs, integral_undef]
    -- ⊢ ¬Integrable fun x => f x
    rwa [hs.integrableOn_iff ht hf] at hfs
    -- 🎉 no goals
#align measure_theory.is_fundamental_domain.set_integral_eq MeasureTheory.IsFundamentalDomain.set_integral_eq
#align measure_theory.is_add_fundamental_domain.set_integral_eq MeasureTheory.IsAddFundamentalDomain.set_integral_eq

/-- If the action of a countable group `G` admits an invariant measure `μ` with a fundamental domain
`s`, then every null-measurable set `t` such that the sets `g • t ∩ s` are pairwise a.e.-disjoint
has measure at most `μ s`. -/
@[to_additive "If the additive action of a countable group `G` admits an invariant measure `μ` with
  a fundamental domain `s`, then every null-measurable set `t` such that the sets `g +ᵥ t ∩ s` are
  pairwise a.e.-disjoint has measure at most `μ s`."]
theorem measure_le_of_pairwise_disjoint (hs : IsFundamentalDomain G s μ)
    (ht : NullMeasurableSet t μ) (hd : Pairwise (AEDisjoint μ on fun g : G => g • t ∩ s)) :
    μ t ≤ μ s :=
  calc
    μ t = ∑' g : G, μ (g • t ∩ s) := hs.measure_eq_tsum t
    _ = μ (⋃ g : G, g • t ∩ s) := Eq.symm <| measure_iUnion₀ hd fun _ =>
      (ht.smul _).inter hs.nullMeasurableSet
    _ ≤ μ s := measure_mono (iUnion_subset fun _ => inter_subset_right _ _)
#align measure_theory.is_fundamental_domain.measure_le_of_pairwise_disjoint MeasureTheory.IsFundamentalDomain.measure_le_of_pairwise_disjoint
#align measure_theory.is_add_fundamental_domain.measure_le_of_pairwise_disjoint MeasureTheory.IsAddFundamentalDomain.measure_le_of_pairwise_disjoint

/-- If the action of a countable group `G` admits an invariant measure `μ` with a fundamental domain
`s`, then every null-measurable set `t` of measure strictly greater than `μ s` contains two
points `x y` such that `g • x = y` for some `g ≠ 1`. -/
@[to_additive "If the additive action of a countable group `G` admits an invariant measure `μ` with
  a fundamental domain `s`, then every null-measurable set `t` of measure strictly greater than
  `μ s` contains two points `x y` such that `g +ᵥ x = y` for some `g ≠ 0`."]
theorem exists_ne_one_smul_eq (hs : IsFundamentalDomain G s μ) (htm : NullMeasurableSet t μ)
    (ht : μ s < μ t) : ∃ x ∈ t, ∃ y ∈ t, ∃ g, g ≠ (1 : G) ∧ g • x = y := by
  contrapose! ht
  -- ⊢ ↑↑μ t ≤ ↑↑μ s
  refine' hs.measure_le_of_pairwise_disjoint htm (Pairwise.aedisjoint fun g₁ g₂ hne => _)
  -- ⊢ (Disjoint on fun g => g • t ∩ s) g₁ g₂
  dsimp [Function.onFun]
  -- ⊢ Disjoint (g₁ • t ∩ s) (g₂ • t ∩ s)
  refine' (Disjoint.inf_left _ _).inf_right _
  -- ⊢ Disjoint (g₁ • t) (g₂ • t)
  rw [Set.disjoint_left]
  -- ⊢ ∀ ⦃a : α⦄, a ∈ g₁ • t → ¬a ∈ g₂ • t
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy : g₂ • y = g₁ • x⟩
  -- ⊢ False
  refine' ht x hx y hy (g₂⁻¹ * g₁) (mt inv_mul_eq_one.1 hne.symm) _
  -- ⊢ (g₂⁻¹ * g₁) • x = y
  rw [mul_smul, ← hxy, inv_smul_smul]
  -- 🎉 no goals
#align measure_theory.is_fundamental_domain.exists_ne_one_smul_eq MeasureTheory.IsFundamentalDomain.exists_ne_one_smul_eq
#align measure_theory.is_add_fundamental_domain.exists_ne_zero_vadd_eq MeasureTheory.IsAddFundamentalDomain.exists_ne_zero_vadd_eq

/-- If `f` is invariant under the action of a countable group `G`, and `μ` is a `G`-invariant
  measure with a fundamental domain `s`, then the `essSup` of `f` restricted to `s` is the same as
  that of `f` on all of its domain. -/
@[to_additive "If `f` is invariant under the action of a countable additive group `G`, and `μ` is a
  `G`-invariant measure with a fundamental domain `s`, then the `ess_sup` of `f` restricted to `s`
  is the same as that of `f` on all of its domain."]
theorem essSup_measure_restrict (hs : IsFundamentalDomain G s μ) {f : α → ℝ≥0∞}
    (hf : ∀ γ : G, ∀ x : α, f (γ • x) = f x) : essSup f (μ.restrict s) = essSup f μ := by
  refine' le_antisymm (essSup_mono_measure' Measure.restrict_le_self) _
  -- ⊢ essSup f μ ≤ essSup f (Measure.restrict μ s)
  rw [essSup_eq_sInf (μ.restrict s) f, essSup_eq_sInf μ f]
  -- ⊢ sInf {a | ↑↑μ {x | a < f x} = 0} ≤ sInf {a | ↑↑(Measure.restrict μ s) {x | a …
  refine' sInf_le_sInf _
  -- ⊢ {a | ↑↑(Measure.restrict μ s) {x | a < f x} = 0} ⊆ {a | ↑↑μ {x | a < f x} = 0}
  rintro a (ha : (μ.restrict s) {x : α | a < f x} = 0)
  -- ⊢ a ∈ {a | ↑↑μ {x | a < f x} = 0}
  rw [Measure.restrict_apply₀' hs.nullMeasurableSet] at ha
  -- ⊢ a ∈ {a | ↑↑μ {x | a < f x} = 0}
  refine' measure_zero_of_invariant hs _ _ ha
  -- ⊢ ∀ (g : G), g • {x | a < f x} = {x | a < f x}
  intro γ
  -- ⊢ γ • {x | a < f x} = {x | a < f x}
  ext x
  -- ⊢ x ∈ γ • {x | a < f x} ↔ x ∈ {x | a < f x}
  rw [mem_smul_set_iff_inv_smul_mem]
  -- ⊢ γ⁻¹ • x ∈ {x | a < f x} ↔ x ∈ {x | a < f x}
  simp only [mem_setOf_eq, hf γ⁻¹ x]
  -- 🎉 no goals
#align measure_theory.is_fundamental_domain.ess_sup_measure_restrict MeasureTheory.IsFundamentalDomain.essSup_measure_restrict
#align measure_theory.is_add_fundamental_domain.ess_sup_measure_restrict MeasureTheory.IsAddFundamentalDomain.essSup_measure_restrict

end IsFundamentalDomain

/-! ### Interior/frontier of a fundamental domain -/

section MeasurableSpace

variable (G) [Group G] [MulAction G α] (s : Set α) {x : α}

/-- The boundary of a fundamental domain, those points of the domain that also lie in a nontrivial
translate. -/
@[to_additive MeasureTheory.addFundamentalFrontier "The boundary of a fundamental domain, those
  points of the domain that also lie in a nontrivial translate."]
def fundamentalFrontier : Set α :=
  s ∩ ⋃ (g : G) (_ : g ≠ 1), g • s
#align measure_theory.fundamental_frontier MeasureTheory.fundamentalFrontier
#align measure_theory.add_fundamental_frontier MeasureTheory.addFundamentalFrontier

/-- The interior of a fundamental domain, those points of the domain not lying in any translate. -/
@[to_additive MeasureTheory.addFundamentalInterior "The interior of a fundamental domain, those
  points of the domain not lying in any translate."]
def fundamentalInterior : Set α :=
  s \ ⋃ (g : G) (_ : g ≠ 1), g • s
#align measure_theory.fundamental_interior MeasureTheory.fundamentalInterior
#align measure_theory.add_fundamental_interior MeasureTheory.addFundamentalInterior

variable {G s}

@[to_additive (attr := simp) MeasureTheory.mem_addFundamentalFrontier]
theorem mem_fundamentalFrontier :
    x ∈ fundamentalFrontier G s ↔ x ∈ s ∧ ∃ g : G, g ≠ 1 ∧ x ∈ g • s := by
  simp [fundamentalFrontier]
  -- 🎉 no goals
#align measure_theory.mem_fundamental_frontier MeasureTheory.mem_fundamentalFrontier
#align measure_theory.mem_add_fundamental_frontier MeasureTheory.mem_addFundamentalFrontier

@[to_additive (attr := simp) MeasureTheory.mem_addFundamentalInterior]
theorem mem_fundamentalInterior :
    x ∈ fundamentalInterior G s ↔ x ∈ s ∧ ∀ g : G, g ≠ 1 → x ∉ g • s := by
  simp [fundamentalInterior]
  -- 🎉 no goals
#align measure_theory.mem_fundamental_interior MeasureTheory.mem_fundamentalInterior
#align measure_theory.mem_add_fundamental_interior MeasureTheory.mem_addFundamentalInterior

@[to_additive MeasureTheory.addFundamentalFrontier_subset]
theorem fundamentalFrontier_subset : fundamentalFrontier G s ⊆ s :=
  inter_subset_left _ _
#align measure_theory.fundamental_frontier_subset MeasureTheory.fundamentalFrontier_subset
#align measure_theory.add_fundamental_frontier_subset MeasureTheory.addFundamentalFrontier_subset

@[to_additive MeasureTheory.addFundamentalInterior_subset]
theorem fundamentalInterior_subset : fundamentalInterior G s ⊆ s :=
  diff_subset _ _
#align measure_theory.fundamental_interior_subset MeasureTheory.fundamentalInterior_subset
#align measure_theory.add_fundamental_interior_subset MeasureTheory.addFundamentalInterior_subset

variable (G s)

@[to_additive MeasureTheory.disjoint_addFundamentalInterior_addFundamentalFrontier]
theorem disjoint_fundamentalInterior_fundamentalFrontier :
    Disjoint (fundamentalInterior G s) (fundamentalFrontier G s) :=
  disjoint_sdiff_self_left.mono_right inf_le_right
#align measure_theory.disjoint_fundamental_interior_fundamental_frontier MeasureTheory.disjoint_fundamentalInterior_fundamentalFrontier
#align measure_theory.disjoint_add_fundamental_interior_add_fundamental_frontier MeasureTheory.disjoint_addFundamentalInterior_addFundamentalFrontier

@[to_additive (attr := simp) MeasureTheory.addFundamentalInterior_union_addFundamentalFrontier]
theorem fundamentalInterior_union_fundamentalFrontier :
    fundamentalInterior G s ∪ fundamentalFrontier G s = s :=
  diff_union_inter _ _
#align measure_theory.fundamental_interior_union_fundamental_frontier MeasureTheory.fundamentalInterior_union_fundamentalFrontier
#align measure_theory.add_fundamental_interior_union_add_fundamental_frontier MeasureTheory.addFundamentalInterior_union_addFundamentalFrontier

@[to_additive (attr := simp) MeasureTheory.addFundamentalFrontier_union_addFundamentalInterior]
theorem fundamentalFrontier_union_fundamentalInterior :
    fundamentalFrontier G s ∪ fundamentalInterior G s = s :=
  inter_union_diff _ _
#align measure_theory.fundamental_frontier_union_fundamental_interior MeasureTheory.fundamentalFrontier_union_fundamentalInterior
-- porting note: there is a typo in `to_additive` in mathlib3, so there is no additive version

@[to_additive (attr := simp) MeasureTheory.sdiff_addFundamentalInterior]
theorem sdiff_fundamentalInterior : s \ fundamentalInterior G s = fundamentalFrontier G s :=
  sdiff_sdiff_right_self
#align measure_theory.sdiff_fundamental_interior MeasureTheory.sdiff_fundamentalInterior
#align measure_theory.sdiff_add_fundamental_interior MeasureTheory.sdiff_addFundamentalInterior

@[to_additive (attr := simp) MeasureTheory.sdiff_addFundamentalFrontier]
theorem sdiff_fundamentalFrontier : s \ fundamentalFrontier G s = fundamentalInterior G s :=
  diff_self_inter
#align measure_theory.sdiff_fundamental_frontier MeasureTheory.sdiff_fundamentalFrontier
#align measure_theory.sdiff_add_fundamental_frontier MeasureTheory.sdiff_addFundamentalFrontier

@[to_additive (attr := simp) MeasureTheory.addFundamentalFrontier_vadd]
theorem fundamentalFrontier_smul [Group H] [MulAction H α] [SMulCommClass H G α] (g : H) :
    fundamentalFrontier G (g • s) = g • fundamentalFrontier G s := by
  simp_rw [fundamentalFrontier, smul_set_inter, smul_set_Union, smul_comm g (_ : G) (_ : Set α)]
  -- 🎉 no goals
#align measure_theory.fundamental_frontier_smul MeasureTheory.fundamentalFrontier_smul
#align measure_theory.add_fundamental_frontier_vadd MeasureTheory.addFundamentalFrontier_vadd

@[to_additive (attr := simp) MeasureTheory.addFundamentalInterior_vadd]
theorem fundamentalInterior_smul [Group H] [MulAction H α] [SMulCommClass H G α] (g : H) :
    fundamentalInterior G (g • s) = g • fundamentalInterior G s := by
  simp_rw [fundamentalInterior, smul_set_sdiff, smul_set_Union, smul_comm g (_ : G) (_ : Set α)]
  -- 🎉 no goals
#align measure_theory.fundamental_interior_smul MeasureTheory.fundamentalInterior_smul
#align measure_theory.add_fundamental_interior_vadd MeasureTheory.addFundamentalInterior_vadd

@[to_additive MeasureTheory.pairwise_disjoint_addFundamentalInterior]
theorem pairwise_disjoint_fundamentalInterior :
    Pairwise (Disjoint on fun g : G => g • fundamentalInterior G s) := by
  refine' fun a b hab => disjoint_left.2 _
  -- ⊢ ∀ ⦃a_1 : α⦄, a_1 ∈ (fun g => g • fundamentalInterior G s) a → ¬a_1 ∈ (fun g  …
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  -- ⊢ False
  rw [mem_fundamentalInterior] at hx hy
  -- ⊢ False
  refine' hx.2 (a⁻¹ * b) _ _
  -- ⊢ a⁻¹ * b ≠ 1
  rwa [Ne.def, inv_mul_eq_iff_eq_mul, mul_one, eq_comm]
  -- ⊢ x ∈ (a⁻¹ * b) • s
  simpa [mul_smul, ← hxy, mem_inv_smul_set_iff] using hy.1
  -- 🎉 no goals
#align measure_theory.pairwise_disjoint_fundamental_interior MeasureTheory.pairwise_disjoint_fundamentalInterior
#align measure_theory.pairwise_disjoint_add_fundamental_interior MeasureTheory.pairwise_disjoint_addFundamentalInterior

variable [Countable G] [MeasurableSpace G] [MeasurableSpace α] [MeasurableSMul G α] {μ : Measure α}
  [SMulInvariantMeasure G α μ]

@[to_additive MeasureTheory.NullMeasurableSet.addFundamentalFrontier]
protected theorem NullMeasurableSet.fundamentalFrontier (hs : NullMeasurableSet s μ) :
    NullMeasurableSet (fundamentalFrontier G s) μ :=
  hs.inter <| .iUnion fun _ => .iUnion fun _ => hs.smul _
#align measure_theory.null_measurable_set.fundamental_frontier MeasureTheory.NullMeasurableSet.fundamentalFrontier
#align measure_theory.null_measurable_set.add_fundamental_frontier MeasureTheory.NullMeasurableSet.addFundamentalFrontier

@[to_additive MeasureTheory.NullMeasurableSet.addFundamentalInterior]
protected theorem NullMeasurableSet.fundamentalInterior (hs : NullMeasurableSet s μ) :
    NullMeasurableSet (fundamentalInterior G s) μ :=
  hs.diff <| .iUnion fun _ => .iUnion fun _ => hs.smul _
#align measure_theory.null_measurable_set.fundamental_interior MeasureTheory.NullMeasurableSet.fundamentalInterior
#align measure_theory.null_measurable_set.add_fundamental_interior MeasureTheory.NullMeasurableSet.addFundamentalInterior

end MeasurableSpace

namespace IsFundamentalDomain

section Group

variable [Countable G] [Group G] [MulAction G α] [MeasurableSpace α] {μ : Measure α} {s : Set α}
  (hs : IsFundamentalDomain G s μ)

@[to_additive MeasureTheory.IsAddFundamentalDomain.measure_addFundamentalFrontier]
theorem measure_fundamentalFrontier : μ (fundamentalFrontier G s) = 0 := by
  simpa only [fundamentalFrontier, iUnion₂_inter, measure_iUnion_null_iff', one_smul,
    measure_iUnion_null_iff, inter_comm s, Function.onFun] using fun g (hg : g ≠ 1) =>
    hs.aedisjoint hg
#align measure_theory.is_fundamental_domain.measure_fundamental_frontier MeasureTheory.IsFundamentalDomain.measure_fundamentalFrontier
#align measure_theory.is_add_fundamental_domain.measure_add_fundamental_frontier MeasureTheory.IsAddFundamentalDomain.measure_addFundamentalFrontier

@[to_additive MeasureTheory.IsAddFundamentalDomain.measure_addFundamentalInterior]
theorem measure_fundamentalInterior : μ (fundamentalInterior G s) = μ s :=
  measure_diff_null' hs.measure_fundamentalFrontier
#align measure_theory.is_fundamental_domain.measure_fundamental_interior MeasureTheory.IsFundamentalDomain.measure_fundamentalInterior
#align measure_theory.is_add_fundamental_domain.measure_add_fundamental_interior MeasureTheory.IsAddFundamentalDomain.measure_addFundamentalInterior

end Group

variable [Countable G] [Group G] [MulAction G α] [MeasurableSpace α] {μ : Measure α} {s : Set α}
  (hs : IsFundamentalDomain G s μ) [MeasurableSpace G] [MeasurableSMul G α]
  [SMulInvariantMeasure G α μ]

protected theorem fundamentalInterior : IsFundamentalDomain G (fundamentalInterior G s) μ where
  nullMeasurableSet := hs.nullMeasurableSet.fundamentalInterior _ _
  ae_covers := by
    simp_rw [ae_iff, not_exists, ← mem_inv_smul_set_iff, setOf_forall, ← compl_setOf,
      setOf_mem_eq, ← compl_iUnion]
    have :
      ((⋃ g : G, g⁻¹ • s) \ ⋃ g : G, g⁻¹ • fundamentalFrontier G s) ⊆
        ⋃ g : G, g⁻¹ • fundamentalInterior G s := by
      simp_rw [diff_subset_iff, ← iUnion_union_distrib, ← smul_set_union (α := G) (β := α),
        fundamentalFrontier_union_fundamentalInterior]; rfl
    refine' eq_bot_mono (μ.mono <| compl_subset_compl.2 this) _
    -- ⊢ ↑↑μ ((⋃ (g : G), g⁻¹ • s) \ ⋃ (g : G), g⁻¹ • fundamentalFrontier G s)ᶜ = ⊥
    simp only [iUnion_inv_smul, compl_sdiff, ENNReal.bot_eq_zero, himp_eq, sup_eq_union,
      @iUnion_smul_eq_setOf_exists _ _ _ _ s]
    exact measure_union_null
      (measure_iUnion_null fun _ => measure_smul_null hs.measure_fundamentalFrontier _) hs.ae_covers
  aedisjoint := (pairwise_disjoint_fundamentalInterior _ _).mono fun _ _ => Disjoint.aedisjoint
#align measure_theory.is_fundamental_domain.fundamental_interior MeasureTheory.IsFundamentalDomain.fundamentalInterior

end IsFundamentalDomain

end MeasureTheory
