/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Alex Kontorovich, Heather Macbeth
-/
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Group.Pointwise

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

* We define the `HasFundamentalDomain` typeclass, in particular to be able to define the `covolume`
of a quotient of `α` by a group `G`, which under reasonable conditions does not depend on the choice
of fundamental domain.

* We define the `QuotientMeasureEqMeasurePreimage` typeclass to describe a situation in which a
measure `μ` on `α ⧸ G` can be computed by taking a measure `ν` on `α` of the intersection of the
pullback with a fundamental domain.

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

/-- A measurable set `s` is a *fundamental domain* for an action of a group `G` on a measurable
space `α` with respect to a measure `α` if the sets `g • s`, `g : G`, are pairwise a.e. disjoint and
cover the whole space. -/
@[to_additive IsAddFundamentalDomain]
structure IsFundamentalDomain (G : Type*) {α : Type*} [One G] [SMul G α] [MeasurableSpace α]
    (s : Set α) (μ : Measure α := by volume_tac) : Prop where
  protected nullMeasurableSet : NullMeasurableSet s μ
  protected ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ s
  protected aedisjoint : Pairwise <| (AEDisjoint μ on fun g : G => g • s)

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
  ae_covers := Eventually.of_forall fun x ↦ (h_exists x).exists
  aedisjoint a b hab := Disjoint.aedisjoint <| disjoint_left.2 fun x hxa hxb => by
    rw [mem_smul_set_iff_inv_smul_mem] at hxa hxb
    exact hab (inv_injective <| (h_exists x).unique hxa hxb)

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
    (h_ae_disjoint : ∀ g ≠ (1 : G), AEDisjoint μ (g • s) s)
    (h_qmp : ∀ g : G, QuasiMeasurePreserving (g • · : α → α) μ μ)
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
      refine le_antisymm (measure_mono <| subset_univ _) ?_
      rw [measure_iUnion₀ aedisjoint h_meas]
      exact h_measure_univ_le }

@[to_additive]
theorem iUnion_smul_ae_eq (h : IsFundamentalDomain G s μ) : ⋃ g : G, g • s =ᵐ[μ] univ :=
  eventuallyEq_univ.2 <| h.ae_covers.mono fun _ ⟨g, hg⟩ =>
    mem_iUnion.2 ⟨g⁻¹, _, hg, inv_smul_smul _ _⟩

@[to_additive]
theorem measure_ne_zero [Countable G] [SMulInvariantMeasure G α μ]
    (hμ : μ ≠ 0) (h : IsFundamentalDomain G s μ) : μ s ≠ 0 := by
  have hc := measure_univ_pos.mpr hμ
  contrapose! hc
  rw [← measure_congr h.iUnion_smul_ae_eq]
  refine le_trans (measure_iUnion_le _) ?_
  simp_rw [measure_smul, hc, tsum_zero, le_refl]

@[to_additive]
theorem mono (h : IsFundamentalDomain G s μ) {ν : Measure α} (hle : ν ≪ μ) :
    IsFundamentalDomain G s ν :=
  ⟨h.1.mono_ac hle, hle h.2, h.aedisjoint.mono fun _ _ h => hle h⟩

@[to_additive]
theorem preimage_of_equiv {ν : Measure β} (h : IsFundamentalDomain G s μ) {f : β → α}
    (hf : QuasiMeasurePreserving f ν μ) {e : G → H} (he : Bijective e)
    (hef : ∀ g, Semiconj f (e g • ·) (g • ·)) : IsFundamentalDomain H (f ⁻¹' s) ν where
  nullMeasurableSet := h.nullMeasurableSet.preimage hf
  ae_covers := (hf.ae h.ae_covers).mono fun x ⟨g, hg⟩ => ⟨e g, by rwa [mem_preimage, hef g x]⟩
  aedisjoint a b hab := by
    lift e to G ≃ H using he
    have : (e.symm a⁻¹)⁻¹ ≠ (e.symm b⁻¹)⁻¹ := by simp [hab]
    have := (h.aedisjoint this).preimage hf
    simp only [Semiconj] at hef
    simpa only [onFun, ← preimage_smul_inv, preimage_preimage, ← hef, e.apply_symm_apply, inv_inv]
      using this

@[to_additive]
theorem image_of_equiv {ν : Measure β} (h : IsFundamentalDomain G s μ) (f : α ≃ β)
    (hf : QuasiMeasurePreserving f.symm ν μ) (e : H ≃ G)
    (hef : ∀ g, Semiconj f (e g • ·) (g • ·)) : IsFundamentalDomain H (f '' s) ν := by
  rw [f.image_eq_preimage]
  refine h.preimage_of_equiv hf e.symm.bijective fun g x => ?_
  rcases f.surjective x with ⟨x, rfl⟩
  rw [← hef _ _, f.symm_apply_apply, f.symm_apply_apply, e.apply_symm_apply]

@[to_additive]
theorem pairwise_aedisjoint_of_ac {ν} (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) :
    Pairwise fun g₁ g₂ : G => AEDisjoint ν (g₁ • s) (g₂ • s) :=
  h.aedisjoint.mono fun _ _ H => hν H

@[to_additive]
theorem smul_of_comm {G' : Type*} [Group G'] [MulAction G' α] [MeasurableSpace G']
    [MeasurableSMul G' α] [SMulInvariantMeasure G' α μ] [SMulCommClass G' G α]
    (h : IsFundamentalDomain G s μ) (g : G') : IsFundamentalDomain G (g • s) μ :=
  h.image_of_equiv (MulAction.toPerm g) (measurePreserving_smul _ _).quasiMeasurePreserving
    (Equiv.refl _) <| smul_comm g

variable [MeasurableSpace G] [MeasurableSMul G α] [SMulInvariantMeasure G α μ]

@[to_additive]
theorem nullMeasurableSet_smul (h : IsFundamentalDomain G s μ) (g : G) :
    NullMeasurableSet (g • s) μ :=
  h.nullMeasurableSet.smul g

@[to_additive]
theorem restrict_restrict (h : IsFundamentalDomain G s μ) (g : G) (t : Set α) :
    (μ.restrict t).restrict (g • s) = μ.restrict (g • s ∩ t) :=
  restrict_restrict₀ ((h.nullMeasurableSet_smul g).mono restrict_le_self)

@[to_additive]
theorem smul (h : IsFundamentalDomain G s μ) (g : G) : IsFundamentalDomain G (g • s) μ :=
  h.image_of_equiv (MulAction.toPerm g) (measurePreserving_smul _ _).quasiMeasurePreserving
    ⟨fun g' => g⁻¹ * g' * g, fun g' => g * g' * g⁻¹, fun g' => by simp [mul_assoc], fun g' => by
      simp [mul_assoc]⟩
    fun g' x => by simp [smul_smul, mul_assoc]

variable [Countable G] {ν : Measure α}

@[to_additive]
theorem sum_restrict_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) :
    (sum fun g : G => ν.restrict (g • s)) = ν := by
  rw [← restrict_iUnion_ae (h.aedisjoint.mono fun i j h => hν h) fun g =>
      (h.nullMeasurableSet_smul g).mono_ac hν,
    restrict_congr_set (hν h.iUnion_smul_ae_eq), restrict_univ]

@[to_additive]
theorem lintegral_eq_tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂ν = ∑' g : G, ∫⁻ x in g • s, f x ∂ν := by
  rw [← lintegral_sum_measure, h.sum_restrict_of_ac hν]

@[to_additive]
theorem sum_restrict (h : IsFundamentalDomain G s μ) : (sum fun g : G => μ.restrict (g • s)) = μ :=
  h.sum_restrict_of_ac (refl _)

@[to_additive]
theorem lintegral_eq_tsum (h : IsFundamentalDomain G s μ) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ :=
  h.lintegral_eq_tsum_of_ac (refl _) f

@[to_additive]
theorem lintegral_eq_tsum' (h : IsFundamentalDomain G s μ) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in s, f (g⁻¹ • x) ∂μ :=
  calc
    ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ := h.lintegral_eq_tsum f
    _ = ∑' g : G, ∫⁻ x in g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫⁻ x in s, f (g⁻¹ • x) ∂μ := tsum_congr fun g => Eq.symm <|
      (measurePreserving_smul g⁻¹ μ).setLIntegral_comp_emb (measurableEmbedding_const_smul _) _ _

@[to_additive] lemma lintegral_eq_tsum'' (h : IsFundamentalDomain G s μ) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in s, f (g • x) ∂μ :=
  (lintegral_eq_tsum' h f).trans ((Equiv.inv G).tsum_eq (fun g ↦ ∫⁻ (x : α) in s, f (g • x) ∂μ))

@[to_additive]
theorem setLIntegral_eq_tsum (h : IsFundamentalDomain G s μ) (f : α → ℝ≥0∞) (t : Set α) :
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ :=
  calc
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ.restrict t :=
      h.lintegral_eq_tsum_of_ac restrict_le_self.absolutelyContinuous _
    _ = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ := by simp only [h.restrict_restrict, inter_comm]

@[deprecated (since := "2024-06-29")]
alias set_lintegral_eq_tsum := setLIntegral_eq_tsum

@[to_additive]
theorem setLIntegral_eq_tsum' (h : IsFundamentalDomain G s μ) (f : α → ℝ≥0∞) (t : Set α) :
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
  calc
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ := h.setLIntegral_eq_tsum f t
    _ = ∑' g : G, ∫⁻ x in t ∩ g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫⁻ x in g⁻¹ • (g • t ∩ s), f x ∂μ := by simp only [smul_set_inter, inv_smul_smul]
    _ = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ := tsum_congr fun g => Eq.symm <|
      (measurePreserving_smul g⁻¹ μ).setLIntegral_comp_emb (measurableEmbedding_const_smul _) _ _

@[deprecated (since := "2024-06-29")]
alias set_lintegral_eq_tsum' := setLIntegral_eq_tsum'

@[to_additive]
theorem measure_eq_tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (t : Set α) :
    ν t = ∑' g : G, ν (t ∩ g • s) := by
  have H : ν.restrict t ≪ μ := Measure.restrict_le_self.absolutelyContinuous.trans hν
  simpa only [setLIntegral_one, Pi.one_def,
    Measure.restrict_apply₀ ((h.nullMeasurableSet_smul _).mono_ac H), inter_comm] using
    h.lintegral_eq_tsum_of_ac H 1

@[to_additive]
theorem measure_eq_tsum' (h : IsFundamentalDomain G s μ) (t : Set α) :
    μ t = ∑' g : G, μ (t ∩ g • s) :=
  h.measure_eq_tsum_of_ac AbsolutelyContinuous.rfl t

@[to_additive]
theorem measure_eq_tsum (h : IsFundamentalDomain G s μ) (t : Set α) :
    μ t = ∑' g : G, μ (g • t ∩ s) := by
  simpa only [setLIntegral_one] using h.setLIntegral_eq_tsum' (fun _ => 1) t

@[to_additive]
theorem measure_zero_of_invariant (h : IsFundamentalDomain G s μ) (t : Set α)
    (ht : ∀ g : G, g • t = t) (hts : μ (t ∩ s) = 0) : μ t = 0 := by
  rw [measure_eq_tsum h]; simp [ht, hts]

/-- Given a measure space with an action of a finite group `G`, the measure of any `G`-invariant set
is determined by the measure of its intersection with a fundamental domain for the action of `G`. -/
@[to_additive measure_eq_card_smul_of_vadd_ae_eq_self "Given a measure space with an action of a
  finite additive group `G`, the measure of any `G`-invariant set is determined by the measure of
  its intersection with a fundamental domain for the action of `G`."]
theorem measure_eq_card_smul_of_smul_ae_eq_self [Finite G] (h : IsFundamentalDomain G s μ)
    (t : Set α) (ht : ∀ g : G, (g • t : Set α) =ᵐ[μ] t) : μ t = Nat.card G • μ (t ∩ s) := by
  haveI : Fintype G := Fintype.ofFinite G
  rw [h.measure_eq_tsum]
  replace ht : ∀ g : G, (g • t ∩ s : Set α) =ᵐ[μ] (t ∩ s : Set α) := fun g =>
    ae_eq_set_inter (ht g) (ae_eq_refl s)
  simp_rw [measure_congr (ht _), tsum_fintype, Finset.sum_const, Nat.card_eq_fintype_card,
    Finset.card_univ]

@[to_additive]
protected theorem setLIntegral_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
    (f : α → ℝ≥0∞) (hf : ∀ (g : G) (x), f (g • x) = f x) :
    ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ :=
  calc
    ∫⁻ x in s, f x ∂μ = ∑' g : G, ∫⁻ x in s ∩ g • t, f x ∂μ := ht.setLIntegral_eq_tsum _ _
    _ = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ := by simp only [hf, inter_comm]
    _ = ∫⁻ x in t, f x ∂μ := (hs.setLIntegral_eq_tsum' _ _).symm

@[deprecated (since := "2024-06-29")]
alias set_lintegral_eq := MeasureTheory.IsFundamentalDomain.setLIntegral_eq

@[to_additive]
theorem measure_set_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ) {A : Set α}
    (hA₀ : MeasurableSet A) (hA : ∀ g : G, (fun x ↦ g • x) ⁻¹' A = A) : μ (A ∩ s) = μ (A ∩ t) := by
  have : ∫⁻ x in s, A.indicator 1 x ∂μ = ∫⁻ x in t, A.indicator 1 x ∂μ := by
    refine hs.setLIntegral_eq ht (Set.indicator A fun _ => 1) fun g x ↦ ?_
    convert (Set.indicator_comp_right (g • · : α → α) (g := fun _ ↦ (1 : ℝ≥0∞))).symm
    rw [hA g]
  simpa [Measure.restrict_apply hA₀, lintegral_indicator hA₀] using this

/-- If `s` and `t` are two fundamental domains of the same action, then their measures are equal. -/
@[to_additive "If `s` and `t` are two fundamental domains of the same action, then their measures
  are equal."]
protected theorem measure_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ) :
    μ s = μ t := by
  simpa only [setLIntegral_one] using hs.setLIntegral_eq ht (fun _ => 1) fun _ _ => rfl

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
    _ ↔ ∀ g : G, AEStronglyMeasurable f (μ.restrict (g⁻¹ • (g⁻¹⁻¹ • s ∩ t))) :=
      inv_surjective.forall
    _ ↔ ∀ g : G, AEStronglyMeasurable f (μ.restrict (g⁻¹ • (g • s ∩ t))) := by simp only [inv_inv]
    _ ↔ ∀ g : G, AEStronglyMeasurable f (μ.restrict (g • s ∩ t)) := by
      refine forall_congr' fun g => ?_
      have he : MeasurableEmbedding (g⁻¹ • · : α → α) := measurableEmbedding_const_smul _
      rw [← image_smul, ← ((measurePreserving_smul g⁻¹ μ).restrict_image_emb he
        _).aestronglyMeasurable_comp_iff he]
      simp only [Function.comp_def, hf]
    _ ↔ AEStronglyMeasurable f (μ.restrict t) := by
      simp only [← aestronglyMeasurable_sum_measure_iff, ← hs.restrict_restrict,
        hs.sum_restrict_of_ac restrict_le_self.absolutelyContinuous]

@[to_additive]
protected theorem hasFiniteIntegral_on_iff (hs : IsFundamentalDomain G s μ)
    (ht : IsFundamentalDomain G t μ) {f : α → E} (hf : ∀ (g : G) (x), f (g • x) = f x) :
    HasFiniteIntegral f (μ.restrict s) ↔ HasFiniteIntegral f (μ.restrict t) := by
  dsimp only [HasFiniteIntegral]
  rw [hs.setLIntegral_eq ht]
  intro g x; rw [hf]

@[to_additive]
protected theorem integrableOn_iff (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
    {f : α → E} (hf : ∀ (g : G) (x), f (g • x) = f x) : IntegrableOn f s μ ↔ IntegrableOn f t μ :=
  and_congr (hs.aEStronglyMeasurable_on_iff ht hf) (hs.hasFiniteIntegral_on_iff ht hf)

variable [NormedSpace ℝ E]

@[to_additive]
theorem integral_eq_tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (f : α → E)
    (hf : Integrable f ν) : ∫ x, f x ∂ν = ∑' g : G, ∫ x in g • s, f x ∂ν := by
  rw [← MeasureTheory.integral_sum_measure, h.sum_restrict_of_ac hν]
  rw [h.sum_restrict_of_ac hν]
  exact hf

@[to_additive]
theorem integral_eq_tsum (h : IsFundamentalDomain G s μ) (f : α → E) (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ :=
  integral_eq_tsum_of_ac h (by rfl) f hf

@[to_additive]
theorem integral_eq_tsum' (h : IsFundamentalDomain G s μ) (f : α → E) (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑' g : G, ∫ x in s, f (g⁻¹ • x) ∂μ :=
  calc
    ∫ x, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ := h.integral_eq_tsum f hf
    _ = ∑' g : G, ∫ x in g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫ x in s, f (g⁻¹ • x) ∂μ := tsum_congr fun g =>
      (measurePreserving_smul g⁻¹ μ).setIntegral_image_emb (measurableEmbedding_const_smul _) _ _

@[to_additive] lemma integral_eq_tsum'' (h : IsFundamentalDomain G s μ)
    (f : α → E) (hf : Integrable f μ) : ∫ x, f x ∂μ = ∑' g : G, ∫ x in s, f (g • x) ∂μ :=
  (integral_eq_tsum' h f hf).trans ((Equiv.inv G).tsum_eq (fun g ↦ ∫ (x : α) in s, f (g • x) ∂μ))

@[to_additive]
theorem setIntegral_eq_tsum (h : IsFundamentalDomain G s μ) {f : α → E} {t : Set α}
    (hf : IntegrableOn f t μ) : ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in t ∩ g • s, f x ∂μ :=
  calc
    ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ.restrict t :=
      h.integral_eq_tsum_of_ac restrict_le_self.absolutelyContinuous f hf
    _ = ∑' g : G, ∫ x in t ∩ g • s, f x ∂μ := by
      simp only [h.restrict_restrict, measure_smul, inter_comm]

@[deprecated (since := "2024-04-17")]
alias set_integral_eq_tsum := setIntegral_eq_tsum

@[to_additive]
theorem setIntegral_eq_tsum' (h : IsFundamentalDomain G s μ) {f : α → E} {t : Set α}
    (hf : IntegrableOn f t μ) : ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
  calc
    ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in t ∩ g • s, f x ∂μ := h.setIntegral_eq_tsum hf
    _ = ∑' g : G, ∫ x in t ∩ g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫ x in g⁻¹ • (g • t ∩ s), f x ∂μ := by simp only [smul_set_inter, inv_smul_smul]
    _ = ∑' g : G, ∫ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
      tsum_congr fun g =>
        (measurePreserving_smul g⁻¹ μ).setIntegral_image_emb (measurableEmbedding_const_smul _) _ _

@[deprecated (since := "2024-04-17")]
alias set_integral_eq_tsum' := setIntegral_eq_tsum'

@[to_additive]
protected theorem setIntegral_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
    {f : α → E} (hf : ∀ (g : G) (x), f (g • x) = f x) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ := by
  by_cases hfs : IntegrableOn f s μ
  · have hft : IntegrableOn f t μ := by rwa [ht.integrableOn_iff hs hf]
    calc
      ∫ x in s, f x ∂μ = ∑' g : G, ∫ x in s ∩ g • t, f x ∂μ := ht.setIntegral_eq_tsum hfs
      _ = ∑' g : G, ∫ x in g • t ∩ s, f (g⁻¹ • x) ∂μ := by simp only [hf, inter_comm]
      _ = ∫ x in t, f x ∂μ := (hs.setIntegral_eq_tsum' hft).symm
  · rw [integral_undef hfs, integral_undef]
    rwa [hs.integrableOn_iff ht hf] at hfs

@[deprecated (since := "2024-04-17")]
alias set_integral_eq := MeasureTheory.IsFundamentalDomain.setIntegral_eq

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
    _ ≤ μ s := measure_mono (iUnion_subset fun _ => inter_subset_right)

/-- If the action of a countable group `G` admits an invariant measure `μ` with a fundamental domain
`s`, then every null-measurable set `t` of measure strictly greater than `μ s` contains two
points `x y` such that `g • x = y` for some `g ≠ 1`. -/
@[to_additive "If the additive action of a countable group `G` admits an invariant measure `μ` with
  a fundamental domain `s`, then every null-measurable set `t` of measure strictly greater than
  `μ s` contains two points `x y` such that `g +ᵥ x = y` for some `g ≠ 0`."]
theorem exists_ne_one_smul_eq (hs : IsFundamentalDomain G s μ) (htm : NullMeasurableSet t μ)
    (ht : μ s < μ t) : ∃ x ∈ t, ∃ y ∈ t, ∃ g, g ≠ (1 : G) ∧ g • x = y := by
  contrapose! ht
  refine hs.measure_le_of_pairwise_disjoint htm (Pairwise.aedisjoint fun g₁ g₂ hne => ?_)
  dsimp [Function.onFun]
  refine (Disjoint.inf_left _ ?_).inf_right _
  rw [Set.disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy : g₂ • y = g₁ • x⟩
  refine ht x hx y hy (g₂⁻¹ * g₁) (mt inv_mul_eq_one.1 hne.symm) ?_
  rw [mul_smul, ← hxy, inv_smul_smul]

/-- If `f` is invariant under the action of a countable group `G`, and `μ` is a `G`-invariant
  measure with a fundamental domain `s`, then the `essSup` of `f` restricted to `s` is the same as
  that of `f` on all of its domain. -/
@[to_additive "If `f` is invariant under the action of a countable additive group `G`, and `μ` is a
  `G`-invariant measure with a fundamental domain `s`, then the `essSup` of `f` restricted to `s`
  is the same as that of `f` on all of its domain."]
theorem essSup_measure_restrict (hs : IsFundamentalDomain G s μ) {f : α → ℝ≥0∞}
    (hf : ∀ γ : G, ∀ x : α, f (γ • x) = f x) : essSup f (μ.restrict s) = essSup f μ := by
  refine le_antisymm (essSup_mono_measure' Measure.restrict_le_self) ?_
  rw [essSup_eq_sInf (μ.restrict s) f, essSup_eq_sInf μ f]
  refine sInf_le_sInf ?_
  rintro a (ha : (μ.restrict s) {x : α | a < f x} = 0)
  rw [Measure.restrict_apply₀' hs.nullMeasurableSet] at ha
  refine measure_zero_of_invariant hs _ ?_ ha
  intro γ
  ext x
  rw [mem_smul_set_iff_inv_smul_mem]
  simp only [mem_setOf_eq, hf γ⁻¹ x]

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

/-- The interior of a fundamental domain, those points of the domain not lying in any translate. -/
@[to_additive MeasureTheory.addFundamentalInterior "The interior of a fundamental domain, those
  points of the domain not lying in any translate."]
def fundamentalInterior : Set α :=
  s \ ⋃ (g : G) (_ : g ≠ 1), g • s

variable {G s}

@[to_additive (attr := simp) MeasureTheory.mem_addFundamentalFrontier]
theorem mem_fundamentalFrontier :
    x ∈ fundamentalFrontier G s ↔ x ∈ s ∧ ∃ g : G, g ≠ 1 ∧ x ∈ g • s := by
  simp [fundamentalFrontier]

@[to_additive (attr := simp) MeasureTheory.mem_addFundamentalInterior]
theorem mem_fundamentalInterior :
    x ∈ fundamentalInterior G s ↔ x ∈ s ∧ ∀ g : G, g ≠ 1 → x ∉ g • s := by
  simp [fundamentalInterior]

@[to_additive MeasureTheory.addFundamentalFrontier_subset]
theorem fundamentalFrontier_subset : fundamentalFrontier G s ⊆ s :=
  inter_subset_left

@[to_additive MeasureTheory.addFundamentalInterior_subset]
theorem fundamentalInterior_subset : fundamentalInterior G s ⊆ s :=
  diff_subset

variable (G s)

@[to_additive MeasureTheory.disjoint_addFundamentalInterior_addFundamentalFrontier]
theorem disjoint_fundamentalInterior_fundamentalFrontier :
    Disjoint (fundamentalInterior G s) (fundamentalFrontier G s) :=
  disjoint_sdiff_self_left.mono_right inf_le_right

@[to_additive (attr := simp) MeasureTheory.addFundamentalInterior_union_addFundamentalFrontier]
theorem fundamentalInterior_union_fundamentalFrontier :
    fundamentalInterior G s ∪ fundamentalFrontier G s = s :=
  diff_union_inter _ _

@[to_additive (attr := simp) MeasureTheory.addFundamentalFrontier_union_addFundamentalInterior]
theorem fundamentalFrontier_union_fundamentalInterior :
    fundamentalFrontier G s ∪ fundamentalInterior G s = s :=
  inter_union_diff _ _

@[to_additive (attr := simp) MeasureTheory.sdiff_addFundamentalInterior]
theorem sdiff_fundamentalInterior : s \ fundamentalInterior G s = fundamentalFrontier G s :=
  sdiff_sdiff_right_self

@[to_additive (attr := simp) MeasureTheory.sdiff_addFundamentalFrontier]
theorem sdiff_fundamentalFrontier : s \ fundamentalFrontier G s = fundamentalInterior G s :=
  diff_self_inter

@[to_additive (attr := simp) MeasureTheory.addFundamentalFrontier_vadd]
theorem fundamentalFrontier_smul [Group H] [MulAction H α] [SMulCommClass H G α] (g : H) :
    fundamentalFrontier G (g • s) = g • fundamentalFrontier G s := by
  simp_rw [fundamentalFrontier, smul_set_inter, smul_set_iUnion, smul_comm g (_ : G) (_ : Set α)]

@[to_additive (attr := simp) MeasureTheory.addFundamentalInterior_vadd]
theorem fundamentalInterior_smul [Group H] [MulAction H α] [SMulCommClass H G α] (g : H) :
    fundamentalInterior G (g • s) = g • fundamentalInterior G s := by
  simp_rw [fundamentalInterior, smul_set_sdiff, smul_set_iUnion, smul_comm g (_ : G) (_ : Set α)]

@[to_additive MeasureTheory.pairwise_disjoint_addFundamentalInterior]
theorem pairwise_disjoint_fundamentalInterior :
    Pairwise (Disjoint on fun g : G => g • fundamentalInterior G s) := by
  refine fun a b hab => disjoint_left.2 ?_
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  rw [mem_fundamentalInterior] at hx hy
  refine hx.2 (a⁻¹ * b) ?_ ?_
  · rwa [Ne, inv_mul_eq_iff_eq_mul, mul_one, eq_comm]
  · simpa [mul_smul, ← hxy, mem_inv_smul_set_iff] using hy.1

variable [Countable G] [MeasurableSpace G] [MeasurableSpace α] [MeasurableSMul G α] {μ : Measure α}
  [SMulInvariantMeasure G α μ]

@[to_additive MeasureTheory.NullMeasurableSet.addFundamentalFrontier]
protected theorem NullMeasurableSet.fundamentalFrontier (hs : NullMeasurableSet s μ) :
    NullMeasurableSet (fundamentalFrontier G s) μ :=
  hs.inter <| .iUnion fun _ => .iUnion fun _ => hs.smul _

@[to_additive MeasureTheory.NullMeasurableSet.addFundamentalInterior]
protected theorem NullMeasurableSet.fundamentalInterior (hs : NullMeasurableSet s μ) :
    NullMeasurableSet (fundamentalInterior G s) μ :=
  hs.diff <| .iUnion fun _ => .iUnion fun _ => hs.smul _

end MeasurableSpace

namespace IsFundamentalDomain

variable [Countable G] [Group G] [MulAction G α] [MeasurableSpace α] {μ : Measure α} {s : Set α}
  (hs : IsFundamentalDomain G s μ)
include hs

section Group


@[to_additive MeasureTheory.IsAddFundamentalDomain.measure_addFundamentalFrontier]
theorem measure_fundamentalFrontier : μ (fundamentalFrontier G s) = 0 := by
  simpa only [fundamentalFrontier, iUnion₂_inter, one_smul, measure_iUnion_null_iff, inter_comm s,
    Function.onFun] using fun g (hg : g ≠ 1) => hs.aedisjoint hg

@[to_additive MeasureTheory.IsAddFundamentalDomain.measure_addFundamentalInterior]
theorem measure_fundamentalInterior : μ (fundamentalInterior G s) = μ s :=
  measure_diff_null' hs.measure_fundamentalFrontier

end Group

variable [MeasurableSpace G] [MeasurableSMul G α] [SMulInvariantMeasure G α μ]

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
    refine eq_bot_mono (μ.mono <| compl_subset_compl.2 this) ?_
    simp only [iUnion_inv_smul, compl_sdiff, ENNReal.bot_eq_zero, himp_eq, sup_eq_union,
      @iUnion_smul_eq_setOf_exists _ _ _ _ s]
    exact measure_union_null
      (measure_iUnion_null fun _ => measure_smul_null hs.measure_fundamentalFrontier _) hs.ae_covers
  aedisjoint := (pairwise_disjoint_fundamentalInterior _ _).mono fun _ _ => Disjoint.aedisjoint

end IsFundamentalDomain

section FundamentalDomainMeasure

variable (G) [Group G] [MulAction G α] [MeasurableSpace α]
  (μ : Measure α)

local notation "α_mod_G" => MulAction.orbitRel G α

local notation "π" => @Quotient.mk _ α_mod_G

variable {G}

@[to_additive addMeasure_map_restrict_apply]
lemma measure_map_restrict_apply (s : Set α) {U : Set (Quotient α_mod_G)}
    (meas_U : MeasurableSet U) :
    (μ.restrict s).map π U = μ ((π ⁻¹' U) ∩ s) := by
  rw [map_apply (f := π) (fun V hV ↦ measurableSet_quotient.mp hV) meas_U,
    Measure.restrict_apply (t := (Quotient.mk α_mod_G ⁻¹' U)) (measurableSet_quotient.mp meas_U)]

@[to_additive]
lemma IsFundamentalDomain.quotientMeasure_eq [Countable G] [MeasurableSpace G] {s t : Set α}
    [SMulInvariantMeasure G α μ] [MeasurableSMul G α] (fund_dom_s : IsFundamentalDomain G s μ)
    (fund_dom_t : IsFundamentalDomain G t μ) :
    (μ.restrict s).map π = (μ.restrict t).map π := by
  ext U meas_U
  rw [measure_map_restrict_apply (meas_U := meas_U), measure_map_restrict_apply (meas_U := meas_U)]
  apply MeasureTheory.IsFundamentalDomain.measure_set_eq fund_dom_s fund_dom_t
  · exact measurableSet_quotient.mp meas_U
  · intro g
    ext x
    have : Quotient.mk α_mod_G (g • x) = Quotient.mk α_mod_G x := by
      apply Quotient.sound
      use g
    simp only [mem_preimage, this]

end FundamentalDomainMeasure

/-! ## `HasFundamentalDomain` typeclass

We define `HasFundamentalDomain` in order to be able to define the `covolume` of a quotient of `α`
by a group `G`, which under reasonable conditions does not depend on the choice of fundamental
domain. Even though any "sensible" action should have a fundamental domain, this is a rather
delicate question which was recently addressed by Misha Kapovich: https://arxiv.org/abs/2301.05325

TODO: Formalize the existence of a Dirichlet domain as in Kapovich's paper.

-/

section HasFundamentalDomain

/-- We say a quotient of `α` by `G` `HasAddFundamentalDomain` if there is a measurable set
  `s` for which `IsAddFundamentalDomain G s` holds. -/
class HasAddFundamentalDomain (G α : Type*) [Zero G] [VAdd G α] [MeasurableSpace α]
    (ν : Measure α := by volume_tac) : Prop where
  ExistsIsAddFundamentalDomain : ∃ s : Set α, IsAddFundamentalDomain G s ν

/-- We say a quotient of `α` by `G` `HasFundamentalDomain` if there is a measurable set `s` for
  which `IsFundamentalDomain G s` holds. -/
class HasFundamentalDomain (G : Type*) (α : Type*) [One G] [SMul G α] [MeasurableSpace α]
    (ν : Measure α := by volume_tac) : Prop where
  ExistsIsFundamentalDomain : ∃ (s : Set α), IsFundamentalDomain G s ν

attribute [to_additive existing] MeasureTheory.HasFundamentalDomain

open Classical in
/-- The `covolume` of an action of `G` on `α` the volume of some fundamental domain, or `0` if
none exists. -/
@[to_additive addCovolume "The `addCovolume` of an action of `G` on `α` is the volume of some
fundamental domain, or `0` if none exists."]
noncomputable def covolume (G α : Type*) [One G] [SMul G α] [MeasurableSpace α]
    (ν : Measure α := by volume_tac) : ℝ≥0∞ :=
  if funDom : HasFundamentalDomain G α ν then ν funDom.ExistsIsFundamentalDomain.choose else 0

variable [Group G] [MulAction G α] [MeasurableSpace α]

/-- If there is a fundamental domain `s`, then `HasFundamentalDomain` holds. -/
@[to_additive]
lemma IsFundamentalDomain.hasFundamentalDomain (ν : Measure α) {s : Set α}
    (fund_dom_s : IsFundamentalDomain G s ν) :
    HasFundamentalDomain G α ν := ⟨⟨s, fund_dom_s⟩⟩

/-- The `covolume` can be computed by taking the `volume` of any given fundamental domain `s`. -/
@[to_additive]
lemma IsFundamentalDomain.covolume_eq_volume (ν : Measure α) [Countable G]
    [MeasurableSpace G] [MeasurableSMul G α] [SMulInvariantMeasure G α ν] {s : Set α}
    (fund_dom_s : IsFundamentalDomain G s ν) : covolume G α ν = ν s := by
  dsimp [covolume]
  simp only [(fund_dom_s.hasFundamentalDomain ν), ↓reduceDIte]
  rw [fund_dom_s.measure_eq]
  exact (fund_dom_s.hasFundamentalDomain ν).ExistsIsFundamentalDomain.choose_spec

end HasFundamentalDomain

/-! ## `QuotientMeasureEqMeasurePreimage` typeclass

This typeclass describes a situation in which a measure `μ` on `α ⧸ G` can be computed by
taking a measure `ν` on `α` of the intersection of the pullback with a fundamental domain.

It's curious that in measure theory, measures can be pushed forward, while in geometry, volumes can
be pulled back. And yet here, we are describing a situation involving measures in a geometric way.

Another viewpoint is that if a set is small enough to fit in a single fundamental domain, then its
`ν` measure in `α` is the same as the `μ` measure of its pushforward in `α ⧸ G`.

-/

section QuotientMeasureEqMeasurePreimage

section additive

variable [AddGroup G] [AddAction G α] [MeasurableSpace α]

local notation "α_mod_G" => AddAction.orbitRel G α

local notation "π" => @Quotient.mk _ α_mod_G

/-- A measure `μ` on the `AddQuotient` of `α` mod `G` satisfies
  `AddQuotientMeasureEqMeasurePreimage` if: for any fundamental domain `t`, and any measurable
  subset `U` of the quotient, `μ U = volume ((π ⁻¹' U) ∩ t)`. -/
class AddQuotientMeasureEqMeasurePreimage (ν : Measure α := by volume_tac)
    (μ : Measure (Quotient α_mod_G)) : Prop where
  addProjection_respects_measure' : ∀ (t : Set α) (_ : IsAddFundamentalDomain G t ν),
    μ = (ν.restrict t).map π

end additive

variable [Group G] [MulAction G α] [MeasurableSpace α]

local notation "α_mod_G" => MulAction.orbitRel G α

local notation "π" => @Quotient.mk _ α_mod_G

/-- Measures `ν` on `α` and `μ` on the `Quotient` of `α` mod `G` satisfy
  `QuotientMeasureEqMeasurePreimage` if: for any fundamental domain `t`, and any measurable subset
  `U` of the quotient, `μ U = ν ((π ⁻¹' U) ∩ t)`. -/
class QuotientMeasureEqMeasurePreimage (ν : Measure α := by volume_tac)
    (μ : Measure (Quotient α_mod_G)) : Prop where
  projection_respects_measure' (t : Set α) : IsFundamentalDomain G t ν → μ = (ν.restrict t).map π

attribute [to_additive]
  MeasureTheory.QuotientMeasureEqMeasurePreimage

@[to_additive addProjection_respects_measure]
lemma IsFundamentalDomain.projection_respects_measure {ν : Measure α}
    (μ : Measure (Quotient α_mod_G)) [i : QuotientMeasureEqMeasurePreimage ν μ] {t : Set α}
    (fund_dom_t : IsFundamentalDomain G t ν) : μ = (ν.restrict t).map π :=
  i.projection_respects_measure' t fund_dom_t

@[to_additive addProjection_respects_measure_apply]
lemma IsFundamentalDomain.projection_respects_measure_apply {ν : Measure α}
    (μ : Measure (Quotient α_mod_G)) [i : QuotientMeasureEqMeasurePreimage ν μ] {t : Set α}
    (fund_dom_t : IsFundamentalDomain G t ν) {U : Set (Quotient α_mod_G)}
    (meas_U : MeasurableSet U) : μ U = ν (π ⁻¹' U ∩ t) := by
  rw [fund_dom_t.projection_respects_measure (μ := μ), measure_map_restrict_apply ν t meas_U]

variable {ν : Measure α}

/-- Any two measures satisfying `QuotientMeasureEqMeasurePreimage` are equal. -/
@[to_additive]
lemma QuotientMeasureEqMeasurePreimage.unique
    [hasFun : HasFundamentalDomain G α ν] (μ μ' : Measure (Quotient α_mod_G))
    [QuotientMeasureEqMeasurePreimage ν μ] [QuotientMeasureEqMeasurePreimage ν μ'] :
    μ = μ' := by
  obtain ⟨𝓕, h𝓕⟩ := hasFun.ExistsIsFundamentalDomain
  rw [h𝓕.projection_respects_measure (μ := μ), h𝓕.projection_respects_measure (μ := μ')]

/-- The quotient map to `α ⧸ G` is measure-preserving between the restriction of `volume` to a
  fundamental domain in `α` and a related measure satisfying `QuotientMeasureEqMeasurePreimage`. -/
@[to_additive IsAddFundamentalDomain.measurePreserving_add_quotient_mk]
theorem IsFundamentalDomain.measurePreserving_quotient_mk
    {𝓕 : Set α} (h𝓕 : IsFundamentalDomain G 𝓕 ν)
    (μ : Measure (Quotient α_mod_G)) [QuotientMeasureEqMeasurePreimage ν μ] :
    MeasurePreserving π (ν.restrict 𝓕) μ where
  measurable := measurable_quotient_mk' (s := α_mod_G)
  map_eq := by
    haveI : HasFundamentalDomain G α ν := ⟨𝓕, h𝓕⟩
    rw [h𝓕.projection_respects_measure (μ := μ)]

variable [SMulInvariantMeasure G α ν] [Countable G] [MeasurableSpace G] [MeasurableSMul G α]

/-- Given a measure upstairs (i.e., on `α`), and a choice `s` of fundamental domain, there's always
an artificial way to generate a measure downstairs such that the pair satisfies the
`QuotientMeasureEqMeasurePreimage` typeclass. -/
@[to_additive]
lemma IsFundamentalDomain.quotientMeasureEqMeasurePreimage_quotientMeasure
    {s : Set α} (fund_dom_s : IsFundamentalDomain G s ν) :
    QuotientMeasureEqMeasurePreimage ν ((ν.restrict s).map π) where
  projection_respects_measure' t fund_dom_t := by rw [fund_dom_s.quotientMeasure_eq _ fund_dom_t]

/-- One can prove `QuotientMeasureEqMeasurePreimage` by checking behavior with respect to a single
fundamental domain. -/
@[to_additive]
lemma IsFundamentalDomain.quotientMeasureEqMeasurePreimage {μ : Measure (Quotient α_mod_G)}
    {s : Set α} (fund_dom_s : IsFundamentalDomain G s ν) (h : μ = (ν.restrict s).map π) :
    QuotientMeasureEqMeasurePreimage ν μ := by
  simpa [h] using fund_dom_s.quotientMeasureEqMeasurePreimage_quotientMeasure


/-- If a fundamental domain has volume 0, then `QuotientMeasureEqMeasurePreimage` holds. -/
@[to_additive]
theorem IsFundamentalDomain.quotientMeasureEqMeasurePreimage_of_zero
    {s : Set α} (fund_dom_s : IsFundamentalDomain G s ν)
    (vol_s : ν s = 0) :
    QuotientMeasureEqMeasurePreimage ν (0 : Measure (Quotient α_mod_G)) := by
  apply fund_dom_s.quotientMeasureEqMeasurePreimage
  ext U meas_U
  simp only [Measure.coe_zero, Pi.zero_apply]
  convert (measure_inter_null_of_null_right (h := vol_s) (Quotient.mk α_mod_G ⁻¹' U)).symm
  rw [measure_map_restrict_apply (meas_U := meas_U)]

/-- If a measure `μ` on a quotient satisfies `QuotientMeasureEqMeasurePreimage` with respect to a
sigma-finite measure `ν`, then it is itself `SigmaFinite`. -/
@[to_additive]
lemma QuotientMeasureEqMeasurePreimage.sigmaFiniteQuotient
    [i : SigmaFinite ν] [i' : HasFundamentalDomain G α ν]
    (μ : Measure (Quotient α_mod_G)) [QuotientMeasureEqMeasurePreimage ν μ] :
    SigmaFinite μ := by
  rw [sigmaFinite_iff]
  obtain ⟨A, hA_meas, hA, hA'⟩ := Measure.toFiniteSpanningSetsIn (h := i)
  simp only [mem_setOf_eq] at hA_meas
  refine ⟨⟨fun n ↦ π '' (A n), by simp, fun n ↦ ?_, ?_⟩⟩
  · obtain ⟨s, fund_dom_s⟩ := i'
    have : π ⁻¹' (π '' (A n)) = _ := MulAction.quotient_preimage_image_eq_union_mul (A n) (G := G)
    have measπAn : MeasurableSet (π '' A n) := by
      let _ : Setoid α := α_mod_G
      rw [measurableSet_quotient, Quotient.mk''_eq_mk, this]
      apply MeasurableSet.iUnion
      exact fun g ↦ MeasurableSet.const_smul (hA_meas n) g
    rw [fund_dom_s.projection_respects_measure_apply (μ := μ) measπAn, this, iUnion_inter]
    refine lt_of_le_of_lt ?_ (hA n)
    rw [fund_dom_s.measure_eq_tsum (A n)]
    exact measure_iUnion_le _
  · rw [← image_iUnion, hA']
    refine image_univ_of_surjective (by convert Quotient.mk'_surjective)

/-- A measure `μ` on `α ⧸ G` satisfying `QuotientMeasureEqMeasurePreimage` and having finite
covolume is a finite measure. -/
@[to_additive]
theorem QuotientMeasureEqMeasurePreimage.isFiniteMeasure_quotient
    (μ : Measure (Quotient α_mod_G)) [QuotientMeasureEqMeasurePreimage ν μ]
    [hasFun : HasFundamentalDomain G α ν] (h : covolume G α ν ≠ ∞) :
    IsFiniteMeasure μ := by
  obtain ⟨𝓕, h𝓕⟩ := hasFun.ExistsIsFundamentalDomain
  rw [h𝓕.projection_respects_measure (μ := μ)]
  have : Fact (ν 𝓕 < ∞) := by
    apply Fact.mk
    convert Ne.lt_top h
    exact (h𝓕.covolume_eq_volume ν).symm
  infer_instance

/-- A finite measure `μ` on `α ⧸ G` satisfying `QuotientMeasureEqMeasurePreimage` has finite
covolume. -/
@[to_additive]
theorem QuotientMeasureEqMeasurePreimage.covolume_ne_top
    (μ : Measure (Quotient α_mod_G)) [QuotientMeasureEqMeasurePreimage ν μ] [IsFiniteMeasure μ] :
    covolume G α ν < ∞ := by
  by_cases hasFun : HasFundamentalDomain G α ν
  · obtain ⟨𝓕, h𝓕⟩ := hasFun.ExistsIsFundamentalDomain
    have H : μ univ < ∞ := IsFiniteMeasure.measure_univ_lt_top
    rw [h𝓕.projection_respects_measure_apply (μ := μ) MeasurableSet.univ] at H
    simpa [h𝓕.covolume_eq_volume ν] using H
  · simp [covolume, hasFun]

end QuotientMeasureEqMeasurePreimage

section QuotientMeasureEqMeasurePreimage


variable [Group G] [MulAction G α] [MeasureSpace α] [Countable G] [MeasurableSpace G]
  [SMulInvariantMeasure G α volume] [MeasurableSMul G α]

local notation "α_mod_G" => MulAction.orbitRel G α

local notation "π" => @Quotient.mk _ α_mod_G

/-- If a measure `μ` on a quotient satisfies `QuotientVolumeEqVolumePreimage` with respect to a
sigma-finite measure, then it is itself `SigmaFinite`. -/
@[to_additive MeasureTheory.instSigmaFiniteAddQuotientOrbitRelInstMeasurableSpaceToMeasurableSpace]
instance [SigmaFinite (volume : Measure α)] [HasFundamentalDomain G α]
    (μ : Measure (Quotient α_mod_G)) [QuotientMeasureEqMeasurePreimage volume μ] :
    SigmaFinite μ :=
  QuotientMeasureEqMeasurePreimage.sigmaFiniteQuotient (ν := (volume : Measure α)) (μ := μ)

end QuotientMeasureEqMeasurePreimage

end MeasureTheory
