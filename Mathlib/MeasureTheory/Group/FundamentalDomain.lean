/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Integral.SetIntegral

#align_import measure_theory.group.fundamental_domain from "leanprover-community/mathlib"@"eb810cf549db839dadf13353dbe69bac55acdbbc"

/-!
# AEFundamental domain of a group action

A set `s` is said to be a *ae-fundamental domain* of an action of a group `G` on a measurable
space `α` with respect to a measure `μ` if

* `s` is a measurable set;

* the sets `g • s` over all `g : G` cover almost all points of the whole space;

* the sets `g • s`, are pairwise a.e. disjoint, i.e., `μ (g₁ • s ∩ g₂ • s) = 0` whenever `g₁ ≠ g₂`;
  we require this for `g₂ = 1` in the definition, then deduce it for any two `g₁ ≠ g₂`.

In this file we prove that in case of a countable group `G` and a measure preserving action, any two
fundamental domains have the same measure, and for a `G`-invariant function, its integrals over any
two fundamental domains are equal to each other.

We also generate additive versions of all theorems in this file using the `to_additive` attribute.

## Main declarations

* `MeasureTheory.IsAEFundamentalDomain`: Predicate for a set to be an ae-fundamental domain of the
  action of a group
* `MeasureTheory.fundamentalFrontier`: Fundamental frontier of a set under the action of a group.
  Elements of `s` that belong to some other translate of `s`.
* `MeasureTheory.fundamentalInterior`: Fundamental interior of a set under the action of a group.
  Elements of `s` that do not belong to any other translate of `s`.
-/


open scoped ENNReal Pointwise Topology NNReal ENNReal MeasureTheory

open MeasureTheory MeasureTheory.Measure Set Function TopologicalSpace Filter

namespace MeasureTheory

/-- A measurable set `s` is an *ae-fundamental domain* for an additive action of an additive
group `G` on a measurable space `α` with respect to a measure `α` if the sets `g +ᵥ s`, `g : G`,
are pairwise a.e. disjoint and cover the whole space. -/
structure IsAddAEFundamentalDomain (G : Type _) {α : Type _} [Zero G] [VAdd G α] [MeasurableSpace α]
    (s : Set α) (μ : Measure α := by volume_tac) : Prop where
  protected nullMeasurableSet : NullMeasurableSet s μ
  protected ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g +ᵥ x ∈ s
  protected aedisjoint : Pairwise <| (AEDisjoint μ on fun g : G => g +ᵥ s)

/-- A measurable set `s` is an *ae-fundamental domain* for an action of a group `G` on a measurable
space `α` with respect to a measure `α` if the sets `g • s`, `g : G`, are pairwise a.e. disjoint
and cover the whole space. -/
@[to_additive IsAddAEFundamentalDomain]
structure IsAEFundamentalDomain (G : Type _) {α : Type _} [One G] [SMul G α] [MeasurableSpace α]
    (s : Set α) (μ : Measure α := by volume_tac) : Prop where
  protected nullMeasurableSet : NullMeasurableSet s μ
  protected ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ s
  protected aedisjoint : Pairwise <| (AEDisjoint μ on fun g : G => g • s)

variable {G H α β E : Type _}

namespace IsAEFundamentalDomain

variable [Group G] [Group H] [MulAction G α] [MeasurableSpace α] [MulAction H β] [MeasurableSpace β]
  [NormedAddCommGroup E] {s t : Set α} {μ : Measure α}

/-- If for each `x : α`, exactly one of `g • x`, `g : G`, belongs to a measurable set `s`, then `s`
is a fundamental domain for the action of `G` on `α`. -/
@[to_additive "If for each `x : α`, exactly one of `g +ᵥ x`, `g : G`, belongs to a measurable set
`s`, then `s` is a fundamental domain for the additive action of `G` on `α`."]
theorem mk' (h_meas : NullMeasurableSet s μ) (h_exists : ∀ x : α, ∃! g : G, g • x ∈ s) :
    IsAEFundamentalDomain G s μ where
  nullMeasurableSet := h_meas
  ae_covers := eventually_of_forall fun x => (h_exists x).exists
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
    IsAEFundamentalDomain G s μ where
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
    (h_ae_disjoint : ∀ (g) (_ : g ≠ (1 : G)), AEDisjoint μ (g • s) s)
    (h_qmp : ∀ g : G, QuasiMeasurePreserving ((· • ·) g : α → α) μ μ)
    (h_measure_univ_le : μ (univ : Set α) ≤ ∑' g : G, μ (g • s)) : IsAEFundamentalDomain G s μ :=
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
      refine' le_antisymm (measure_mono <| subset_univ _) _
      rw [measure_iUnion₀ aedisjoint h_meas]
      exact h_measure_univ_le }

@[to_additive]
theorem iUnion_smul_ae_eq (h : IsAEFundamentalDomain G s μ) : ⋃ g : G, g • s =ᵐ[μ] univ :=
  eventuallyEq_univ.2 <| h.ae_covers.mono fun _ ⟨g, hg⟩ =>
    mem_iUnion.2 ⟨g⁻¹, _, hg, inv_smul_smul _ _⟩

@[to_additive]
theorem mono (h : IsAEFundamentalDomain G s μ) {ν : Measure α} (hle : ν ≪ μ) :
    IsAEFundamentalDomain G s ν :=
  ⟨h.1.mono_ac hle, hle h.2, h.aedisjoint.mono fun _ _ h => hle h⟩

@[to_additive]
theorem preimage_of_equiv {ν : Measure β} (h : IsAEFundamentalDomain G s μ) {f : β → α}
    (hf : QuasiMeasurePreserving f ν μ) {e : G → H} (he : Bijective e)
    (hef : ∀ g, Semiconj f (e g • ·) (g • ·)) : IsAEFundamentalDomain H (f ⁻¹' s) ν where
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
theorem image_of_equiv {ν : Measure β} (h : IsAEFundamentalDomain G s μ) (f : α ≃ β)
    (hf : QuasiMeasurePreserving f.symm ν μ) (e : H ≃ G)
    (hef : ∀ g, Semiconj f (e g • ·) (g • ·)) : IsAEFundamentalDomain H (f '' s) ν := by
  rw [f.image_eq_preimage]
  refine' h.preimage_of_equiv hf e.symm.bijective fun g x => _
  rcases f.surjective x with ⟨x, rfl⟩
  rw [← hef _ _, f.symm_apply_apply, f.symm_apply_apply, e.apply_symm_apply]

@[to_additive]
theorem pairwise_aedisjoint_of_ac {ν} (h : IsAEFundamentalDomain G s μ) (hν : ν ≪ μ) :
    Pairwise fun g₁ g₂ : G => AEDisjoint ν (g₁ • s) (g₂ • s) :=
  h.aedisjoint.mono fun _ _ H => hν H

@[to_additive]
theorem smul_of_comm {G' : Type _} [Group G'] [MulAction G' α] [MeasurableSpace G']
    [MeasurableSMul G' α] [SMulInvariantMeasure G' α μ] [SMulCommClass G' G α]
    (h : IsAEFundamentalDomain G s μ) (g : G') : IsAEFundamentalDomain G (g • s) μ :=
  h.image_of_equiv (MulAction.toPerm g) (measurePreserving_smul _ _).quasiMeasurePreserving
    (Equiv.refl _) <| smul_comm g

variable [MeasurableSpace G] [MeasurableSMul G α] [SMulInvariantMeasure G α μ]

@[to_additive]
theorem nullMeasurableSet_smul (h : IsAEFundamentalDomain G s μ) (g : G) :
    NullMeasurableSet (g • s) μ :=
  h.nullMeasurableSet.smul g

@[to_additive]
theorem restrict_restrict (h : IsAEFundamentalDomain G s μ) (g : G) (t : Set α) :
    (μ.restrict t).restrict (g • s) = μ.restrict (g • s ∩ t) :=
  restrict_restrict₀ ((h.nullMeasurableSet_smul g).mono restrict_le_self)

@[to_additive]
theorem smul (h : IsAEFundamentalDomain G s μ) (g : G) : IsAEFundamentalDomain G (g • s) μ :=
  h.image_of_equiv (MulAction.toPerm g) (measurePreserving_smul _ _).quasiMeasurePreserving
    ⟨fun g' => g⁻¹ * g' * g, fun g' => g * g' * g⁻¹, fun g' => by simp [mul_assoc], fun g' => by
      simp [mul_assoc]⟩
    fun g' x => by simp [smul_smul, mul_assoc]

variable [Countable G] {ν : Measure α}

@[to_additive]
theorem sum_restrict_of_ac (h : IsAEFundamentalDomain G s μ) (hν : ν ≪ μ) :
    (sum fun g : G => ν.restrict (g • s)) = ν := by
  rw [← restrict_iUnion_ae (h.aedisjoint.mono fun i j h => hν h) fun g =>
      (h.nullMeasurableSet_smul g).mono_ac hν,
    restrict_congr_set (hν h.iUnion_smul_ae_eq), restrict_univ]

@[to_additive]
theorem lintegral_eq_tsum_of_ac (h : IsAEFundamentalDomain G s μ) (hν : ν ≪ μ) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂ν = ∑' g : G, ∫⁻ x in g • s, f x ∂ν := by
  rw [← lintegral_sum_measure, h.sum_restrict_of_ac hν]

@[to_additive]
theorem sum_restrict (h : IsAEFundamentalDomain G s μ) : (sum fun g : G => μ.restrict (g • s)) = μ :=
  h.sum_restrict_of_ac (refl _)

@[to_additive]
theorem lintegral_eq_tsum (h : IsAEFundamentalDomain G s μ) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ :=
  h.lintegral_eq_tsum_of_ac (refl _) f

@[to_additive]
theorem lintegral_eq_tsum' (h : IsAEFundamentalDomain G s μ) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in s, f (g⁻¹ • x) ∂μ :=
  calc
    ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ := h.lintegral_eq_tsum f
    _ = ∑' g : G, ∫⁻ x in g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫⁻ x in s, f (g⁻¹ • x) ∂μ := tsum_congr fun g => Eq.symm <|
      (measurePreserving_smul g⁻¹ μ).set_lintegral_comp_emb (measurableEmbedding_const_smul _) _ _

@[to_additive]
theorem set_lintegral_eq_tsum (h : IsAEFundamentalDomain G s μ) (f : α → ℝ≥0∞) (t : Set α) :
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ :=
  calc
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ.restrict t :=
      h.lintegral_eq_tsum_of_ac restrict_le_self.absolutelyContinuous _
    _ = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ := by simp only [h.restrict_restrict, inter_comm]

@[to_additive]
theorem set_lintegral_eq_tsum' (h : IsAEFundamentalDomain G s μ) (f : α → ℝ≥0∞) (t : Set α) :
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
  calc
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ := h.set_lintegral_eq_tsum f t
    _ = ∑' g : G, ∫⁻ x in t ∩ g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫⁻ x in g⁻¹ • (g • t ∩ s), f x ∂μ := by simp only [smul_set_inter, inv_smul_smul]
    _ = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ := tsum_congr fun g => Eq.symm <|
      (measurePreserving_smul g⁻¹ μ).set_lintegral_comp_emb (measurableEmbedding_const_smul _) _ _

@[to_additive]
theorem measure_eq_tsum_of_ac (h : IsAEFundamentalDomain G s μ) (hν : ν ≪ μ) (t : Set α) :
    ν t = ∑' g : G, ν (t ∩ g • s) := by
  have H : ν.restrict t ≪ μ := Measure.restrict_le_self.absolutelyContinuous.trans hν
  simpa only [set_lintegral_one, Pi.one_def,
    Measure.restrict_apply₀ ((h.nullMeasurableSet_smul _).mono_ac H), inter_comm] using
    h.lintegral_eq_tsum_of_ac H 1

@[to_additive]
theorem measure_eq_tsum' (h : IsAEFundamentalDomain G s μ) (t : Set α) :
    μ t = ∑' g : G, μ (t ∩ g • s) :=
  h.measure_eq_tsum_of_ac AbsolutelyContinuous.rfl t

@[to_additive]
theorem measure_eq_tsum (h : IsAEFundamentalDomain G s μ) (t : Set α) :
    μ t = ∑' g : G, μ (g • t ∩ s) := by
  simpa only [set_lintegral_one] using h.set_lintegral_eq_tsum' (fun _ => 1) t

@[to_additive]
theorem measure_zero_of_invariant (h : IsAEFundamentalDomain G s μ) (t : Set α)
    (ht : ∀ g : G, g • t = t) (hts : μ (t ∩ s) = 0) : μ t = 0 := by
  rw [measure_eq_tsum h]; simp [ht, hts]

/-- Given a measure space with an action of a finite group `G`, the measure of any `G`-invariant set
is determined by the measure of its intersection with a fundamental domain for the action of `G`. -/
@[to_additive measure_eq_card_smul_of_vadd_ae_eq_self "Given a measure space with an action of a
  finite additive group `G`, the measure of any `G`-invariant set is determined by the measure of
  its intersection with a fundamental domain for the action of `G`."]
theorem measure_eq_card_smul_of_smul_ae_eq_self [Finite G] (h : IsAEFundamentalDomain G s μ)
    (t : Set α) (ht : ∀ g : G, (g • t : Set α) =ᵐ[μ] t) : μ t = Nat.card G • μ (t ∩ s) := by
  haveI : Fintype G := Fintype.ofFinite G
  rw [h.measure_eq_tsum]
  replace ht : ∀ g : G, (g • t ∩ s : Set α) =ᵐ[μ] (t ∩ s : Set α) := fun g =>
    ae_eq_set_inter (ht g) (ae_eq_refl s)
  simp_rw [measure_congr (ht _), tsum_fintype, Finset.sum_const, Nat.card_eq_fintype_card,
    Finset.card_univ]

@[to_additive]
protected theorem set_lintegral_eq (hs : IsAEFundamentalDomain G s μ) (ht : IsAEFundamentalDomain G t μ)
    (f : α → ℝ≥0∞) (hf : ∀ (g : G) (x), f (g • x) = f x) :
    ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ :=
  calc
    ∫⁻ x in s, f x ∂μ = ∑' g : G, ∫⁻ x in s ∩ g • t, f x ∂μ := ht.set_lintegral_eq_tsum _ _
    _ = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ := by simp only [hf, inter_comm]
    _ = ∫⁻ x in t, f x ∂μ := (hs.set_lintegral_eq_tsum' _ _).symm

@[to_additive]
theorem measure_set_eq (hs : IsAEFundamentalDomain G s μ) (ht : IsAEFundamentalDomain G t μ) {A : Set α}
    (hA₀ : MeasurableSet A) (hA : ∀ g : G, (fun x => g • x) ⁻¹' A = A) : μ (A ∩ s) = μ (A ∩ t) := by
  have : ∫⁻ x in s, A.indicator 1 x ∂μ = ∫⁻ x in t, A.indicator 1 x ∂μ := by
    refine hs.set_lintegral_eq ht (Set.indicator A fun _ => 1) fun g x ↦ ?_
    convert (Set.indicator_comp_right (g • · : α → α) (g := fun _ ↦ (1 : ℝ≥0∞))).symm
    rw [hA g]
  simpa [Measure.restrict_apply hA₀, lintegral_indicator _ hA₀] using this

/-- If `s` and `t` are two fundamental domains of the same action, then their measures are equal. -/
@[to_additive "If `s` and `t` are two fundamental domains of the same action, then their measures
  are equal."]
protected theorem measure_eq (hs : IsAEFundamentalDomain G s μ) (ht : IsAEFundamentalDomain G t μ) :
    μ s = μ t := by
  simpa only [set_lintegral_one] using hs.set_lintegral_eq ht (fun _ => 1) fun _ _ => rfl

@[to_additive]
protected theorem aEStronglyMeasurable_on_iff {β : Type _} [TopologicalSpace β]
    [PseudoMetrizableSpace β] (hs : IsAEFundamentalDomain G s μ) (ht : IsAEFundamentalDomain G t μ)
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
      refine' forall_congr' fun g => _
      have he : MeasurableEmbedding ((· • ·) g⁻¹ : α → α) := measurableEmbedding_const_smul _
      rw [← image_smul, ← ((measurePreserving_smul g⁻¹ μ).restrict_image_emb he
        _).aestronglyMeasurable_comp_iff he]
      simp only [(· ∘ ·), hf]
    _ ↔ AEStronglyMeasurable f (μ.restrict t) := by
      simp only [← aestronglyMeasurable_sum_measure_iff, ← hs.restrict_restrict,
        hs.sum_restrict_of_ac restrict_le_self.absolutelyContinuous]

@[to_additive]
protected theorem hasFiniteIntegral_on_iff (hs : IsAEFundamentalDomain G s μ)
    (ht : IsAEFundamentalDomain G t μ) {f : α → E} (hf : ∀ (g : G) (x), f (g • x) = f x) :
    HasFiniteIntegral f (μ.restrict s) ↔ HasFiniteIntegral f (μ.restrict t) := by
  dsimp only [HasFiniteIntegral]
  rw [hs.set_lintegral_eq ht]
  intro g x; rw [hf]

@[to_additive]
protected theorem integrableOn_iff (hs : IsAEFundamentalDomain G s μ) (ht : IsAEFundamentalDomain G t μ)
    {f : α → E} (hf : ∀ (g : G) (x), f (g • x) = f x) : IntegrableOn f s μ ↔ IntegrableOn f t μ :=
  and_congr (hs.aEStronglyMeasurable_on_iff ht hf) (hs.hasFiniteIntegral_on_iff ht hf)

variable [NormedSpace ℝ E] [CompleteSpace E]

@[to_additive]
theorem integral_eq_tsum_of_ac (h : IsAEFundamentalDomain G s μ) (hν : ν ≪ μ) (f : α → E)
    (hf : Integrable f ν) : ∫ x, f x ∂ν = ∑' g : G, ∫ x in g • s, f x ∂ν := by
  rw [← MeasureTheory.integral_sum_measure, h.sum_restrict_of_ac hν]
  rw [h.sum_restrict_of_ac hν]
  exact hf

@[to_additive]
theorem integral_eq_tsum (h : IsAEFundamentalDomain G s μ) (f : α → E) (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ :=
  integral_eq_tsum_of_ac h (by rfl) f hf

@[to_additive]
theorem integral_eq_tsum' (h : IsAEFundamentalDomain G s μ) (f : α → E) (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑' g : G, ∫ x in s, f (g⁻¹ • x) ∂μ :=
  calc
    ∫ x, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ := h.integral_eq_tsum f hf
    _ = ∑' g : G, ∫ x in g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫ x in s, f (g⁻¹ • x) ∂μ := tsum_congr fun g =>
      (measurePreserving_smul g⁻¹ μ).set_integral_image_emb (measurableEmbedding_const_smul _) _ _

@[to_additive]
theorem set_integral_eq_tsum (h : IsAEFundamentalDomain G s μ) {f : α → E} {t : Set α}
    (hf : IntegrableOn f t μ) : ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in t ∩ g • s, f x ∂μ :=
  calc
    ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ.restrict t :=
      h.integral_eq_tsum_of_ac restrict_le_self.absolutelyContinuous f hf
    _ = ∑' g : G, ∫ x in t ∩ g • s, f x ∂μ := by
      simp only [h.restrict_restrict, measure_smul, inter_comm]

@[to_additive]
theorem set_integral_eq_tsum' (h : IsAEFundamentalDomain G s μ) {f : α → E} {t : Set α}
    (hf : IntegrableOn f t μ) : ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
  calc
    ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in t ∩ g • s, f x ∂μ := h.set_integral_eq_tsum hf
    _ = ∑' g : G, ∫ x in t ∩ g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫ x in g⁻¹ • (g • t ∩ s), f x ∂μ := by simp only [smul_set_inter, inv_smul_smul]
    _ = ∑' g : G, ∫ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
      tsum_congr fun g =>
        (measurePreserving_smul g⁻¹ μ).set_integral_image_emb (measurableEmbedding_const_smul _) _ _

@[to_additive]
protected theorem set_integral_eq (hs : IsAEFundamentalDomain G s μ) (ht : IsAEFundamentalDomain G t μ)
    {f : α → E} (hf : ∀ (g : G) (x), f (g • x) = f x) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ := by
  by_cases hfs : IntegrableOn f s μ
  · have hft : IntegrableOn f t μ := by rwa [ht.integrableOn_iff hs hf]
    calc
      ∫ x in s, f x ∂μ = ∑' g : G, ∫ x in s ∩ g • t, f x ∂μ := ht.set_integral_eq_tsum hfs
      _ = ∑' g : G, ∫ x in g • t ∩ s, f (g⁻¹ • x) ∂μ := by simp only [hf, inter_comm]
      _ = ∫ x in t, f x ∂μ := (hs.set_integral_eq_tsum' hft).symm
  · rw [integral_undef hfs, integral_undef]
    rwa [hs.integrableOn_iff ht hf] at hfs

/-- If the action of a countable group `G` admits an invariant measure `μ` with a fundamental domain
`s`, then every null-measurable set `t` such that the sets `g • t ∩ s` are pairwise a.e.-disjoint
has measure at most `μ s`. -/
@[to_additive "If the additive action of a countable group `G` admits an invariant measure `μ` with
  a fundamental domain `s`, then every null-measurable set `t` such that the sets `g +ᵥ t ∩ s` are
  pairwise a.e.-disjoint has measure at most `μ s`."]
theorem measure_le_of_pairwise_disjoint (hs : IsAEFundamentalDomain G s μ)
    (ht : NullMeasurableSet t μ) (hd : Pairwise (AEDisjoint μ on fun g : G => g • t ∩ s)) :
    μ t ≤ μ s :=
  calc
    μ t = ∑' g : G, μ (g • t ∩ s) := hs.measure_eq_tsum t
    _ = μ (⋃ g : G, g • t ∩ s) := Eq.symm <| measure_iUnion₀ hd fun _ =>
      (ht.smul _).inter hs.nullMeasurableSet
    _ ≤ μ s := measure_mono (iUnion_subset fun _ => inter_subset_right _ _)

/-- If the action of a countable group `G` admits an invariant measure `μ` with a fundamental domain
`s`, then every null-measurable set `t` of measure strictly greater than `μ s` contains two
points `x y` such that `g • x = y` for some `g ≠ 1`. -/
@[to_additive "If the additive action of a countable group `G` admits an invariant measure `μ` with
  a fundamental domain `s`, then every null-measurable set `t` of measure strictly greater than
  `μ s` contains two points `x y` such that `g +ᵥ x = y` for some `g ≠ 0`."]
theorem exists_ne_one_smul_eq (hs : IsAEFundamentalDomain G s μ) (htm : NullMeasurableSet t μ)
    (ht : μ s < μ t) : ∃ x ∈ t, ∃ y ∈ t, ∃ g, g ≠ (1 : G) ∧ g • x = y := by
  contrapose! ht
  refine' hs.measure_le_of_pairwise_disjoint htm (Pairwise.aedisjoint fun g₁ g₂ hne => _)
  dsimp [Function.onFun]
  refine' (Disjoint.inf_left _ _).inf_right _
  rw [Set.disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy : g₂ • y = g₁ • x⟩
  refine' ht x hx y hy (g₂⁻¹ * g₁) (mt inv_mul_eq_one.1 hne.symm) _
  rw [mul_smul, ← hxy, inv_smul_smul]

/-- If `f` is invariant under the action of a countable group `G`, and `μ` is a `G`-invariant
  measure with a fundamental domain `s`, then the `essSup` of `f` restricted to `s` is the same as
  that of `f` on all of its domain. -/
@[to_additive "If `f` is invariant under the action of a countable additive group `G`, and `μ` is a
  `G`-invariant measure with a fundamental domain `s`, then the `ess_sup` of `f` restricted to `s`
  is the same as that of `f` on all of its domain."]
theorem essSup_measure_restrict (hs : IsAEFundamentalDomain G s μ) {f : α → ℝ≥0∞}
    (hf : ∀ γ : G, ∀ x : α, f (γ • x) = f x) : essSup f (μ.restrict s) = essSup f μ := by
  refine' le_antisymm (essSup_mono_measure' Measure.restrict_le_self) _
  rw [essSup_eq_sInf (μ.restrict s) f, essSup_eq_sInf μ f]
  refine' sInf_le_sInf _
  rintro a (ha : (μ.restrict s) {x : α | a < f x} = 0)
  rw [Measure.restrict_apply₀' hs.nullMeasurableSet] at ha
  refine' measure_zero_of_invariant hs _ _ ha
  intro γ
  ext x
  rw [mem_smul_set_iff_inv_smul_mem]
  simp only [mem_setOf_eq, hf γ⁻¹ x]

end IsAEFundamentalDomain

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
  inter_subset_left _ _

@[to_additive MeasureTheory.addFundamentalInterior_subset]
theorem fundamentalInterior_subset : fundamentalInterior G s ⊆ s :=
  diff_subset _ _

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
-- porting note: there is a typo in `to_additive` in mathlib3, so there is no additive version

@[to_additive (attr := simp) MeasureTheory.sdiff_addFundamentalInterior]
theorem sdiff_fundamentalInterior : s \ fundamentalInterior G s = fundamentalFrontier G s :=
  sdiff_sdiff_right_self

@[to_additive (attr := simp) MeasureTheory.sdiff_addFundamentalFrontier]
theorem sdiff_fundamentalFrontier : s \ fundamentalFrontier G s = fundamentalInterior G s :=
  diff_self_inter

@[to_additive (attr := simp) MeasureTheory.addFundamentalFrontier_vadd]
theorem fundamentalFrontier_smul [Group H] [MulAction H α] [SMulCommClass H G α] (g : H) :
    fundamentalFrontier G (g • s) = g • fundamentalFrontier G s := by
  simp_rw [fundamentalFrontier, smul_set_inter, smul_set_Union, smul_comm g (_ : G) (_ : Set α)]

@[to_additive (attr := simp) MeasureTheory.addFundamentalInterior_vadd]
theorem fundamentalInterior_smul [Group H] [MulAction H α] [SMulCommClass H G α] (g : H) :
    fundamentalInterior G (g • s) = g • fundamentalInterior G s := by
  simp_rw [fundamentalInterior, smul_set_sdiff, smul_set_Union, smul_comm g (_ : G) (_ : Set α)]

@[to_additive MeasureTheory.pairwise_disjoint_addFundamentalInterior]
theorem pairwise_disjoint_fundamentalInterior :
    Pairwise (Disjoint on fun g : G => g • fundamentalInterior G s) := by
  refine' fun a b hab => disjoint_left.2 _
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  rw [mem_fundamentalInterior] at hx hy
  refine' hx.2 (a⁻¹ * b) _ _
  rwa [Ne.def, inv_mul_eq_iff_eq_mul, mul_one, eq_comm]
  simpa [mul_smul, ← hxy, mem_inv_smul_set_iff] using hy.1

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

namespace IsAEFundamentalDomain

section Group

variable [Countable G] [Group G] [MulAction G α] [MeasurableSpace α] {μ : Measure α} {s : Set α}
  (hs : IsAEFundamentalDomain G s μ)

@[to_additive MeasureTheory.IsAddFundamentalDomain.measure_addFundamentalFrontier]
theorem measure_fundamentalFrontier : μ (fundamentalFrontier G s) = 0 := by
  simpa only [fundamentalFrontier, iUnion₂_inter, measure_iUnion_null_iff', one_smul,
    measure_iUnion_null_iff, inter_comm s, Function.onFun] using fun g (hg : g ≠ 1) =>
    hs.aedisjoint hg

@[to_additive MeasureTheory.IsAddFundamentalDomain.measure_addFundamentalInterior]
theorem measure_fundamentalInterior : μ (fundamentalInterior G s) = μ s :=
  measure_diff_null' hs.measure_fundamentalFrontier

end Group

variable [Countable G] [Group G] [MulAction G α] [MeasurableSpace α] {μ : Measure α} {s : Set α}
  (hs : IsAEFundamentalDomain G s μ) [MeasurableSpace G] [MeasurableSMul G α]
  [SMulInvariantMeasure G α μ]

protected theorem fundamentalInterior : IsAEFundamentalDomain G (fundamentalInterior G s) μ where
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
    simp only [iUnion_inv_smul, compl_sdiff, ENNReal.bot_eq_zero, himp_eq, sup_eq_union,
      @iUnion_smul_eq_setOf_exists _ _ _ _ s]
    exact measure_union_null
      (measure_iUnion_null fun _ => measure_smul_null hs.measure_fundamentalFrontier _) hs.ae_covers
  aedisjoint := (pairwise_disjoint_fundamentalInterior _ _).mono fun _ _ => Disjoint.aedisjoint

end IsAEFundamentalDomain


-- work 6/23/23

section FundamentalDomainMeasure

variable [Group G] [MulAction G α] [MeasurableSpace α]

local notation "α_mod_G" => MulAction.orbitRel G α

local notation "π" => @Quotient.mk _ α_mod_G

attribute [aesop norm unfold] Disjoint

-- if we encounter problems about the quotient measure being badly behaved on non-measurable sets,
-- use Caratheodory construction `outer_measure.to_measure` ...
noncomputable def _root_.Set.quotientMeasure (s : Set α) (μ : Measure α)
    (hs : MeasurableSet s) : Measure (Quotient α_mod_G) := by
  apply Measure.ofMeasurable (fun U _ => μ ((π ⁻¹' U) ∩ s)) (by simp)
  intro f meas_f disjoint_f
  let ff : ℕ → Set α := fun n => π ⁻¹' (f n) ∩ s
  have meas_ff : ∀ n, MeasurableSet (ff n) :=
    fun n => (measurableSet_quotient.mp (meas_f n)).inter hs
  have disjoint_ff : Pairwise (Disjoint on fun (n : ℕ) => ff n)
  · intro x y x_ne_y
    have := Disjoint.preimage π (disjoint_f x_ne_y)
    rw [Function.onFun_apply]
    aesop
  convert μ.m_iUnion meas_ff disjoint_ff using 1
  simp [iUnion_inter]

-- noncomputable def _root_.Set.quotientMeasureSpace (s : Set α) (μ : Measure α)
--     (hs : MeasurableSet s) : MeasureSpace (Quotient α_mod_G) :=
--   { Quotient.instMeasurableSpace with
--     volume := s.quotientMeasure μ hs }

lemma _root_.Set.quotientMeasure_apply (s : Set α) (μ : Measure α)
    (hs : MeasurableSet s) {U : Set (Quotient α_mod_G)} (meas_U : MeasurableSet U) :
    (s.quotientMeasure μ hs) U = μ ((π ⁻¹' U) ∩ s) :=
  MeasureTheory.Measure.ofMeasurable_apply U meas_U

lemma _root_.Set.quotientMeasure_eq_map_restrict (s : Set α) (μ : Measure α)
    (hs : MeasurableSet s) :
    (s.quotientMeasure μ hs) = Measure.map π (μ.restrict s) := by
  ext U meas_U
  rw [Measure.map_apply, Measure.restrict_apply]
  · exact quotientMeasure_apply _ _ _ meas_U
  · exact measurableSet_quotient.mp meas_U
  · intro V hV
    exact measurableSet_quotient.mp hV
  · exact meas_U

lemma _root_.Set.quotientMeasure_invariant [Countable G] [MeasurableSpace G] {s t : Set α}
    {μ : Measure α} [SMulInvariantMeasure G α μ] [MeasurableSMul G α]
    (fund_dom_s : IsAEFundamentalDomain G s μ) (fund_dom_t : IsAEFundamentalDomain G t μ)
    (meas_s : MeasurableSet s) (meas_t : MeasurableSet t) :
    (s.quotientMeasure μ meas_s : Measure (Quotient α_mod_G)) = t.quotientMeasure μ meas_t := by
  apply MeasureTheory.Measure.ext
  intro U meas_U
  rw [quotientMeasure_apply _ _ _ meas_U, quotientMeasure_apply _ _ _ meas_U]
  apply MeasureTheory.IsAEFundamentalDomain.measure_set_eq fund_dom_s fund_dom_t
  · exact measurableSet_quotient.mp meas_U
  · intro g
    simp only
    ext x
    have : Quotient.mk α_mod_G (g • x) = Quotient.mk α_mod_G x
    · apply Quotient.sound
      use g
    aesop


end FundamentalDomainMeasure

section HasFundamentalDomain

/-- We say a quotient of `α` by `G` `HasFundamentalDomain` if there is a measurable set `s` for
  which `IsAEFundamentalDomain G s` holds -/
class HasFundamentalDomain (G : Type _) (α : Type _) [One G] [SMul G α]
  [MeasureSpace α] : Prop :=
(has_fundamental_domain_characterization :
  ∃ (s : Set α), IsAEFundamentalDomain G s ∧ MeasurableSet s)

def covolume (G : Type _) (α : Type _) [One G] [SMul G α] [MeasureSpace α]
    [funDom : HasFundamentalDomain G α] : ℝ≥0∞ :=
  volume funDom.has_fundamental_domain_characterization.choose

lemma covolume_eq_volume (G : Type _) (α : Type _) [Group G] [MulAction G α] [MeasurableSpace G]
    [Countable G] [MeasureSpace α] [MeasurableSMul G α] [SMulInvariantMeasure G α volume]
    [funDom : HasFundamentalDomain G α] (s : Set α) (fund_dom_s : IsAEFundamentalDomain G s) :
    covolume G α = volume s := by
  rw [covolume]
  rw [fund_dom_s.measure_eq]
  exact funDom.has_fundamental_domain_characterization.choose_spec.1

end HasFundamentalDomain

section QuotientVolumeEqVolume

variable (G α : Type _) [Group G] [MulAction G α] [MeasureSpace α]

local notation "α_mod_G" => MulAction.orbitRel G α

local notation "π" => @Quotient.mk _ α_mod_G

set_option linter.unusedVariables false in
class QuotientVolumeEqVolumePreimage (μ : Measure (Quotient α_mod_G)) --[MeasureSpace (Quotient α_mod_G)]
: Prop where
  projection_respects_measure : ∀ (t : Set α) (fund_dom_t : IsAEFundamentalDomain G t)
    (meas_t : MeasurableSet t) (U : Set (Quotient α_mod_G)) (meas_U : MeasurableSet U),
    μ U = volume (π ⁻¹' U ∩ t)

/-- If you want to make an instance of the typeclass, you can do it starting from any given
  fundamental domain -/
lemma Set.quotientMeasureSpace.QuotientVolumeEqVolumePreimage [Countable G] [MeasurableSpace G]
    [SMulInvariantMeasure G α volume] [MeasurableSMul G α] (s : Set α) (meas_s : MeasurableSet s)
    (fund_dom_s : IsAEFundamentalDomain G s) :
    @QuotientVolumeEqVolumePreimage G α _ _ _ (s.quotientMeasure volume meas_s) :=
  { projection_respects_measure := by
      intro t fund_dom_t meas_t U meas_U
      rw [quotientMeasure_invariant fund_dom_s fund_dom_t meas_s meas_t,
        quotientMeasure_apply _ _ _ meas_U] }


lemma quotientVolumeEqVolumePreimage_map_restrict [Countable G] [MeasurableSpace G]
    [SMulInvariantMeasure G α volume] [MeasurableSMul G α] (s : Set α) (meas_s : MeasurableSet s)
    (fund_dom_s : IsAEFundamentalDomain G s) :
    @QuotientVolumeEqVolumePreimage G α _ _ _ (Measure.map π (volume.restrict s)) := by
  convert Set.quotientMeasureSpace.QuotientVolumeEqVolumePreimage G α s meas_s fund_dom_s
  exact Eq.symm (quotientMeasure_eq_map_restrict s volume meas_s)


/-- Any two measures satisfying `QuotientVolumeEqVolumePreimage` are equal. -/
lemma QuotientVolumeEqVolumePreimage.unique
    [hasFun : HasFundamentalDomain G α]
    (μ ν : Measure (Quotient α_mod_G))
    [QuotientVolumeEqVolumePreimage G α μ] [QuotientVolumeEqVolumePreimage G α ν] :
    μ = ν := by
  ext U meas_U
  obtain ⟨𝓕, h𝓕, meas_𝓕⟩ := hasFun.has_fundamental_domain_characterization
  rw [QuotientVolumeEqVolumePreimage.projection_respects_measure 𝓕 h𝓕 meas_𝓕 U meas_U,
    QuotientVolumeEqVolumePreimage.projection_respects_measure 𝓕 h𝓕 meas_𝓕 U meas_U]

/-- Any measure satisfying `QuotientVolumeEqVolumePreimage` is equal to the quotient measure
  associated to the fundamental domain. -/
lemma QuotientVolumeEqVolumePreimage.eq_quotient_measure [Countable G] [MeasurableSpace G]
    [SMulInvariantMeasure G α volume] [MeasurableSMul G α] (s : Set α) (meas_s : MeasurableSet s)
    (fund_dom_s : IsAEFundamentalDomain G s) (μ : Measure (Quotient α_mod_G))
    [QuotientVolumeEqVolumePreimage G α μ] :
    μ = s.quotientMeasure volume meas_s := by
  haveI : HasFundamentalDomain G α := ⟨⟨s, fund_dom_s, meas_s⟩⟩
  haveI := Set.quotientMeasureSpace.QuotientVolumeEqVolumePreimage G α s meas_s fund_dom_s
  apply QuotientVolumeEqVolumePreimage.unique

lemma QuotientVolumeEqVolumePreimage.eq_map_restrict [Countable G] [MeasurableSpace G]
    [SMulInvariantMeasure G α volume] [MeasurableSMul G α] (s : Set α) (meas_s : MeasurableSet s)
    (fund_dom_s : IsAEFundamentalDomain G s) (μ : Measure (Quotient α_mod_G))
    [QuotientVolumeEqVolumePreimage G α μ] :
    μ = Measure.map π (volume.restrict s) := by
  rw [QuotientVolumeEqVolumePreimage.eq_quotient_measure G α s meas_s fund_dom_s μ]
  exact Set.quotientMeasure_eq_map_restrict s volume meas_s


/-- The quotient map to `α ⧸ G` is measure-preserving between the restriction of `volume` to a
  fundamental domain in `α` and a related measure satisfying `QuotientVolumeEqVolumePreimage`. -/
theorem measurePreserving_quotient_mk_of_quotientVolumeEqVolumePreimage
    [Countable G] [MeasurableSpace G] [MeasurableSMul G α]
    [SMulInvariantMeasure G α volume]
    (𝓕 : Set α) (h𝓕 : IsAEFundamentalDomain G 𝓕)
    (meas_𝓕 : MeasurableSet 𝓕) (μ : Measure (Quotient α_mod_G))
    [QuotientVolumeEqVolumePreimage G α μ] :
    MeasurePreserving π (volume.restrict 𝓕) μ where
  measurable := measurable_quotient_mk' (s := α_mod_G)
  map_eq := by
    haveI : HasFundamentalDomain G α := ⟨𝓕, h𝓕, meas_𝓕⟩
    rw [QuotientVolumeEqVolumePreimage.eq_map_restrict (μ := μ) (s := 𝓕)]
    · assumption
    · assumption

end QuotientVolumeEqVolume

---- NEW 8/8/23

section DirichletPolyhedron

variable {α : Type _} [MetricSpace α]  (G : Type _) [Group G] [Countable G] [MulAction G α]
  [MeasurableSpace α] [OpensMeasurableSpace α]

--local notation "α_mod_G" => MulAction.orbitRel G α

--local notation "π" => @Quotient.mk _ α_mod_G

def DirichletPolyhedron (x : α) : Set α :=
  {y : α | ∀ g : G, dist x y ≤ dist (g • x) y}

theorem DirichletPolyhedron_eq_Inter (x : α) :
    DirichletPolyhedron G x = ⋂ g : G, {y : α | dist x y ≤ dist (g • x) y} := by
  ext y
  simp only [DirichletPolyhedron, mem_setOf_eq, mem_iInter]

theorem IsAEFundamentalDomain_of_DirichletPolyhedron --[LocallyCompactSpace α]
    [ProperSpace α] [IsometricSMul G α]
    [i₁ : ProperlyDiscontinuousSMul G α] (x : α) (hx : ∀ g : G, g • x ≠ x) {μ : Measure α} :
    IsAEFundamentalDomain G (DirichletPolyhedron G x) μ where
  nullMeasurableSet := by
    apply MeasurableSet.nullMeasurableSet
    dsimp [NullMeasurableSet]
    rw [DirichletPolyhedron_eq_Inter]
    apply MeasurableSet.iInter
    intro g
    apply @IsClosed.measurableSet α ({y | dist x y ≤ dist (g • x) y}) _ _ _
    rw [← isOpen_compl_iff]
    suffices h : IsOpen {y : α | dist (g • x) y < dist x y}
    · convert h using 1
      ext y
      simp only [mem_compl_iff, mem_setOf_eq, not_le]
    · apply isOpen_lt
      · exact @Continuous.dist α α _ _ (fun y ↦ (g • x)) (fun y ↦ y) continuous_const continuous_id
      · exact @Continuous.dist α α _ _ (fun y ↦ x) (fun y ↦ y) continuous_const continuous_id
  ae_covers := by
    filter_upwards
    set s := DirichletPolyhedron G x
    intro y
    let t := Metric.closedBall y (dist x y)
    have comp_t : IsCompact t := isCompact_closedBall y (dist x y)
    have fin_orbit := i₁.finite_disjoint_inter_image comp_t comp_t
    set Γ := {γ : G | (fun x ↦ γ • x) '' t ∩ t ≠ ∅}
    have nonempty_Γ : Set.Nonempty Γ := by
      use 1
      simp only [image_smul, Metric.smul_closedBall, ne_eq, mem_setOf_eq, one_smul, inter_self,
        Metric.closedBall_eq_empty, not_lt]
      exact dist_nonneg
    obtain ⟨g, -, hg⟩ :=
      @Set.exists_min_image G ℝ _ Γ (fun γ ↦ dist x (γ • y)) fin_orbit nonempty_Γ
    use g
    simp only [DirichletPolyhedron, mem_setOf_eq]
    intro γ
    have dist_eq : dist (γ • x) (g • y) = dist x ((γ⁻¹ * g) • y) := by
      convert @dist_smul G α _ _ _ γ x ((γ⁻¹ * g) • y) using 2
      rw [← mul_smul]
      simp
    have := hg (γ⁻¹ * g)
    by_cases hγ : (γ⁻¹ * g) ∈ Γ
    · have := this hγ
      convert this using 1
    · simp only [image_smul, Metric.smul_closedBall, ne_eq, mem_setOf_eq, not_not] at hγ
      rw [dist_eq]
      sorry

    -- have : (⋃ g : G, (fun y ↦ g • y) '' s) = univ := by
    --   ext z
    --   simp only [image_smul, mem_iUnion, mem_univ, iff_true]


  aedisjoint := by
    set s := DirichletPolyhedron G x
    intro g₁ g₂ h
    change μ (( (fun y ↦ g₁ • y) '' s) ∩  (fun y ↦ g₂ • y) '' s) = 0

    sorry




end DirichletPolyhedron

end MeasureTheory
