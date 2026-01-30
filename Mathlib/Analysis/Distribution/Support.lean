/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Support of distributions


-/

@[expose] public noncomputable section

variable {ι α β 𝕜 E F F₁ F₂ R V : Type*}

section abstract

variable [FunLike F α β] [TopologicalSpace α] [Zero β]

variable {f g : F → V} {s s₁ s₂ : Set α}

section IsVanishingOn

section Zero

variable [Zero V]

def IsVanishingOn (f : F → V) (s : Set α) : Prop :=
    ∀ (u : F), tsupport u ⊆ s → f u = 0

variable (F V s) in
@[simp, grind .]
theorem isVanishingOn_zero : IsVanishingOn (0 : F → V) s := by
  simp [IsVanishingOn]

@[simp]
theorem isVanishingOn_univ_iff : IsVanishingOn f Set.univ ↔ f = 0 := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ by simp [hf]⟩
  ext u
  simpa [IsVanishingOn] using hf u

theorem IsVanishingOn.mono (hs : s₂ ⊆ s₁) (hf : IsVanishingOn f s₁) : IsVanishingOn f s₂ :=
  fun u hu ↦ hf u (hu.trans hs)

end Zero

section Monoid

@[grind .]
theorem IsVanishingOn.add [AddMonoid V] (hf : IsVanishingOn f s₁) (hg : IsVanishingOn g s₂) :
    IsVanishingOn (f + g) (s₁ ∩ s₂) := by
  intro u hu
  simp [hf u (hu.trans Set.inter_subset_left), hg u (hu.trans Set.inter_subset_right)]

variable [SubtractionMonoid V]

@[grind .]
theorem IsVanishingOn.neg (hf : IsVanishingOn f s) :
    IsVanishingOn (-f) s := by
  intro u hu
  simpa using hf u hu

@[grind .]
theorem IsVanishingOn.sub (hf : IsVanishingOn f s₁)
    (hg : IsVanishingOn g s₂) :
    IsVanishingOn (f - g) (s₁ ∩ s₂) := by
  intro u hu
  simp [hf u (hu.trans Set.inter_subset_left), hg u (hu.trans Set.inter_subset_right)]

end Monoid

section Module

variable [Semiring R] [AddCommMonoid V] [Module R V]

@[grind .]
theorem IsVanishingOn.smul (hf : IsVanishingOn f s) (r : R) :
    IsVanishingOn (r • f) s := by
  intro u hu
  simp [hf u hu]

end Module

end IsVanishingOn

section dsupport

section Zero

variable [Zero V]

/-- The distributional support is the smallest closed subset of `E` on which a distribution does not
vanish. -/
def dsupport (f : F → V) : Set α := ⋂₀ { s | IsVanishingOn f sᶜ ∧ IsClosed s}

theorem mem_dsupport_iff (x : α) :
    x ∈ dsupport f ↔ ∀ (s : Set α), IsVanishingOn f sᶜ → IsClosed s → x ∈ s := by
  simp [dsupport]

theorem mem_dsupport_of_forall_exists_ne (x : α) (h : ∀ (s : Set α) (_ : x ∈ s) (_ : IsOpen s),
    ∃ u : F, tsupport u ⊆ s ∧ f u ≠ 0) : x ∈ dsupport f := by
  rw [mem_dsupport_iff]
  intro s hs hs'
  by_cases! h' : x ∈ s
  · exact h'
  exfalso
  obtain ⟨u, h₁, h₂⟩ := h sᶜ h' IsClosed.isOpen_compl
  exact h₂ (hs u h₁)

@[simp high]
theorem mem_dsupport_compl_iff (x : α) :
    x ∈ (dsupport f)ᶜ ↔ ∃ (s : Set α), IsVanishingOn f s ∧ IsOpen s ∧ x ∈ s := by
  simp only [dsupport, Set.mem_compl_iff, Set.mem_sInter, Set.mem_setOf_eq, and_imp, not_forall]
  constructor
  · intro ⟨s, hs₁, hs₂, h⟩
    use sᶜ, hs₁, IsClosed.isOpen_compl
    exact h
  · intro ⟨s, hs₁, hs₂, h⟩
    use sᶜ
    simp only [Set.mem_compl_iff, not_not, isClosed_compl_iff, exists_prop, compl_compl]
    exact ⟨hs₁, hs₂, h⟩

/-- The complement of the support is given by all open sets on which `f` vanishes. -/
theorem dsupport_compl_eq : (dsupport f)ᶜ = ⋃₀ { a | IsVanishingOn f a ∧ IsOpen a } := by
  simp [dsupport, Set.compl_sInter, Set.compl_image_set_of]

@[grind .]
theorem dsupport_subset_dsupport
    (h : ∀ (s : Set α) (_ : IsOpen s), IsVanishingOn g s → IsVanishingOn f s) :
    dsupport f ⊆ dsupport g := by
  intro x hx
  rw [mem_dsupport_iff] at hx ⊢
  intro s hs hs'
  apply hx s (h sᶜ IsClosed.isOpen_compl hs) hs'

@[grind .]
theorem isClosed_dsupport : IsClosed (dsupport f) := by
  grind [dsupport, isClosed_sInter]

@[simp]
theorem support_zero_eq_emptyset : dsupport (0 : F → V) = ∅ := by
  simp only [dsupport, isVanishingOn_zero, true_and, Set.sInter_eq_empty_iff, Set.mem_setOf_eq]
  intro x
  use ∅
  simp

end Zero

section Monoid

theorem support_add_subset [AddMonoid V] : dsupport (f + g) ⊆ dsupport f ∪ dsupport g := by
  rw [← Set.compl_subset_compl, Set.compl_union]
  intro x hx
  rw [mem_dsupport_compl_iff]
  simp only [Set.mem_inter_iff, mem_dsupport_compl_iff] at hx
  obtain ⟨⟨s₁, hs₁, hs₁', hs₁''⟩, s₂, hs₂, hs₂', hs₂''⟩ := hx
  use s₁ ∩ s₂
  exact ⟨hs₁.add hs₂, hs₁'.inter hs₂', Set.mem_inter hs₁'' hs₂''⟩

variable [SubtractionMonoid V]

@[simp]
theorem support_neg_eq : dsupport (-f) = dsupport f := by
  apply subset_antisymm
  all_goals grind [neg_neg]

theorem support_sub_subset : dsupport (f - g) ⊆ dsupport f ∪ dsupport g := by
  grw [sub_eq_add_neg, support_add_subset, support_neg_eq]

end Monoid

section Module

variable [Semiring R] [AddCommMonoid V] [Module R V]

theorem support_smul_subset (r : R) : dsupport (r • f) ⊆ dsupport f := by grind

end Module

end dsupport

end abstract

open SchwartzMap ContinuousLinearMap MeasureTheory MeasureTheory.Measure

open scoped Nat NNReal ContDiff

namespace TemperedDistribution

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℂ F]

section IsVanishingOn

variable {f : 𝓢'(E, F)} {g : 𝓢'(E, F)} {s s₁ s₂ : Set E}

open scoped Topology

-- Hörmander 7.1.8
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem foo (f : 𝓢(E, F)) : ∃ (u : ℕ → 𝓢(E, F)), Filter.Tendsto u Filter.atTop (𝓝 f) ∧
    ∀ i, tsupport (u i) ⊆ tsupport f ∧ HasCompactSupport (u i) := by
  set g := ExistsContDiffBumpBase.y (E := E) (1/2)
  have hg₁ : ContDiff ℝ ∞ g := by sorry
  have hg₂ : tsupport g ⊆ Metric.ball 0 (1/2) := by sorry
  sorry

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem isVanishingOn_iff_forall_hasCompactSupport : _root_.IsVanishingOn f s ↔
    ∀ (u : 𝓢(E, ℂ)), HasCompactSupport u → tsupport u ⊆ s → f u = 0 := by
  constructor
  · intro h u hu₁
    exact h u
  intro h u hu
  obtain ⟨v, hv₁, hv₂⟩ := foo u
  have hv₃ : f ∘ v = 0 := by
    ext i
    apply h (v i) (hv₂ i).2 ((hv₂ i).1.trans hu)
  have lim₁ : Filter.Tendsto (f ∘ v) Filter.atTop (𝓝 (f u)) :=
    (f.continuous.tendsto u).comp hv₁
  have lim₂ : Filter.Tendsto (f ∘ v) Filter.atTop (𝓝 0) := by
    rw [hv₃]
    apply tendsto_const_nhds
  exact tendsto_nhds_unique lim₁ lim₂

variable [FiniteDimensional ℝ E] [Finite ι] in
theorem IsVanishingOn.iUnion {s : ι → Set E} (hs : ∀ i, IsOpen (s i))
    (hs' : ∀ i, Bornology.IsBounded (s i)) (hf : ∀ i, IsVanishingOn f (s i)) :
    IsVanishingOn f (⋃ i, s i) := by
  -- The boundedness condition is not strictly necessary, but we would need a partition of unity
  -- with temperate growth functions to remove this restriction.
  intro u hu
  have : IsClosed (tsupport u) := isClosed_tsupport u
  obtain ⟨g, hg⟩ := Normed.SmoothPartitionOfUnity.exists_isSubordinate (isClosed_tsupport u) s hs hu
  have hg' : ∀ i, (g i).HasTemperateGrowth := by
    intro i
    --apply Complex.ofRealCLM.hasTemperateGrowth.comp
    -- It remains to show that `g i` has temperate growth, which follows from being compactly
    -- supported
    have : HasCompactSupport (g i) := (hs' i).isCompact_closure.of_isClosed_subset
      (isClosed_tsupport _) ((hg i).trans subset_closure)
    exact this.hasTemperateGrowth (g.contDiff i)
  set u' := fun i ↦ SchwartzMap.smulLeftCLM ℂ (g i) u
  have hu' : ∀ i, u' i = fun x ↦ g i x • u x := fun i ↦ smulLeftCLM_apply (hg' i) u
  haveI := Fintype.ofFinite ι
  have : u = ∑ i, u' i := by
    ext x
    have : ∀ y ∈ tsupport u, ∑ i, g i y = 1 := by
      intro y hy
      simpa [finsum_eq_sum_of_fintype] using g.sum_eq_one' y hy
    simp only [SchwartzMap.sum_apply, hu', ← Finset.sum_smul, u']
    by_cases h : x ∈ tsupport u
    · simp [this x h]
    · simp [image_eq_zero_of_notMem_tsupport h]
  rw [this, _root_.map_sum]
  apply Fintype.sum_eq_zero
  intro i
  apply hf i
  grw [← hg i]
  exact tsupport_smulLeftCLM_subset_left (g i) u

@[grind .]
theorem IsVanishingOn.smulLeftCLM (hf : IsVanishingOn f s) {g : E → ℂ} (hg : g.HasTemperateGrowth) :
    IsVanishingOn (smulLeftCLM F g f) s := by
  intro u hu
  apply hf ((SchwartzMap.smulLeftCLM ℂ g) u)
  rw [SchwartzMap.smulLeftCLM_apply hg]
  exact (tsupport_smul_subset_right g u).trans hu

open LineDeriv

@[grind .]
theorem IsVanishingOn.lineDerivOp (hf : IsVanishingOn f s) (m : E) :
    IsVanishingOn (∂_{m} f : 𝓢'(E, F)) s := by
  intro u hu
  simp only [lineDerivOp_apply_apply, map_neg, neg_eq_zero]
  exact hf (∂_{m} u) <| (tsupport_lineDerivOp_subset m u).trans hu

@[grind .]
theorem IsVanishingOn.iteratedLineDerivOp {n : ℕ} (hf : IsVanishingOn f s) (m : Fin n → E) :
    IsVanishingOn (∂^{m} f : 𝓢'(E, F)) s := by
  induction n with
  | zero =>
    exact hf
  | succ n IH =>
    exact lineDerivOp (IH <| Fin.tail m) (m 0)

@[grind .]
theorem isVanishingOn_delta (x : E) : IsVanishingOn (delta x) {x}ᶜ := by
  intro u hu
  rw [Set.subset_compl_singleton_iff] at hu
  apply image_eq_zero_of_notMem_tsupport hu

end IsVanishingOn

section Support

variable {f : 𝓢'(E, F)} {g : 𝓢'(E, F)} {s : Set E}

/-- The complement of the support is given by all *bounded* open sets on which `f` vanishes. -/
theorem support_compl_eq_sUnion_isBounded :
    (dsupport f)ᶜ = ⋃₀ { a | IsVanishingOn f a ∧ IsOpen a ∧ Bornology.IsBounded a } := by
  rw [dsupport_compl_eq]
  apply subset_antisymm
  · simp only [Set.sUnion_subset_iff, Set.mem_setOf_eq, and_imp]
    intro s hs₁ hs₂
    have : s = ⋃ (ε : ℝ) (_ : 0 < ε), s ∩ Metric.ball 0 ε := by
      have : ⋃ (ε : ℝ) (_ : 0 < ε), Metric.ball (0 : E) ε = Set.univ := by
        rw [Set.iUnion₂_eq_univ_iff]
        intro x
        use ‖x‖ + 1, by positivity
        simp
      simp [← Set.inter_iUnion₂, this]
    rw [this]
    simp only [Set.iUnion_subset_iff]
    intro ε hε
    apply Set.subset_sUnion_of_mem
    refine ⟨hs₁.mono Set.inter_subset_left, hs₂.inter Metric.isOpen_ball, ?_⟩
    exact Bornology.IsBounded.subset Metric.isBounded_ball Set.inter_subset_right
  simp only [Set.sUnion_subset_iff, Set.mem_setOf_eq, and_imp]
  intro s hs₁ hs₂ hs₃
  exact Set.subset_sUnion_of_mem ⟨hs₁, hs₂⟩

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem isVanishingOn_support_compl : IsVanishingOn f (dsupport f)ᶜ := by
  rw [support_compl_eq_sUnion_isBounded, isVanishingOn_iff_forall_hasCompactSupport,
    Set.sUnion_eq_iUnion]
  intro u hu hf
  rw [hasCompactSupport_def] at hu
  obtain ⟨s, hs⟩ := hu.elim_finite_subcover _ (fun ⟨s, _, h, _⟩ ↦ h) hf
  apply IsVanishingOn.iUnion (s := fun (i : s) ↦ i) (fun ⟨⟨s, _, h, _⟩, _⟩ ↦ h)
    (fun ⟨⟨s, _, _, h⟩, _⟩ ↦ h) (fun ⟨⟨s, h, _, _⟩, _⟩ ↦ h)
  rwa [Set.iUnion_subtype]

theorem support_smulLeftCLM_subset {g : E → ℂ} (hg : g.HasTemperateGrowth) :
    dsupport (smulLeftCLM F g f) ⊆ dsupport f := by grind

open LineDeriv

theorem support_lineDerivOp_subset (m : E) : dsupport (∂_{m} f : 𝓢'(E, F)) ⊆ dsupport f := by grind

theorem support_iteratedLineDerivOp_subset {n : ℕ} (m : Fin n → E) :
    dsupport (∂^{m} f : 𝓢'(E, F)) ⊆ dsupport f := by grind

open scoped Topology

theorem support_delta [FiniteDimensional ℝ E] (x : E) : dsupport (delta x) = {x} := by
  apply subset_antisymm
  · intro x' hx'
    rw [mem_dsupport_iff] at hx'
    exact hx' {x} (isVanishingOn_delta x) (T1Space.t1 x)
  rintro x rfl
  apply mem_dsupport_of_forall_exists_ne
  intro s hx hs
  obtain ⟨u, h₁, h₂, h₃, -, h₄⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) ((IsOpen.mem_nhds_iff hs).mpr hx)
  have h₁' : tsupport (Complex.ofRealCLM ∘ u) ⊆ s := (tsupport_comp_subset rfl _).trans h₁
  have h₂' : HasCompactSupport (Complex.ofRealCLM ∘ u) := h₂.comp_left rfl
  use h₂'.toSchwartzMap (Complex.ofRealCLM.contDiff.comp h₃)
  exact ⟨h₁', by simp [h₄]⟩

end Support

end TemperedDistribution
