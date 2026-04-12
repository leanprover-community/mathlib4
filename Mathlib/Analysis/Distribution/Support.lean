/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution

/-! # Support of distributions

We define the support of a distribution, `dsupport u`, as the intersection of all closed sets for
which `u` vanishes on the complement.
For this we also define a predicate `IsVanishingOn` that asserts that a map `f : F → V` vanishes on
`s : Set α` if for all `u : F` with `tsupport u ⊆ s` it follows that `f u = 0`.

These definitions work independently of a specific class of distributions (classical, tempered, or
compactly supported) and all basic properties are proved in an abstract setting using `FunLike`.

## Main definitions
* `IsVanishingOn`: A distribution vanishes on a set if it acts trivially on all test functions
  supported in that subset.
* `dsupport`: The support of a distribution is the intersection of all closed sets for which that
  distribution vanishes on the complement of the set.

## Main statements
* `TemperedDistribution.dsupport_delta`: The support of the delta distribution is a single point.

-/

@[expose] public noncomputable section

variable {ι α β 𝕜 E F F₁ F₂ R V : Type*}

open scoped Topology

namespace Distribution

section IsVanishingOn

variable [FunLike F α β] [TopologicalSpace α] [Zero β]

variable {f g : F → V} {s s₁ s₂ : Set α}

/-! ### Vanishing of distributions -/

section Zero

variable [Zero V]

/-- A distribution `f` vanishes on a set `s` if it vanishes for all test functions `u` with
`tsupport u ⊆ s`.

To make this definition work for all types of distributions, we define it for any function from
a `FunLike` type to a type with zero. -/
def IsVanishingOn (f : F → V) (s : Set α) : Prop :=
    ∀ (u : F), tsupport u ⊆ s → f u = 0

@[gcongr]
theorem IsVanishingOn.mono ⦃s₁ s₂ : Set α⦄ (hs : s₂ ⊆ s₁) (hf : IsVanishingOn f s₁) :
    IsVanishingOn f s₂ :=
  (hf · <| ·.trans hs)

theorem not_isVanishingOn_mono ⦃s₁ s₂ : Set α⦄ (hs : s₁ ⊆ s₂) (hf : ¬ IsVanishingOn f s₁) :
    ¬ IsVanishingOn f s₂ :=
  (hf <| ·.mono hs)

theorem not_isVanishingOn_iff :
    ¬ IsVanishingOn f s ↔ ∃ u : F, tsupport u ⊆ s ∧ f u ≠ 0 := by
  simp [IsVanishingOn]

end Zero

end IsVanishingOn

section dsupport

/-! ### Support -/

section Zero

variable [FunLike F α β] [TopologicalSpace α] [Zero β] [Zero V]

variable {f g : F → V} {s s₁ s₂ : Set α}

/-- The distributional support of `f` is the intersection of all closed sets `s` such that `f`
vanishes on the complement of `s`.

To make this definition work for all types of distributions, we define it for any function from
a `FunLike` type to a type with zero. -/
def dsupport (f : F → V) : Set α := ⋂₀ { s | IsVanishingOn f sᶜ ∧ IsClosed s}

theorem mem_dsupport_iff (x : α) :
    x ∈ dsupport f ↔ ∀ (s : Set α), IsVanishingOn f sᶜ → IsClosed s → x ∈ s := by
  simp [dsupport]

/-- The complement of the support is the largest open set on which `f` vanishes. -/
theorem dsupport_compl_eq : (dsupport f)ᶜ = ⋃₀ { a | IsVanishingOn f a ∧ IsOpen a } := by
  simp [dsupport, Set.compl_sInter, Set.compl_image_set_of]

@[simp high]
theorem notMem_dsupport_iff (x : α) :
    x ∉ (dsupport f) ↔ ∃ (s : Set α), IsVanishingOn f s ∧ IsOpen s ∧ x ∈ s := by
  simp [← Set.mem_compl_iff, dsupport_compl_eq, Set.mem_sUnion, and_assoc]

theorem mem_dsupport_iff_not_isVanishingOn (x : α) :
    x ∈ dsupport f ↔ ∀ s, x ∈ s → IsOpen s → ¬ IsVanishingOn f s := by
  grind only [notMem_dsupport_iff]

theorem mem_dsupport_iff_forall_exists_ne (x : α) :
    x ∈ dsupport f ↔ ∀ s, x ∈ s → IsOpen s → ∃ u : F, tsupport u ⊆ s ∧ f u ≠ 0 := by
  simp_rw [mem_dsupport_iff_not_isVanishingOn, not_isVanishingOn_iff]

theorem mem_dsupport_iff_frequently {x : α} :
    x ∈ dsupport f ↔ ∃ᶠ u in (𝓝 x).smallSets, ¬ IsVanishingOn f u := by
  rw [nhds_basis_opens x |>.frequently_smallSets not_isVanishingOn_mono]
  simpa using mem_dsupport_iff_not_isVanishingOn x

theorem _root_.Filter.HasBasis.mem_dsupport {ι : Sort*} {p : ι → Prop}
    {s : ι → Set α} {x : α} (hl : (𝓝 x).HasBasis p s) :
    x ∈ dsupport f ↔ ∀ (i : ι), p i → ¬ IsVanishingOn f (s i) := by
  rw [mem_dsupport_iff_frequently]
  exact hl.frequently_smallSets not_isVanishingOn_mono

theorem notMem_dsupport_iff_eventually {x : α} :
    x ∉ dsupport f ↔ ∀ᶠ u in (𝓝 x).smallSets, IsVanishingOn f u := by
  simp [mem_dsupport_iff_frequently]

theorem _root_.Filter.HasBasis.notMem_dsupport {ι : Sort*} {p : ι → Prop}
    {s : ι → Set α} {x : α} (hl : (𝓝 x).HasBasis p s) :
    x ∉ dsupport f ↔ ∃ i, p i ∧ IsVanishingOn f (s i) := by
  simp [hl.mem_dsupport]

@[gcongr]
theorem dsupport_subset_dsupport
    (h : ∀ (s : Set α) (_ : IsOpen s), IsVanishingOn g s → IsVanishingOn f s) :
    dsupport f ⊆ dsupport g :=
  Set.sInter_mono fun s ⟨g_van, s_cl⟩ ↦ ⟨h sᶜ s_cl.isOpen_compl g_van, s_cl⟩

@[grind .]
theorem isClosed_dsupport : IsClosed (dsupport f) := by
  grind [dsupport, isClosed_sInter]

theorem IsVanishingOn.disjoint_dsupport (h : IsVanishingOn f s) (s_open : IsOpen s) :
    Disjoint s (dsupport f) := by
  rw [← Set.subset_compl_iff_disjoint_right, dsupport_compl_eq]
  exact Set.subset_sUnion_of_mem ⟨h, s_open⟩

end Zero

end dsupport

section normed

variable [FunLike F α β] [PseudoMetricSpace α] [Zero β] [Zero V]

variable {f : F → V}

/-- The complement of the support is given by all *bounded* open sets on which `f` vanishes. -/
theorem compl_dsupport_eq_sUnion_isBounded :
    (dsupport f)ᶜ = ⋃₀ { a | IsVanishingOn f a ∧ IsOpen a ∧ Bornology.IsBounded a } := by
  ext x
  grind [(Metric.hasBasis_nhds_isOpen_isBounded x).notMem_dsupport]

end normed

/-! ## Tempered distributions -/

open SchwartzMap Distribution TemperedDistribution

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℂ F]

variable {f : 𝓢'(E, F)} {s : Set E}

namespace IsVanishingOn

open scoped Topology

@[grind .]
theorem smulLeftCLM (hf : IsVanishingOn f s) {g : E → ℂ} (hg : g.HasTemperateGrowth) :
    IsVanishingOn (smulLeftCLM F g f) s := by
  intro u hu
  apply hf ((SchwartzMap.smulLeftCLM ℂ g) u)
  rw [SchwartzMap.smulLeftCLM_apply hg]
  exact (tsupport_smul_subset_right g u).trans hu

open LineDeriv

@[grind .]
theorem lineDerivOp (hf : IsVanishingOn f s) (m : E) :
    IsVanishingOn (∂_{m} f : 𝓢'(E, F)) s := by
  intro u hu
  simp only [lineDerivOp_apply_apply, map_neg, neg_eq_zero]
  exact hf (∂_{m} u) <| (tsupport_fderiv_apply_subset ℝ m).trans hu

@[grind .]
theorem iteratedLineDerivOp {n : ℕ} (hf : IsVanishingOn f s) (m : Fin n → E) :
    IsVanishingOn (∂^{m} f : 𝓢'(E, F)) s := by
  induction n with
  | zero =>
    exact hf
  | succ n IH =>
    exact (IH <| Fin.tail m).lineDerivOp (m 0)

@[grind .]
theorem _root_.TemperedDistribution.isVanishingOn_delta (x : E) :
    IsVanishingOn (TemperedDistribution.delta x) {x}ᶜ := by
  intro u hu
  rw [Set.subset_compl_singleton_iff] at hu
  apply image_eq_zero_of_notMem_tsupport hu

end IsVanishingOn

section Support

theorem dsupport_smulLeftCLM_subset {g : E → ℂ} (hg : g.HasTemperateGrowth) :
    dsupport (smulLeftCLM F g f) ⊆ dsupport f := by
  gcongr; grind

open LineDeriv

theorem dsupport_lineDerivOp_subset (m : E) : dsupport (∂_{m} f : 𝓢'(E, F)) ⊆ dsupport f := by
  gcongr; grind

theorem dsupport_iteratedLineDerivOp_subset {n : ℕ} (m : Fin n → E) :
    dsupport (∂^{m} f : 𝓢'(E, F)) ⊆ dsupport f := by
  gcongr; grind

theorem dsupport_delta [FiniteDimensional ℝ E] (x : E) :
    dsupport (TemperedDistribution.delta x) = {x} := by
  apply subset_antisymm
  · intro x' hx'
    rw [mem_dsupport_iff] at hx'
    exact hx' {x} (isVanishingOn_delta x) (T1Space.t1 x)
  rintro x rfl
  rw [mem_dsupport_iff_forall_exists_ne]
  intro s hx hs
  obtain ⟨u, h₁, h₂, h₃, -, h₄⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) ((IsOpen.mem_nhds_iff hs).mpr hx)
  have h₁' : tsupport (Complex.ofRealCLM ∘ u) ⊆ s := (tsupport_comp_subset rfl _).trans h₁
  have h₂' : HasCompactSupport (Complex.ofRealCLM ∘ u) := h₂.comp_left rfl
  use h₂'.toSchwartzMap (Complex.ofRealCLM.contDiff.comp h₃)
  exact ⟨h₁', by simp [h₄]⟩

end Support

end Distribution
