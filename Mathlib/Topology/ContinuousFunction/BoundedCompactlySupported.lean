/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.RingTheory.TwoSidedIdeal.Lattice

open Set BoundedContinuousFunction

/-!
# Compactly supported bounded continuous functions

The two-sided ideal of compactly supported bounded continuous functions taking values in a metric
space, with the uniform distance.
-/

section CompactlySupported

/-- The two-sided ideal of compactly supported functions. -/
def compactlySupported (α γ : Type*) [TopologicalSpace α] [NonUnitalNormedRing γ] :
    TwoSidedIdeal (α →ᵇ γ) :=
  .mk' {z | HasCompactSupport z} .zero .add .neg' .mul_left .mul_right

variable {α γ : Type*} [TopologicalSpace α] [NonUnitalNormedRing γ]

@[inherit_doc]
scoped[BoundedContinuousFunction] notation
  "C_cb(" α ", " γ ")" => compactlySupported α γ

lemma mem_compactlySupported {f : α →ᵇ γ} :
    f ∈ C_cb(α, γ) ↔ HasCompactSupport f :=
  TwoSidedIdeal.mem_mk' {z : α →ᵇ γ | HasCompactSupport z} .zero .add .neg' .mul_left .mul_right f

lemma exist_norm_eq [c : Nonempty α] {f : α →ᵇ γ} (h : f ∈ C_cb(α, γ)) : ∃ (x : α),
    ‖f x‖ = ‖f‖ := by
  by_cases hs : (tsupport f).Nonempty
  · obtain ⟨x, _, hmax⟩ := mem_compactlySupported.mp h |>.exists_isMaxOn hs <|
      (map_continuous f).norm.continuousOn
    refine ⟨x, le_antisymm (norm_coe_le_norm f x) (norm_le (norm_nonneg _) |>.mpr fun y ↦ ?_)⟩
    by_cases hy : y ∈ tsupport f
    · exact hmax hy
    · simp [image_eq_zero_of_nmem_tsupport hy]
  · suffices f = 0 by simp [this]
    rwa [not_nonempty_iff_eq_empty, tsupport_eq_empty_iff, ← coe_zero, ← DFunLike.ext'_iff] at hs

theorem norm_lt_iff_of_compactlySupported {f : α →ᵇ γ} (h : f ∈ C_cb(α, γ)) {M : ℝ}
    (M0 : 0 < M) : ‖f‖ < M ↔ ∀ (x : α), ‖f x‖ < M := by
  constructor
  · intro hn x
    exact lt_of_le_of_lt (norm_coe_le_norm f x) hn
  · by_cases he : Nonempty α
    · intro ha
      obtain ⟨x, hx⟩ := exist_norm_eq h
      rw [← hx]
      exact ha x
    · rw [not_nonempty_iff] at he
      intro _
      rw [norm_eq_zero_of_empty]
      exact M0

theorem norm_lt_iff_of_nonempty_compactlySupported [c : Nonempty α] {f : α →ᵇ γ}
    (h : f ∈ C_cb(α, γ)) {M : ℝ} : ‖f‖ < M ↔ ∀ (x : α), ‖f x‖ < M := by
  constructor
  · intro hn x
    exact lt_of_le_of_lt (norm_coe_le_norm f x) hn
  · intro ha
    obtain ⟨x, _⟩ := exists_true_iff_nonempty.mpr c
    apply (norm_lt_iff_of_compactlySupported h (lt_of_le_of_lt (norm_nonneg (f x)) (ha x))).mpr ha

theorem compactlySupported_eq_top_of_isCompact (h : IsCompact (Set.univ : Set α)) :
    C_cb(α, γ) = ⊤ :=
  eq_top_iff.mpr fun _ _ ↦ h.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)

/- This is intentionally not marked `@[simp]` to prevent Lean looking for a `CompactSpace α`
instance every time it sees `C_cb(α, γ)`. -/
theorem compactlySupported_eq_top [CompactSpace α] : C_cb(α, γ) = ⊤ :=
  compactlySupported_eq_top_of_isCompact CompactSpace.isCompact_univ

theorem compactlySupported_eq_top_iff [Nontrivial γ] :
    C_cb(α, γ) = ⊤ ↔ IsCompact (Set.univ : Set α) := by
  refine ⟨fun h ↦ ?_, compactlySupported_eq_top_of_isCompact⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : γ)
  let f : α →ᵇ γ := const α x
  have hf : f ∈ C_cb(α, γ) := by rw [h]; trivial -- missing `TwoSidedIdeal.mem_top` simp lemma
  convert (mem_compactlySupported.mp hf).isCompact
  rw [eq_comm, Set.eq_univ_iff_forall]
  exact fun _ ↦ subset_tsupport _ <| by simpa [f]

lemma hasCompactSupport_mul_of_continuous_compactlySupported (f : α →ᵇ γ) (hf : f ∈ C_cb(α, γ))
    (g : α → γ) : HasCompactSupport ((g * f : α → γ)) := HasCompactSupport.mul_left
  (mem_compactlySupported.mp hf)

/- A compactly supported continuous function is automatically bounded. This constructor gives
an object of `α →ᵇ γ` from `g : α → γ` and these assumptions. -/
def ofCompactSupport (g : α → γ) (hg₁ : Continuous g) (hg₂ : HasCompactSupport g) : α →ᵇ γ where
  toFun := g
  continuous_toFun := hg₁
  map_bounded' := by
    by_cases hs : (tsupport g).Nonempty
    · obtain ⟨z, _, hmax⟩ := hg₂.exists_isMaxOn hs <| hg₁.norm.continuousOn
      have : ∀ (x : α), ‖g x‖ ≤ ‖g z‖ := by
        intro x
        by_cases hx : x ∈ tsupport g
        · exact isMaxOn_iff.mp hmax x hx
        · rw [image_eq_zero_of_nmem_tsupport hx]
          simp only [norm_zero, norm_nonneg]
      use 2 * ‖g z‖
      intro x y
      rw [dist_eq_norm]
      apply le_trans (norm_sub_le _ _)
      calc ‖g x‖ + ‖g y‖ ≤ ‖g z‖ + ‖g y‖ := by exact add_le_add_right (this x) ‖g y‖
      _ ≤ ‖g z‖ + ‖g z‖ := by exact (add_le_add_iff_left ‖g z‖).mpr (this y)
      _ = 2 * ‖g z‖ := by exact Eq.symm (two_mul ‖g z‖)
    · push_neg at hs
      use 0
      intro x y
      rw [dist_eq_norm]
      simp only [norm_le_zero_iff]
      rw [tsupport_eq_empty_iff.mp hs]
      simp only [Pi.zero_apply, sub_self]

lemma ofCompactSupport_mem (g : α → γ) (hg₁ : Continuous g) (hg₂ : HasCompactSupport g) :
    ofCompactSupport g hg₁ hg₂ ∈ C_cb(α, γ) := mem_compactlySupported.mpr hg₂

instance : SMul C(α, γ) C_cb(α, γ) where
  smul := fun (g : C(α, γ)) => (fun (f : C_cb(α, γ)) =>
    ⟨ofCompactSupport (g * (f : α →ᵇ γ) : α → γ) (Continuous.mul g.2 f.1.1.2)
    (hasCompactSupport_mul_of_continuous_compactlySupported f.1 f.2 g), by
      apply mem_compactlySupported.mpr
      rw [ofCompactSupport]
      apply hasCompactSupport_mul_of_continuous_compactlySupported
      simp only [SetLike.coe_mem]
    ⟩)

end CompactlySupported
