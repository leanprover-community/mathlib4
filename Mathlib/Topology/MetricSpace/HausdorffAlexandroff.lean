/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Data.Real.OfDigits
import Mathlib.Topology.Compactness.HilbertCubeEmbedding
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.UnitInterval

/-!
# Hausdorff–Alexandroff Theorem

In this file, we prove the Hausdorff–Alexandroff theorem, which states that every compact
metric space is a continuous image of the Cantor set.

## Proof Outline

First, note that the Cantor set is homeomorphic to `ℕ → Bool`, as shown in
`Mathlib.Topology.Instances.CantorSet`. Therefore, in this file, we work only with the space
`ℕ → Bool` and refer to it as the "Cantor space".

The proof consists of three steps. Let `X` be a compact metric space.

1. Every compact metric space is homeomorphic to a closed subset of the Hilbert cube.
   This is already proved in `Mathlib.Topology.Compactness.HilbertCubeEmbedding`. Using this result,
   we may assume that `X` is a closed subset of the Hilbert cube.
2. We construct a continuous surjection `cantorToHilbert` from the Cantor space to the Hilbert
   cube.
3. Taking the preimage of `X` under this surjection, it remains to prove that any closed
   subset of the Cantor space is the continuous image of the Cantor space.
-/

/-- Convert a sequence of binary digits to a real number from `unitInterval`. -/
noncomputable def fromBinary (b : ℕ → Bool) : unitInterval :=
  let φ : (ℕ → Bool) ≃ₜ (ℕ → Fin 2) := Homeomorph.piCongrRight
    (fun _ ↦ finTwoEquiv.toHomeomorphOfDiscrete.symm)
  let x : ℝ := ofDigits (φ b)
  have hx : x ∈ Set.Icc 0 1 := by
    simp [x]
    constructor
    · exact ofDigits_nonneg
    · exact ofDigits_le_one
  ⟨x, hx⟩

theorem fromBinary_continuous : Continuous fromBinary := by
  unfold fromBinary
  apply Continuous.subtype_mk
  have : (fun x ↦ ofDigits
      ((Homeomorph.piCongrRight fun _ ↦ finTwoEquiv.toHomeomorphOfDiscrete.symm) x)) =
      ofDigits ∘ (Homeomorph.piCongrRight fun _ ↦ finTwoEquiv.toHomeomorphOfDiscrete.symm) := by
    ext
    simp
  rw [this, Homeomorph.comp_continuous_iff']
  exact ofDigits_continuous

theorem fromBinary_surjective : Function.Surjective fromBinary := by
  intro x
  obtain ⟨x, hx⟩ := x
  by_cases hx_one : x = 1
  · use fun _ ↦ true
    have : fromBinary (fun _ ↦ true) = ofDigits (b := 2) (fun _ ↦ 1) := by
      simp only [fromBinary, Equiv.toHomeomorphOfDiscrete,
        Equiv.toHomeomorph_symm, Fin.isValue]
      congr
    simp only [hx_one, Set.Icc.mk_one, Subtype.eq_iff, this, ofDigits, ofDigitsTerm, Fin.isValue,
      Fin.val_one, Nat.cast_one, Nat.cast_ofNat, pow_succ, mul_inv_rev, ← inv_pow, one_mul,
      Set.Icc.coe_one]
    rw [Summable.tsum_mul_left]
    · rw [tsum_geometric_inv_two]
      simp
    · convert summable_geometric_two
      eta_expand
      simp
  replace hx : x ∈ Set.Ico 0 1 := by
    simp at hx ⊢
    exact ⟨hx.left, by apply hx.right.lt_of_ne' (by symm; simpa)⟩
  use finTwoEquiv ∘ (toDigits x 2)
  simp only [fromBinary, Subtype.mk.injEq]
  conv => rhs; rw [← toDigits_ofDigits 2 x (by simp) hx]
  congr
  ext n
  simp only [Homeomorph.piCongrRight_apply, Function.comp_apply]
  congr
  simp [Equiv.toHomeomorphOfDiscrete]

/-- A continuous surjection from the Cantor space to the Hilbert cube. -/
noncomputable def cantorToHilbert (x : ℕ → Bool) : ℕ → unitInterval :=
  Pi.map (fun _ b ↦ fromBinary b) (cantorSpace_homeomorph_nat_cantorSpace x)

theorem cantorToHilbert_continuous : Continuous cantorToHilbert := by
  unfold cantorToHilbert
  apply continuous_pi
  intro i
  apply fromBinary_continuous.comp
  fun_prop

theorem cantorToHilbert_surjective : Function.Surjective cantorToHilbert := by
  unfold cantorToHilbert
  change Function.Surjective
    ((Pi.map (fun x b ↦ fromBinary b)) ∘ cantorSpace_homeomorph_nat_cantorSpace)
  apply Function.Surjective.comp
  · apply Function.Surjective.piMap
    intro _
    apply fromBinary_surjective
  · exact Homeomorph.surjective cantorSpace_homeomorph_nat_cantorSpace

attribute [local instance] PiNat.metricSpace in
theorem exists_retractionCantorSet {X : Set (ℕ → Bool)} (h_closed : IsClosed X)
    (h_nonempty : X.Nonempty) : ∃ f : (ℕ → Bool) → (ℕ → Bool), Continuous f ∧ Set.range f = X := by
  rcases PiNat.exists_lipschitz_retraction_of_isClosed h_closed h_nonempty with ⟨f, fs, frange, hf⟩
  exact ⟨f, hf.continuous, frange⟩

theorem exists_nat_bool_continuous_surjective_of_compact (X : Type*) [Nonempty X] [MetricSpace X]
    [CompactSpace X] : ∃ f : (ℕ → Bool) → X, Continuous f ∧ Function.Surjective f := by
  obtain ⟨emb, h_emb⟩ := exists_closed_embedding_to_hilbert_cube X
  let KH : Set (ℕ → unitInterval) := Set.range emb
  let KC : Set (ℕ → Bool) := cantorToHilbert ⁻¹' KH
  have hKC_closed : IsClosed KC := by
    apply IsClosed.preimage
    · exact cantorToHilbert_continuous
    · simp only [KH]
      apply Topology.IsClosedEmbedding.isClosed_range h_emb
  have hKC_nonempty : KC.Nonempty := by
    apply Set.Nonempty.preimage
    · exact Set.range_nonempty emb
    · exact cantorToHilbert_surjective
  rcases exists_retractionCantorSet hKC_closed hKC_nonempty with ⟨f, hf_continuous, hf_surjective⟩
  let f' : (ℕ → Bool) → KC := Subtype.coind f (by simp [← hf_surjective])
  have hf'_continuous : Continuous f' := Continuous.subtype_mk hf_continuous _
  have hf'_surjective : Function.Surjective f' := by
    intro ⟨y, hy⟩
    simp only [← hf_surjective, Set.mem_range] at hy
    obtain ⟨x, hx⟩ := hy
    use x
    simpa [Subtype.eq_iff]
  let g : X ≃ₜ KH := by
    apply Topology.IsEmbedding.toHomeomorph
    apply Topology.IsClosedEmbedding.toIsEmbedding h_emb
  let h : KC → KH := KH.restrictPreimage cantorToHilbert
  have hh_continuous : Continuous h := Continuous.restrictPreimage cantorToHilbert_continuous
  have hh_surjective : Function.Surjective h :=
    Set.restrictPreimage_surjective _ cantorToHilbert_surjective
  use g.symm ∘ h ∘ f'
  constructor
  · apply Continuous.comp
    · exact Homeomorph.continuous_symm g
    exact Continuous.comp hh_continuous hf'_continuous
  · apply Function.Surjective.comp
    · exact Homeomorph.surjective g.symm
    exact Function.Surjective.comp hh_surjective hf'_surjective
