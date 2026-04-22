/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
module

public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin

/-!
# Assouad's dual VC bound

Given a family of sets `𝒜 : Finset (Finset α)` and a ground set `X : Finset α`,
the *dual family* of `𝒜` relative to `X` assigns to each `x ∈ X` the subfamily
`{A ∈ 𝒜 | x ∈ A}` of elements of `𝒜` containing `x`. This file establishes
Assouad's 1983 dual VC bound: if `𝒜.vcDim ≤ d`, then
`(𝒜.dualFamily X).vcDim ≤ 2 ^ (d + 1) - 1`.

The proof is Assouad's original bitstring-coding argument. The `2 ^ (d + 1) - 1`
bound is tight for small `d` (e.g. halfspaces in `ℝ` realise the `d = 1` case).

## Main definitions

* `Finset.dualFamily`: the dual family of a set family relative to a ground
  set.
* `Finset.mem_dualFamily`: membership characterisation.
* `Finset.exists_shatters_of_dualFamily_shatters`: the bitstring-coding lemma.
  A subfamily of size `2 ^ (d + 1)` shattered by the dual family yields a
  `(d + 1)`-element subset of the ground set shattered by the original family.
* `Finset.vcDim_dualFamily_le`: Assouad's VC bound for the dual family.

## References

* [P. Assouad, *Densité et dimension*, Ann. Inst. Fourier **33** (3) (1983),
  Theorem 2.13][assouad1983]
* [J. Matoušek, *Lectures on Discrete Geometry*, Graduate Texts in
  Mathematics **212**, Springer, 2002, §10.3 Lemma 10.3.3][matousek2002]

## Tags

VC dimension, dual VC dimension, shattering, Assouad
-/

@[expose] public section

namespace Finset

variable {α : Type*} [DecidableEq α] {𝒜 : Finset (Finset α)} {X : Finset α}
  {𝒞 : Finset (Finset α)}

/-- The **dual family** of `𝒜 : Finset (Finset α)` relative to a ground set
`X : Finset α`: for each `x ∈ X`, the subfamily `{A ∈ 𝒜 | x ∈ A}`.

Viewing `𝒜` as rows of a binary incidence matrix indexed by `X × 𝒜`, the
dual family is the collection of its columns. -/
def dualFamily (𝒜 : Finset (Finset α)) (X : Finset α) :
    Finset (Finset (Finset α)) :=
  X.image fun x ↦ 𝒜.filter fun A ↦ x ∈ A

@[simp]
lemma mem_dualFamily :
    𝒞 ∈ 𝒜.dualFamily X ↔ ∃ x ∈ X, 𝒜.filter (fun A ↦ x ∈ A) = 𝒞 := by
  simp only [dualFamily, mem_image]

/-- **Bitstring coding (Assouad 1983, Theorem 2.13).** If `𝒜.dualFamily X`
shatters a subfamily `S` of size at least `2 ^ (d + 1)`, then `𝒜` shatters
some `(d + 1)`-element subset of `X`.

This is the combinatorial core of the dual VC bound: embed the `2 ^ (d + 1)`
bit-patterns of length `d + 1` into `S`; for each coordinate, shattering
provides a ground-set element distinguishing the patterns with that bit set;
these `d + 1` elements are then shattered by `𝒜`. -/
theorem exists_shatters_of_dualFamily_shatters
    (𝒜 : Finset (Finset α)) (X : Finset α)
    {S : Finset (Finset α)} (hS : (𝒜.dualFamily X).Shatters S)
    {d : ℕ} (hcard : 2 ^ (d + 1) ≤ S.card) :
    ∃ T : Finset α, T ⊆ X ∧ T.card = d + 1 ∧ 𝒜.Shatters T := by
  classical
  -- `S ⊆ 𝒜`: shatter `S` with `t = S`, extract `u ∈ 𝒜.dualFamily X` with
  -- `S ⊆ u ⊆ 𝒜`.
  have hSsub : S ⊆ 𝒜 := by
    obtain ⟨u, hu, huS⟩ := hS (Finset.Subset.refl S)
    obtain ⟨x, _, rfl⟩ := mem_dualFamily.mp hu
    have hS_sub_filter : S ⊆ 𝒜.filter (fun A ↦ x ∈ A) := by
      rw [← huS]; exact Finset.inter_subset_right
    exact fun A hA ↦ (mem_filter.mp (hS_sub_filter hA)).1
  -- Embed `(Fin (d + 1) → Bool)` injectively into `S` via cardinality.
  have hcardeq : Fintype.card (Fin (d + 1) → Bool) = Fintype.card (Fin (2 ^ (d + 1))) := by
    rw [Fintype.card_pi_const, Fintype.card_bool, Fintype.card_fin]
  let equivBool : (Fin (d + 1) → Bool) ≃ Fin (2 ^ (d + 1)) :=
    Fintype.equivOfCardEq hcardeq
  let embed : (Fin (d + 1) → Bool) → ↥S :=
    S.equivFin.symm ∘ Fin.castLEEmb hcard ∘ equivBool
  have hembed_inj : Function.Injective embed :=
    S.equivFin.symm.injective.comp ((Fin.castLEEmb hcard).injective.comp
      equivBool.injective)
  -- For each coordinate `k`, `T_k := {A ∈ S | (embed⁻¹ A) k = true}`.
  let T_k (k : Fin (d + 1)) : Finset (Finset α) :=
    S.filter fun A ↦ ∃ b : Fin (d + 1) → Bool, (embed b).val = A ∧ b k = true
  have hT_k_sub (k) : T_k k ⊆ S := Finset.filter_subset _ _
  -- Extract distinguishing ground-set elements `x k ∈ X`.
  have hcols (k : Fin (d + 1)) :
      ∃ x : α, x ∈ X ∧ ∀ A ∈ S, x ∈ A ↔ A ∈ T_k k := by
    obtain ⟨u, hu, huT⟩ := hS (hT_k_sub k)
    obtain ⟨x, hxX, rfl⟩ := mem_dualFamily.mp hu
    refine ⟨x, hxX, fun A hA ↦ ?_⟩
    have hAu : A ∈ 𝒜.filter (fun B ↦ x ∈ B) ↔ x ∈ A := by
      rw [mem_filter]
      exact ⟨And.right, fun h ↦ ⟨hSsub hA, h⟩⟩
    refine ⟨fun hxA ↦ ?_, fun hAT ↦ ?_⟩
    · have hA' : A ∈ S ∩ 𝒜.filter (fun B ↦ x ∈ B) :=
        mem_inter.mpr ⟨hA, hAu.mpr hxA⟩
      rw [huT] at hA'; exact hA'
    · have hA' : A ∈ S ∩ 𝒜.filter (fun B ↦ x ∈ B) := by rw [huT]; exact hAT
      exact hAu.mp (mem_inter.mp hA').2
  choose x hxX hx using hcols
  -- Bit-value witness: `x k ∈ (embed b).val ↔ b k = true`.
  have hx_embed (b : Fin (d + 1) → Bool) (k : Fin (d + 1)) :
      x k ∈ (embed b).val ↔ b k = true := by
    have hmem : (embed b).val ∈ S := (embed b).property
    by_cases hbk : b k = true
    · refine ⟨fun _ ↦ hbk, fun _ ↦ (hx k (embed b).val hmem).mpr ?_⟩
      exact mem_filter.mpr ⟨hmem, b, rfl, hbk⟩
    · simp only [Bool.not_eq_true] at hbk
      refine ⟨fun hxA ↦ ?_,
        fun h ↦ by rw [hbk] at h; exact absurd h (by decide)⟩
      obtain ⟨_, b', hb'eq, hb'k⟩ :=
        mem_filter.mp ((hx k (embed b).val hmem).mp hxA)
      have : b' = b := hembed_inj (Subtype.ext hb'eq)
      rw [this, hbk] at hb'k
      exact absurd hb'k (by decide)
  -- `x` is injective on `Fin (d + 1)`.
  have hx_inj : Function.Injective x := by
    intro j k hjk
    by_contra hne
    let b₀ : Fin (d + 1) → Bool := fun i ↦ i == j
    have h1 : x j ∈ (embed b₀).val :=
      (hx_embed b₀ j).mpr (by simp [b₀])
    have h2 : x k ∉ (embed b₀).val := fun hxk ↦ by
      have : b₀ k = true := (hx_embed b₀ k).mp hxk
      simp only [b₀] at this
      exact hne (beq_iff_eq.mp this).symm
    exact h2 (hjk ▸ h1)
  -- Assemble `T := image x`. The three bullets discharge `T ⊆ X`,
  -- `#T = d + 1` (by injectivity of `x`), and `𝒜.Shatters T` (decode
  -- each `t ⊆ T` as a bit-pattern, then apply `hx_embed`).
  refine ⟨Finset.univ.image x, ?_, ?_, ?_⟩
  · rintro y hy
    obtain ⟨k, _, rfl⟩ := mem_image.mp hy
    exact hxX k
  · rw [card_image_of_injective _ hx_inj, card_univ, Fintype.card_fin]
  · intro t ht
    let g : Fin (d + 1) → Bool := fun k ↦ decide (x k ∈ t)
    refine ⟨(embed g).val, hSsub (embed g).property, ?_⟩
    ext y
    simp only [mem_inter]
    refine ⟨fun ⟨hyT, hyE⟩ ↦ ?_, fun hyt ↦ ?_⟩
    · obtain ⟨k, _, rfl⟩ := mem_image.mp hyT
      exact of_decide_eq_true ((hx_embed g k).mp hyE)
    · have hyT : y ∈ Finset.univ.image x := ht hyt
      obtain ⟨k, _, rfl⟩ := mem_image.mp hyT
      exact ⟨hyT, (hx_embed g k).mpr (decide_eq_true hyt)⟩

/-- **Assouad's dual VC bound.** If `𝒜 : Finset (Finset α)` has VC dimension
at most `d`, then for any ground set `X : Finset α` the dual family has VC
dimension at most `2 ^ (d + 1) - 1`.

This is the Finset-level form of the standard statement
`vcDim(𝒞*) ≤ 2 ^ (vcDim(𝒞) + 1) - 1` (Assouad 1983, Theorem 2.13;
Matoušek, *Lectures on Discrete Geometry*, §10.3 Lemma 10.3.3). -/
theorem vcDim_dualFamily_le (𝒜 : Finset (Finset α)) (X : Finset α)
    {d : ℕ} (hvc : 𝒜.vcDim ≤ d) :
    (𝒜.dualFamily X).vcDim ≤ 2 ^ (d + 1) - 1 := by
  by_contra hlt
  push Not at hlt
  have hge : 2 ^ (d + 1) ≤ (𝒜.dualFamily X).vcDim := by omega
  have hpos : 0 < 2 ^ (d + 1) := Nat.two_pow_pos (d + 1)
  obtain ⟨S, hS_mem, hS_card⟩ :=
    (Finset.le_sup_iff hpos).mp (hge : 2 ^ (d + 1) ≤ _)
  obtain ⟨T, _, hT_card, hT_shat⟩ :=
    exists_shatters_of_dualFamily_shatters 𝒜 X (mem_shatterer.mp hS_mem) hS_card
  have : d + 1 ≤ 𝒜.vcDim := hT_card ▸ hT_shat.card_le_vcDim
  lia

end Finset
