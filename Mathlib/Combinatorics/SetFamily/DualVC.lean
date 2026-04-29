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

The proof is Assouad's original bitstring-coding argument. This bound works well
for small `d`.


## Main definitions

* `Finset.dualFamily`: the dual family of a set family relative to a ground
  set.
* `Finset.mem_dualFamily`: membership characterisation.
* `Finset.exists_shatters_of_dualFamily_shatters`: the bitstring-coding lemma.
  A subfamily of size `2 ^ n` shattered by the dual family yields an
  `n`-element subset of the ground set shattered by the original family.
* `Finset.vcDim_dualFamily_le`: Assouad's VC bound for the dual family.

## References

* [P. Assouad, *Densité et dimension*, Ann. Inst. Fourier **33** (3) (1983),
  Theorem 2.13][assouad1983]
* [J. Matoušek, *Lectures on Discrete Geometry*, Graduate Texts in
  Mathematics **212**, Springer, 2002, §10.3 Lemma 10.3.3][matousek2002]

## Tags

VC dimension, dual VC dimension, shattering, Assouad
-/

public section

namespace Finset

variable {α : Type*} [DecidableEq α] {𝒜 : Finset (Finset α)} {X : Finset α}
  {𝒞 : Finset (Finset α)}

/-- The **dual family** of `𝒜 : Finset (Finset α)` relative to a ground set
`X : Finset α`: for each `x ∈ X`, the subfamily `{A ∈ 𝒜 | x ∈ A}`.

Viewing `𝒜` as rows of a binary incidence matrix indexed by `X × 𝒜`, the
dual family is the collection of its columns. -/
@[expose]
def dualFamily (𝒜 : Finset (Finset α)) (X : Finset α) :
    Finset (Finset (Finset α)) :=
  X.image fun x ↦ 𝒜.filter fun A ↦ x ∈ A

@[simp]
lemma mem_dualFamily :
    𝒞 ∈ 𝒜.dualFamily X ↔ ∃ x ∈ X, 𝒜.filter (fun A ↦ x ∈ A) = 𝒞 := by
  simp only [dualFamily, mem_image]

/-- A subfamily shattered by `𝒜.dualFamily X` is itself a subfamily of `𝒜`:
take `t = S` in the shattering hypothesis, then any superset `u ∈ 𝒜.dualFamily X`
of `S` is a filter on `𝒜`. -/
private lemma subset_of_dualFamily_shatters {S : Finset (Finset α)}
    (hS : (𝒜.dualFamily X).Shatters S) : S ⊆ 𝒜 := by
  obtain ⟨u, hu, hSu⟩ := hS.exists_superset
  obtain ⟨_, _, rfl⟩ := mem_dualFamily.mp hu
  exact hSu.trans (filter_subset _ _)

/-- Embedding `(Fin n → Bool) ↪ ↥S` when `2 ^ n ≤ #S`,
via `(Fin n → Bool) ≃ Fin (2 ^ n) ↪ Fin #S ≃ ↥S`. -/
private noncomputable def cubeEmbedding {n : ℕ} (S : Finset (Finset α))
    (hcard : 2 ^ n ≤ S.card) :
    (Fin n → Bool) ↪ ↥S :=
  ((Fintype.equivOfCardEq (by rw [Fintype.card_pi_const, Fintype.card_bool,
    Fintype.card_fin])).toEmbedding.trans (Fin.castLEEmb hcard)).trans
    S.equivFin.symm.toEmbedding

/-- The image of `{b : Fin n → Bool | b k = true}` under a cube embedding. -/
private def cubeBitSlice {n : ℕ} {S : Finset (Finset α)} (cube : (Fin n → Bool) ↪ ↥S)
    (k : Fin n) : Finset (Finset α) :=
  ((Finset.univ : Finset (Fin n → Bool)).filter fun b ↦ b k = true).image
    fun b ↦ (cube b).val

private lemma cubeBitSlice_subset {n : ℕ} {S : Finset (Finset α)}
    (cube : (Fin n → Bool) ↪ ↥S) (k : Fin n) : cubeBitSlice cube k ⊆ S := by
  intro A hA
  obtain ⟨b, _, rfl⟩ := mem_image.mp hA
  exact (cube b).property

/-- Codeword `(cube b).val` is in `cubeBitSlice cube k` iff `b k = true`. -/
private lemma mem_cubeBitSlice_iff {n : ℕ} {S : Finset (Finset α)}
    (cube : (Fin n → Bool) ↪ ↥S) (b : Fin n → Bool) (k : Fin n) :
    (cube b).val ∈ cubeBitSlice cube k ↔ b k = true := by
  simp only [cubeBitSlice, mem_image, mem_filter, mem_univ, true_and]
  refine ⟨fun ⟨b', hb'k, hb'eq⟩ ↦ ?_, fun hk ↦ ⟨b, hk, rfl⟩⟩
  rwa [cube.injective (Subtype.ext hb'eq)] at hb'k

/-- **Bitstring coding (Assouad 1983, Theorem 2.13).** If `𝒜.dualFamily X`
shatters a subfamily `S` of size at least `2 ^ n`, then `𝒜` shatters
some `n`-element subset of `X`.

This is the combinatorial side of the dual VC bound: embed the `2 ^ n`
bit-patterns of length `n` into `S`; for each coordinate, shattering
provides a ground-set element distinguishing the patterns with that bit set;
these `n` elements are then shattered by `𝒜`. -/
theorem exists_shatters_of_dualFamily_shatters
    (𝒜 : Finset (Finset α)) (X : Finset α)
    {S : Finset (Finset α)} (hS : (𝒜.dualFamily X).Shatters S)
    {n : ℕ} (hcard : 2 ^ n ≤ S.card) :
    ∃ T : Finset α, T ⊆ X ∧ T.card = n ∧ 𝒜.Shatters T := by
  classical
  have hSsub : S ⊆ 𝒜 := subset_of_dualFamily_shatters hS
  let cube := cubeEmbedding S hcard
  have hcols (k : Fin n) :
      ∃ x : α, x ∈ X ∧ ∀ A ∈ S, x ∈ A ↔ A ∈ cubeBitSlice cube k := by
    obtain ⟨u, hu, huT⟩ := hS (cubeBitSlice_subset cube k)
    obtain ⟨x, hxX, rfl⟩ := mem_dualFamily.mp hu
    refine ⟨x, hxX, fun A hA ↦ ?_⟩
    rw [← huT]; simp [mem_inter, mem_filter, hA, hSsub hA]
  choose x hxX hx using hcols
  have hx_cube (b : Fin n → Bool) (k : Fin n) :
      x k ∈ (cube b).val ↔ b k = true :=
    (hx k (cube b).val (cube b).property).trans (mem_cubeBitSlice_iff cube b k)
  -- `x` is injective via the singleton bitstring `b i := (i = j)`.
  have hx_inj : Function.Injective x := fun j k hjk ↦ by
    by_contra hne
    have h1 : x j ∈ (cube fun i ↦ decide (i = j)).val :=
      (hx_cube _ j).mpr (by simp)
    have h2 : x k ∉ (cube fun i ↦ decide (i = j)).val := fun hxk ↦
      hne (of_decide_eq_true ((hx_cube _ k).mp hxk)).symm
    exact h2 (hjk ▸ h1)
  refine ⟨univ.map ⟨x, hx_inj⟩, ?_, by simp, fun t ht ↦ ?_⟩
  · intro y hy
    obtain ⟨k, _, rfl⟩ := mem_map.mp hy
    exact hxX k
  · refine ⟨(cube fun k ↦ decide (x k ∈ t)).val, hSsub (cube _).property, ?_⟩
    ext y
    refine mem_inter.trans ⟨fun ⟨hyT, hyA⟩ ↦ ?_, fun hyt ↦ ?_⟩
    · obtain ⟨k, _, rfl⟩ := mem_map.mp hyT
      exact of_decide_eq_true ((hx_cube _ k).mp hyA)
    · obtain ⟨k, _, rfl⟩ := mem_map.mp (ht hyt)
      exact ⟨ht hyt, (hx_cube _ k).mpr (decide_eq_true hyt)⟩

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
  have hge : 2 ^ (d + 1) ≤ (𝒜.dualFamily X).vcDim := by lia
  have hpos : 0 < 2 ^ (d + 1) := Nat.two_pow_pos (d + 1)
  obtain ⟨S, hS_mem, hS_card⟩ :=
    (Finset.le_sup_iff hpos).mp (hge : 2 ^ (d + 1) ≤ _)
  obtain ⟨T, _, hT_card, hT_shat⟩ :=
    exists_shatters_of_dualFamily_shatters 𝒜 X (mem_shatterer.mp hS_mem) hS_card
  have : d + 1 ≤ 𝒜.vcDim := hT_card ▸ hT_shat.card_le_vcDim
  lia

end Finset
