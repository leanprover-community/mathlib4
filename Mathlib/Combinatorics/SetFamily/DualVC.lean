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
  have hSsub : S ⊆ 𝒜 := subset_of_dualFamily_shatters hS
  -- Embed `(Fin (d + 1) → Bool)` into `↥S` as a `Function.Embedding` via
  -- cardinality: `(Fin (d + 1) → Bool) ≃ Fin (2 ^ (d + 1)) ↪ Fin #S ≃ ↥S`.
  have hcardeq : Fintype.card (Fin (d + 1) → Bool) = Fintype.card (Fin (2 ^ (d + 1))) := by
    rw [Fintype.card_pi_const, Fintype.card_bool, Fintype.card_fin]
  let cube : (Fin (d + 1) → Bool) ↪ ↥S :=
    ((Fintype.equivOfCardEq hcardeq).toEmbedding.trans (Fin.castLEEmb hcard)).trans
      S.equivFin.symm.toEmbedding
  -- For each coordinate `k`, the codeword-bit slice of `S`.
  let T_k (k : Fin (d + 1)) : Finset (Finset α) :=
    S.filter fun A ↦ ∃ b : Fin (d + 1) → Bool, (cube b).val = A ∧ b k = true
  -- A codeword `(cube b).val` lies in `T_k k` exactly when `b k = true`.
  have mem_Tk_cube_iff (b : Fin (d + 1) → Bool) (k : Fin (d + 1)) :
      (cube b).val ∈ T_k k ↔ b k = true := by
    refine ⟨fun hb ↦ ?_, fun hk ↦ mem_filter.mpr ⟨(cube b).property, b, rfl, hk⟩⟩
    obtain ⟨_, b', hb'eq, hb'k⟩ := mem_filter.mp hb
    rwa [cube.injective (Subtype.ext hb'eq)] at hb'k
  -- Extract distinguishing ground-set elements `x k ∈ X` from shattering
  -- of the slice `T_k k`.
  have hT_k_sub (k) : T_k k ⊆ S := filter_subset _ _
  have hcols (k : Fin (d + 1)) :
      ∃ x : α, x ∈ X ∧ ∀ A ∈ S, x ∈ A ↔ A ∈ T_k k := by
    obtain ⟨u, hu, huT⟩ := hS (hT_k_sub k)
    obtain ⟨x, hxX, rfl⟩ := mem_dualFamily.mp hu
    refine ⟨x, hxX, fun A hA ↦ ?_⟩
    rw [← huT]; simp [mem_inter, mem_filter, hA, hSsub hA]
  choose x hxX hx using hcols
  -- The bit-value witness collapses to a one-line composition of equivalences:
  -- `x k ∈ A ↔ A ∈ T_k k` (from `hx`) followed by `A ∈ T_k k ↔ b k = true`
  -- (from `mem_Tk_cube_iff`), specialised to `A := (cube b).val`.
  have hx_cube (b : Fin (d + 1) → Bool) (k : Fin (d + 1)) :
      x k ∈ (cube b).val ↔ b k = true :=
    (hx k (cube b).val (cube b).property).trans (mem_Tk_cube_iff b k)
  -- `x` is injective on `Fin (d + 1)` via the singleton bitstring `b i := (i = j)`.
  have hx_inj : Function.Injective x := fun j k hjk ↦ by
    by_contra hne
    have h1 : x j ∈ (cube fun i ↦ decide (i = j)).val :=
      (hx_cube _ j).mpr (by simp)
    have h2 : x k ∉ (cube fun i ↦ decide (i = j)).val := fun hxk ↦
      hne (of_decide_eq_true ((hx_cube _ k).mp hxk)).symm
    exact h2 (hjk ▸ h1)
  -- Assemble `T := univ.map ⟨x, hx_inj⟩`. The three bullets discharge
  -- `T ⊆ X` (each `x k ∈ X`), `#T = d + 1` (by `card_map`), and
  -- `𝒜.Shatters T` (decode each `t ⊆ T` as a Boolean codeword `g k := x k ∈ t`
  -- and apply `hx_cube`).
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
  have hge : 2 ^ (d + 1) ≤ (𝒜.dualFamily X).vcDim := by grind
  have hpos : 0 < 2 ^ (d + 1) := Nat.two_pow_pos (d + 1)
  obtain ⟨S, hS_mem, hS_card⟩ :=
    (Finset.le_sup_iff hpos).mp (hge : 2 ^ (d + 1) ≤ _)
  obtain ⟨T, _, hT_card, hT_shat⟩ :=
    exists_shatters_of_dualFamily_shatters 𝒜 X (mem_shatterer.mp hS_mem) hS_card
  have : d + 1 ≤ 𝒜.vcDim := hT_card ▸ hT_shat.card_le_vcDim
  lia

end Finset
