/-
Copyright (c) 2026 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Inna Capdeboscq, Damiano Testa
-/

module

public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Subnormal subgroups

In this file, we define subnormal subgroups.

We also show some basic results about the interaction of subnormality and simplicity of groups.
These should cover most of the results needed in this case.

## Main Definition

`IsSubnormal H`: A subgroup `H` of a group `G` satisfies `IsSubnormal` if
* either `H = ⊤`;
* or there is a subgroup `K` of `G` containing `H` and such that `H` is normal in `K` and
  `K` satisfies `IsSubnormal`.

## Main Statements

* `eq_bot_or_top_of_isSimpleGroup`: the only subnormal subgroups of simple groups are
  `⊥`, the trivial subgroup, and `⊤`, the whole group.
* `isSubnormal_iff`: Shows that `IsSubnormal H` holds if and only if there is
  an increasing chain of subgroups, each normal in the following, starting from `H` and
  reaching `⊤` in a finite number of steps.
* `IsSubnormal.trans`: The relation of being `IsSubnormal` is transitive.

## Implementation Notes

We deviate from the common informal definition of subnormality and use an inductive predicate.
This turns out to be more convenient to work with.
We show the equivalence of the current definition with the existence of chains in
`isSubnormal_iff`.
-/

variable {G : Type*} [Group G] {H K : Subgroup G}

@[expose] public section

namespace Subgroup

/-- A subgroup `H` of a group `G` satisfies `IsSubnormal` if
* either `H = ⊤`;
* or there is a subgroup `K` of `G` containing `H` and such that `H` is normal in `K` and
  `K` satisfies `IsSubnormal`.

Equivalently, `H.IsSubnormal` means that there is a chain of subgroups
`H₀ ≤ H₁ ≤ ... ≤ Hₙ` such that
* `H = H₀`,
* `G = Hₙ`,
* for each `i ∈ {0, ..., n - 1}`, `Hᵢ` is a normal subgroup of `Hᵢ₊₁`.

See `isSubnormal_iff` for this characterisation.
-/
inductive IsSubnormal : Subgroup G → Prop where
  /-- The whole subgroup `G` is subnormal in itself. -/
  | top : IsSubnormal (⊤ : Subgroup G)
  /-- A subgroup `H` is subnormal if there is a subnormal subgroup `K` containing `H` that is
  subnormal itself and such that `H` is normal in `K`. -/
  | step : ∀ H K, (h_le : H ≤ K) → (hSubn : IsSubnormal K) → (hN : (H.subgroupOf K).Normal) →
    IsSubnormal H

/-- An additive subgroup `H` of an additive group `G` satisfies `IsSubnormal` if
* either `H = ⊤`;
* or there is an additive subgroup `K` of `G` containing `H` and such that `H` is normal in `K` and
  `K` satisfies `IsSubnormal`.

Equivalently, `H.IsSubnormal` means that there is a chain of additive subgroups
`H₀ ≤ H₁ ≤ ... ≤ Hₙ` such that
* `H = H₀`,
* `G = Hₙ`,
* for each `i ∈ {0, ..., n - 1}`, `Hᵢ` is a normal additive subgroup of `Hᵢ₊₁`.

See `isSubnormal_iff` for this characterisation.
-/
inductive _root_.AddSubgroup.IsSubnormal {G : Type*} [AddGroup G] : AddSubgroup G → Prop where
  /-- The whole additive subgroup `G` is subnormal in itself. -/
  | top : IsSubnormal (⊤ : AddSubgroup G)
  /-- An additive subgroup `H` is subnormal if there is a subnormal additive subgroup `K`
  containing `H` that is subnormal itself and such that `H` is normal in `K`. -/
  | step : ∀ H K, (h_le : H ≤ K) → (hSubn : IsSubnormal K) → (hN : (H.addSubgroupOf K).Normal) →
    IsSubnormal H

attribute [simp] Subgroup.IsSubnormal.top

/-- A normal subgroup is subnormal. -/
@[to_additive /-- A normal additive subgroup is subnormal. -/]
lemma Normal.isSubnormal (hn : H.Normal) : IsSubnormal H :=
  IsSubnormal.step _ ⊤ le_top IsSubnormal.top normal_subgroupOf

namespace IsSubnormal

/-- The trivial subgroup is subnormal. -/
@[to_additive (attr := simp) /-- The trivial additive subgroup is subnormal. -/]
lemma bot : IsSubnormal (⊥ : Subgroup G) := normal_bot.isSubnormal

/-- A subnormal subgroup of a simple group is normal. -/
@[to_additive /-- A subnormal additive subgroup of a simple additive group is normal. -/]
lemma normal_of_isSimpleGroup (hG : IsSimpleGroup G) (hN : H.IsSubnormal) :
    H.Normal := by
  induction hN with
  | top => simp
  | step H K h_le hSubn hN Knorm =>
    obtain rfl | rfl := Knorm.eq_bot_or_eq_top
    · grind
    · grind [!normal_subgroupOf_iff_le_normalizer_inf, inf_of_le_left, normalizer_eq_top_iff]

/-- A subnormal subgroup of a simple group is either trivial or the whole group. -/
@[to_additive /-- A subnormal additive subgroup of a simple additive group is either trivial or the
whole group. -/]
lemma eq_bot_or_top_of_isSimpleGroup (hG : IsSimpleGroup G) (hN : IsSubnormal H) :
    H = ⊥ ∨ H = ⊤ :=
  (hN.normal_of_isSimpleGroup hG).eq_bot_or_eq_top

@[to_additive]
lemma iff_eq_top_or_exists :
    IsSubnormal H ↔ H = ⊤ ∨ ∃ K, H < K ∧ IsSubnormal K ∧ (H.subgroupOf K).Normal where
  mp h := by
    induction h with
    | top => simp
    | step H K HK hS hN ih =>
      obtain rfl | ⟨K', HK', hS', hN'⟩ := ih
      · obtain rfl | hH := eq_or_ne H ⊤
        · simp
        · exact Or.inr ⟨⊤, by simp [hH.lt_top , *]⟩
      right
      obtain rfl | hH := eq_or_ne H K
      · use K'
      · exact ⟨K, by simpa [*] using HK.lt_of_ne hH⟩
  mpr h := by
    obtain rfl | ⟨K, HK, Ksn, h⟩ := h
    · exact top
    · exact step _ _ HK.le Ksn h

/-- A proper subnormal subgroup is contained in a proper normal subgroup. -/
@[to_additive /-- A proper subnormal additive subgroup is contained in a proper normal additive
subgroup. -/]
lemma exists_normal_and_le_and_lt_top_of_ne (hN : H.IsSubnormal) (ne_top : H ≠ ⊤) :
    ∃ K, K.Normal ∧ H ≤ K ∧ K < ⊤ := by
  induction hN with
  | top => contradiction
  | step H K h_le hSubn hN ih =>
    obtain rfl | K_ne := eq_or_ne K ⊤
    · rw [normal_subgroupOf_iff_le_normalizer h_le, top_le_iff, normalizer_eq_top_iff] at hN
      exact ⟨H, hN, le_rfl, ne_top.lt_top⟩
    · grind

/--
A subnormal subgroup is either the whole group or it is contained in a proper normal subgroup.
-/
@[to_additive /-- A subnormal additive subgroup is either the whole group or it is contained in a
proper normal additive subgroup. -/]
lemma lt_normal (hN : H.IsSubnormal) : H = ⊤ ∨ ∃ K, K.Normal ∧ H ≤ K ∧ K < ⊤ := by
  obtain rfl | H_ne := eq_or_ne H ⊤
  · simp
  · grind only [iff_eq_top_or_exists, exists_normal_and_le_and_lt_top_of_ne]

/--
A characterisation of satisfying `IsSubnormal` in terms of chains of subgroups, each normal in
the following one.

The sequence stabilises once it reaches `⊤`, which is guaranteed at the asserted `n`.
-/
-- TODO: consider using `MonotoneOn f {i | i ≤ n}` or some variant.
@[to_additive /-- A characterisation of satisfying `IsSubnormal` in terms of chains of additive
subgroups, each normal in the following one.

The sequence stabilises once it reaches `⊤`, which is guaranteed at the asserted `n`. -/]
lemma isSubnormal_iff : H.IsSubnormal ↔
    ∃ n, ∃ f : ℕ → Subgroup G,
    (Monotone f) ∧ (∀ i, ((f i).subgroupOf (f (i + 1))).Normal) ∧
      f 0 = H ∧ f n = ⊤ where
  mp h := by
    induction h with
    | top =>
      use 0, fun _ ↦ ⊤, ?_, (by simp)
      exact monotone_nat_of_le_succ fun _ ↦ le_top
    | step H K h_le hSubn hN ih =>
      obtain ⟨n, f, hf, f0, fn⟩ := ih
      use n + 1, fun | 0 => H | n + 1 => f n, ?_, ?_
      · grind
      · refine monotone_nat_of_le_succ ?_
        grind only [monotone_iff_forall_lt]
      · grind
  mpr := by
    rintro ⟨n, hyps⟩
    revert H
    induction n with
    | zero => simp_all
    | succ n ih =>
      rintro J ⟨F, hF, H_le, rfl, ih1⟩
      refine step _ _ (hF <| Nat.le_add_right 0 1) ?_ (H_le _)
      refine ih ⟨fun n ↦ F (n + 1), ?_⟩
      grind only [Monotone, monotone_iff_forall_lt]

alias ⟨exists_chain, _⟩ := isSubnormal_iff

/--
Subnormality is transitive.

This version involves an explicit `subtype`; the version `IsSubnormal.trans` does not.
-/
@[to_additive /-- Subnormality is transitive.

This version involves an explicit `subtype`; the version `IsSubnormal.trans` does not. -/]
protected
lemma trans' {H : Subgroup K} (Hsn : IsSubnormal H) (Ksn : IsSubnormal K) :
    IsSubnormal (H.map K.subtype) := by
  induction Hsn with
  | top =>
    rwa [← MonoidHom.range_eq_map, range_subtype]
  | step A B h_le hSubn hN ih =>
    refine step (A.map K.subtype) (B.map K.subtype) (map_mono h_le) ih ?_
    rw [normal_subgroupOf_iff_le_normalizer h_le] at hN
    rw [normal_subgroupOf_iff_le_normalizer (map_mono h_le)]
    exact le_trans (map_mono hN) (le_normalizer_map _)

/--
If `H` is a subnormal subgroup of `K` and `K` is a subnormal subgroup of `G`,
then `H` is a subnormal subgroup of `G`.
-/
@[to_additive /-- If `H` is a subnormal additive subgroup of `K` and `K` is a subnormal
additive subgroup of `G`, then `H` is a subnormal additive subgroup of `G`. -/]
protected
lemma trans (HK : H ≤ K) (Hsn : IsSubnormal (H.subgroupOf K)) (Ksn : IsSubnormal K) :
    IsSubnormal H := by
  have key := Hsn.trans' Ksn
  rwa [map_subgroupOf_eq_of_le HK] at key

end Subgroup.IsSubnormal
