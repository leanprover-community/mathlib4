/-
Copyright (c) 2026 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Inna Capdeboscq, Damiano Testa
-/

module

public import Mathlib.GroupTheory.Subgroup.Simple

/-! # Subnormal subgroups

In this file, we define subnormal subgroups in `IsSubnormal`.
We also prove a few basic facts.

* The definition is equivalent to the existence of a finite chain of inclusions of
  subgroups, each normal in the successor, starting at the subgroup itself and
  ending with the whole group (`IsSubnormal_iff`).
* The relation of being `IsSubnormal` is transitive (`trans`).
* The image of a subnormal subgroup under a surjective group homomorphism is subnormal (`map`).
* The quotient of a subnormal subgroup is a subnormal subgroup (`quotient` --
  this is a convenient specialisation of `map`).
* The inverse image of a subnormal group is subnormal (`comap`, as well as the specialization
  `subgroupOf` for the case in which the `comap` is `subgroupOf`).
-/

variable {G : Type*} [Group G] {H K : Subgroup G}

@[expose] public section

namespace Subgroup

-- Adding this lemma to the `simp` set means that `simp` can prove that characteristic subgroups
-- are normal.  In particular, the two trivial subgroups `⊥` and `⊤` are normal.
attribute [local simp] normal_of_characteristic

/-- A subgroup `H` of a group satisfies `IsSubnormal` if
* either `H = ⊤`;
* or there is a subgroup `K` of `G` containing `H` and such that `H` is normal in `K` and
  `K` satisfies `IsSubnormal`.
Equivalently, `H.IsSubnormal` means that there is a finite chain of subgroups
`H₀ ≤ H₁ ≤ ... ≤ Hₙ` such that
* `H = H₀`,
* `G = Hₙ`,
* for each `i ∈ {0, ..., n - 1}`, `Hᵢ` is a normal subgroup of `Hₙ₋₁`.
See `IsSubnormal_iff` for this characterisation.
-/
inductive IsSubnormal : Subgroup G → Prop where
  /-- The whole subgroup `G` is subnormal in itself. -/
  | top : IsSubnormal (⊤ : Subgroup G)
  /-- A subgroup `H` is subnormal if there is a subnormal subgroup `K` containing `H` that is
  subnormal itself and such that `H` is normal in `K`. -/
  | step : ∀ H K, (h_le : H ≤ K) → (hSubn : IsSubnormal K) → (hN : (H.subgroupOf K).Normal) →
    IsSubnormal H

attribute [simp] Subgroup.IsSubnormal.top

/-- A normal subgroup is subnormal. -/
lemma Normal.isSubnormal (hn : H.Normal) : IsSubnormal H :=
  IsSubnormal.step _ ⊤ le_top IsSubnormal.top normal_subgroupOf

namespace IsSubnormal

/-- The trivial subgroup is subnormal. -/
@[simp] lemma bot : IsSubnormal (⊥ : Subgroup G) := (normal_of_characteristic ⊥).isSubnormal

/-- A subnormal subgroup of a simple group is normal. -/
lemma normal_of_isSimpleGroup (hG : IsSimpleGroup G) (hN : H.IsSubnormal) :
    H.Normal := by
  induction hN with
  | top => simp
  | step H K h_le hSubn hN ih =>
    obtain rfl | rfl := Normal.eq_bot_or_eq_top ih
    · grind
    · grind [!normal_subgroupOf_iff_le_normalizer_inf, inf_of_le_left, normalizer_eq_top_iff]

/-- A subnormal subgroup of a simple group is either trivial or the whole group. -/
lemma eq_bot_or_top_of_isSimpleGroup (hG : IsSimpleGroup G) (hN : IsSubnormal H) :
    H = ⊥ ∨ H = ⊤ :=
  (hN.normal_of_isSimpleGroup hG).eq_bot_or_eq_top

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
      · exact ⟨K, by simpa [*] using lt_of_le_of_ne HK hH⟩
  mpr h := by
    obtain rfl | ⟨K, HK, Ksn, h⟩ := h
    · exact top
    · exact step _ _ HK.le Ksn h

/-- A proper subnormal subgroup is contained in a proper normal subgroup. -/
lemma exists_normal_and_ne_top_of_ne (hN : H.IsSubnormal) (ne_top : H ≠ ⊤) :
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
lemma le_normal (hN : H.IsSubnormal) : H = ⊤ ∨ ∃ K, K < ⊤ ∧ K.Normal ∧ H ≤ K := by
  obtain rfl | H_ne := eq_or_ne H ⊤
  · simp
  · grind only [iff_eq_top_or_exists, exists_normal_and_ne_top_of_ne]

/--
A characterisation of satisfying `IsSubnormal` in terms of chains of subgroups, each normal in
the following one.
This version forces the chain to terminate with the `⊤` subgroup *twice*.
See `IsSubnormal_iff` for a version that does not do this.
-/
-- TODO: consider using `MonotoneOn f {i | i ≤ n}` or some variant.
lemma IsSubnormal_iff' : H.IsSubnormal ↔
    ∃ n, ∃ f : ℕ → Subgroup G,
    (∀ i ≤ n, f i ≤ f (i + 1)) ∧ (∀ i ≤ n, ((f i).subgroupOf (f (i + 1))).Normal) ∧
      f 0 = H ∧ f n = ⊤ where
  mp h := by
    induction h with
    | top =>
      use 0, fun _ ↦ ⊤
      simp
    | step H K h_le hSubn hN ih =>
      obtain ⟨n, f, hf, f0, fn⟩ := ih
      use n + 1, fun | 0 => H | n + 1 => f n
      grind
  mpr := by
    rintro ⟨n, hyps⟩
    revert H
    induction n with
    | zero => simp_all
    | succ n ih =>
      rintro J ⟨F, hF, H_le, rfl, ih1⟩
      apply step
      · exact hF _ (by simp only [Nat.le_add_left])
      · exact ih ⟨fun n ↦ F (n + 1), by grind only⟩
      · grind only

/--
A characterisation of satisfying `IsSubnormal` in terms of chains of subgroups, each normal in
the following one.
This version forces the chain to terminate with the `⊤` subgroup *once*.
Depending on the context, it may be a little harder to use than `IsSubnormal_iff'`, due to the
hypotheses involving strict inequalities.
-/
-- TODO: consider using `MonotoneOn f {i | i ≤ n}` or some variant.
lemma IsSubnormal_iff : H.IsSubnormal ↔
    ∃ n, ∃ f : ℕ → Subgroup G,
    (∀ i < n, f i ≤ f (i + 1)) ∧ (∀ i < n, ((f i).subgroupOf (f (i + 1))).Normal) ∧
      f 0 = H ∧ f n = ⊤ where
  mp h := by
    obtain ⟨n, f, hyps⟩ := IsSubnormal_iff'.mp h
    use n, f
    grind
  mpr := by
    rintro ⟨n, f, hyps⟩
    apply (IsSubnormal_iff' (H := H)).mpr
    use n, fun i ↦ if i ≤ n then f i else ⊤
    refine ⟨?_, ?_, ?_, ?_⟩
    · grind only
    · dsimp only
      intro i a
      split_ifs with hi
      · grind only
      · have : i = n := by grind
        simp [*]
    · grind
    · grind

alias ⟨exists_chain, _⟩ := IsSubnormal_iff

protected
lemma trans' {H : Subgroup K} (Hsn : IsSubnormal H) (Ksn : IsSubnormal K) :
    IsSubnormal (H.map K.subtype) := by
  induction Hsn with
  | top =>
    rwa [← MonoidHom.range_eq_map, range_subtype]
  | step A B h_le hSubn hN ih =>
    apply step (A.map K.subtype) (B.map K.subtype) (map_mono h_le) ih
    rw [normal_subgroupOf_iff_le_normalizer h_le] at hN
    rw [normal_subgroupOf_iff_le_normalizer (map_mono h_le)]
    exact le_trans (map_mono hN) (le_normalizer_map _)

/--
If `H` is a subnormal subgroup of `K` and `K` is a subnormal subgroup of `G`, then
`H` is a subnormal subgroup of `G`.
-/
protected
lemma trans (HK : H ≤ K) (Hsn : IsSubnormal (H.subgroupOf K)) (Ksn : IsSubnormal K) :
    IsSubnormal H := by
  have key := Hsn.trans' Ksn
  rwa [map_subgroupOf_eq_of_le HK] at key

end Subgroup.IsSubnormal
