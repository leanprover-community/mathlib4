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

namespace IsSubnormal

/-- The trivial subgroup is subnormal. -/
@[simp] lemma bot : IsSubnormal (⊥ : Subgroup G) := step _ ⊤ le_top top normal_subgroupOf

/-- A normal subgroup is subnormal. -/
lemma _root_.Subgroup.Normal.isSubnormal (hn : H.Normal) : IsSubnormal H :=
  step _ ⊤ le_top top normal_subgroupOf

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
    IsSubnormal H ↔ H = ⊤ ∨ ∃ K, H ≤ K ∧ IsSubnormal K ∧ (H.subgroupOf K).Normal where
  mp h := by
    induction h with grind
  mpr h := by
    obtain rfl | ⟨K, HK, Ksn, h⟩ := h
    · exact top
    · exact step _ _ HK Ksn h

/-- A proper subnormal subgroup is contained in a proper normal subgroup. -/
lemma exists_normal_and_ne_top_of_ne (hN : H.IsSubnormal) (ne_top : H ≠ ⊤) :
    ∃ K, K.Normal ∧ H ≤ K ∧ K ≠ ⊤ := by
  induction hN with
  | top => contradiction
  | step H K h_le hSubn hN ih =>
    obtain rfl | K_ne := eq_or_ne K ⊤
    · use H
      rw [(normal_subgroupOf_iff_le_normalizer h_le)] at hN
      grind only [normalizer_eq_top_iff, → top_unique]
    · grind

/-- A subnormal subgroup is contained in a normal subgroup. -/
lemma le_normal (hN : H.IsSubnormal) : ∃ K, K.Normal ∧ H ≤ K := by
  induction hN
  · simp
  · grind

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

/--
If `H` is a subnormal subgroup of `K` and `K` is a subnormal subgroup of `G`, then
`H` is a subnormal subgroup of `G`.
-/
lemma trans (HK : H ≤ K) (Hsn : IsSubnormal (H.subgroupOf K)) (Ksn : IsSubnormal K) :
    IsSubnormal H := by
  rw [IsSubnormal_iff'] at Hsn Ksn ⊢
  obtain ⟨nH, fH, hypsH⟩ := Hsn
  obtain ⟨nK, fK, hypsK⟩ := Ksn
  use nH + nK, fun n ↦ if n ≤ nH then (fH n).map K.subtype else fK (n - nH)
  constructor
  · intros i hi
    split_ifs with h1 h2
    · simp [*]
    · have : map K.subtype ⊤ = K := by ext; simp
      grind
    · grind
    · grind
  constructor
  · intro i hi
    split_ifs with h1
    · split
      · rename_i inH
        rw [if_pos h1]
        have := hypsH.2.1 _ inH
        rw [normal_subgroupOf_iff_le_normalizer_inf] at this ⊢
        intro g hg
        simp only [mem_map, subtype_apply, Subtype.exists, exists_and_right, exists_eq_right] at hg
        obtain ⟨g', hg'⟩ := hg
        have := this hg'
        simp_all only [inf_of_le_left, map_subtype_le_map_subtype]
        rw [mem_normalizer_iff] at this ⊢
        simp only [Subtype.forall, MulMemClass.mk_mul_mk, mem_map, subtype_apply, Subtype.exists,
          exists_and_right, exists_eq_right] at this ⊢
        intro h'
        constructor
        · rintro ⟨x, hx⟩
          constructor
          · exact (this h' x).mp hx
          · exact mul_mem (mul_mem g' x) (inv_mem g')
        · rintro ⟨hconj, hx⟩
          have h'K : h' ∈ K := by
            have := mul_mem hconj g'
            have := mul_mem (inv_mem g') this
            simpa [mul_assoc] using this
          use h'K, (this h' h'K).mpr hx
      · grind
    · rw [if_neg (by grind)]
      obtain rfl | inh := eq_or_ne nH i
      · rw [if_pos le_rfl, hypsH.2.2.2, Nat.add_sub_cancel_left, ← hypsK.2.2.1,
          show map (fK 0).subtype ⊤ = fK 0 by ext; simp]
        simpa using (hypsK.2.1 0 (by grind))
      · rw [if_neg (by grind), Nat.sub_add_comm (not_lt.mp h1)]
        refine (hypsK.2.1 (i - nH) ?_)
        grind
  rw [if_pos (Nat.zero_le _)]
  constructor
  · simp_all only [subgroupOf_map_subtype, inf_of_le_left]
  · obtain rfl | inh := eq_or_ne nK 0
    · grind only [toGroup.hcongr_3, subgroupOf_eq_top, top_subgroupOf, map_subgroupOf_eq_of_le]
    · grind

end Subgroup.IsSubnormal
