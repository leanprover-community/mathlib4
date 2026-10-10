/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.GroupAction.MultiplePrimitivity

import Mathlib.Algebra.Group.Pointwise.Set.Card

/-! # Theorems of Jordan

A proof of theorems of Jordan regarding primitive permutation groups.

This mostly follows the book [Wielandt, *Finite permutation groups*][Wielandt-1964].

- `MulAction.IsPreprimitive.is_two_pretransitive` and
  `MulAction.IsPreprimitive.is_two_preprimitive` are technical lemmas
  that prove 2-pretransitivity / 2-preprimitivity for some group
  primitive actions given the transitivity / primitivity of
  `ofFixingSubgroup G s` (Wielandt, 13.1)

- `MulAction.IsPreprimitive.is_two_pretransitive_of_normal` and
  `MulAction.IsPreprimitive.is_two_preprimitive_of_normal` prove
  2-pretransitivity / 2-preprimitivity for a normal subgroup `N` of `G`
  given the transitivity / primitivity of `ofFixingSubgroup N s`;
  `MulAction.IsPreprimitive.is_two_pretransitive'` and
  `MulAction.IsPreprimitive.is_two_preprimitive_strong_jordan` apply them
  to the normal closure of `fixingSubgroup G s` (Wielandt, 13.1')

- `MulAction.IsPreprimitive.isMultiplyPreprimitive`:
  A multiple preprimitivity criterion of Jordan (1871) for a preprimitive
  action: the hypothesis is the preprimitivity of the `SubMulAction`
  of `fixingSubgroup s` on `ofFixingSubgroup G s` (Wielandt, 13.2)

- `Equiv.Perm.eq_top_of_isPreprimitive_of_isSwap_mem` :
  a primitive subgroup of a permutation group that contains a
  swap is equal to the full permutation group (Wielandt, 13.3)

- `Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem` :
  a primitive subgroup of a permutation group that contains a 3-cycle
  contains the alternating group (Wielandt, 13.3)

## TODO

- Prove `Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem`:
  a primitive subgroup of a permutation group that contains
  a cycle of *prime* order contains the alternating group (Wielandt, 13.9).

-/

public section

open MulAction SubMulAction Subgroup

open scoped Pointwise

section Jordan

variable {G α : Type*} [Group G] [MulAction G α]

/-- In a 2-transitive action, the normal closure of stabilizers is the full group. -/
theorem normalClosure_of_stabilizer_eq_top (hsn' : 2 < ENat.card α)
    (hG' : IsMultiplyPretransitive G α 2) {a : α} :
    normalClosure ((stabilizer G a) : Set G) = ⊤ := by
  have : IsPretransitive G α := by
    rw [← is_one_pretransitive_iff]
    exact isMultiplyPretransitive_of_le' (one_le_two) (le_of_lt hsn')
  have : Nontrivial α := by
    rw [← ENat.one_lt_card_iff_nontrivial]
    exact lt_trans (by simp) hsn'
  have hGa : IsCoatom (stabilizer G a) := by
    rw [isCoatom_stabilizer_iff_preprimitive]
    exact isPreprimitive_of_is_two_pretransitive hG'
  apply hGa.right
  -- Remains to prove: (stabilizer G a) < Subgroup.normalClosure (stabilizer G a)
  constructor
  · apply le_normalClosure
  · intro hyp
    have : Nontrivial (ofStabilizer G a) := by
      rw [← ENat.one_lt_card_iff_nontrivial]
      apply lt_of_add_lt_add_right
      rwa [ENat_card_ofStabilizer_add_one_eq]
    rw [nontrivial_iff] at this
    obtain ⟨b, c, hbc⟩ := this
    have : IsPretransitive (stabilizer G a) (ofStabilizer G a) := by
      rw [← is_one_pretransitive_iff]
      rwa [← ofStabilizer.isMultiplyPretransitive]
    -- get g ∈ stabilizer G a, g • b = c,
    obtain ⟨⟨g, hg⟩, hgbc⟩ := exists_smul_eq (stabilizer G a) b c
    apply hbc
    rw [← SetLike.coe_eq_coe] at hgbc ⊢
    obtain ⟨h, hinvab⟩ := exists_smul_eq G (b : α) a
    rw [eq_comm, ← inv_smul_eq_iff] at hinvab
    rw [← hgbc, SetLike.val_smul, ← hinvab, inv_smul_eq_iff, eq_comm]
    simp only [subgroup_smul_def, smul_smul, ← mul_assoc, ← mem_stabilizer_iff]
    exact hyp (normalClosure_normal.conj_mem g (le_normalClosure hg) h)

open MulAction.IsPreprimitive

open scoped Pointwise

/-- Jordan's criteria for 2-pretransitivity and 2-preprimitivity, for a normal subgroup:
let `G` act preprimitively on a finite type `α`, let `N` be a normal subgroup of `G`,
and let `s` be a nonempty subset of `α` whose complement has at least two points.
If `fixingSubgroup N s` acts transitively (resp. preprimitively) on the complement of `s`,
then `N` acts 2-pretransitively (resp. 2-preprimitively). -/
theorem MulAction.IsPreprimitive.is_two_motive_of_normal
    (hG : IsPreprimitive G α) {N : Subgroup G} [hN : N.Normal] {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α) :
    (IsPretransitive (fixingSubgroup N s) (ofFixingSubgroup N s) →
      IsMultiplyPretransitive N α 2) ∧
    (IsPreprimitive (fixingSubgroup N s) (ofFixingSubgroup N s) →
      IsMultiplyPreprimitive N α 2) := by
  have : Finite α := Nat.finite_of_card_ne_zero (by omega)
  induction n using Nat.strong_induction_on generalizing s with | _ n hrec
  have hsc : 1 < sᶜ.ncard := by
    have := Set.ncard_add_ncard_compl s
    omega
  rcases n with _ | n
  · obtain ⟨a, rfl⟩ := Set.ncard_eq_one.mp hsn
    suffices IsPretransitive (fixingSubgroup N {a}) (ofFixingSubgroup N {a}) →
        IsPretransitive N α by
      refine ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩
      · have := this hs
        rw [ofStabilizer.isMultiplyPretransitive (a := a), is_one_pretransitive_iff]
        exact .of_surjective_map ofFixingSubgroup_of_singleton_bijective.surjective hs
      · have := this hs.toIsPretransitive
        rw [isMultiplyPreprimitive_succ_iff_ofStabilizer N α le_rfl (a := a),
          is_one_preprimitive_iff]
        exact .of_surjective ofFixingSubgroup_of_singleton_bijective.surjective
    intro hs
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.one_lt_ncard_iff_nontrivial.mp hsc
    obtain ⟨k, hk⟩ := exists_smul_eq (fixingSubgroup N {a})
      (⟨x, hx⟩ : ofFixingSubgroup N {a}) ⟨y, hy⟩
    exact IsQuasiPreprimitive.isPretransitive_of_normal fun h ↦
      hxy <| (Set.eq_univ_iff_forall.mp h x k).symm.trans (congrArg Subtype.val hk)
  obtain ⟨g, hlt, hne, hu⟩ : ∃ g : G, (s ∩ g • s).ncard < s.ncard ∧ (s ∩ g • s).Nonempty ∧
      s ∪ g • s ≠ .univ := by
    rcases Nat.lt_or_ge (2 * s.ncard) (Nat.card α) with h | h
    · obtain ⟨a, ha, b, hb, hab⟩ := Set.one_lt_ncard_iff_nontrivial.mp (by omega : 1 < s.ncard)
      obtain ⟨g, hga, hgb⟩ := exists_mem_smul_and_notMem_smul (G := G) s.toFinite ⟨a, ha⟩
        (fun h ↦ by simp [h] at hsc) hab
      refine ⟨g, Set.ncard_lt_ncard ⟨Set.inter_subset_left, fun h ↦ hgb (h hb).2⟩,
        ⟨a, ha, hga⟩, Set.union_ne_univ_of_ncard_add_ncard_lt ?_⟩
      rwa [Set.ncard_smul_set, ← two_mul]
    · obtain ⟨a, ha, b, hb, hab⟩ := Set.one_lt_ncard_iff_nontrivial.mp hsc
      obtain ⟨g, hga, hgb⟩ := exists_mem_smul_and_notMem_smul (G := G) sᶜ.toFinite ⟨a, ha⟩
        (Set.compl_ne_univ.mpr (Set.nonempty_of_ncard_ne_zero (by omega))) hab
      simp only [Set.smul_set_compl, Set.mem_compl_iff, not_not] at hga hgb
      have hu : s ∪ g • s ≠ .univ := fun h ↦ (h ▸ Set.mem_univ a).elim ha hga
      refine ⟨g, (Set.ncard_lt_ncard ⟨Set.inter_subset_right, fun h ↦ hb (h hgb).1⟩).trans_eq
        (Set.ncard_smul_set g s), Set.nonempty_inter_of_le_ncard_add_ncard ?_ hu, hu⟩
      rwa [Set.ncard_smul_set, ← two_mul]
  obtain ⟨c, hc⟩ : ∃ c, c ∉ s ∧ c ∉ g • s := by simpa [Set.eq_univ_iff_forall] using hu
  have key (hs : IsPretransitive (fixingSubgroup N s) (ofFixingSubgroup N s)) :
      IsPretransitive (fixingSubgroup N (s ∩ g • s)) (ofFixingSubgroup N (s ∩ g • s)) := by
    rw [isPretransitive_iff_base (⟨c, fun h ↦ hc.1 h.1⟩ : ofFixingSubgroup N (s ∩ g • s))]
    rintro ⟨x, hx⟩
    rcases not_and_or.mp hx with hxs | hxs
    · obtain ⟨⟨k, hk⟩, hkx⟩ := exists_smul_eq (fixingSubgroup N s)
        (⟨c, hc.1⟩ : ofFixingSubgroup N s) ⟨x, hxs⟩
      exact ⟨⟨k, fixingSubgroup_antitone N α Set.inter_subset_left hk⟩,
        Subtype.ext (congrArg Subtype.val hkx :)⟩
    · rw [Set.mem_smul_set_iff_inv_smul_mem] at hxs hc
      obtain ⟨⟨k, hk⟩, hkx⟩ := exists_smul_eq (fixingSubgroup N s)
        (⟨g⁻¹ • c, hc.2⟩ : ofFixingSubgroup N s) ⟨g⁻¹ • x, hxs⟩
      rw [mem_fixingSubgroup_iff] at hk
      refine ⟨⟨⟨g * k * g⁻¹, hN.conj_mem k k.prop g⟩, (mem_fixingSubgroup_iff N).mpr
        fun y hy ↦ ?_⟩, Subtype.ext ?_⟩
      · simpa [mul_smul, Subgroup.smul_def, smul_eq_iff_eq_inv_smul] using
          hk _ (Set.mem_smul_set_iff_inv_smul_mem.mp hy.2)
      · simpa [mul_smul, eq_inv_smul_iff, Subgroup.smul_def] using congrArg Subtype.val hkx
  have hpos := (Set.ncard_pos (s := s ∩ g • s)).mpr hne
  have h := hrec ((s ∩ g • s).ncard - 1) (by omega) (s := s ∩ g • s) (by omega) (by omega)
  refine ⟨fun hs ↦ h.1 (key hs), fun hs ↦ h.2 ?_⟩
  have := key hs.toIsPretransitive
  apply IsPreprimitive.of_card_lt (f := ofFixingSubgroup_of_inclusion N Set.inter_subset_left)
  rw [show Nat.card (ofFixingSubgroup N (s ∩ g • s)) = (s ∩ g • s)ᶜ.ncard from
    Nat.card_coe_set_eq _, Set.ncard_range_of_injective ofFixingSubgroup_of_inclusion_injective,
    show Nat.card (ofFixingSubgroup N s) = sᶜ.ncard from Nat.card_coe_set_eq _, Set.compl_inter]
  refine (Set.ncard_union_lt sᶜ.toFinite (g • s)ᶜ.toFinite ?_).trans_le ?_
  · rwa [Set.disjoint_compl_right_iff_subset, Set.compl_subset_iff_union]
  · rw [← Set.smul_set_compl, Set.ncard_smul_set, two_mul]

/-- Jordan's criterion `MulAction.IsPreprimitive.is_two_pretransitive` for a normal subgroup:
if `N` is a normal subgroup of `G` and `fixingSubgroup N s` acts transitively
on `ofFixingSubgroup N s`, then `N` acts 2-pretransitively. -/
theorem MulAction.IsPreprimitive.is_two_pretransitive_of_normal
    (hG : IsPreprimitive G α) {N : Subgroup G} [N.Normal] {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α)
    (hs_trans : IsPretransitive (fixingSubgroup N s) (ofFixingSubgroup N s)) :
    IsMultiplyPretransitive N α 2 :=
  (hG.is_two_motive_of_normal hsn hsn').1 hs_trans

/-- Jordan's criterion `MulAction.IsPreprimitive.is_two_preprimitive` for a normal subgroup:
if `N` is a normal subgroup of `G` and `fixingSubgroup N s` acts preprimitively
on `ofFixingSubgroup N s`, then `N` acts 2-preprimitively. -/
theorem MulAction.IsPreprimitive.is_two_preprimitive_of_normal
    (hG : IsPreprimitive G α) {N : Subgroup G} [N.Normal] {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α)
    (hs_prim : IsPreprimitive (fixingSubgroup N s) (ofFixingSubgroup N s)) :
    IsMultiplyPreprimitive N α 2 :=
  (hG.is_two_motive_of_normal hsn hsn').2 hs_prim

/-- A stronger version of Jordan's criterion for 2-pretransitivity (Wielandt, 13.1'):
under the hypotheses of `MulAction.IsPreprimitive.is_two_pretransitive`,
the normal closure of `fixingSubgroup G s` acts 2-pretransitively.

The bound cannot be weakened to `n + 1 < Nat.card α`: in the natural action of `S₃` on three
points, fixing two points gives a trivial subgroup acting transitively on the singleton complement.
Its normal closure is trivial and does not act 2-pretransitively. -/
theorem MulAction.IsPreprimitive.is_two_pretransitive'
    (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α)
    (hs_trans : IsPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s)) :
    IsMultiplyPretransitive (normalClosure (fixingSubgroup G s : Set G)) α 2 := by
  refine hG.is_two_pretransitive_of_normal hsn hsn' ⟨fun x y ↦ ?_⟩
  obtain ⟨⟨k, hk⟩, hkxy⟩ := exists_smul_eq (fixingSubgroup G s)
    (⟨x, x.prop⟩ : ofFixingSubgroup G s) ⟨y, y.prop⟩
  exact ⟨⟨⟨k, le_normalClosure hk⟩, hk⟩, Subtype.ext (congrArg Subtype.val hkxy :)⟩

/-- A stronger version of Jordan's criterion for 2-preprimitivity (Wielandt, 13.1'):
under the hypotheses of `MulAction.IsPreprimitive.is_two_preprimitive`,
the normal closure of `fixingSubgroup G s` acts 2-preprimitively. -/
theorem MulAction.IsPreprimitive.is_two_preprimitive_strong_jordan
    (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α)
    (hs_prim : IsPreprimitive (fixingSubgroup G s) (ofFixingSubgroup G s)) :
    IsMultiplyPreprimitive (normalClosure (fixingSubgroup G s : Set G)) α 2 := by
  let N := normalClosure (fixingSubgroup G s : Set G)
  let f : ofFixingSubgroup G s →ₑ[fun k : fixingSubgroup G s ↦
      (⟨⟨k, le_normalClosure k.prop⟩, k.prop⟩ : fixingSubgroup N s)] ofFixingSubgroup N s :=
    { toFun x := ⟨x, x.prop⟩, map_smul' _ _ := rfl }
  exact hG.is_two_preprimitive_of_normal hsn hsn' <|
    IsPreprimitive.of_surjective (f := f) fun x ↦ ⟨⟨x, x.prop⟩, rfl⟩

/-- Simultaneously prove `MulAction.IsPreprimitive.is_two_pretransitive`
and `MulAction.IsPreprimitive.is_two_preprimitive`. -/
@[deprecated "Use `is_two_pretransitive` or `is_two_preprimitive` instead."
  (since := "2026-10-08")]
theorem MulAction.IsPreprimitive.is_two_motive_of_is_motive
    (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α) :
    (IsPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s)
      → IsMultiplyPretransitive G α 2)
    ∧ (IsPreprimitive (fixingSubgroup G s) (ofFixingSubgroup G s)
      → IsMultiplyPreprimitive G α 2) := by
  refine ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩
  · have := hG.is_two_pretransitive' hsn hsn' hs
    exact .of_isScalarTower (normalClosure (fixingSubgroup G s : Set G))
  · exact (hG.is_two_preprimitive_strong_jordan hsn hsn' hs).of_bijective_map
      (φ := Subtype.val) (f := ⟨id, fun _ _ ↦ rfl⟩) Function.bijective_id

/-- A criterion due to Jordan for being 2-pretransitive (Wielandt, 13.1) -/
theorem MulAction.IsPreprimitive.is_two_pretransitive
    (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α)
    (hs_trans : IsPretransitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)) :
    IsMultiplyPretransitive G α 2 := by
  have := hG.is_two_pretransitive' hsn hsn' hs_trans
  exact .of_isScalarTower (normalClosure (fixingSubgroup G s : Set G))

/-- A criterion due to Jordan for being 2-preprimitive (Wielandt, 13.1) -/
theorem MulAction.IsPreprimitive.is_two_preprimitive
    (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α)
    (hs_prim : IsPreprimitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)) :
    IsMultiplyPreprimitive G α 2 :=
  (hG.is_two_preprimitive_strong_jordan hsn hsn' hs_prim).of_bijective_map
    (φ := Subtype.val) (f := ⟨id, fun _ _ ↦ rfl⟩) Function.bijective_id

/-- Jordan's multiple primitivity criterion (Wielandt, 13.3) -/
theorem MulAction.IsPreprimitive.isMultiplyPreprimitive
    (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α)
    (hprim : IsPreprimitive (fixingSubgroup G s) (ofFixingSubgroup G s)) :
    IsMultiplyPreprimitive G α (n + 2) := by
  have hα : Finite α := Or.resolve_right (finite_or_infinite α) (fun _ ↦ by
    simp [Nat.card_eq_zero_of_infinite] at hsn')
  induction n generalizing α hα G with
  -- case n = 0
  | zero => simpa using is_two_preprimitive hG hsn hsn' hprim
  -- Induction step
  | succ n hrec =>
    suffices ∃ (a : α) (t : Set (SubMulAction.ofStabilizer G a)),
      a ∈ s ∧ s = insert a (Subtype.val '' t) by
      obtain ⟨a, t, _, hst⟩ := this
      have ha' : a ∉ Subtype.val '' t := by
        intro h; rw [Set.mem_image] at h; obtain ⟨x, hx⟩ := h
        apply x.prop; rw [hx.right]; exact Set.mem_singleton a
      have ht_prim : IsPreprimitive (stabilizer G a) (SubMulAction.ofStabilizer G a) := by
        rw [← is_one_preprimitive_iff]
        rw [← isMultiplyPreprimitive_succ_iff_ofStabilizer]
        · apply is_two_preprimitive hG hsn hsn' hprim
        · simp
      have : IsPreprimitive ↥(fixingSubgroup G (insert a (Subtype.val '' t)))
          (ofFixingSubgroup G (insert a (Subtype.val '' t))) :=
        IsPreprimitive.of_surjective
          (ofFixingSubgroup_of_eq_bijective (hst := hst)).surjective
      have hGs' : IsPreprimitive (fixingSubgroup (stabilizer G a) t)
        (ofFixingSubgroup (stabilizer G a) t) :=
        IsPreprimitive.of_surjective
          ofFixingSubgroup_insert_map_bijective.surjective
      rw [isMultiplyPreprimitive_succ_iff_ofStabilizer G (a := a) _ (Nat.le_add_left 1 (n + 1))]
      refine hrec ht_prim ?_ ?_ hGs' Subtype.finite
      · -- t.card = Nat.succ n
        rw [← Set.ncard_image_of_injective t Subtype.val_injective]
        apply Nat.add_right_cancel
        rw [← Set.ncard_insert_of_notMem ha', ← hst, hsn]
      · -- n + 2 < Nat.card (SubMulAction.ofStabilizer G α a)
        rw [← Nat.add_lt_add_iff_right, nat_card_ofStabilizer_add_one_eq]
        exact hsn'
    -- ∃ a t, a ∈ s ∧ s = insert a (Subtype.val '' t)
    suffices s.Nonempty by
      obtain ⟨a, ha⟩ := this
      use a, Subtype.val ⁻¹' s, ha
      ext x
      by_cases hx : x = a <;> simp [hx, mem_ofStabilizer_iff, ha]
    rw [← Set.ncard_pos, hsn]; apply Nat.succ_pos

end Jordan

section Subgroups

namespace Equiv.Perm

open Equiv

variable {α : Type*}

variable {G : Subgroup (Perm α)}

theorem subgroup_eq_top_of_nontrivial [Finite α] (hα : Nat.card α ≤ 2) (hG : Nontrivial G) :
    G = (⊤ : Subgroup (Perm α)) := by
  apply Subgroup.eq_top_of_le_card
  rw [Nat.card_perm]
  apply (Nat.factorial_le hα).trans
  rwa [Nat.factorial_two, Nat.succ_le_iff, one_lt_card_iff_ne_bot, ← nontrivial_iff_ne_bot]

theorem isMultiplyPretransitive_of_nontrivial {K : Type*} [Group K] [MulAction K α]
    (hα : Nat.card α = 2) (hK : fixedPoints K α ≠ .univ) (n : ℕ) :
    IsMultiplyPretransitive K α n := by
  have : Finite α := Or.resolve_right (finite_or_infinite α) (fun _ ↦ by
    simp [Nat.card_eq_zero_of_infinite] at hα)
  have : Fintype α := Fintype.ofFinite α
  suffices h2 : IsMultiplyPretransitive K α 2 by
    by_cases hn : n ≤ 2
    · apply MulAction.isMultiplyPretransitive_of_le' hn
      simp [← hα]
    · suffices (IsEmpty (Fin n ↪ α)) by infer_instance
      rwa [← not_nonempty_iff, Function.Embedding.nonempty_iff_card_le, Fintype.card_fin,
        ← Nat.card_eq_fintype_card, hα]
  let φ := MulAction.toPermHom K α
  let f : α →ₑ[φ] α :=
    { toFun := id
      map_smul' := fun _ _ ↦ rfl }
  have hf : Function.Bijective f := Function.bijective_id
  suffices Function.Surjective φ by
    unfold IsMultiplyPretransitive
    rw [IsPretransitive.of_embedding_congr this hf (n := Fin 2), ← hα]
    apply Perm.isMultiplyPretransitive
  rw [← MonoidHom.range_eq_top]
  apply Subgroup.eq_top_of_card_eq
  apply le_antisymm (card_le_card_group φ.range)
  simp only [Nat.card_perm, hα, Nat.factorial_two]
  by_contra H
  simp only [not_le, Nat.lt_succ_iff, Finite.card_le_one_iff_subsingleton] at H
  apply hK
  apply Set.eq_univ_of_univ_subset
  intro a _ g
  suffices φ g = φ 1 by
    conv_rhs => rw [← one_smul K a]
    simp only [← toPerm_apply, ← toPermHom_apply K α g]
    exact congrFun (congrArg DFunLike.coe this) a
  simpa [← Subtype.coe_inj] using H.elim ⟨_, ⟨g, rfl⟩⟩ ⟨_, ⟨1, rfl⟩⟩

variable [Fintype α] [DecidableEq α]

theorem isPretransitive_of_isCycle_mem {g : Perm α}
    (hgc : g.IsCycle) (hg : g ∈ G) :
    IsPretransitive (fixingSubgroup G (g.support : Set α)ᶜ)
      (SubMulAction.ofFixingSubgroup G (g.support : Set α)ᶜ) := by
  obtain ⟨a, _, hgc⟩ := hgc
  have hs : ∀ x : α, g • x ≠ x ↔
    x ∈ SubMulAction.ofFixingSubgroup G ((↑g.support : Set α)ᶜ) := by
    intro x
    simp [SubMulAction.mem_ofFixingSubgroup_iff]
  suffices ∀ x ∈ SubMulAction.ofFixingSubgroup G ((↑g.support : Set α)ᶜ),
      ∃ k : fixingSubgroup G ((↑g.support : Set α)ᶜ), x = k • a by
    rw [isPretransitive_iff]
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨k, hk⟩ := this x hx
    obtain ⟨k', hk'⟩ := this y hy
    use k' * k⁻¹
    rw [← SetLike.coe_eq_coe]
    simp only [SetLike.mk_smul_mk]
    rw [hk, hk', smul_smul, inv_mul_cancel_right]
  intro x hx
  have hg' : (⟨g, hg⟩ : ↥G) ∈ fixingSubgroup G ((↑g.support : Set α)ᶜ) := by
    simp_rw [mem_fixingSubgroup_iff G]
    intro y hy
    simpa only [Set.mem_compl_iff, Finset.mem_coe, notMem_support] using! hy
  let g' : fixingSubgroup (↥G) ((↑g.support : Set α)ᶜ) := ⟨(⟨g, hg⟩ : ↥G), hg'⟩
  obtain ⟨i, hi⟩ := hgc ((hs x).mpr hx)
  exact ⟨g' ^ i, hi.symm⟩

set_option backward.isDefEq.respectTransparency false in
omit [Fintype α] in variable [Finite α] in
/-- A primitive subgroup of `Equiv.Perm α` that contains a swap
is the full permutation group (Jordan). -/
theorem subgroup_eq_top_of_isPreprimitive_of_isSwap_mem
    (hG : IsPreprimitive G α) (g : Perm α) (h2g : IsSwap g) (hg : g ∈ G) :
    G = ⊤ := by
  classical
  have := Fintype.ofFinite α
  rcases Nat.lt_or_ge (Nat.card α) 3 with hα3 | hα3
  · -- trivial case : Nat.card α ≤ 2
    rw [Nat.lt_succ_iff] at hα3
    apply Subgroup.eq_top_of_card_eq
    simp only [Nat.card_eq_fintype_card]
    apply le_antisymm (Fintype.card_subtype_le _)
    rw [← Nat.card_eq_fintype_card, Nat.card_perm]
    refine le_trans (Nat.factorial_le hα3) ?_
    rw [Nat.factorial_two]
    have : Nonempty G := One.instNonempty
    apply Nat.le_of_dvd Fintype.card_pos
    rw [← h2g.orderOf, orderOf_submonoid ⟨g, hg⟩]
    exact orderOf_dvd_card
  -- important case : Nat.card α ≥ 3
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' hα3
  have hsc : Set.ncard ((g.support)ᶜ : Set α) = n + 1 := by
    apply Nat.add_left_cancel
    rw [Set.ncard_add_ncard_compl, Set.ncard_coe_finset,
      card_support_eq_two.mpr h2g, add_comm, hn]
  apply eq_top_of_isMultiplyPretransitive
  suffices IsMultiplyPreprimitive G α (Nat.card α - 1) by
    apply IsMultiplyPreprimitive.isMultiplyPretransitive
  rw [show Nat.card α - 1 = n + 2 by grind]
  apply hG.isMultiplyPreprimitive hsc
  · rw [hn]; apply Nat.lt_add_one
  have := isPretransitive_of_isCycle_mem h2g.isCycle hg
  apply IsPreprimitive.of_prime_card
  convert Nat.prime_two
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← card_support_eq_two.mpr h2g]
  simp [SubMulAction.mem_ofFixingSubgroup_iff, support]

/-- A primitive subgroup of `Equiv.Perm α` that contains a 3-cycle
contains the alternating group (Jordan). -/
theorem alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
    (hG : IsPreprimitive G α) {g : Perm α} (h3g : IsThreeCycle g) (hg : g ∈ G) :
    alternatingGroup α ≤ G := by
  classical
  rcases Nat.lt_or_ge (Nat.card α) 4 with hα4 | hα4
  · -- trivial case : Fintype.card α ≤ 3
    rw [Nat.lt_succ_iff] at hα4
    apply alternatingGroup_le_of_index_le_two
    rw [← Nat.mul_le_mul_right_iff (k := Nat.card G) (Nat.card_pos),
      Subgroup.index_mul_card, Nat.card_perm]
    apply le_trans (Nat.factorial_le hα4)
    rw [show Nat.factorial 3 = 2 * 3 by simp [Nat.factorial]]
    simp only [mul_le_mul_iff_right₀, Nat.succ_pos]
    apply Nat.le_of_dvd Nat.card_pos
    suffices 3 = orderOf (⟨g, hg⟩ : G) by
      rw [this, Nat.card_eq_fintype_card]
      exact orderOf_dvd_card
    simp only [orderOf_mk, h3g.orderOf]
    -- important case : Nat.card α ≥ 4
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' hα4
  apply IsMultiplyPretransitive.alternatingGroup_le
  suffices IsMultiplyPreprimitive G α (Nat.card α - 2) from
    IsMultiplyPreprimitive.isMultiplyPretransitive ..
  rw [show Nat.card α - 2 = n + 2 by grind]
  apply hG.isMultiplyPreprimitive (s := (g.supportᶜ : Set α))
  · apply Nat.add_left_cancel
    rw [Set.ncard_add_ncard_compl, Set.ncard_coe_finset,
      h3g.card_support, add_comm, hn]
  · grind
  have := isPretransitive_of_isCycle_mem h3g.isCycle hg
  apply IsPreprimitive.of_prime_card
  convert Nat.prime_three
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← h3g.card_support]
  apply congr_arg
  ext x
  simp [SubMulAction.mem_ofFixingSubgroup_iff]

end Equiv.Perm

end Subgroups
