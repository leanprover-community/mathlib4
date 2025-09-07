/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.GroupTheory.Index

/-!
# Complements

In this file we define the complement of a subgroup.

## Main definitions

- `Subgroup.IsComplement S T` where `S` and `T` are subsets of `G` states that every `g : G` can be
  written uniquely as a product `s * t` for `s ∈ S`, `t ∈ T`.
- `H.LeftTransversal` where `H` is a subgroup of `G` is the type of all left-complements of `H`,
  i.e. the set of all `S : Set G` that contain exactly one element of each left coset of `H`.
- `H.RightTransversal` where `H` is a subgroup of `G` is the set of all right-complements of `H`,
  i.e. the set of all `T : Set G` that contain exactly one element of each right coset of `H`.

## Main results

- `isComplement'_of_coprime` : Subgroups of coprime order are complements.
-/

open Function Set
open scoped Pointwise

namespace Subgroup

variable {G : Type*} [Group G] (H K : Subgroup G) (S T : Set G)

/-- `S` and `T` are complements if `(*) : S × T → G` is a bijection.
  This notion generalizes left transversals, right transversals, and complementary subgroups. -/
@[to_additive /-- `S` and `T` are complements if `(+) : S × T → G` is a bijection -/]
def IsComplement : Prop :=
  Function.Bijective fun x : S × T => x.1.1 * x.2.1

/-- `H` and `K` are complements if `(*) : H × K → G` is a bijection -/
@[to_additive /-- `H` and `K` are complements if `(+) : H × K → G` is a bijection -/]
abbrev IsComplement' :=
  IsComplement (H : Set G) (K : Set G)

variable {H K S T}

@[to_additive]
theorem isComplement'_def : IsComplement' H K ↔ IsComplement (H : Set G) (K : Set G) :=
  Iff.rfl

@[to_additive]
theorem isComplement_iff_existsUnique :
    IsComplement S T ↔ ∀ g : G, ∃! x : S × T, x.1.1 * x.2.1 = g :=
  Function.bijective_iff_existsUnique _

@[to_additive]
theorem IsComplement.existsUnique (h : IsComplement S T) (g : G) :
    ∃! x : S × T, x.1.1 * x.2.1 = g :=
  isComplement_iff_existsUnique.mp h g

@[to_additive]
theorem IsComplement'.symm (h : IsComplement' H K) : IsComplement' K H := by
  let ϕ : H × K ≃ K × H :=
    Equiv.mk (fun x => ⟨x.2⁻¹, x.1⁻¹⟩) (fun x => ⟨x.2⁻¹, x.1⁻¹⟩)
      (fun x => Prod.ext (inv_inv _) (inv_inv _)) fun x => Prod.ext (inv_inv _) (inv_inv _)
  let ψ : G ≃ G := Equiv.mk (fun g : G => g⁻¹) (fun g : G => g⁻¹) inv_inv inv_inv
  suffices hf : (ψ ∘ fun x : H × K => x.1.1 * x.2.1) = (fun x : K × H => x.1.1 * x.2.1) ∘ ϕ by
    rw [isComplement'_def, IsComplement, ← Equiv.bijective_comp ϕ]
    apply (congr_arg Function.Bijective hf).mp -- Porting note: This was a `rw` in mathlib3
    rwa [ψ.comp_bijective]
  exact funext fun x => mul_inv_rev _ _

@[to_additive]
theorem isComplement'_comm : IsComplement' H K ↔ IsComplement' K H :=
  ⟨IsComplement'.symm, IsComplement'.symm⟩

@[to_additive]
theorem isComplement_univ_singleton {g : G} : IsComplement (univ : Set G) {g} :=
  ⟨fun ⟨_, _, rfl⟩ ⟨_, _, rfl⟩ h => Prod.ext (Subtype.ext (mul_right_cancel h)) rfl, fun x =>
    ⟨⟨⟨x * g⁻¹, ⟨⟩⟩, g, rfl⟩, inv_mul_cancel_right x g⟩⟩

@[to_additive]
theorem isComplement_singleton_univ {g : G} : IsComplement ({g} : Set G) univ :=
  ⟨fun ⟨⟨_, rfl⟩, _⟩ ⟨⟨_, rfl⟩, _⟩ h => Prod.ext rfl (Subtype.ext (mul_left_cancel h)), fun x =>
    ⟨⟨⟨g, rfl⟩, g⁻¹ * x, ⟨⟩⟩, mul_inv_cancel_left g x⟩⟩

@[to_additive]
theorem isComplement_singleton_left {g : G} : IsComplement {g} S ↔ S = univ := by
  refine
    ⟨fun h => top_le_iff.mp fun x _ => ?_, fun h => (congr_arg _ h).mpr isComplement_singleton_univ⟩
  obtain ⟨⟨⟨z, rfl : z = g⟩, y, _⟩, hy⟩ := h.2 (g * x)
  rwa [← mul_left_cancel hy]

@[to_additive]
theorem isComplement_singleton_right {g : G} : IsComplement S {g} ↔ S = univ := by
  refine
    ⟨fun h => top_le_iff.mp fun x _ => ?_, fun h => h ▸ isComplement_univ_singleton⟩
  obtain ⟨y, hy⟩ := h.2 (x * g)
  conv_rhs at hy => rw [← show y.2.1 = g from y.2.2]
  rw [← mul_right_cancel hy]
  exact y.1.2

@[to_additive]
theorem isComplement_univ_left : IsComplement univ S ↔ ∃ g : G, S = {g} := by
  refine
    ⟨fun h => Set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨?_, fun a ha b hb => ?_⟩, ?_⟩
  · obtain ⟨a, _⟩ := h.2 1
    exact ⟨a.2.1, a.2.2⟩
  · have : (⟨⟨_, mem_top a⁻¹⟩, ⟨a, ha⟩⟩ : (⊤ : Set G) × S) = ⟨⟨_, mem_top b⁻¹⟩, ⟨b, hb⟩⟩ :=
      h.1 ((inv_mul_cancel a).trans (inv_mul_cancel b).symm)
    exact Subtype.ext_iff.mp (Prod.ext_iff.mp this).2
  · rintro ⟨g, rfl⟩
    exact isComplement_univ_singleton

@[to_additive]
theorem isComplement_univ_right : IsComplement S univ ↔ ∃ g : G, S = {g} := by
  refine
    ⟨fun h => Set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨?_, fun a ha b hb => ?_⟩, ?_⟩
  · obtain ⟨a, _⟩ := h.2 1
    exact ⟨a.1.1, a.1.2⟩
  · have : (⟨⟨a, ha⟩, ⟨_, mem_top a⁻¹⟩⟩ : S × (⊤ : Set G)) = ⟨⟨b, hb⟩, ⟨_, mem_top b⁻¹⟩⟩ :=
      h.1 ((mul_inv_cancel a).trans (mul_inv_cancel b).symm)
    exact Subtype.ext_iff.mp (Prod.ext_iff.mp this).1
  · rintro ⟨g, rfl⟩
    exact isComplement_singleton_univ

@[to_additive]
lemma IsComplement.mul_eq (h : IsComplement S T) : S * T = univ :=
  eq_univ_of_forall fun x ↦ by simpa [mem_mul] using (h.existsUnique x).exists

@[to_additive (attr := simp)]
lemma not_isComplement_empty_left : ¬ IsComplement ∅ T :=
  fun h ↦ by simpa [eq_comm (a := ∅)] using h.mul_eq

@[to_additive (attr := simp)]
lemma not_isComplement_empty_right : ¬ IsComplement S ∅ :=
  fun h ↦ by simpa [eq_comm (a := ∅)] using h.mul_eq

@[to_additive]
lemma IsComplement.nonempty_left (hst : IsComplement S T) : S.Nonempty := by
  contrapose! hst; simp [hst]

@[to_additive]
lemma IsComplement.nonempty_right (hst : IsComplement S T) : T.Nonempty := by
  contrapose! hst; simp [hst]

@[to_additive] lemma IsComplement.pairwiseDisjoint_smul (hst : IsComplement S T) :
    S.PairwiseDisjoint (· • T) := fun a ha b hb hab ↦ disjoint_iff_forall_ne.2 <| by
  rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
  exact hst.1.ne (a₁ := (⟨a, ha⟩, ⟨c, hc⟩)) (a₂:= (⟨b, hb⟩, ⟨d, hd⟩)) (by simp [hab])

@[to_additive AddSubgroup.IsComplement.card_mul_card]
lemma IsComplement.card_mul_card (h : IsComplement S T) : Nat.card S * Nat.card T = Nat.card G :=
  (Nat.card_prod _ _).symm.trans <| Nat.card_congr <| Equiv.ofBijective _ h

@[to_additive]
theorem isComplement'_top_bot : IsComplement' (⊤ : Subgroup G) ⊥ :=
  isComplement_univ_singleton

@[to_additive]
theorem isComplement'_bot_top : IsComplement' (⊥ : Subgroup G) ⊤ :=
  isComplement_singleton_univ

@[to_additive (attr := simp)]
theorem isComplement'_bot_left : IsComplement' ⊥ H ↔ H = ⊤ :=
  isComplement_singleton_left.trans coe_eq_univ

@[to_additive (attr := simp)]
theorem isComplement'_bot_right : IsComplement' H ⊥ ↔ H = ⊤ :=
  isComplement_singleton_right.trans coe_eq_univ

@[to_additive (attr := simp)]
theorem isComplement'_top_left : IsComplement' ⊤ H ↔ H = ⊥ :=
  isComplement_univ_left.trans coe_eq_singleton

@[to_additive (attr := simp)]
theorem isComplement'_top_right : IsComplement' H ⊤ ↔ H = ⊥ :=
  isComplement_univ_right.trans coe_eq_singleton

@[to_additive]
lemma isComplement_iff_existsUnique_inv_mul_mem :
    IsComplement S T ↔ ∀ g, ∃! s : S, (s : G)⁻¹ * g ∈ T := by
  convert isComplement_iff_existsUnique with g
  constructor <;> rintro ⟨x, hx, hx'⟩
  · exact ⟨(x, ⟨_, hx⟩), by simp, by aesop⟩
  · exact ⟨x.1, by simp [← hx], fun y hy ↦ (Prod.ext_iff.1 <| by simpa using hx' (y, ⟨_, hy⟩)).1⟩

@[to_additive]
lemma isComplement_iff_existsUnique_mul_inv_mem :
    IsComplement S T ↔ ∀ g, ∃! t : T, g * (t : G)⁻¹ ∈ S := by
  convert isComplement_iff_existsUnique with g
  constructor <;> rintro ⟨x, hx, hx'⟩
  · exact ⟨(⟨_, hx⟩, x), by simp, by aesop⟩
  · exact ⟨x.2, by simp [← hx], fun y hy ↦ (Prod.ext_iff.1 <| by simpa using hx' (⟨_, hy⟩, y)).2⟩

@[to_additive]
lemma isComplement_subgroup_right_iff_existsUnique_quotientGroupMk :
    IsComplement S H ↔ ∀ q : G ⧸ H, ∃! s : S, QuotientGroup.mk s.1 = q := by
  simp_rw [isComplement_iff_existsUnique_inv_mul_mem, SetLike.mem_coe, ← QuotientGroup.eq,
    QuotientGroup.forall_mk]

set_option linter.docPrime false in
@[to_additive]
lemma isComplement_subgroup_left_iff_existsUnique_quotientMk'' :
    IsComplement H T ↔
      ∀ q : Quotient (QuotientGroup.rightRel H), ∃! t : T, Quotient.mk'' t.1 = q := by
  simp_rw [isComplement_iff_existsUnique_mul_inv_mem, SetLike.mem_coe,
    ← QuotientGroup.rightRel_apply, ← Quotient.eq'', Quotient.forall]

@[to_additive]
lemma isComplement_subgroup_right_iff_bijective :
    IsComplement S H ↔ Bijective (S.restrict (QuotientGroup.mk : G → G ⧸ H)) :=
  isComplement_subgroup_right_iff_existsUnique_quotientGroupMk.trans
    (bijective_iff_existsUnique (S.restrict QuotientGroup.mk)).symm

@[to_additive]
lemma isComplement_subgroup_left_iff_bijective :
    IsComplement H T ↔
      Bijective (T.restrict (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H))) :=
  isComplement_subgroup_left_iff_existsUnique_quotientMk''.trans
    (bijective_iff_existsUnique (T.restrict Quotient.mk'')).symm

@[to_additive]
lemma IsComplement.card_left (h : IsComplement S H) : Nat.card S = H.index :=
  Nat.card_congr <| .ofBijective _ <| isComplement_subgroup_right_iff_bijective.mp h

@[to_additive]
theorem IsComplement.ncard_left (h : IsComplement S H) : S.ncard = H.index := by
  rw [← Nat.card_coe_set_eq, h.card_left]

@[to_additive]
lemma IsComplement.card_right (h : IsComplement H T) : Nat.card T = H.index :=
  Nat.card_congr <| (Equiv.ofBijective _ <| isComplement_subgroup_left_iff_bijective.mp h).trans <|
    QuotientGroup.quotientRightRelEquivQuotientLeftRel H

@[to_additive]
theorem IsComplement.ncard_right (h : IsComplement H T) : T.ncard = H.index := by
  rw [← Nat.card_coe_set_eq, h.card_right]

@[to_additive]
lemma isComplement_range_left {f : G ⧸ H → G} (hf : ∀ q, ↑(f q) = q) :
    IsComplement (range f) H := by
  rw [isComplement_subgroup_right_iff_bijective]
  refine ⟨?_, fun q ↦ ⟨⟨f q, q, rfl⟩, hf q⟩⟩
  rintro ⟨-, q₁, rfl⟩ ⟨-, q₂, rfl⟩ h
  exact Subtype.ext <| congr_arg f <| ((hf q₁).symm.trans h).trans (hf q₂)

@[to_additive]
lemma isComplement_range_right {f : Quotient (QuotientGroup.rightRel H) → G}
    (hf : ∀ q, Quotient.mk'' (f q) = q) : IsComplement H (range f) := by
  rw [isComplement_subgroup_left_iff_bijective]
  refine ⟨?_, fun q ↦ ⟨⟨f q, q, rfl⟩, hf q⟩⟩
  rintro ⟨-, q₁, rfl⟩ ⟨-, q₂, rfl⟩ h
  exact Subtype.ext <| congr_arg f <| ((hf q₁).symm.trans h).trans (hf q₂)

@[to_additive]
lemma exists_isComplement_left (H : Subgroup G) (g : G) : ∃ S, IsComplement S H ∧ g ∈ S := by
  classical
  refine ⟨Set.range (Function.update Quotient.out _ g), isComplement_range_left fun q ↦ ?_,
    QuotientGroup.mk g, Function.update_self (Quotient.mk'' g) g Quotient.out⟩
  by_cases hq : q = Quotient.mk'' g
  · exact hq.symm ▸ congr_arg _ (Function.update_self (Quotient.mk'' g) g Quotient.out)
  · refine Function.update_of_ne ?_ g Quotient.out ▸ q.out_eq'
    exact hq

@[to_additive]
lemma exists_isComplement_right (H : Subgroup G) (g : G) :
    ∃ T, IsComplement H T ∧ g ∈ T := by
  classical
  refine ⟨Set.range (Function.update Quotient.out _ g), isComplement_range_right fun q ↦ ?_,
    Quotient.mk'' g, Function.update_self (Quotient.mk'' g) g Quotient.out⟩
  by_cases hq : q = Quotient.mk'' g
  · exact hq.symm ▸ congr_arg _ (Function.update_self (Quotient.mk'' g) g Quotient.out)
  · refine Function.update_of_ne ?_ g Quotient.out ▸ q.out_eq'
    exact hq

/-- Given two subgroups `H' ⊆ H`, there exists a left transversal to `H'` inside `H`. -/
@[to_additive /-- Given two subgroups `H' ⊆ H`, there exists a transversal to `H'` inside `H` -/]
lemma exists_left_transversal_of_le {H' H : Subgroup G} (h : H' ≤ H) :
    ∃ S : Set G, S * H' = H ∧ Nat.card S * Nat.card H' = Nat.card H := by
  let H'' : Subgroup H := H'.comap H.subtype
  have : H' = H''.map H.subtype := by simp [H'', h]
  rw [this]
  obtain ⟨S, cmem, -⟩ := H''.exists_isComplement_left 1
  refine ⟨H.subtype '' S, ?_, ?_⟩
  · have : H.subtype '' (S * H'') = H.subtype '' S * H''.map H.subtype := image_mul H.subtype
    rw [← this, cmem.mul_eq]
    simp
  · rw [← cmem.card_mul_card]
    refine congr_arg₂ (· * ·) ?_ ?_ <;>
      exact Nat.card_congr (Equiv.Set.image _ _ <| subtype_injective H).symm

/-- Given two subgroups `H' ⊆ H`, there exists a right transversal to `H'` inside `H`. -/
@[to_additive /-- Given two subgroups `H' ⊆ H`, there exists a transversal to `H'` inside `H` -/]
lemma exists_right_transversal_of_le {H' H : Subgroup G} (h : H' ≤ H) :
    ∃ S : Set G, H' * S = H ∧ Nat.card H' * Nat.card S = Nat.card H := by
  let H'' : Subgroup H := H'.comap H.subtype
  have : H' = H''.map H.subtype := by simp [H'', h]
  rw [this]
  obtain ⟨S, cmem, -⟩ := H''.exists_isComplement_right 1
  refine ⟨H.subtype '' S, ?_, ?_⟩
  · have : H.subtype '' (H'' * S) = H''.map H.subtype * H.subtype '' S := image_mul H.subtype
    rw [← this, cmem.mul_eq]
    simp
  · have : Nat.card H'' * Nat.card S = Nat.card H := cmem.card_mul_card
    rw [← this]
    refine congr_arg₂ (· * ·) ?_ ?_ <;>
      exact Nat.card_congr (Equiv.Set.image _ _ <| subtype_injective H).symm

namespace IsComplement

/-- The equivalence `G ≃ S × T`, such that the inverse is  `(*) : S × T → G` -/
noncomputable def equiv {S T : Set G} (hST : IsComplement S T) : G ≃ S × T :=
  (Equiv.ofBijective (fun x : S × T => x.1.1 * x.2.1) hST).symm

variable (hST : IsComplement S T) (hHT : IsComplement H T) (hSK : IsComplement S K)

@[simp] theorem equiv_symm_apply (x : S × T) : (hST.equiv.symm x : G) = x.1.1 * x.2.1 := rfl

@[simp]
theorem equiv_fst_mul_equiv_snd (g : G) : ↑(hST.equiv g).fst * (hST.equiv g).snd = g :=
  (Equiv.ofBijective (fun x : S × T => x.1.1 * x.2.1) hST).right_inv g

theorem equiv_fst_eq_mul_inv (g : G) : ↑(hST.equiv g).fst = g * ((hST.equiv g).snd : G)⁻¹ :=
  eq_mul_inv_of_mul_eq (hST.equiv_fst_mul_equiv_snd g)

theorem equiv_snd_eq_inv_mul (g : G) : ↑(hST.equiv g).snd = ((hST.equiv g).fst : G)⁻¹ * g :=
  eq_inv_mul_of_mul_eq (hST.equiv_fst_mul_equiv_snd g)

theorem equiv_fst_eq_iff_leftCosetEquivalence {g₁ g₂ : G} :
    (hSK.equiv g₁).fst = (hSK.equiv g₂).fst ↔ LeftCosetEquivalence K g₁ g₂ := by
  rw [LeftCosetEquivalence, leftCoset_eq_iff]
  constructor
  · intro h
    rw [← hSK.equiv_fst_mul_equiv_snd g₂, ← hSK.equiv_fst_mul_equiv_snd g₁, ← h,
      mul_inv_rev, ← mul_assoc, inv_mul_cancel_right, ← coe_inv, ← coe_mul]
    exact Subtype.property _
  · intro h
    apply (isComplement_iff_existsUnique_inv_mul_mem.1 hSK g₁).unique
    · -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_fst_eq_mul_inv]; simp
    · rw [SetLike.mem_coe, ← mul_mem_cancel_right h]
      -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_fst_eq_mul_inv]; simp [← mul_assoc]

theorem equiv_snd_eq_iff_rightCosetEquivalence {g₁ g₂ : G} :
    (hHT.equiv g₁).snd = (hHT.equiv g₂).snd ↔ RightCosetEquivalence H g₁ g₂ := by
  rw [RightCosetEquivalence, rightCoset_eq_iff]
  constructor
  · intro h
    rw [← hHT.equiv_fst_mul_equiv_snd g₂, ← hHT.equiv_fst_mul_equiv_snd g₁, ← h,
      mul_inv_rev, mul_assoc, mul_inv_cancel_left, ← coe_inv, ← coe_mul]
    exact Subtype.property _
  · intro h
    apply (isComplement_iff_existsUnique_mul_inv_mem.1 hHT g₁).unique
    · -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_snd_eq_inv_mul]; simp
    · rw [SetLike.mem_coe, ← mul_mem_cancel_left h]
      -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_snd_eq_inv_mul, mul_assoc]; simp

theorem leftCosetEquivalence_equiv_fst (g : G) :
    LeftCosetEquivalence K g ((hSK.equiv g).fst : G) := by
  -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
  rw [equiv_fst_eq_mul_inv]; simp [LeftCosetEquivalence, leftCoset_eq_iff]

theorem rightCosetEquivalence_equiv_snd (g : G) :
    RightCosetEquivalence H g ((hHT.equiv g).snd : G) := by
  -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
  rw [RightCosetEquivalence, rightCoset_eq_iff, equiv_snd_eq_inv_mul]; simp

theorem equiv_fst_eq_self_of_mem_of_one_mem {g : G} (h1 : 1 ∈ T) (hg : g ∈ S) :
    (hST.equiv g).fst = ⟨g, hg⟩ := by
  have : hST.equiv.symm (⟨g, hg⟩, ⟨1, h1⟩) = g := by
    rw [equiv, Equiv.ofBijective]; simp
  conv_lhs => rw [← this, Equiv.apply_symm_apply]

theorem equiv_snd_eq_self_of_mem_of_one_mem {g : G} (h1 : 1 ∈ S) (hg : g ∈ T) :
    (hST.equiv g).snd = ⟨g, hg⟩ := by
  have : hST.equiv.symm (⟨1, h1⟩, ⟨g, hg⟩) = g := by
    rw [equiv, Equiv.ofBijective]; simp
  conv_lhs => rw [← this, Equiv.apply_symm_apply]

theorem equiv_snd_eq_one_of_mem_of_one_mem {g : G} (h1 : 1 ∈ T) (hg : g ∈ S) :
    (hST.equiv g).snd = ⟨1, h1⟩ := by
  ext
  rw [equiv_snd_eq_inv_mul, equiv_fst_eq_self_of_mem_of_one_mem _ h1 hg, inv_mul_cancel]

theorem equiv_fst_eq_one_of_mem_of_one_mem {g : G} (h1 : 1 ∈ S) (hg : g ∈ T) :
    (hST.equiv g).fst = ⟨1, h1⟩ := by
  ext
  rw [equiv_fst_eq_mul_inv, equiv_snd_eq_self_of_mem_of_one_mem _ h1 hg, mul_inv_cancel]

theorem equiv_mul_right (g : G) (k : K) :
    hSK.equiv (g * k) = ((hSK.equiv g).fst, (hSK.equiv g).snd * k) := by
  have : (hSK.equiv (g * k)).fst = (hSK.equiv g).fst :=
    hSK.equiv_fst_eq_iff_leftCosetEquivalence.2
      (by simp [LeftCosetEquivalence, leftCoset_eq_iff])
  ext
  · rw [this]
  · rw [coe_mul, equiv_snd_eq_inv_mul, this, equiv_snd_eq_inv_mul, mul_assoc]

theorem equiv_mul_right_of_mem {g k : G} (h : k ∈ K) :
    hSK.equiv (g * k) = ((hSK.equiv g).fst, (hSK.equiv g).snd * ⟨k, h⟩) :=
  equiv_mul_right _ g ⟨k, h⟩

theorem equiv_mul_left (h : H) (g : G) :
    hHT.equiv (h * g) = (h * (hHT.equiv g).fst, (hHT.equiv g).snd) := by
  have : (hHT.equiv (h * g)).2 = (hHT.equiv g).2 := hHT.equiv_snd_eq_iff_rightCosetEquivalence.2 ?_
  · ext
    · rw [coe_mul, equiv_fst_eq_mul_inv, this, equiv_fst_eq_mul_inv, mul_assoc]
    · rw [this]
  · simp [RightCosetEquivalence, ← smul_smul]

theorem equiv_mul_left_of_mem {h g : G} (hh : h ∈ H) :
    hHT.equiv (h * g) = (⟨h, hh⟩ * (hHT.equiv g).fst, (hHT.equiv g).snd) :=
  equiv_mul_left _ ⟨h, hh⟩ g

theorem equiv_one (hs1 : 1 ∈ S) (ht1 : 1 ∈ T) :
    hST.equiv 1 = (⟨1, hs1⟩, ⟨1, ht1⟩) := by
  rw [Equiv.apply_eq_iff_eq_symm_apply]; simp [equiv]

theorem equiv_fst_eq_self_iff_mem {g : G} (h1 : 1 ∈ T) :
    ((hST.equiv g).fst : G) = g ↔ g ∈ S := by
  constructor
  · intro h
    rw [← h]
    exact Subtype.prop _
  · intro h
    rw [hST.equiv_fst_eq_self_of_mem_of_one_mem h1 h]

theorem equiv_snd_eq_self_iff_mem {g : G} (h1 : 1 ∈ S) :
    ((hST.equiv g).snd : G) = g ↔ g ∈ T := by
  constructor
  · intro h
    rw [← h]
    exact Subtype.prop _
  · intro h
    rw [hST.equiv_snd_eq_self_of_mem_of_one_mem h1 h]

theorem coe_equiv_fst_eq_one_iff_mem {g : G} (h1 : 1 ∈ S) :
    ((hST.equiv g).fst : G) = 1 ↔ g ∈ T := by
  rw [equiv_fst_eq_mul_inv, mul_inv_eq_one, eq_comm, equiv_snd_eq_self_iff_mem _ h1]

theorem coe_equiv_snd_eq_one_iff_mem {g : G} (h1 : 1 ∈ T) :
    ((hST.equiv g).snd : G) = 1 ↔ g ∈ S := by
  rw [equiv_snd_eq_inv_mul, inv_mul_eq_one, equiv_fst_eq_self_iff_mem _ h1]

/-- A left transversal is in bijection with left cosets. -/
@[to_additive /-- A left transversal is in bijection with left cosets. -/]
noncomputable def leftQuotientEquiv (hS : IsComplement S H) : G ⧸ H ≃ S :=
  (Equiv.ofBijective _ (isComplement_subgroup_right_iff_bijective.mp hS)).symm

/-- A left transversal is finite iff the subgroup has finite index. -/
@[to_additive /-- A left transversal is finite iff the subgroup has finite index. -/]
theorem finite_left_iff (h : IsComplement S H) : Finite S ↔ H.FiniteIndex := by
  rw [← h.leftQuotientEquiv.finite_iff]
  exact ⟨fun _ ↦ finiteIndex_of_finite_quotient, fun _ ↦ finite_quotient_of_finiteIndex⟩

@[to_additive]
lemma finite_left [H.FiniteIndex] (hS : IsComplement S H) : S.Finite := hS.finite_left_iff.2 ‹_›

@[to_additive]
theorem quotientGroupMk_leftQuotientEquiv (hS : IsComplement S H) (q : G ⧸ H) :
    Quotient.mk'' (leftQuotientEquiv hS q : G) = q :=
  hS.leftQuotientEquiv.symm_apply_apply q

@[to_additive]
theorem leftQuotientEquiv_apply {f : G ⧸ H → G} (hf : ∀ q, (f q : G ⧸ H) = q) (q : G ⧸ H) :
    (leftQuotientEquiv (isComplement_range_left hf) q : G) = f q := by
  refine (Subtype.ext_iff.mp ?_).trans (Subtype.coe_mk (f q) ⟨q, rfl⟩)
  exact (leftQuotientEquiv (isComplement_range_left hf)).apply_eq_iff_eq_symm_apply.mpr (hf q).symm

/-- A left transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that left coset. -/
@[to_additive /-- A left transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that left coset. -/]
noncomputable def toLeftFun (hS : IsComplement S H) : G → S := leftQuotientEquiv hS ∘ Quotient.mk''

@[to_additive]
theorem inv_toLeftFun_mul_mem (hS : IsComplement S H) (g : G) :
    (toLeftFun hS g : G)⁻¹ * g ∈ H :=
  QuotientGroup.leftRel_apply.mp <| Quotient.exact' <| quotientGroupMk_leftQuotientEquiv _ _

@[to_additive]
theorem inv_mul_toLeftFun_mem (hS : IsComplement S H) (g : G) :
    g⁻¹ * toLeftFun hS g ∈ H :=
  (congr_arg (· ∈ H) (by rw [mul_inv_rev, inv_inv])).mp (H.inv_mem (inv_toLeftFun_mul_mem hS g))

/-- A right transversal is in bijection with right cosets. -/
@[to_additive /-- A right transversal is in bijection with right cosets. -/]
noncomputable def rightQuotientEquiv (hT : IsComplement H T) :
    Quotient (QuotientGroup.rightRel H) ≃ T :=
  (Equiv.ofBijective _ (isComplement_subgroup_left_iff_bijective.mp hT)).symm

/-- A right transversal is finite iff the subgroup has finite index. -/
@[to_additive /-- A right transversal is finite iff the subgroup has finite index. -/]
theorem finite_right_iff (h : IsComplement H T) : Finite T ↔ H.FiniteIndex := by
  rw [← h.rightQuotientEquiv.finite_iff,
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).finite_iff]
  exact ⟨fun _ ↦ finiteIndex_of_finite_quotient, fun _ ↦ finite_quotient_of_finiteIndex⟩

@[to_additive]
lemma finite_right [H.FiniteIndex] (hT : IsComplement H T) : T.Finite := hT.finite_right_iff.2 ‹_›

@[to_additive]
theorem mk''_rightQuotientEquiv (hT : IsComplement H T)
     (q : Quotient (QuotientGroup.rightRel H)) : Quotient.mk'' (rightQuotientEquiv hT q : G) = q :=
  (rightQuotientEquiv hT).symm_apply_apply q

@[to_additive]
theorem rightQuotientEquiv_apply {f : Quotient (QuotientGroup.rightRel H) → G}
    (hf : ∀ q, Quotient.mk'' (f q) = q) (q : Quotient (QuotientGroup.rightRel H)) :
    (rightQuotientEquiv (isComplement_range_right hf) q : G) = f q := by
  refine (Subtype.ext_iff.mp ?_).trans (Subtype.coe_mk (f q) ⟨q, rfl⟩)
  exact (rightQuotientEquiv (isComplement_range_right hf)).apply_eq_iff_eq_symm_apply.2 (hf q).symm

/-- A right transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that right coset. -/
@[to_additive /-- A right transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that right coset. -/]
noncomputable def toRightFun (hT : IsComplement H T) : G → T := rightQuotientEquiv hT ∘ .mk''

@[to_additive]
theorem mul_inv_toRightFun_mem (hT : IsComplement H T) (g : G) :
    g * (toRightFun hT g : G)⁻¹ ∈ H :=
  QuotientGroup.rightRel_apply.mp <| Quotient.exact' <| mk''_rightQuotientEquiv _ _

@[to_additive]
theorem toRightFun_mul_inv_mem (hT : IsComplement H T) (g : G) :
    (toRightFun hT g : G) * g⁻¹ ∈ H :=
  (congr_arg (· ∈ H) (by rw [mul_inv_rev, inv_inv])).mp (H.inv_mem (mul_inv_toRightFun_mem hT g))

@[to_additive]
theorem encard_left [H.FiniteIndex] (h : IsComplement S H) : S.encard = H.index := by
  rw [← h.finite_left.cast_ncard_eq, h.ncard_left]

@[to_additive]
theorem encard_right [H.FiniteIndex] (h : IsComplement H T) : T.encard = H.index := by
  rw [← h.finite_right.cast_ncard_eq, h.ncard_right]

end IsComplement

section Action

open Pointwise MulAction

/-- The collection of left transversals of a subgroup -/
@[to_additive /-- The collection of left transversals of a subgroup. -/]
abbrev LeftTransversal (H : Subgroup G) := {S : Set G // IsComplement S H}

/-- The collection of right transversals of a subgroup -/
@[to_additive /-- The collection of right transversals of a subgroup. -/]
abbrev RightTransversal (H : Subgroup G) := {T : Set G // IsComplement H T}

variable {F : Type*} [Group F] [MulAction F G] [QuotientAction F H]

@[to_additive]
noncomputable instance : MulAction F H.LeftTransversal where
  smul f T :=
    ⟨f • (T : Set G), by
      refine isComplement_iff_existsUnique_inv_mul_mem.mpr fun g => ?_
      obtain ⟨t, ht1, ht2⟩ := isComplement_iff_existsUnique_inv_mul_mem.mp T.2 (f⁻¹ • g)
      refine ⟨⟨f • (t : G), Set.smul_mem_smul_set t.2⟩, ?_, ?_⟩
      · exact smul_inv_smul f g ▸ QuotientAction.inv_mul_mem f ht1
      · rintro ⟨-, t', ht', rfl⟩ h
        replace h := QuotientAction.inv_mul_mem f⁻¹ h
        simp only [Subtype.ext_iff, smul_left_cancel_iff, inv_smul_smul] at h ⊢
        exact Subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ h)⟩
  one_smul T := Subtype.ext (one_smul F (T : Set G))
  mul_smul f₁ f₂ T := Subtype.ext (mul_smul f₁ f₂ (T : Set G))

@[to_additive]
theorem smul_toLeftFun (f : F) (S : H.LeftTransversal) (g : G) :
    (f • (S.2.toLeftFun g : G)) = (f • S).2.toLeftFun (f • g) :=
  Subtype.ext_iff.mp <| @ExistsUnique.unique (↥(f • (S : Set G))) (fun s => (↑s)⁻¹ * f • g ∈ H)
    (isComplement_iff_existsUnique_inv_mul_mem.mp (f • S).2 (f • g))
    ⟨f • (S.2.toLeftFun g : G), Set.smul_mem_smul_set (Subtype.coe_prop _)⟩
      ((f • S).2.toLeftFun (f • g))
    (QuotientAction.inv_mul_mem f (S.2.inv_toLeftFun_mul_mem g))
      ((f • S).2.inv_toLeftFun_mul_mem (f • g))

@[to_additive]
theorem smul_leftQuotientEquiv (f : F) (S : H.LeftTransversal) (q : G ⧸ H) :
    f • (S.2.leftQuotientEquiv  q : G) = (f • S).2.leftQuotientEquiv (f • q) :=
  Quotient.inductionOn' q fun g => smul_toLeftFun f S g

@[to_additive]
theorem smul_apply_eq_smul_apply_inv_smul (f : F) (S : H.LeftTransversal) (q : G ⧸ H) :
    ((f • S).2.leftQuotientEquiv q : G) = f • (S.2.leftQuotientEquiv (f⁻¹ • q) : G) := by
  rw [smul_leftQuotientEquiv, smul_inv_smul]

end Action

@[to_additive]
instance : Inhabited H.LeftTransversal :=
  ⟨⟨Set.range Quotient.out, isComplement_range_left Quotient.out_eq'⟩⟩

@[to_additive]
instance : Inhabited H.RightTransversal :=
  ⟨⟨Set.range Quotient.out, isComplement_range_right Quotient.out_eq'⟩⟩

theorem IsComplement'.isCompl (h : IsComplement' H K) : IsCompl H K := by
  refine
    ⟨disjoint_iff_inf_le.mpr fun g ⟨p, q⟩ =>
        let x : H × K := ⟨⟨g, p⟩, 1⟩
        let y : H × K := ⟨1, g, q⟩
        Subtype.ext_iff.mp
          (Prod.ext_iff.mp (show x = y from h.1 ((mul_one g).trans (one_mul g).symm))).1,
      codisjoint_iff_le_sup.mpr fun g _ => ?_⟩
  obtain ⟨⟨h, k⟩, rfl⟩ := h.2 g
  exact Subgroup.mul_mem_sup h.2 k.2

theorem IsComplement'.sup_eq_top (h : IsComplement' H K) : H ⊔ K = ⊤ :=
  h.isCompl.sup_eq_top

theorem IsComplement'.disjoint (h : IsComplement' H K) : Disjoint H K :=
  h.isCompl.disjoint

theorem IsComplement'.index_eq_card (h : IsComplement' H K) : K.index = Nat.card H :=
  h.card_left.symm

/-- If `H` and `K` are complementary with `K` normal, then `G ⧸ K` is isomorphic to `H`. -/
@[simps!]
noncomputable def IsComplement'.QuotientMulEquiv [K.Normal] (h : H.IsComplement' K) :
    G ⧸ K ≃* H :=
  MulEquiv.symm
  { h.leftQuotientEquiv.symm with
    map_mul' := fun _ _ ↦ rfl }

theorem IsComplement.card_mul (h : IsComplement S T) :
    Nat.card S * Nat.card T = Nat.card G :=
  (Nat.card_prod _ _).symm.trans (Nat.card_eq_of_bijective _ h)

theorem IsComplement'.card_mul (h : IsComplement' H K) :
    Nat.card H * Nat.card K = Nat.card G :=
  IsComplement.card_mul h

theorem isComplement'_of_disjoint_and_mul_eq_univ (h1 : Disjoint H K)
    (h2 : ↑H * ↑K = (Set.univ : Set G)) : IsComplement' H K := by
  refine ⟨mul_injective_of_disjoint h1, fun g => ?_⟩
  obtain ⟨h, hh, k, hk, hg⟩ := Set.eq_univ_iff_forall.mp h2 g
  exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), hg⟩

theorem isComplement'_of_card_mul_and_disjoint [Finite G]
    (h1 : Nat.card H * Nat.card K = Nat.card G) (h2 : Disjoint H K) :
    IsComplement' H K :=
  (Nat.bijective_iff_injective_and_card _).mpr
    ⟨mul_injective_of_disjoint h2, (Nat.card_prod H K).trans h1⟩

theorem isComplement'_iff_card_mul_and_disjoint [Finite G] :
    IsComplement' H K ↔ Nat.card H * Nat.card K = Nat.card G ∧ Disjoint H K :=
  ⟨fun h => ⟨h.card_mul, h.disjoint⟩, fun h => isComplement'_of_card_mul_and_disjoint h.1 h.2⟩

theorem isComplement'_of_coprime [Finite G]
    (h1 : Nat.card H * Nat.card K = Nat.card G)
    (h2 : Nat.Coprime (Nat.card H) (Nat.card K)) : IsComplement' H K :=
  isComplement'_of_card_mul_and_disjoint h1 (disjoint_iff.mpr (inf_eq_bot_of_coprime h2))

theorem isComplement'_stabilizer {α : Type*} [MulAction G α] (a : α)
    (h1 : ∀ h : H, h • a = a → h = 1) (h2 : ∀ g : G, ∃ h : H, h • g • a = a) :
    IsComplement' H (MulAction.stabilizer G a) := by
  refine isComplement_iff_existsUnique.mpr fun g => ?_
  obtain ⟨h, hh⟩ := h2 g
  have hh' : (↑h * g) • a = a := by rwa [mul_smul]
  refine ⟨⟨h⁻¹, h * g, hh'⟩, inv_mul_cancel_left ↑h g, ?_⟩
  rintro ⟨h', g, hg : g • a = a⟩ rfl
  specialize h1 (h * h') (by rwa [mul_smul, smul_def h', ← hg, ← mul_smul, hg])
  refine Prod.ext (eq_inv_of_mul_eq_one_right h1) (Subtype.ext ?_)
  rwa [Subtype.ext_iff, coe_one, coe_mul, ← right_eq_mul, mul_assoc (↑h) (↑h') g] at h1

end Subgroup
