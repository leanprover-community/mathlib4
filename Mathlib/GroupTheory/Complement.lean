/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Data.ZMod.Quotient

/-!
# Complements

In this file we define the complement of a subgroup.

## Main definitions

- `IsComplement S T` where `S` and `T` are subsets of `G` states that every `g : G` can be
  written uniquely as a product `s * t` for `s ∈ S`, `t ∈ T`.
- `leftTransversals T` where `T` is a subset of `G` is the set of all left-complements of `T`,
  i.e. the set of all `S : Set G` that contain exactly one element of each left coset of `T`.
- `rightTransversals S` where `S` is a subset of `G` is the set of all right-complements of `S`,
  i.e. the set of all `T : Set G` that contain exactly one element of each right coset of `S`.
- `transferTransversal H g` is a specific `leftTransversal` of `H` that is used in the
  computation of the transfer homomorphism evaluated at an element `g : G`.

## Main results

- `isComplement'_of_coprime` : Subgroups of coprime order are complements.
-/

open Set
open scoped Pointwise

namespace Subgroup

variable {G : Type*} [Group G] (H K : Subgroup G) (S T : Set G)

/-- `S` and `T` are complements if `(*) : S × T → G` is a bijection.
  This notion generalizes left transversals, right transversals, and complementary subgroups. -/
@[to_additive "`S` and `T` are complements if `(+) : S × T → G` is a bijection"]
def IsComplement : Prop :=
  Function.Bijective fun x : S × T => x.1.1 * x.2.1

/-- `H` and `K` are complements if `(*) : H × K → G` is a bijection -/
@[to_additive "`H` and `K` are complements if `(+) : H × K → G` is a bijection"]
abbrev IsComplement' :=
  IsComplement (H : Set G) (K : Set G)

/-- The set of left-complements of `T : Set G` -/
@[to_additive "The set of left-complements of `T : Set G`"]
def leftTransversals : Set (Set G) :=
  { S : Set G | IsComplement S T }

/-- The set of right-complements of `S : Set G` -/
@[to_additive "The set of right-complements of `S : Set G`"]
def rightTransversals : Set (Set G) :=
  { T : Set G | IsComplement S T }

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
theorem mem_leftTransversals_iff_existsUnique_inv_mul_mem :
    S ∈ leftTransversals T ↔ ∀ g : G, ∃! s : S, (s : G)⁻¹ * g ∈ T := by
  rw [leftTransversals, Set.mem_setOf_eq, isComplement_iff_existsUnique]
  refine ⟨fun h g => ?_, fun h g => ?_⟩
  · obtain ⟨x, h1, h2⟩ := h g
    exact
      ⟨x.1, (congr_arg (· ∈ T) (eq_inv_mul_of_mul_eq h1)).mp x.2.2, fun y hy =>
        (Prod.ext_iff.mp (h2 ⟨y, (↑y)⁻¹ * g, hy⟩ (mul_inv_cancel_left ↑y g))).1⟩
  · obtain ⟨x, h1, h2⟩ := h g
    refine ⟨⟨x, (↑x)⁻¹ * g, h1⟩, mul_inv_cancel_left (↑x) g, fun y hy => ?_⟩
    have hf := h2 y.1 ((congr_arg (· ∈ T) (eq_inv_mul_of_mul_eq hy)).mp y.2.2)
    exact Prod.ext hf (Subtype.ext (eq_inv_mul_of_mul_eq (hf ▸ hy)))

@[to_additive]
theorem mem_rightTransversals_iff_existsUnique_mul_inv_mem :
    S ∈ rightTransversals T ↔ ∀ g : G, ∃! s : S, g * (s : G)⁻¹ ∈ T := by
  rw [rightTransversals, Set.mem_setOf_eq, isComplement_iff_existsUnique]
  refine ⟨fun h g => ?_, fun h g => ?_⟩
  · obtain ⟨x, h1, h2⟩ := h g
    exact
      ⟨x.2, (congr_arg (· ∈ T) (eq_mul_inv_of_mul_eq h1)).mp x.1.2, fun y hy =>
        (Prod.ext_iff.mp (h2 ⟨⟨g * (↑y)⁻¹, hy⟩, y⟩ (inv_mul_cancel_right g y))).2⟩
  · obtain ⟨x, h1, h2⟩ := h g
    refine ⟨⟨⟨g * (↑x)⁻¹, h1⟩, x⟩, inv_mul_cancel_right g x, fun y hy => ?_⟩
    have hf := h2 y.2 ((congr_arg (· ∈ T) (eq_mul_inv_of_mul_eq hy)).mp y.1.2)
    exact Prod.ext (Subtype.ext (eq_mul_inv_of_mul_eq (hf ▸ hy))) hf

@[to_additive]
theorem mem_leftTransversals_iff_existsUnique_quotient_mk''_eq :
    S ∈ leftTransversals (H : Set G) ↔
      ∀ q : Quotient (QuotientGroup.leftRel H), ∃! s : S, Quotient.mk'' s.1 = q := by
  simp_rw [mem_leftTransversals_iff_existsUnique_inv_mul_mem, SetLike.mem_coe, ←
    QuotientGroup.eq]
  exact ⟨fun h q => Quotient.inductionOn' q h, fun h g => h (Quotient.mk'' g)⟩

@[to_additive]
theorem mem_rightTransversals_iff_existsUnique_quotient_mk''_eq :
    S ∈ rightTransversals (H : Set G) ↔
      ∀ q : Quotient (QuotientGroup.rightRel H), ∃! s : S, Quotient.mk'' s.1 = q := by
  simp_rw [mem_rightTransversals_iff_existsUnique_mul_inv_mem, SetLike.mem_coe, ←
    QuotientGroup.rightRel_apply, ← Quotient.eq'']
  exact ⟨fun h q => Quotient.inductionOn' q h, fun h g => h (Quotient.mk'' g)⟩

@[to_additive]
theorem mem_leftTransversals_iff_bijective :
    S ∈ leftTransversals (H : Set G) ↔
      Function.Bijective (S.restrict (Quotient.mk'' : G → Quotient (QuotientGroup.leftRel H))) :=
  mem_leftTransversals_iff_existsUnique_quotient_mk''_eq.trans
    (Function.bijective_iff_existsUnique (S.restrict Quotient.mk'')).symm

@[to_additive]
theorem mem_rightTransversals_iff_bijective :
    S ∈ rightTransversals (H : Set G) ↔
      Function.Bijective (S.restrict (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H))) :=
  mem_rightTransversals_iff_existsUnique_quotient_mk''_eq.trans
    (Function.bijective_iff_existsUnique (S.restrict Quotient.mk'')).symm

@[to_additive]
theorem card_left_transversal (h : S ∈ leftTransversals (H : Set G)) : Nat.card S = H.index :=
  Nat.card_congr <| Equiv.ofBijective _ <| mem_leftTransversals_iff_bijective.mp h

@[to_additive]
theorem card_right_transversal (h : S ∈ rightTransversals (H : Set G)) : Nat.card S = H.index :=
  Nat.card_congr <|
    (Equiv.ofBijective _ <| mem_rightTransversals_iff_bijective.mp h).trans <|
      QuotientGroup.quotientRightRelEquivQuotientLeftRel H

@[to_additive]
theorem range_mem_leftTransversals {f : G ⧸ H → G} (hf : ∀ q, ↑(f q) = q) :
    Set.range f ∈ leftTransversals (H : Set G) :=
  mem_leftTransversals_iff_bijective.mpr
    ⟨by rintro ⟨-, q₁, rfl⟩ ⟨-, q₂, rfl⟩ h
        exact Subtype.ext <| congr_arg f <| ((hf q₁).symm.trans h).trans (hf q₂),
      fun q => ⟨⟨f q, q, rfl⟩, hf q⟩⟩

@[to_additive]
theorem range_mem_rightTransversals {f : Quotient (QuotientGroup.rightRel H) → G}
    (hf : ∀ q, Quotient.mk'' (f q) = q) : Set.range f ∈ rightTransversals (H : Set G) :=
  mem_rightTransversals_iff_bijective.mpr
    ⟨by rintro ⟨-, q₁, rfl⟩ ⟨-, q₂, rfl⟩ h
        exact Subtype.ext <| congr_arg f <| ((hf q₁).symm.trans h).trans (hf q₂),
      fun q => ⟨⟨f q, q, rfl⟩, hf q⟩⟩

@[to_additive]
lemma exists_left_transversal (H : Subgroup G) (g : G) :
    ∃ S ∈ leftTransversals (H : Set G), g ∈ S := by
  classical
    refine
      ⟨Set.range (Function.update Quotient.out _ g), range_mem_leftTransversals fun q => ?_,
        Quotient.mk'' g, Function.update_same (Quotient.mk'' g) g Quotient.out⟩
    by_cases hq : q = Quotient.mk'' g
    · exact hq.symm ▸ congr_arg _ (Function.update_same (Quotient.mk'' g) g Quotient.out)
    · refine (Function.update_noteq ?_ g Quotient.out) ▸ q.out_eq'
      exact hq

@[to_additive]
lemma exists_right_transversal (H : Subgroup G) (g : G) :
    ∃ S ∈ rightTransversals (H : Set G), g ∈ S := by
  classical
    refine
      ⟨Set.range (Function.update Quotient.out _ g), range_mem_rightTransversals fun q => ?_,
        Quotient.mk'' g, Function.update_same (Quotient.mk'' g) g Quotient.out⟩
    by_cases hq : q = Quotient.mk'' g
    · exact hq.symm ▸ congr_arg _ (Function.update_same (Quotient.mk'' g) g Quotient.out)
    · exact Eq.trans (congr_arg _ (Function.update_noteq hq g Quotient.out)) q.out_eq'

/-- Given two subgroups `H' ⊆ H`, there exists a left transversal to `H'` inside `H`. -/
@[to_additive "Given two subgroups `H' ⊆ H`, there exists a transversal to `H'` inside `H`"]
lemma exists_left_transversal_of_le {H' H : Subgroup G} (h : H' ≤ H) :
    ∃ S : Set G, S * H' = H ∧ Nat.card S * Nat.card H' = Nat.card H := by
  let H'' : Subgroup H := H'.comap H.subtype
  have : H' = H''.map H.subtype := by simp [H'', h]
  rw [this]
  obtain ⟨S, cmem, -⟩ := H''.exists_left_transversal 1
  refine ⟨H.subtype '' S, ?_, ?_⟩
  · have : H.subtype '' (S * H'') = H.subtype '' S * H''.map H.subtype := image_mul H.subtype
    rw [← this, cmem.mul_eq]
    simp [Set.ext_iff]
  · rw [← cmem.card_mul_card]
    refine congr_arg₂ (· * ·) ?_ ?_ <;>
      exact Nat.card_congr (Equiv.Set.image _ _ <| subtype_injective H).symm

/-- Given two subgroups `H' ⊆ H`, there exists a right transversal to `H'` inside `H`. -/
@[to_additive "Given two subgroups `H' ⊆ H`, there exists a transversal to `H'` inside `H`"]
lemma exists_right_transversal_of_le {H' H : Subgroup G} (h : H' ≤ H) :
    ∃ S : Set G, H' * S = H ∧ Nat.card H' * Nat.card S = Nat.card H := by
  let H'' : Subgroup H := H'.comap H.subtype
  have : H' = H''.map H.subtype := by simp [H'', h]
  rw [this]
  obtain ⟨S, cmem, -⟩ := H''.exists_right_transversal 1
  refine ⟨H.subtype '' S, ?_, ?_⟩
  · have : H.subtype '' (H'' * S) = H''.map H.subtype * H.subtype '' S := image_mul H.subtype
    rw [← this, cmem.mul_eq]
    simp [Set.ext_iff]
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
    apply (mem_leftTransversals_iff_existsUnique_inv_mul_mem.1 hSK g₁).unique
    · -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_fst_eq_mul_inv]; simp
    · rw [SetLike.mem_coe, ← mul_mem_cancel_right h]
      -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_fst_eq_mul_inv]; simp [equiv_fst_eq_mul_inv, ← mul_assoc]

theorem equiv_snd_eq_iff_rightCosetEquivalence {g₁ g₂ : G} :
    (hHT.equiv g₁).snd = (hHT.equiv g₂).snd ↔ RightCosetEquivalence H g₁ g₂ := by
  rw [RightCosetEquivalence, rightCoset_eq_iff]
  constructor
  · intro h
    rw [← hHT.equiv_fst_mul_equiv_snd g₂, ← hHT.equiv_fst_mul_equiv_snd g₁, ← h,
      mul_inv_rev, mul_assoc, mul_inv_cancel_left, ← coe_inv, ← coe_mul]
    exact Subtype.property _
  · intro h
    apply (mem_rightTransversals_iff_existsUnique_mul_inv_mem.1 hHT g₁).unique
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

-- This lemma has always been bad, but the linter only noticed after https://github.com/leanprover/lean4/pull/2644.
@[simp, nolint simpNF]
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

-- This lemma has always been bad, but the linter only noticed after https://github.com/leanprover/lean4/pull/2644.
@[simp, nolint simpNF]
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

end IsComplement

namespace MemLeftTransversals

/-- A left transversal is in bijection with left cosets. -/
@[to_additive "A left transversal is in bijection with left cosets."]
noncomputable def toEquiv (hS : S ∈ Subgroup.leftTransversals (H : Set G)) : G ⧸ H ≃ S :=
  (Equiv.ofBijective _ (Subgroup.mem_leftTransversals_iff_bijective.mp hS)).symm

@[to_additive "A left transversal is finite iff the subgroup has finite index"]
theorem finite_iff
    (h : S ∈ Subgroup.leftTransversals (H : Set G)) :
    Finite S ↔ H.FiniteIndex := by
  rw [← (Subgroup.MemLeftTransversals.toEquiv h).finite_iff]
  exact ⟨fun _ ↦ finiteIndex_of_finite_quotient H, fun _ ↦ finite_quotient_of_finiteIndex H⟩

@[to_additive]
theorem mk''_toEquiv (hS : S ∈ Subgroup.leftTransversals (H : Set G)) (q : G ⧸ H) :
    Quotient.mk'' (toEquiv hS q : G) = q :=
  (toEquiv hS).symm_apply_apply q

@[to_additive]
theorem toEquiv_apply {f : G ⧸ H → G} (hf : ∀ q, (f q : G ⧸ H) = q) (q : G ⧸ H) :
    (toEquiv (range_mem_leftTransversals hf) q : G) = f q := by
  refine (Subtype.ext_iff.mp ?_).trans (Subtype.coe_mk (f q) ⟨q, rfl⟩)
  exact (toEquiv (range_mem_leftTransversals hf)).apply_eq_iff_eq_symm_apply.mpr (hf q).symm

/-- A left transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that left coset. -/
@[to_additive "A left transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that left coset."]
noncomputable def toFun (hS : S ∈ Subgroup.leftTransversals (H : Set G)) : G → S :=
  toEquiv hS ∘ Quotient.mk''

@[to_additive]
theorem inv_toFun_mul_mem (hS : S ∈ Subgroup.leftTransversals (H : Set G)) (g : G) :
    (toFun hS g : G)⁻¹ * g ∈ H :=
  QuotientGroup.leftRel_apply.mp <| Quotient.exact' <| mk''_toEquiv _ _

@[to_additive]
theorem inv_mul_toFun_mem (hS : S ∈ Subgroup.leftTransversals (H : Set G)) (g : G) :
    g⁻¹ * toFun hS g ∈ H :=
  (congr_arg (· ∈ H) (by rw [mul_inv_rev, inv_inv])).mp (H.inv_mem (inv_toFun_mul_mem hS g))

end MemLeftTransversals

namespace MemRightTransversals

/-- A right transversal is in bijection with right cosets. -/
@[to_additive "A right transversal is in bijection with right cosets."]
noncomputable def toEquiv (hS : S ∈ Subgroup.rightTransversals (H : Set G)) :
    Quotient (QuotientGroup.rightRel H) ≃ S :=
  (Equiv.ofBijective _ (Subgroup.mem_rightTransversals_iff_bijective.mp hS)).symm

@[to_additive "A right transversal is finite iff the subgroup has finite index"]
theorem finite_iff
    (h : S ∈ Subgroup.rightTransversals (H : Set G)) :
    Finite S ↔ H.FiniteIndex := by
  rw [← (Subgroup.MemRightTransversals.toEquiv h).finite_iff,
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).finite_iff]
  exact ⟨fun _ ↦ finiteIndex_of_finite_quotient H, fun _ ↦ finite_quotient_of_finiteIndex H⟩

@[to_additive]
theorem mk''_toEquiv (hS : S ∈ Subgroup.rightTransversals (H : Set G))
    (q : Quotient (QuotientGroup.rightRel H)) : Quotient.mk'' (toEquiv hS q : G) = q :=
  (toEquiv hS).symm_apply_apply q

@[to_additive]
theorem toEquiv_apply {f : Quotient (QuotientGroup.rightRel H) → G}
    (hf : ∀ q, Quotient.mk'' (f q) = q) (q : Quotient (QuotientGroup.rightRel H)) :
    (toEquiv (range_mem_rightTransversals hf) q : G) = f q := by
  refine (Subtype.ext_iff.mp ?_).trans (Subtype.coe_mk (f q) ⟨q, rfl⟩)
  exact (toEquiv (range_mem_rightTransversals hf)).apply_eq_iff_eq_symm_apply.mpr (hf q).symm

/-- A right transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that right coset. -/
@[to_additive "A right transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that right coset."]
noncomputable def toFun (hS : S ∈ Subgroup.rightTransversals (H : Set G)) : G → S :=
  toEquiv hS ∘ Quotient.mk''

@[to_additive]
theorem mul_inv_toFun_mem (hS : S ∈ Subgroup.rightTransversals (H : Set G)) (g : G) :
    g * (toFun hS g : G)⁻¹ ∈ H :=
  QuotientGroup.rightRel_apply.mp <| Quotient.exact' <| mk''_toEquiv _ _

@[to_additive]
theorem toFun_mul_inv_mem (hS : S ∈ Subgroup.rightTransversals (H : Set G)) (g : G) :
    (toFun hS g : G) * g⁻¹ ∈ H :=
  (congr_arg (· ∈ H) (by rw [mul_inv_rev, inv_inv])).mp (H.inv_mem (mul_inv_toFun_mem hS g))

end MemRightTransversals

section Action

open Pointwise MulAction MemLeftTransversals

variable {F : Type*} [Group F] [MulAction F G] [QuotientAction F H]

@[to_additive]
noncomputable instance : MulAction F (leftTransversals (H : Set G)) where
  smul f T :=
    ⟨f • (T : Set G), by
      refine mem_leftTransversals_iff_existsUnique_inv_mul_mem.mpr fun g => ?_
      obtain ⟨t, ht1, ht2⟩ := mem_leftTransversals_iff_existsUnique_inv_mul_mem.mp T.2 (f⁻¹ • g)
      refine ⟨⟨f • (t : G), Set.smul_mem_smul_set t.2⟩, ?_, ?_⟩
      · exact smul_inv_smul f g ▸ QuotientAction.inv_mul_mem f ht1
      · rintro ⟨-, t', ht', rfl⟩ h
        replace h := QuotientAction.inv_mul_mem f⁻¹ h
        simp only [Subtype.ext_iff, Subtype.coe_mk, smul_left_cancel_iff, inv_smul_smul] at h ⊢
        exact Subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ h)⟩
  one_smul T := Subtype.ext (one_smul F (T : Set G))
  mul_smul f₁ f₂ T := Subtype.ext (mul_smul f₁ f₂ (T : Set G))

@[to_additive]
theorem smul_toFun (f : F) (T : leftTransversals (H : Set G)) (g : G) :
    (f • (toFun T.2 g : G)) = toFun (f • T).2 (f • g) :=
  Subtype.ext_iff.mp <| @ExistsUnique.unique (↥(f • (T : Set G))) (fun s => (↑s)⁻¹ * f • g ∈ H)
    (mem_leftTransversals_iff_existsUnique_inv_mul_mem.mp (f • T).2 (f • g))
    ⟨f • (toFun T.2 g : G), Set.smul_mem_smul_set (Subtype.coe_prop _)⟩ (toFun (f • T).2 (f • g))
    (QuotientAction.inv_mul_mem f (inv_toFun_mul_mem T.2 g)) (inv_toFun_mul_mem (f • T).2 (f • g))

@[to_additive]
theorem smul_toEquiv (f : F) (T : leftTransversals (H : Set G)) (q : G ⧸ H) :
    f • (toEquiv T.2 q : G) = toEquiv (f • T).2 (f • q) :=
  Quotient.inductionOn' q fun g => smul_toFun f T g

@[to_additive]
theorem smul_apply_eq_smul_apply_inv_smul (f : F) (T : leftTransversals (H : Set G)) (q : G ⧸ H) :
    (toEquiv (f • T).2 q : G) = f • (toEquiv T.2 (f⁻¹ • q) : G) := by
  rw [smul_toEquiv, smul_inv_smul]

end Action

@[to_additive]
instance : Inhabited (leftTransversals (H : Set G)) :=
  ⟨⟨Set.range Quotient.out, range_mem_leftTransversals Quotient.out_eq'⟩⟩

@[to_additive]
instance : Inhabited (rightTransversals (H : Set G)) :=
  ⟨⟨Set.range Quotient.out, range_mem_rightTransversals Quotient.out_eq'⟩⟩

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
  (card_left_transversal h).symm

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
  rwa [Subtype.ext_iff, coe_one, coe_mul, ← self_eq_mul_left, mul_assoc (↑h) (↑h') g] at h1

end Subgroup

namespace Subgroup

open Equiv Function MemLeftTransversals MulAction MulAction.quotient ZMod

universe u

variable {G : Type u} [Group G] (H : Subgroup G) (g : G)

/-- Partition `G ⧸ H` into orbits of the action of `g : G`. -/
noncomputable def quotientEquivSigmaZMod :
    G ⧸ H ≃ Σq : orbitRel.Quotient (zpowers g) (G ⧸ H), ZMod (minimalPeriod (g • ·) q.out) :=
  (selfEquivSigmaOrbits (zpowers g) (G ⧸ H)).trans
    (sigmaCongrRight fun q => orbitZPowersEquiv g q.out)

theorem quotientEquivSigmaZMod_symm_apply (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
    (k : ZMod (minimalPeriod (g • ·) q.out)) :
    (quotientEquivSigmaZMod H g).symm ⟨q, k⟩ = g ^ (cast k : ℤ) • q.out :=
  rfl

theorem quotientEquivSigmaZMod_apply (q : orbitRel.Quotient (zpowers g) (G ⧸ H)) (k : ℤ) :
    quotientEquivSigmaZMod H g (g ^ k • q.out) = ⟨q, k⟩ := by
  rw [apply_eq_iff_eq_symm_apply, quotientEquivSigmaZMod_symm_apply, ZMod.coe_intCast,
    zpow_smul_mod_minimalPeriod]

/-- The transfer transversal as a function. Given a `⟨g⟩`-orbit `q₀, g • q₀, ..., g ^ (m - 1) • q₀`
  in `G ⧸ H`, an element `g ^ k • q₀` is mapped to `g ^ k • g₀` for a fixed choice of
  representative `g₀` of `q₀`. -/
noncomputable def transferFunction : G ⧸ H → G := fun q =>
  g ^ (cast (quotientEquivSigmaZMod H g q).2 : ℤ) * (quotientEquivSigmaZMod H g q).1.out.out

theorem transferFunction_apply (q : G ⧸ H) :
    transferFunction H g q =
      g ^ (cast (quotientEquivSigmaZMod H g q).2 : ℤ) *
        (quotientEquivSigmaZMod H g q).1.out.out :=
  rfl

theorem coe_transferFunction (q : G ⧸ H) : ↑(transferFunction H g q) = q := by
  rw [transferFunction_apply, ← smul_eq_mul, Quotient.coe_smul_out,
    ← quotientEquivSigmaZMod_symm_apply, Sigma.eta, symm_apply_apply]

/-- The transfer transversal as a set. Contains elements of the form `g ^ k • g₀` for fixed choices
  of representatives `g₀` of fixed choices of representatives `q₀` of `⟨g⟩`-orbits in `G ⧸ H`. -/
def transferSet : Set G :=
  Set.range (transferFunction H g)

theorem mem_transferSet (q : G ⧸ H) : transferFunction H g q ∈ transferSet H g :=
  ⟨q, rfl⟩

/-- The transfer transversal. Contains elements of the form `g ^ k • g₀` for fixed choices
  of representatives `g₀` of fixed choices of representatives `q₀` of `⟨g⟩`-orbits in `G ⧸ H`. -/
def transferTransversal : leftTransversals (H : Set G) :=
  ⟨transferSet H g, range_mem_leftTransversals (coe_transferFunction H g)⟩

theorem transferTransversal_apply (q : G ⧸ H) :
    ↑(toEquiv (transferTransversal H g).2 q) = transferFunction H g q :=
  toEquiv_apply (coe_transferFunction H g) q

theorem transferTransversal_apply' (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
    (k : ZMod (minimalPeriod (g • ·) q.out)) :
    ↑(toEquiv (transferTransversal H g).2 (g ^ (cast k : ℤ) • q.out)) =
      g ^ (cast k : ℤ) * q.out.out := by
  rw [transferTransversal_apply, transferFunction_apply, ← quotientEquivSigmaZMod_symm_apply,
    apply_symm_apply]

theorem transferTransversal_apply'' (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
    (k : ZMod (minimalPeriod (g • ·) q.out)) :
    ↑(toEquiv (g • transferTransversal H g).2 (g ^ (cast k : ℤ) • q.out)) =
      if k = 0 then g ^ minimalPeriod (g • ·) q.out * q.out.out
      else g ^ (cast k : ℤ) * q.out.out := by
  rw [smul_apply_eq_smul_apply_inv_smul, transferTransversal_apply, transferFunction_apply, ←
    mul_smul, ← zpow_neg_one, ← zpow_add, quotientEquivSigmaZMod_apply, smul_eq_mul, ← mul_assoc,
    ← zpow_one_add, Int.cast_add, Int.cast_neg, Int.cast_one, intCast_cast, cast_id', id, ←
    sub_eq_neg_add, cast_sub_one, add_sub_cancel]
  by_cases hk : k = 0
  · rw [if_pos hk, if_pos hk, zpow_natCast]
  · rw [if_neg hk, if_neg hk]

end Subgroup
