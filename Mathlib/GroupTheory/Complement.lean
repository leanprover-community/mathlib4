/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Data.ZMod.Quotient

#align_import group_theory.complement from "leanprover-community/mathlib"@"6ca1a09bc9aa75824bf97388c9e3b441fc4ccf3f"

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


open BigOperators Pointwise

namespace Subgroup

variable {G : Type*} [Group G] (H K : Subgroup G) (S T : Set G)

/-- `S` and `T` are complements if `(*) : S × T → G` is a bijection.
  This notion generalizes left transversals, right transversals, and complementary subgroups. -/
@[to_additive "`S` and `T` are complements if `(+) : S × T → G` is a bijection"]
def IsComplement : Prop :=
  Function.Bijective fun x : S × T => x.1.1 * x.2.1
#align subgroup.is_complement Subgroup.IsComplement
#align add_subgroup.is_complement AddSubgroup.IsComplement

/-- `H` and `K` are complements if `(*) : H × K → G` is a bijection -/
@[to_additive "`H` and `K` are complements if `(+) : H × K → G` is a bijection"]
abbrev IsComplement' :=
  IsComplement (H : Set G) (K : Set G)
#align subgroup.is_complement' Subgroup.IsComplement'
#align add_subgroup.is_complement' AddSubgroup.IsComplement'

/-- The set of left-complements of `T : Set G` -/
@[to_additive "The set of left-complements of `T : Set G`"]
def leftTransversals : Set (Set G) :=
  { S : Set G | IsComplement S T }
#align subgroup.left_transversals Subgroup.leftTransversals
#align add_subgroup.left_transversals AddSubgroup.leftTransversals

/-- The set of right-complements of `S : Set G` -/
@[to_additive "The set of right-complements of `S : Set G`"]
def rightTransversals : Set (Set G) :=
  { T : Set G | IsComplement S T }
#align subgroup.right_transversals Subgroup.rightTransversals
#align add_subgroup.right_transversals AddSubgroup.rightTransversals

variable {H K S T}

@[to_additive]
theorem isComplement'_def : IsComplement' H K ↔ IsComplement (H : Set G) (K : Set G) :=
  Iff.rfl
#align subgroup.is_complement'_def Subgroup.isComplement'_def
#align add_subgroup.is_complement'_def AddSubgroup.isComplement'_def

@[to_additive]
theorem isComplement_iff_existsUnique :
    IsComplement S T ↔ ∀ g : G, ∃! x : S × T, x.1.1 * x.2.1 = g :=
  Function.bijective_iff_existsUnique _
#align subgroup.is_complement_iff_exists_unique Subgroup.isComplement_iff_existsUnique
#align add_subgroup.is_complement_iff_exists_unique AddSubgroup.isComplement_iff_existsUnique

@[to_additive]
theorem IsComplement.existsUnique (h : IsComplement S T) (g : G) :
    ∃! x : S × T, x.1.1 * x.2.1 = g :=
  isComplement_iff_existsUnique.mp h g
#align subgroup.is_complement.exists_unique Subgroup.IsComplement.existsUnique
#align add_subgroup.is_complement.exists_unique AddSubgroup.IsComplement.existsUnique

@[to_additive]
theorem IsComplement'.symm (h : IsComplement' H K) : IsComplement' K H := by
  let ϕ : H × K ≃ K × H :=
    Equiv.mk (fun x => ⟨x.2⁻¹, x.1⁻¹⟩) (fun x => ⟨x.2⁻¹, x.1⁻¹⟩)
      (fun x => Prod.ext (inv_inv _) (inv_inv _)) fun x => Prod.ext (inv_inv _) (inv_inv _)
  let ψ : G ≃ G := Equiv.mk (fun g : G => g⁻¹) (fun g : G => g⁻¹) inv_inv inv_inv
  -- ⊢ IsComplement' K H
  suffices hf : (ψ ∘ fun x : H × K => x.1.1 * x.2.1) = (fun x : K × H => x.1.1 * x.2.1) ∘ ϕ by
    rw [isComplement'_def, IsComplement, ← Equiv.bijective_comp ϕ]
    apply (congr_arg Function.Bijective hf).mp -- porting note: This was a `rw` in mathlib3
    rwa [ψ.comp_bijective]
  exact funext fun x => mul_inv_rev _ _
  -- 🎉 no goals
#align subgroup.is_complement'.symm Subgroup.IsComplement'.symm
#align add_subgroup.is_complement'.symm AddSubgroup.IsComplement'.symm

@[to_additive]
theorem isComplement'_comm : IsComplement' H K ↔ IsComplement' K H :=
  ⟨IsComplement'.symm, IsComplement'.symm⟩
#align subgroup.is_complement'_comm Subgroup.isComplement'_comm
#align add_subgroup.is_complement'_comm AddSubgroup.isComplement'_comm

@[to_additive]
theorem isComplement_top_singleton {g : G} : IsComplement (⊤ : Set G) {g} :=
  ⟨fun ⟨_, _, rfl⟩ ⟨_, _, rfl⟩ h => Prod.ext (Subtype.ext (mul_right_cancel h)) rfl, fun x =>
    ⟨⟨⟨x * g⁻¹, ⟨⟩⟩, g, rfl⟩, inv_mul_cancel_right x g⟩⟩
#align subgroup.is_complement_top_singleton Subgroup.isComplement_top_singleton
#align add_subgroup.is_complement_top_singleton AddSubgroup.isComplement_top_singleton

@[to_additive]
theorem isComplement_singleton_top {g : G} : IsComplement ({g} : Set G) ⊤ :=
  ⟨fun ⟨⟨_, rfl⟩, _⟩ ⟨⟨_, rfl⟩, _⟩ h => Prod.ext rfl (Subtype.ext (mul_left_cancel h)), fun x =>
    ⟨⟨⟨g, rfl⟩, g⁻¹ * x, ⟨⟩⟩, mul_inv_cancel_left g x⟩⟩
#align subgroup.is_complement_singleton_top Subgroup.isComplement_singleton_top
#align add_subgroup.is_complement_singleton_top AddSubgroup.isComplement_singleton_top

@[to_additive]
theorem isComplement_singleton_left {g : G} : IsComplement {g} S ↔ S = ⊤ := by
  refine'
    ⟨fun h => top_le_iff.mp fun x _ => _, fun h => (congr_arg _ h).mpr isComplement_singleton_top⟩
  obtain ⟨⟨⟨z, rfl : z = g⟩, y, _⟩, hy⟩ := h.2 (g * x)
  -- ⊢ x ∈ S
  rwa [← mul_left_cancel hy]
  -- 🎉 no goals
#align subgroup.is_complement_singleton_left Subgroup.isComplement_singleton_left
#align add_subgroup.is_complement_singleton_left AddSubgroup.isComplement_singleton_left

@[to_additive]
theorem isComplement_singleton_right {g : G} : IsComplement S {g} ↔ S = ⊤ := by
  refine'
    ⟨fun h => top_le_iff.mp fun x _ => _, fun h => h ▸ isComplement_top_singleton⟩
  obtain ⟨y, hy⟩ := h.2 (x * g)
  -- ⊢ x ∈ S
  conv_rhs at hy => rw [← show y.2.1 = g from y.2.2]
  -- ⊢ x ∈ S
  rw [← mul_right_cancel hy]
  -- ⊢ ↑y.fst ∈ S
  exact y.1.2
  -- 🎉 no goals
#align subgroup.is_complement_singleton_right Subgroup.isComplement_singleton_right
#align add_subgroup.is_complement_singleton_right AddSubgroup.isComplement_singleton_right

@[to_additive]
theorem isComplement_top_left : IsComplement ⊤ S ↔ ∃ g : G, S = {g} := by
  refine'
    ⟨fun h => Set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨_, fun a ha b hb => _⟩, _⟩
  · obtain ⟨a, _⟩ := h.2 1
    -- ⊢ Set.Nonempty S
    exact ⟨a.2.1, a.2.2⟩
    -- 🎉 no goals
  · have : (⟨⟨_, mem_top a⁻¹⟩, ⟨a, ha⟩⟩ : (⊤ : Set G) × S) = ⟨⟨_, mem_top b⁻¹⟩, ⟨b, hb⟩⟩ :=
      h.1 ((inv_mul_self a).trans (inv_mul_self b).symm)
    exact Subtype.ext_iff.mp (Prod.ext_iff.mp this).2
    -- 🎉 no goals
  · rintro ⟨g, rfl⟩
    -- ⊢ IsComplement ⊤ {g}
    exact isComplement_top_singleton
    -- 🎉 no goals
#align subgroup.is_complement_top_left Subgroup.isComplement_top_left
#align add_subgroup.is_complement_top_left AddSubgroup.isComplement_top_left

@[to_additive]
theorem isComplement_top_right : IsComplement S ⊤ ↔ ∃ g : G, S = {g} := by
  refine'
    ⟨fun h => Set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨_, fun a ha b hb => _⟩, _⟩
  · obtain ⟨a, _⟩ := h.2 1
    -- ⊢ Set.Nonempty S
    exact ⟨a.1.1, a.1.2⟩
    -- 🎉 no goals
  · have : (⟨⟨a, ha⟩, ⟨_, mem_top a⁻¹⟩⟩ : S × (⊤ : Set G)) = ⟨⟨b, hb⟩, ⟨_, mem_top b⁻¹⟩⟩ :=
      h.1 ((mul_inv_self a).trans (mul_inv_self b).symm)
    exact Subtype.ext_iff.mp (Prod.ext_iff.mp this).1
    -- 🎉 no goals
  · rintro ⟨g, rfl⟩
    -- ⊢ IsComplement {g} ⊤
    exact isComplement_singleton_top
    -- 🎉 no goals
#align subgroup.is_complement_top_right Subgroup.isComplement_top_right
#align add_subgroup.is_complement_top_right AddSubgroup.isComplement_top_right

@[to_additive]
theorem isComplement'_top_bot : IsComplement' (⊤ : Subgroup G) ⊥ :=
  isComplement_top_singleton
#align subgroup.is_complement'_top_bot Subgroup.isComplement'_top_bot
#align add_subgroup.is_complement'_top_bot AddSubgroup.isComplement'_top_bot

@[to_additive]
theorem isComplement'_bot_top : IsComplement' (⊥ : Subgroup G) ⊤ :=
  isComplement_singleton_top
#align subgroup.is_complement'_bot_top Subgroup.isComplement'_bot_top
#align add_subgroup.is_complement'_bot_top AddSubgroup.isComplement'_bot_top

@[to_additive (attr := simp)]
theorem isComplement'_bot_left : IsComplement' ⊥ H ↔ H = ⊤ :=
  isComplement_singleton_left.trans coe_eq_univ
#align subgroup.is_complement'_bot_left Subgroup.isComplement'_bot_left
#align add_subgroup.is_complement'_bot_left AddSubgroup.isComplement'_bot_left

@[to_additive (attr := simp)]
theorem isComplement'_bot_right : IsComplement' H ⊥ ↔ H = ⊤ :=
  isComplement_singleton_right.trans coe_eq_univ
#align subgroup.is_complement'_bot_right Subgroup.isComplement'_bot_right
#align add_subgroup.is_complement'_bot_right AddSubgroup.isComplement'_bot_right

@[to_additive (attr := simp)]
theorem isComplement'_top_left : IsComplement' ⊤ H ↔ H = ⊥ :=
  isComplement_top_left.trans coe_eq_singleton
#align subgroup.is_complement'_top_left Subgroup.isComplement'_top_left
#align add_subgroup.is_complement'_top_left AddSubgroup.isComplement'_top_left

@[to_additive (attr := simp)]
theorem isComplement'_top_right : IsComplement' H ⊤ ↔ H = ⊥ :=
  isComplement_top_right.trans coe_eq_singleton
#align subgroup.is_complement'_top_right Subgroup.isComplement'_top_right
#align add_subgroup.is_complement'_top_right AddSubgroup.isComplement'_top_right

@[to_additive]
theorem mem_leftTransversals_iff_existsUnique_inv_mul_mem :
    S ∈ leftTransversals T ↔ ∀ g : G, ∃! s : S, (s : G)⁻¹ * g ∈ T := by
  rw [leftTransversals, Set.mem_setOf_eq, isComplement_iff_existsUnique]
  -- ⊢ (∀ (g : G), ∃! x, ↑x.fst * ↑x.snd = g) ↔ ∀ (g : G), ∃! s, (↑s)⁻¹ * g ∈ T
  refine' ⟨fun h g => _, fun h g => _⟩
  -- ⊢ ∃! s, (↑s)⁻¹ * g ∈ T
  · obtain ⟨x, h1, h2⟩ := h g
    -- ⊢ ∃! s, (↑s)⁻¹ * g ∈ T
    exact
      ⟨x.1, (congr_arg (· ∈ T) (eq_inv_mul_of_mul_eq h1)).mp x.2.2, fun y hy =>
        (Prod.ext_iff.mp (h2 ⟨y, (↑y)⁻¹ * g, hy⟩ (mul_inv_cancel_left ↑y g))).1⟩
  · obtain ⟨x, h1, h2⟩ := h g
    -- ⊢ ∃! x, ↑x.fst * ↑x.snd = g
    refine' ⟨⟨x, (↑x)⁻¹ * g, h1⟩, mul_inv_cancel_left (↑x) g, fun y hy => _⟩
    -- ⊢ y = (x, { val := (↑x)⁻¹ * g, property := h1 })
    have hf := h2 y.1 ((congr_arg (· ∈ T) (eq_inv_mul_of_mul_eq hy)).mp y.2.2)
    -- ⊢ y = (x, { val := (↑x)⁻¹ * g, property := h1 })
    exact Prod.ext hf (Subtype.ext (eq_inv_mul_of_mul_eq (hf ▸ hy)))
    -- 🎉 no goals
#align subgroup.mem_left_transversals_iff_exists_unique_inv_mul_mem Subgroup.mem_leftTransversals_iff_existsUnique_inv_mul_mem
#align add_subgroup.mem_left_transversals_iff_exists_unique_neg_add_mem AddSubgroup.mem_leftTransversals_iff_existsUnique_neg_add_mem

@[to_additive]
theorem mem_rightTransversals_iff_existsUnique_mul_inv_mem :
    S ∈ rightTransversals T ↔ ∀ g : G, ∃! s : S, g * (s : G)⁻¹ ∈ T := by
  rw [rightTransversals, Set.mem_setOf_eq, isComplement_iff_existsUnique]
  -- ⊢ (∀ (g : G), ∃! x, ↑x.fst * ↑x.snd = g) ↔ ∀ (g : G), ∃! s, g * (↑s)⁻¹ ∈ T
  refine' ⟨fun h g => _, fun h g => _⟩
  -- ⊢ ∃! s, g * (↑s)⁻¹ ∈ T
  · obtain ⟨x, h1, h2⟩ := h g
    -- ⊢ ∃! s, g * (↑s)⁻¹ ∈ T
    exact
      ⟨x.2, (congr_arg (· ∈ T) (eq_mul_inv_of_mul_eq h1)).mp x.1.2, fun y hy =>
        (Prod.ext_iff.mp (h2 ⟨⟨g * (↑y)⁻¹, hy⟩, y⟩ (inv_mul_cancel_right g y))).2⟩
  · obtain ⟨x, h1, h2⟩ := h g
    -- ⊢ ∃! x, ↑x.fst * ↑x.snd = g
    refine' ⟨⟨⟨g * (↑x)⁻¹, h1⟩, x⟩, inv_mul_cancel_right g x, fun y hy => _⟩
    -- ⊢ y = ({ val := g * (↑x)⁻¹, property := h1 }, x)
    have hf := h2 y.2 ((congr_arg (· ∈ T) (eq_mul_inv_of_mul_eq hy)).mp y.1.2)
    -- ⊢ y = ({ val := g * (↑x)⁻¹, property := h1 }, x)
    exact Prod.ext (Subtype.ext (eq_mul_inv_of_mul_eq (hf ▸ hy))) hf
    -- 🎉 no goals
#align subgroup.mem_right_transversals_iff_exists_unique_mul_inv_mem Subgroup.mem_rightTransversals_iff_existsUnique_mul_inv_mem
#align add_subgroup.mem_right_transversals_iff_exists_unique_add_neg_mem AddSubgroup.mem_rightTransversals_iff_existsUnique_add_neg_mem

@[to_additive]
theorem mem_leftTransversals_iff_existsUnique_quotient_mk''_eq :
    S ∈ leftTransversals (H : Set G) ↔
      ∀ q : Quotient (QuotientGroup.leftRel H), ∃! s : S, Quotient.mk'' s.1 = q := by
  simp_rw [mem_leftTransversals_iff_existsUnique_inv_mul_mem, SetLike.mem_coe, ←
    QuotientGroup.eq']
  exact ⟨fun h q => Quotient.inductionOn' q h, fun h g => h (Quotient.mk'' g)⟩
  -- 🎉 no goals
#align subgroup.mem_left_transversals_iff_exists_unique_quotient_mk'_eq Subgroup.mem_leftTransversals_iff_existsUnique_quotient_mk''_eq
#align add_subgroup.mem_left_transversals_iff_exists_unique_quotient_mk'_eq AddSubgroup.mem_leftTransversals_iff_existsUnique_quotient_mk''_eq

@[to_additive]
theorem mem_rightTransversals_iff_existsUnique_quotient_mk''_eq :
    S ∈ rightTransversals (H : Set G) ↔
      ∀ q : Quotient (QuotientGroup.rightRel H), ∃! s : S, Quotient.mk'' s.1 = q := by
  simp_rw [mem_rightTransversals_iff_existsUnique_mul_inv_mem, SetLike.mem_coe, ←
    QuotientGroup.rightRel_apply, ← Quotient.eq'']
  exact ⟨fun h q => Quotient.inductionOn' q h, fun h g => h (Quotient.mk'' g)⟩
  -- 🎉 no goals
#align subgroup.mem_right_transversals_iff_exists_unique_quotient_mk'_eq Subgroup.mem_rightTransversals_iff_existsUnique_quotient_mk''_eq
#align add_subgroup.mem_right_transversals_iff_exists_unique_quotient_mk'_eq AddSubgroup.mem_rightTransversals_iff_existsUnique_quotient_mk''_eq

@[to_additive]
theorem mem_leftTransversals_iff_bijective :
    S ∈ leftTransversals (H : Set G) ↔
      Function.Bijective (S.restrict (Quotient.mk'' : G → Quotient (QuotientGroup.leftRel H))) :=
  mem_leftTransversals_iff_existsUnique_quotient_mk''_eq.trans
    (Function.bijective_iff_existsUnique (S.restrict Quotient.mk'')).symm
#align subgroup.mem_left_transversals_iff_bijective Subgroup.mem_leftTransversals_iff_bijective
#align add_subgroup.mem_left_transversals_iff_bijective AddSubgroup.mem_leftTransversals_iff_bijective

@[to_additive]
theorem mem_rightTransversals_iff_bijective :
    S ∈ rightTransversals (H : Set G) ↔
      Function.Bijective (S.restrict (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H))) :=
  mem_rightTransversals_iff_existsUnique_quotient_mk''_eq.trans
    (Function.bijective_iff_existsUnique (S.restrict Quotient.mk'')).symm
#align subgroup.mem_right_transversals_iff_bijective Subgroup.mem_rightTransversals_iff_bijective
#align add_subgroup.mem_right_transversals_iff_bijective AddSubgroup.mem_rightTransversals_iff_bijective

@[to_additive]
theorem card_left_transversal (h : S ∈ leftTransversals (H : Set G)) : Nat.card S = H.index :=
  Nat.card_congr <| Equiv.ofBijective _ <| mem_leftTransversals_iff_bijective.mp h
#align subgroup.card_left_transversal Subgroup.card_left_transversal
#align add_subgroup.card_left_transversal AddSubgroup.card_left_transversal

@[to_additive]
theorem card_right_transversal (h : S ∈ rightTransversals (H : Set G)) : Nat.card S = H.index :=
  Nat.card_congr <|
    (Equiv.ofBijective _ <| mem_rightTransversals_iff_bijective.mp h).trans <|
      QuotientGroup.quotientRightRelEquivQuotientLeftRel H
#align subgroup.card_right_transversal Subgroup.card_right_transversal
#align add_subgroup.card_right_transversal AddSubgroup.card_right_transversal

@[to_additive]
theorem range_mem_leftTransversals {f : G ⧸ H → G} (hf : ∀ q, ↑(f q) = q) :
    Set.range f ∈ leftTransversals (H : Set G) :=
  mem_leftTransversals_iff_bijective.mpr
    ⟨by rintro ⟨-, q₁, rfl⟩ ⟨-, q₂, rfl⟩ h
        -- ⊢ { val := f q₁, property := (_ : ∃ y, f y = f q₁) } = { val := f q₂, property …
        exact Subtype.ext $ congr_arg f $ ((hf q₁).symm.trans h).trans (hf q₂),
        -- 🎉 no goals
      fun q => ⟨⟨f q, q, rfl⟩, hf q⟩⟩
#align subgroup.range_mem_left_transversals Subgroup.range_mem_leftTransversals
#align add_subgroup.range_mem_left_transversals AddSubgroup.range_mem_leftTransversals

@[to_additive]
theorem range_mem_rightTransversals {f : Quotient (QuotientGroup.rightRel H) → G}
    (hf : ∀ q, Quotient.mk'' (f q) = q) : Set.range f ∈ rightTransversals (H : Set G) :=
  mem_rightTransversals_iff_bijective.mpr
    ⟨by rintro ⟨-, q₁, rfl⟩ ⟨-, q₂, rfl⟩ h
        -- ⊢ { val := f q₁, property := (_ : ∃ y, f y = f q₁) } = { val := f q₂, property …
        exact Subtype.ext $ congr_arg f $ ((hf q₁).symm.trans h).trans (hf q₂),
        -- 🎉 no goals
      fun q => ⟨⟨f q, q, rfl⟩, hf q⟩⟩
#align subgroup.range_mem_right_transversals Subgroup.range_mem_rightTransversals
#align add_subgroup.range_mem_right_transversals AddSubgroup.range_mem_rightTransversals

@[to_additive]
theorem exists_left_transversal (g : G) : ∃ S ∈ leftTransversals (H : Set G), g ∈ S := by
  classical
    refine'
      ⟨Set.range (Function.update Quotient.out' _ g), range_mem_leftTransversals fun q => _,
        Quotient.mk'' g, Function.update_same (Quotient.mk'' g) g Quotient.out'⟩
    by_cases hq : q = Quotient.mk'' g
    · exact hq.symm ▸ congr_arg _ (Function.update_same (Quotient.mk'' g) g Quotient.out')
    · refine' (Function.update_noteq _ g Quotient.out') ▸ q.out_eq'
      exact hq
#align subgroup.exists_left_transversal Subgroup.exists_left_transversal
#align add_subgroup.exists_left_transversal AddSubgroup.exists_left_transversal

@[to_additive]
theorem exists_right_transversal (g : G) : ∃ S ∈ rightTransversals (H : Set G), g ∈ S := by
  classical
    refine'
      ⟨Set.range (Function.update Quotient.out' _ g), range_mem_rightTransversals fun q => _,
        Quotient.mk'' g, Function.update_same (Quotient.mk'' g) g Quotient.out'⟩
    by_cases hq : q = Quotient.mk'' g
    · exact hq.symm ▸ congr_arg _ (Function.update_same (Quotient.mk'' g) g Quotient.out')
    · exact Eq.trans (congr_arg _ (Function.update_noteq hq g Quotient.out')) q.out_eq'
#align subgroup.exists_right_transversal Subgroup.exists_right_transversal
#align add_subgroup.exists_right_transversal AddSubgroup.exists_right_transversal

namespace MemLeftTransversals

/-- A left transversal is in bijection with left cosets. -/
@[to_additive "A left transversal is in bijection with left cosets."]
noncomputable def toEquiv (hS : S ∈ Subgroup.leftTransversals (H : Set G)) : G ⧸ H ≃ S :=
  (Equiv.ofBijective _ (Subgroup.mem_leftTransversals_iff_bijective.mp hS)).symm
#align subgroup.mem_left_transversals.to_equiv Subgroup.MemLeftTransversals.toEquiv
#align add_subgroup.mem_left_transversals.to_equiv AddSubgroup.MemLeftTransversals.toEquiv

@[to_additive]
theorem mk''_toEquiv (hS : S ∈ Subgroup.leftTransversals (H : Set G)) (q : G ⧸ H) :
    Quotient.mk'' (toEquiv hS q : G) = q :=
  (toEquiv hS).symm_apply_apply q
#align subgroup.mem_left_transversals.mk'_to_equiv Subgroup.MemLeftTransversals.mk''_toEquiv
#align add_subgroup.mem_left_transversals.mk'_to_equiv AddSubgroup.MemLeftTransversals.mk''_toEquiv

@[to_additive]
theorem toEquiv_apply {f : G ⧸ H → G} (hf : ∀ q, (f q : G ⧸ H) = q) (q : G ⧸ H) :
    (toEquiv (range_mem_leftTransversals hf) q : G) = f q := by
  refine' (Subtype.ext_iff.mp _).trans (Subtype.coe_mk (f q) ⟨q, rfl⟩)
  -- ⊢ ↑(toEquiv (_ : (Set.range fun q => f q) ∈ leftTransversals ↑H)) q = { val := …
  exact (toEquiv (range_mem_leftTransversals hf)).apply_eq_iff_eq_symm_apply.mpr (hf q).symm
  -- 🎉 no goals
#align subgroup.mem_left_transversals.to_equiv_apply Subgroup.MemLeftTransversals.toEquiv_apply
#align add_subgroup.mem_left_transversals.to_equiv_apply AddSubgroup.MemLeftTransversals.toEquiv_apply

/-- A left transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that left coset. -/
@[to_additive "A left transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that left coset."]
noncomputable def toFun (hS : S ∈ Subgroup.leftTransversals (H : Set G)) : G → S :=
  toEquiv hS ∘ Quotient.mk''
#align subgroup.mem_left_transversals.to_fun Subgroup.MemLeftTransversals.toFun
#align add_subgroup.mem_left_transversals.to_fun AddSubgroup.MemLeftTransversals.toFun

@[to_additive]
theorem inv_toFun_mul_mem (hS : S ∈ Subgroup.leftTransversals (H : Set G)) (g : G) :
    (toFun hS g : G)⁻¹ * g ∈ H :=
  QuotientGroup.leftRel_apply.mp <| Quotient.exact' <| mk''_toEquiv _ _
#align subgroup.mem_left_transversals.inv_to_fun_mul_mem Subgroup.MemLeftTransversals.inv_toFun_mul_mem
#align add_subgroup.mem_left_transversals.neg_to_fun_add_mem AddSubgroup.MemLeftTransversals.neg_toFun_add_mem

@[to_additive]
theorem inv_mul_toFun_mem (hS : S ∈ Subgroup.leftTransversals (H : Set G)) (g : G) :
    g⁻¹ * toFun hS g ∈ H :=
  (congr_arg (· ∈ H) (by rw [mul_inv_rev, inv_inv])).mp (H.inv_mem (inv_toFun_mul_mem hS g))
                         -- 🎉 no goals
#align subgroup.mem_left_transversals.inv_mul_to_fun_mem Subgroup.MemLeftTransversals.inv_mul_toFun_mem
#align add_subgroup.mem_left_transversals.neg_add_to_fun_mem AddSubgroup.MemLeftTransversals.neg_add_toFun_mem

end MemLeftTransversals

namespace MemRightTransversals

/-- A right transversal is in bijection with right cosets. -/
@[to_additive "A right transversal is in bijection with right cosets."]
noncomputable def toEquiv (hS : S ∈ Subgroup.rightTransversals (H : Set G)) :
    Quotient (QuotientGroup.rightRel H) ≃ S :=
  (Equiv.ofBijective _ (Subgroup.mem_rightTransversals_iff_bijective.mp hS)).symm
#align subgroup.mem_right_transversals.to_equiv Subgroup.MemRightTransversals.toEquiv
#align add_subgroup.mem_right_transversals.to_equiv AddSubgroup.MemRightTransversals.toEquiv

@[to_additive]
theorem mk''_toEquiv (hS : S ∈ Subgroup.rightTransversals (H : Set G))
    (q : Quotient (QuotientGroup.rightRel H)) : Quotient.mk'' (toEquiv hS q : G) = q :=
  (toEquiv hS).symm_apply_apply q
#align subgroup.mem_right_transversals.mk'_to_equiv Subgroup.MemRightTransversals.mk''_toEquiv
#align add_subgroup.mem_right_transversals.mk'_to_equiv AddSubgroup.MemRightTransversals.mk''_toEquiv

@[to_additive]
theorem toEquiv_apply {f : Quotient (QuotientGroup.rightRel H) → G}
    (hf : ∀ q, Quotient.mk'' (f q) = q) (q : Quotient (QuotientGroup.rightRel H)) :
    (toEquiv (range_mem_rightTransversals hf) q : G) = f q := by
  refine' (Subtype.ext_iff.mp _).trans (Subtype.coe_mk (f q) ⟨q, rfl⟩)
  -- ⊢ ↑(toEquiv (_ : (Set.range fun q => f q) ∈ rightTransversals ↑H)) q = { val : …
  exact (toEquiv (range_mem_rightTransversals hf)).apply_eq_iff_eq_symm_apply.mpr (hf q).symm
  -- 🎉 no goals
#align subgroup.mem_right_transversals.to_equiv_apply Subgroup.MemRightTransversals.toEquiv_apply
#align add_subgroup.mem_right_transversals.to_equiv_apply AddSubgroup.MemRightTransversals.toEquiv_apply

/-- A right transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that right coset. -/
@[to_additive "A right transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that right coset."]
noncomputable def toFun (hS : S ∈ Subgroup.rightTransversals (H : Set G)) : G → S :=
  toEquiv hS ∘ Quotient.mk''
#align subgroup.mem_right_transversals.to_fun Subgroup.MemRightTransversals.toFun
#align add_subgroup.mem_right_transversals.to_fun AddSubgroup.MemRightTransversals.toFun

@[to_additive]
theorem mul_inv_toFun_mem (hS : S ∈ Subgroup.rightTransversals (H : Set G)) (g : G) :
    g * (toFun hS g : G)⁻¹ ∈ H :=
  QuotientGroup.rightRel_apply.mp <| Quotient.exact' <| mk''_toEquiv _ _
#align subgroup.mem_right_transversals.mul_inv_to_fun_mem Subgroup.MemRightTransversals.mul_inv_toFun_mem
#align add_subgroup.mem_right_transversals.add_neg_to_fun_mem AddSubgroup.MemRightTransversals.add_neg_toFun_mem

@[to_additive]
theorem toFun_mul_inv_mem (hS : S ∈ Subgroup.rightTransversals (H : Set G)) (g : G) :
    (toFun hS g : G) * g⁻¹ ∈ H :=
  (congr_arg (· ∈ H) (by rw [mul_inv_rev, inv_inv])).mp (H.inv_mem (mul_inv_toFun_mem hS g))
                         -- 🎉 no goals
#align subgroup.mem_right_transversals.to_fun_mul_inv_mem Subgroup.MemRightTransversals.toFun_mul_inv_mem
#align add_subgroup.mem_right_transversals.to_fun_add_neg_mem AddSubgroup.MemRightTransversals.toFun_add_neg_mem

end MemRightTransversals

section Action

open Pointwise MulAction MemLeftTransversals

variable {F : Type*} [Group F] [MulAction F G] [QuotientAction F H]

@[to_additive]
noncomputable instance : MulAction F (leftTransversals (H : Set G)) where
  smul f T :=
    ⟨f • (T : Set G), by
      refine' mem_leftTransversals_iff_existsUnique_inv_mul_mem.mpr fun g => _
      -- ⊢ ∃! s, (↑s)⁻¹ * g ∈ ↑H
      obtain ⟨t, ht1, ht2⟩ := mem_leftTransversals_iff_existsUnique_inv_mul_mem.mp T.2 (f⁻¹ • g)
      -- ⊢ ∃! s, (↑s)⁻¹ * g ∈ ↑H
      refine' ⟨⟨f • (t : G), Set.smul_mem_smul_set t.2⟩, _, _⟩
      -- ⊢ (fun s => (↑s)⁻¹ * g ∈ ↑H) { val := f • ↑t, property := (_ : f • ↑t ∈ f • ↑T …
      · exact smul_inv_smul f g ▸ QuotientAction.inv_mul_mem f ht1
        -- 🎉 no goals
      · rintro ⟨-, t', ht', rfl⟩ h
        -- ⊢ { val := (fun x => f • x) t', property := (_ : ∃ a, a ∈ ↑T ∧ (fun x => f • x …
        replace h := QuotientAction.inv_mul_mem f⁻¹ h
        -- ⊢ { val := (fun x => f • x) t', property := (_ : ∃ a, a ∈ ↑T ∧ (fun x => f • x …
        simp only [Subtype.ext_iff, Subtype.coe_mk, smul_left_cancel_iff, inv_smul_smul] at h ⊢
        -- ⊢ t' = ↑t
        exact Subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ h)⟩
        -- 🎉 no goals
  one_smul T := Subtype.ext (one_smul F (T : Set G))
  mul_smul f₁ f₂ T := Subtype.ext (mul_smul f₁ f₂ (T : Set G))

@[to_additive]
theorem smul_toFun (f : F) (T : leftTransversals (H : Set G)) (g : G) :
    (f • (toFun T.2 g : G)) = toFun (f • T).2 (f • g) :=
  Subtype.ext_iff.mp $ @ExistsUnique.unique (↥(f • (T : Set G))) (fun s => (↑s)⁻¹ * f • g ∈ H)
    (mem_leftTransversals_iff_existsUnique_inv_mul_mem.mp (f • T).2 (f • g))
    ⟨f • (toFun T.2 g : G), Set.smul_mem_smul_set (Subtype.coe_prop _)⟩ (toFun (f • T).2 (f • g))
    (QuotientAction.inv_mul_mem f (inv_toFun_mul_mem T.2 g)) (inv_toFun_mul_mem (f • T).2 (f • g))
#align subgroup.smul_to_fun Subgroup.smul_toFun
#align add_subgroup.vadd_to_fun AddSubgroup.vadd_toFun

@[to_additive]
theorem smul_toEquiv (f : F) (T : leftTransversals (H : Set G)) (q : G ⧸ H) :
    f • (toEquiv T.2 q : G) = toEquiv (f • T).2 (f • q) :=
  Quotient.inductionOn' q fun g => smul_toFun f T g
#align subgroup.smul_to_equiv Subgroup.smul_toEquiv
#align add_subgroup.vadd_to_equiv AddSubgroup.vadd_toEquiv

@[to_additive]
theorem smul_apply_eq_smul_apply_inv_smul (f : F) (T : leftTransversals (H : Set G)) (q : G ⧸ H) :
    (toEquiv (f • T).2 q : G) = f • (toEquiv T.2 (f⁻¹ • q) : G) := by
  rw [smul_toEquiv, smul_inv_smul]
  -- 🎉 no goals
#align subgroup.smul_apply_eq_smul_apply_inv_smul Subgroup.smul_apply_eq_smul_apply_inv_smul
#align add_subgroup.vadd_apply_eq_vadd_apply_neg_vadd AddSubgroup.vadd_apply_eq_vadd_apply_neg_vadd

end Action

@[to_additive]
instance : Inhabited (leftTransversals (H : Set G)) :=
  ⟨⟨Set.range Quotient.out', range_mem_leftTransversals Quotient.out_eq'⟩⟩

@[to_additive]
instance : Inhabited (rightTransversals (H : Set G)) :=
  ⟨⟨Set.range Quotient.out', range_mem_rightTransversals Quotient.out_eq'⟩⟩

theorem IsComplement'.isCompl (h : IsComplement' H K) : IsCompl H K := by
  refine'
    ⟨disjoint_iff_inf_le.mpr fun g ⟨p, q⟩ =>
        let x : H × K := ⟨⟨g, p⟩, 1⟩
        let y : H × K := ⟨1, g, q⟩
        Subtype.ext_iff.mp
          (Prod.ext_iff.mp (show x = y from h.1 ((mul_one g).trans (one_mul g).symm))).1,
      codisjoint_iff_le_sup.mpr fun g _ => _⟩
  obtain ⟨⟨h, k⟩, rfl⟩ := h.2 g
  -- ⊢ (fun x => ↑x.fst * ↑x.snd) (h, k) ∈ H ⊔ K
  exact Subgroup.mul_mem_sup h.2 k.2
  -- 🎉 no goals
#align subgroup.is_complement'.is_compl Subgroup.IsComplement'.isCompl

theorem IsComplement'.sup_eq_top (h : IsComplement' H K) : H ⊔ K = ⊤ :=
  h.isCompl.sup_eq_top
#align subgroup.is_complement'.sup_eq_top Subgroup.IsComplement'.sup_eq_top

theorem IsComplement'.disjoint (h : IsComplement' H K) : Disjoint H K :=
  h.isCompl.disjoint
#align subgroup.is_complement'.disjoint Subgroup.IsComplement'.disjoint

theorem IsComplement'.index_eq_card (h : IsComplement' H K) : K.index = Nat.card H :=
  (card_left_transversal h).symm
#align subgroup.is_complement'.index_eq_card Subgroup.IsComplement'.index_eq_card

theorem IsComplement.card_mul [Fintype G] [Fintype S] [Fintype T] (h : IsComplement S T) :
    Fintype.card S * Fintype.card T = Fintype.card G :=
  (Fintype.card_prod _ _).symm.trans (Fintype.card_of_bijective h)
#align subgroup.is_complement.card_mul Subgroup.IsComplement.card_mul

theorem IsComplement'.card_mul [Fintype G] [Fintype H] [Fintype K] (h : IsComplement' H K) :
    Fintype.card H * Fintype.card K = Fintype.card G :=
  IsComplement.card_mul h
#align subgroup.is_complement'.card_mul Subgroup.IsComplement'.card_mul

theorem isComplement'_of_disjoint_and_mul_eq_univ (h1 : Disjoint H K)
    (h2 : ↑H * ↑K = (Set.univ : Set G)) : IsComplement' H K := by
  refine' ⟨mul_injective_of_disjoint h1, fun g => _⟩
  -- ⊢ ∃ a, (fun x => ↑x.fst * ↑x.snd) a = g
  obtain ⟨h, k, hh, hk, hg⟩ := Set.eq_univ_iff_forall.mp h2 g
  -- ⊢ ∃ a, (fun x => ↑x.fst * ↑x.snd) a = g
  exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), hg⟩
  -- 🎉 no goals
#align subgroup.is_complement'_of_disjoint_and_mul_eq_univ Subgroup.isComplement'_of_disjoint_and_mul_eq_univ

theorem isComplement'_of_card_mul_and_disjoint [Fintype G] [Fintype H] [Fintype K]
    (h1 : Fintype.card H * Fintype.card K = Fintype.card G) (h2 : Disjoint H K) :
    IsComplement' H K :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨mul_injective_of_disjoint h2, (Fintype.card_prod H K).trans h1⟩
#align subgroup.is_complement'_of_card_mul_and_disjoint Subgroup.isComplement'_of_card_mul_and_disjoint

theorem isComplement'_iff_card_mul_and_disjoint [Fintype G] [Fintype H] [Fintype K] :
    IsComplement' H K ↔ Fintype.card H * Fintype.card K = Fintype.card G ∧ Disjoint H K :=
  ⟨fun h => ⟨h.card_mul, h.disjoint⟩, fun h => isComplement'_of_card_mul_and_disjoint h.1 h.2⟩
#align subgroup.is_complement'_iff_card_mul_and_disjoint Subgroup.isComplement'_iff_card_mul_and_disjoint

theorem isComplement'_of_coprime [Fintype G] [Fintype H] [Fintype K]
    (h1 : Fintype.card H * Fintype.card K = Fintype.card G)
    (h2 : Nat.coprime (Fintype.card H) (Fintype.card K)) : IsComplement' H K :=
  isComplement'_of_card_mul_and_disjoint h1 (disjoint_iff.mpr (inf_eq_bot_of_coprime h2))
#align subgroup.is_complement'_of_coprime Subgroup.isComplement'_of_coprime

theorem isComplement'_stabilizer {α : Type*} [MulAction G α] (a : α)
    (h1 : ∀ h : H, h • a = a → h = 1) (h2 : ∀ g : G, ∃ h : H, h • g • a = a) :
    IsComplement' H (MulAction.stabilizer G a) := by
  refine' isComplement_iff_existsUnique.mpr fun g => _
  -- ⊢ ∃! x, ↑x.fst * ↑x.snd = g
  obtain ⟨h, hh⟩ := h2 g
  -- ⊢ ∃! x, ↑x.fst * ↑x.snd = g
  have hh' : (↑h * g) • a = a := by rwa [mul_smul]
  -- ⊢ ∃! x, ↑x.fst * ↑x.snd = g
  refine' ⟨⟨h⁻¹, h * g, hh'⟩, inv_mul_cancel_left ↑h g, _⟩
  -- ⊢ ∀ (y : ↑↑H × ↑↑(MulAction.stabilizer G a)), (fun x => ↑x.fst * ↑x.snd = g) y …
  rintro ⟨h', g, hg : g • a = a⟩ rfl
  -- ⊢ (h', { val := g, property := hg }) = (h⁻¹, { val := ↑h * (↑(h', { val := g,  …
  specialize h1 (h * h') (by rwa [mul_smul, smul_def h', ← hg, ← mul_smul, hg])
  -- ⊢ (h', { val := g, property := hg }) = (h⁻¹, { val := ↑h * (↑(h', { val := g,  …
  refine' Prod.ext (eq_inv_of_mul_eq_one_right h1) (Subtype.ext _)
  -- ⊢ ↑(h', { val := g, property := hg }).snd = ↑(h⁻¹, { val := ↑h * (↑(h', { val  …
  rwa [Subtype.ext_iff, coe_one, coe_mul, ← self_eq_mul_left, mul_assoc (↑h) (↑h') g] at h1
  -- 🎉 no goals
#align subgroup.is_complement'_stabilizer Subgroup.isComplement'_stabilizer

end Subgroup

namespace Subgroup

open Equiv Function MemLeftTransversals MulAction MulAction.quotient ZMod

universe u

variable {G : Type u} [Group G] (H : Subgroup G) (g : G)

/-- Partition `G ⧸ H` into orbits of the action of `g : G`. -/
noncomputable def quotientEquivSigmaZMod :
    G ⧸ H ≃ Σq : orbitRel.Quotient (zpowers g) (G ⧸ H), ZMod (minimalPeriod ((· • ·) g) q.out') :=
  (selfEquivSigmaOrbits (zpowers g) (G ⧸ H)).trans
    (sigmaCongrRight fun q => orbitZpowersEquiv g q.out')
#align subgroup.quotient_equiv_sigma_zmod Subgroup.quotientEquivSigmaZMod

theorem quotientEquivSigmaZMod_symm_apply (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
    (k : ZMod (minimalPeriod ((· • ·) g) q.out')) :
    (quotientEquivSigmaZMod H g).symm ⟨q, k⟩ = g ^ (k : ℤ) • q.out' :=
  rfl
#align subgroup.quotient_equiv_sigma_zmod_symm_apply Subgroup.quotientEquivSigmaZMod_symm_apply

theorem quotientEquivSigmaZMod_apply (q : orbitRel.Quotient (zpowers g) (G ⧸ H)) (k : ℤ) :
    quotientEquivSigmaZMod H g (g ^ k • q.out') = ⟨q, k⟩ := by
  rw [apply_eq_iff_eq_symm_apply, quotientEquivSigmaZMod_symm_apply, ZMod.coe_int_cast,
    zpow_smul_mod_minimalPeriod]
#align subgroup.quotient_equiv_sigma_zmod_apply Subgroup.quotientEquivSigmaZMod_apply

/-- The transfer transversal as a function. Given a `⟨g⟩`-orbit `q₀, g • q₀, ..., g ^ (m - 1) • q₀`
  in `G ⧸ H`, an element `g ^ k • q₀` is mapped to `g ^ k • g₀` for a fixed choice of
  representative `g₀` of `q₀`. -/
noncomputable def transferFunction : G ⧸ H → G := fun q =>
  g ^ ((quotientEquivSigmaZMod H g q).2 : ℤ) * (quotientEquivSigmaZMod H g q).1.out'.out'
#align subgroup.transfer_function Subgroup.transferFunction

theorem transferFunction_apply (q : G ⧸ H) :
    transferFunction H g q =
      g ^ ((quotientEquivSigmaZMod H g q).2 : ℤ) * (quotientEquivSigmaZMod H g q).1.out'.out' :=
  rfl
#align subgroup.transfer_function_apply Subgroup.transferFunction_apply

theorem coe_transferFunction (q : G ⧸ H) : ↑(transferFunction H g q) = q := by
  rw [transferFunction_apply, ← smul_eq_mul, Quotient.coe_smul_out',
    ← quotientEquivSigmaZMod_symm_apply, Sigma.eta, symm_apply_apply]
#align subgroup.coe_transfer_function Subgroup.coe_transferFunction

/-- The transfer transversal as a set. Contains elements of the form `g ^ k • g₀` for fixed choices
  of representatives `g₀` of fixed choices of representatives `q₀` of `⟨g⟩`-orbits in `G ⧸ H`. -/
def transferSet : Set G :=
  Set.range (transferFunction H g)
#align subgroup.transfer_set Subgroup.transferSet

theorem mem_transferSet (q : G ⧸ H) : transferFunction H g q ∈ transferSet H g :=
  ⟨q, rfl⟩
#align subgroup.mem_transfer_set Subgroup.mem_transferSet

/-- The transfer transversal. Contains elements of the form `g ^ k • g₀` for fixed choices
  of representatives `g₀` of fixed choices of representatives `q₀` of `⟨g⟩`-orbits in `G ⧸ H`. -/
def transferTransversal : leftTransversals (H : Set G) :=
  ⟨transferSet H g, range_mem_leftTransversals (coe_transferFunction H g)⟩
#align subgroup.transfer_transversal Subgroup.transferTransversal

theorem transferTransversal_apply (q : G ⧸ H) :
    ↑(toEquiv (transferTransversal H g).2 q) = transferFunction H g q :=
  toEquiv_apply (coe_transferFunction H g) q
#align subgroup.transfer_transversal_apply Subgroup.transferTransversal_apply

theorem transferTransversal_apply' (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
    (k : ZMod (minimalPeriod ((· • ·) g) q.out')) :
    ↑(toEquiv (transferTransversal H g).2 (g ^ (k : ℤ) • q.out')) = g ^ (k : ℤ) * q.out'.out' := by
  rw [transferTransversal_apply, transferFunction_apply, ← quotientEquivSigmaZMod_symm_apply,
    apply_symm_apply]
#align subgroup.transfer_transversal_apply' Subgroup.transferTransversal_apply'

theorem transferTransversal_apply'' (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
    (k : ZMod (minimalPeriod ((· • ·) g) q.out')) :
    ↑(toEquiv (g • transferTransversal H g).2 (g ^ (k : ℤ) • q.out')) =
      if k = 0 then g ^ minimalPeriod ((· • ·) g) q.out' * q.out'.out'
      else g ^ (k : ℤ) * q.out'.out' := by
  rw [smul_apply_eq_smul_apply_inv_smul, transferTransversal_apply, transferFunction_apply, ←
    mul_smul, ← zpow_neg_one, ← zpow_add, quotientEquivSigmaZMod_apply, smul_eq_mul, ← mul_assoc,
    ← zpow_one_add, Int.cast_add, Int.cast_neg, Int.cast_one, int_cast_cast, cast_id', id.def, ←
    sub_eq_neg_add, cast_sub_one, add_sub_cancel'_right]
  by_cases hk : k = 0
  -- ⊢ (g ^ if k = 0 then ↑(minimalPeriod ((fun x x_1 => x • x_1) g) (Quotient.out' …
  · rw [if_pos hk, if_pos hk, zpow_ofNat]
    -- 🎉 no goals
  · rw [if_neg hk, if_neg hk]
    -- 🎉 no goals
#align subgroup.transfer_transversal_apply'' Subgroup.transferTransversal_apply''

end Subgroup
