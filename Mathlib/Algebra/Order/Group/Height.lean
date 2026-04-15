/-
Copyright (c) 2025 Judith Ludwig, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Junyan Xu
-/
module
public import Mathlib.Algebra.Order.Group.Convex
public import Mathlib.Data.Finite.Card
public import Mathlib.Data.Real.Embedding
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Birkhoff

/-! # Height of a totally ordered abelian group -/

public section

variable {α : Type*} [CommGroup α] [LinearOrder α]

namespace LinearOrderedCommGroup

variable (α) in
/-- The height of a totally ordered abelian group is the number of non-trivial convex subgroups. -/
@[expose, to_additive /-- The height of a totally ordered additive abelian group
is the number of non-trivial convex subgroups. -/]
noncomputable def height : ℕ∞ := .card {G : ConvexSubgroup α // G ≠ ⊥}

@[to_additive] theorem height_eq_card_convexSubgroup_sub_one :
    height α = .card (ConvexSubgroup α) - 1 := by
  apply ENat.add_right_injective_of_ne_top ENat.one_ne_top
  convert congr_arg Cardinal.toENat (Cardinal.mk_sum_compl {(⊥ : ConvexSubgroup α)})
  · simp; rfl
  · exact add_tsub_cancel_of_le ((ENat.one_le_card_iff_nonempty _).mpr inferInstance)

@[to_additive] theorem height_eq_zero_iff : height α = 0 ↔ Subsingleton α := by
  rw [height, ENat.card_eq_zero_iff_empty]
  constructor <;> intro h
  · contrapose! h; simpa using exists_ne _
  · simpa [isEmpty_iff, eq_comm] using Subsingleton.elim _

end LinearOrderedCommGroup

section

variable [IsOrderedMonoid α]

@[to_additive finite_finiteArchimedeanClass_iff_convexAddSubgroup]
lemma finite_finiteMulArchimedeanClass_iff_convexSubgroup :
    Finite (FiniteMulArchimedeanClass α) ↔ Finite (ConvexSubgroup α) := by
  rw [ConvexSubgroup.equivUpperSet.finite_iff]
  constructor <;> intro
  · rw [OrderIso.upperSetWithTopOfFinite.toEquiv.finite_iff, WithTop]; infer_instance
  · exact .of_injective _ (OrderEmbedding.infIrredUpperSet.toEmbedding.trans (.subtype _)).injective

open LinearOrderedCommGroup

@[to_additive height_eq_card_finiteArchimedeanClass]
lemma height_eq_card_finiteMulArchimedeanClass :
    height α = ENat.card (FiniteMulArchimedeanClass α) := by
  rw [height_eq_card_convexSubgroup_sub_one]
  by_cases fin : Finite (FiniteMulArchimedeanClass α)
  · simp_rw [ENat.card_congr <| ConvexSubgroup.equivUpperSet.trans
      OrderIso.upperSetWithTopOfFinite.toEquiv, ENat.card, WithTop, ← Nat.cast_card,
      Finite.card_option, Nat.cast_add, map_add, map_natCast]
    rfl
  · have := finite_finiteMulArchimedeanClass_iff_convexSubgroup.not.mp fin
    rw [not_finite_iff_infinite] at fin this
    simp_rw [ENat.card_eq_top_of_infinite]
    rfl

@[to_additive archimedean_iff_height_le_one]
lemma mulArchimedean_iff_height_le_one : MulArchimedean α ↔ height α ≤ 1 := by
  rw [height_eq_card_finiteMulArchimedeanClass, ENat.card_le_one_iff_subsingleton,
    ← FiniteMulArchimedeanClass.subsingleton_iff_mulArchimedean]

lemma mulArchimedean_iff_exists_orderMonoidHom :
    MulArchimedean α ↔ ∃ f : α →*o Multiplicative ℝ, Function.Injective f where
  mp _ := have ⟨f, hf⟩ := Archimedean.exists_orderAddMonoidHom_real_injective (Additive α)
    ⟨⟨⟨⟨f, f.map_zero⟩, f.map_add⟩, f.monotone'⟩, hf⟩
  mpr := fun ⟨f, hf⟩ ↦ .comap f.toMonoidHom (f.monotone'.strictMono_of_injective hf)

theorem MulArchimedean.tfae : List.TFAE
  [ MulArchimedean α,
    height α ≤ 1,
    ∃ f : α →*o Multiplicative ℝ, Function.Injective f] := by
  tfae_have 1 ↔ 2 := mulArchimedean_iff_height_le_one
  tfae_have 1 ↔ 3 := mulArchimedean_iff_exists_orderMonoidHom
  tfae_finish

/-- Equivalent characterisations for height 1. (Bourbaki, Eléments de mathématique. Fasc. XXX.
Algèbre commutative. Chapitre 6: Valuations. §4 No5 proposition 8) -/
theorem MulArchimedean.tfae_of_nontrivial [Nontrivial α] : List.TFAE
  [ MulArchimedean α,
    height α = 1,
    ∃ f : α →*o Multiplicative ℝ, Function.Injective f] := by
  convert MulArchimedean.tfae (α := α) using 3
  rw [le_iff_eq_or_lt, or_iff_left]
  rw [ENat.lt_one_iff_eq_zero, height_eq_zero_iff]
  exact not_subsingleton α

end

section Archimedean

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

lemma archimedean_iff_exists_orderAddMonoidHom :
    Archimedean α ↔ ∃ f : α →+o ℝ, Function.Injective f where
  mp _ := Archimedean.exists_orderAddMonoidHom_real_injective α
  mpr := fun ⟨f, hf⟩ ↦ .comap f.toAddMonoidHom (f.monotone'.strictMono_of_injective hf)

theorem Archimedean.tfae : List.TFAE
  [ Archimedean α,
    LinearOrderedAddCommGroup.height α ≤ 1,
    ∃ f : α →+o ℝ, Function.Injective f] := by
  tfae_have 1 ↔ 2 := archimedean_iff_height_le_one
  tfae_have 1 ↔ 3 := archimedean_iff_exists_orderAddMonoidHom
  tfae_finish

theorem Archimedean.tfae_of_nontrivial [Nontrivial α] : List.TFAE
  [ Archimedean α,
    LinearOrderedAddCommGroup.height α = 1,
    ∃ f : α →+o ℝ, Function.Injective f] := by
  convert Archimedean.tfae (α := α) using 3
  rw [le_iff_eq_or_lt, or_iff_left]
  rw [ENat.lt_one_iff_eq_zero, LinearOrderedAddCommGroup.height_eq_zero_iff]
  exact not_subsingleton α

end Archimedean
