/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Data.W.Cardinal
import Mathlib.FieldTheory.Subfield
import Mathlib.Tactic.FinCases

/-!
# Cardinality of the division ring generated by a set

`Subfield.cardinal_mk_closure_le_max`: the cardinality of the (sub-)division ring
generated by a set is bounded by the cardinality of the set unless it is finite.

The method used to prove this (via `WType`) can be easily generalized to other algebraic
structures, but those cardinalities can usually be obtained by other means, using some
explicit universal objects.

-/

universe u

variable {α : Type u} (s : Set α)

namespace Subfield

private abbrev Operands : Fin 6 ⊕ s → Type
  | .inl 0 => Bool -- add
  | .inl 1 => Bool -- mul
  | .inl 2 => Unit -- neg
  | .inl 3 => Unit -- inv
  | .inl 4 => Empty -- zero
  | .inl 5 => Empty -- one
  | .inr _ => Empty -- s

variable [DivisionRing α]

private def operate : (Σ n, Operands s n → closure s) → closure s
  | ⟨.inl 0, f⟩ => f false + f true
  | ⟨.inl 1, f⟩ => f false * f true
  | ⟨.inl 2, f⟩ => - f ()
  | ⟨.inl 3, f⟩ => (f ())⁻¹
  | ⟨.inl 4, _⟩ => 0
  | ⟨.inl 5, _⟩ => 1
  | ⟨.inr a, _⟩ => ⟨a, subset_closure a.prop⟩

private def rangeOfWType : Subfield (closure s) where
  carrier := Set.range (WType.elim _ <| operate s)
  add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨WType.mk (.inl 0) (Bool.rec x y), by rfl⟩
  mul_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨WType.mk (.inl 1) (Bool.rec x y), by rfl⟩
  neg_mem' := by rintro _ ⟨x, rfl⟩; exact ⟨WType.mk (.inl 2) fun _ ↦ x, rfl⟩
  inv_mem' := by rintro _ ⟨x, rfl⟩; exact ⟨WType.mk (.inl 3) fun _ ↦ x, rfl⟩
  zero_mem' := ⟨WType.mk (.inl 4) Empty.rec, rfl⟩
  one_mem' := ⟨WType.mk (.inl 5) Empty.rec, rfl⟩

private lemma rangeOfWType_eq_top : rangeOfWType s = ⊤ := top_le_iff.mp fun a _ ↦ by
  rw [← SetLike.mem_coe, ← Subtype.val_injective.mem_set_image]
  change ↑a ∈ map (closure s).subtype _
  refine closure_le.mpr (fun a ha ↦ ?_) a.prop
  exact ⟨⟨a, subset_closure ha⟩, ⟨WType.mk (.inr ⟨a, ha⟩) Empty.rec, rfl⟩, rfl⟩

private lemma surjective_ofWType : Function.Surjective (WType.elim _ <| operate s) := by
  rw [← Set.range_iff_surjective]
  exact SetLike.coe_set_eq.mpr (rangeOfWType_eq_top s)

open Cardinal

lemma cardinal_mk_closure_le_max : #(closure s) ≤ max #s ℵ₀ :=
  (Cardinal.mk_le_of_surjective <| surjective_ofWType s).trans <| by
    convert WType.cardinal_mk_le_max_aleph0_of_finite' using 1
    · rw [lift_uzero, mk_sum, lift_uzero]
      have : lift.{u,0} #(Fin 6) < ℵ₀ := lift_lt_aleph0.mpr (lt_aleph0_of_finite _)
      obtain h|h := lt_or_le #s ℵ₀
      · rw [max_eq_right h.le, max_eq_right]
        exact (add_lt_aleph0 this h).le
      · rw [max_eq_left h, add_eq_right h (this.le.trans h), max_eq_left h]
    rintro (n|_)
    · fin_cases n <;> infer_instance
    infer_instance

lemma cardinal_mk_closure [Infinite s] : #(closure s) = #s :=
  ((cardinal_mk_closure_le_max s).trans_eq <| max_eq_left <| aleph0_le_mk s).antisymm
    (mk_le_mk_of_subset subset_closure)

end Subfield
