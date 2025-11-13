/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Tactic.Ring

/-!
# The lattice of ideals in a ring

Some basic results on lattice operations on ideals: `⊥`, `⊤`, `⊔`, `⊓`.

## TODO

Support right ideals, and two-sided ideals over non-commutative rings.
-/


universe u v w

variable {α : Type u} {β : Type v} {F : Type w}

open Set Function

open Pointwise

section Semiring

namespace Ideal

variable [Semiring α] (I : Ideal α) {a b : α}

instance (priority := low) : IsTwoSided (⊥ : Ideal α) :=
  ⟨fun _ h ↦ by rw [h, zero_mul]; exact zero_mem _⟩

instance (priority := low) : IsTwoSided (⊤ : Ideal α) := ⟨fun _ _ ↦ trivial⟩

instance (priority := low) {ι} (I : ι → Ideal α) [∀ i, (I i).IsTwoSided] : (⨅ i, I i).IsTwoSided :=
  ⟨fun _ h ↦ (Submodule.mem_iInf _).mpr (mul_mem_right _ _ <| (Submodule.mem_iInf _).mp h ·)⟩

theorem eq_top_of_unit_mem (x y : α) (hx : x ∈ I) (h : y * x = 1) : I = ⊤ :=
  eq_top_iff.2 fun z _ =>
    calc
      z * y * x ∈ I := I.mul_mem_left _ hx
      _ = z * (y * x) := mul_assoc z y x
      _ = z := by rw [h, mul_one]

theorem eq_top_of_isUnit_mem {x} (hx : x ∈ I) (h : IsUnit x) : I = ⊤ :=
  let ⟨y, hy⟩ := h.exists_left_inv
  eq_top_of_unit_mem I x y hx hy

theorem eq_top_iff_one : I = ⊤ ↔ (1 : α) ∈ I :=
  ⟨by rintro rfl; trivial, fun h => eq_top_of_unit_mem _ _ 1 h (by simp)⟩

theorem ne_top_iff_one : I ≠ ⊤ ↔ (1 : α) ∉ I :=
  not_congr I.eq_top_iff_one

section Lattice

variable {R : Type u} [Semiring R]

theorem mem_sup_left {S T : Ideal R} : ∀ {x : R}, x ∈ S → x ∈ S ⊔ T :=
  @le_sup_left _ _ S T

theorem mem_sup_right {S T : Ideal R} : ∀ {x : R}, x ∈ T → x ∈ S ⊔ T :=
  @le_sup_right _ _ S T

theorem mem_iSup_of_mem {ι : Sort*} {S : ι → Ideal R} (i : ι) : ∀ {x : R}, x ∈ S i → x ∈ iSup S :=
  @le_iSup _ _ _ S _

theorem mem_sSup_of_mem {S : Set (Ideal R)} {s : Ideal R} (hs : s ∈ S) :
    ∀ {x : R}, x ∈ s → x ∈ sSup S :=
  @le_sSup _ _ _ _ hs

theorem mem_sInf {s : Set (Ideal R)} {x : R} : x ∈ sInf s ↔ ∀ ⦃I⦄, I ∈ s → x ∈ I :=
  ⟨fun hx I his => hx I ⟨I, iInf_pos his⟩, fun H _I ⟨_J, hij⟩ => hij ▸ fun _S ⟨hj, hS⟩ => hS ▸ H hj⟩

theorem mem_inf {I J : Ideal R} {x : R} : x ∈ I ⊓ J ↔ x ∈ I ∧ x ∈ J :=
  Iff.rfl

theorem mem_iInf {ι : Sort*} {I : ι → Ideal R} {x : R} : x ∈ iInf I ↔ ∀ i, x ∈ I i :=
  Submodule.mem_iInf _

theorem mem_bot {x : R} : x ∈ (⊥ : Ideal R) ↔ x = 0 :=
  Submodule.mem_bot _

end Lattice

end Ideal

end Semiring

section DivisionSemiring

variable {K : Type u} [DivisionSemiring K] (I : Ideal K)

namespace Ideal

/-- All ideals in a division (semi)ring are trivial. -/
theorem eq_bot_or_top : I = ⊥ ∨ I = ⊤ := by
  rw [or_iff_not_imp_right]
  change _ ≠ _ → _
  rw [Ideal.ne_top_iff_one]
  intro h1
  rw [eq_bot_iff]
  intro r hr
  by_cases H : r = 0; · simpa
  simpa [H, h1] using I.mul_mem_left r⁻¹ hr

end Ideal

end DivisionSemiring
