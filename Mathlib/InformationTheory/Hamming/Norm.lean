/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.InformationTheory.Hamming.Group
/-!
# Hamming norm

Defines the Hamming norm, the number of non-zero entries in `x : Hamming β`, shows that it
relates to the Hamming distance in the obvious way, and defines a `NormedAddGroup` instance
for Hamming types.
-/

namespace DHamming

variable {α ι : Type*} {β γ : ι → Type*} {f : ∀ i, β i → γ i} {x y : DHamming β}
    [Fintype ι] [∀ i, DecidableEq (β i)] [∀ i, DecidableEq (γ i)]


open Finset

section

variable [∀ i, Zero (β i)] [∀ i, Zero (γ i)]

instance : Norm (DHamming β) := ⟨fun x => #{i | x.toPi i ≠ 0}⟩

theorem dist_zero_right : dist x 0 = ‖x‖ := rfl

theorem dist_zero_left : dist (0 : DHamming β) x = ‖x‖ := dist_comm _ _

theorem norm_nonneg : 0 ≤ ‖x‖ := Nat.cast_nonneg _

theorem norm_eq_zero : ‖x‖ = 0 ↔ x = 0 := dist_eq_zero (y := (0 : DHamming β))
theorem norm_ne_zero : ‖x‖ ≠ 0 ↔ x ≠ 0 := norm_eq_zero.not
theorem norm_pos : 0 < ‖x‖ ↔ x ≠ 0 := by
  rw [← ne_iff_lt_iff_le.mpr norm_nonneg, ← norm_ne_zero, ne_comm]

theorem norm_zero : ‖(0 : DHamming β)‖ = 0 := by rw [norm_eq_zero]

theorem norm_lt_one {x : DHamming β} : ‖x‖ < 1 ↔ x = 0 := dist_lt_one (y := 0)

theorem norm_le_card {x : DHamming β} : ‖x‖ ≤ Fintype.card ι := dist_le_card (y := 0)

@[push_cast] theorem norm_eq_card : ‖x‖ = #{i | x.toPi i ≠ 0} := rfl

theorem norm_map_le_norm (hf : ∀ i, f i 0 = 0) : ‖x.map f‖ ≤ ‖x‖ := by
  simp_rw [← dist_zero_right, ← map_zero hf, dist_map_map_le_dist]

theorem norm_map_of_injective (hf₁ : ∀ i, Function.Injective (f i)) (hf₂ : ∀ i, f i 0 = 0) :
    ‖x.map f‖ = ‖x‖ := by
  simp_rw [← dist_zero_right, ← map_zero hf₂, dist_map_map_of_injective hf₁]

theorem norm_smul_le_norm [Zero α] [∀ i, SMulWithZero α (β i)] {k : α} : ‖k • x‖ ≤ ‖x‖ :=
  norm_map_le_norm (fun _ => smul_zero _)

theorem norm_smul [Zero α] [∀ i, SMulWithZero α (β i)] {k : α} (hk : ∀ i, IsSMulRegular (β i) k) :
    ‖k • x‖ = ‖x‖ := norm_map_of_injective hk (fun _ => smul_zero _)

end

instance [∀ i, AddGroup (β i)] : NormedAddGroup (DHamming β) where
  dist_eq _ _ := by
    push_cast
    simp_rw [sub_toPi, sub_ne_zero]

instance [∀ i, AddCommGroup (β i)] : NormedAddCommGroup (DHamming β) where
  dist_eq := fun x y => NormedAddGroup.dist_eq x y

@[push_cast]
theorem nnnorm_eq_card [∀ i, AddGroup (β i)] :
    ‖x‖₊ = #{i | x.toPi i ≠ 0} := rfl

end DHamming
