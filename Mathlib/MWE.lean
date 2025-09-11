import Mathlib

universe u

open BigOperators Group ComplexConjugate
open Module Module.End
open Multiset
open Polynomial
open LinearMap

variable {G : Type} [Group G] [Finite G]

theorem root_unity_alg_int (z : ℂ) (hz : z ^ (Nat.card G) = 1) : IsIntegral ℤ z := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ (Nat.card G)
  obtain ⟨_, _, h⟩ := hζ.eq_pow_of_pow_eq_one hz

  let p : ℤ[X] := (X : ℤ[X]) ^ (Nat.card G) - 1
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hnez : Nat.card G ≠ 0 := by grind
  have hm : Monic p := monic_X_pow_sub_C (1 : ℤ) hnez
  -- now what... IsIntegral.of_aeval_monic ?  AdjoinRoot.isIntegral_root' ?
  sorry
