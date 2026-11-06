/-
Copyright (c) 2026 Kirill Kondrashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kirill Kondrashov, Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Orientation

/-!
# Orientations and volume forms on exterior powers

This file relates module orientations to volume forms on top exterior powers.

## Main definitions

* `exteriorPower.volOrientation`: the orientation associated to a volume form.
* `exteriorPower.volOfOrientation`: a volume form compatible with a positive orientation.
-/

@[expose] public section

noncomputable section

namespace exteriorPower

open Module Set

variable {R M : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M]

/-- The orientation associated to a volume form. -/
public def volOrientation {n : ℕ} (vol : ⋀[R]^n M ≃ₗ[R] R) : Orientation R M (Fin n) :=
  rayOfNeZero R ((alternatingMapLinearEquiv (R := R) (n := n) (N := R)).symm vol.toLinearMap) <| by
    apply (alternatingMapLinearEquiv (R := R) (n := n) (N := R)).symm.map_ne_zero_iff.mpr
    intro h
    have := congrArg (fun f : ⋀[R]^n M →ₗ[R] R => f (vol.symm 1)) h
    simp at this

@[simp]
public lemma volOrientation_trans_neg {n : ℕ} (vol : ⋀[R]^n M ≃ₗ[R] R) :
    volOrientation (vol.trans (.neg R)) = -volOrientation vol := by
  simp only [volOrientation, neg_rayOfNeZero]
  congr 1

variable [Module.Finite R M] [Module.Free R M]

/-- Every orientation of a finite free module is given by a volume form. -/
public lemma exists_volOrientation_eq (o : Orientation R M (Fin (finrank R M))) :
    ∃ vol : ⋀[R]^(finrank R M) M ≃ₗ[R] R, volOrientation vol = o := by
  classical
  let b := Module.finBasis R M
  let : Unique (powersetCard (Fin (finrank R M)) (finrank R M)) := {
    default := ⟨Finset.univ, by simp⟩
    uniq s := Subtype.ext <| Finset.eq_univ_of_card _ <| by simp
  }
  let vol := (b.exteriorPower (finrank R M)).equiv (Basis.singleton _ R) (Equiv.refl _)
  have h : o = volOrientation vol ∨ o = -volOrientation vol := by
    rcases b.orientation_eq_or_eq_neg o with ho | ho <;>
      rcases b.orientation_eq_or_eq_neg (volOrientation vol) with hv | hv <;>
        simp [ho, hv]
  rcases h with h | h
  · exact ⟨vol, h.symm⟩
  · exact ⟨vol.trans (.neg R), by simpa only [volOrientation_trans_neg] using h.symm⟩

variable [Module.Oriented R M (Fin (finrank R M))]

/-- A volume form compatible with the positive orientation on a finite free module. -/
public def volOfOrientation : ⋀[R]^(finrank R M) M ≃ₗ[R] R :=
  (exists_volOrientation_eq positiveOrientation).choose

@[simp]
public lemma volOrientation_volOfOrientation :
    volOrientation (volOfOrientation (R := R) (M := M)) = positiveOrientation :=
  (exists_volOrientation_eq positiveOrientation).choose_spec

end exteriorPower
