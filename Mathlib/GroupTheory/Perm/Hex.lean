/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Perm.Images
public import Mathlib.GroupTheory.Perm.Basic

/-! Basic conversions between Hex permutations and permutations of `Fin n`. -/

public section

namespace Hex

variable {n : Nat}

/-- The equivalence of `Fin n` given by a forward permutation: `p.get`
one way, `p.inv.get` the other. -/
@[expose] def Perm.toEquiv (p : Perm n) : Fin n ≃ Fin n where
  toFun := p.get
  invFun := p.inv.get
  left_inv := p.inv_get_get
  right_inv := p.get_inv_get

@[simp] theorem Perm.toEquiv_apply (p : Perm n) (i : Fin n) :
    p.toEquiv i = p.get i := rfl

/-- The forward permutation with the same action as an equivalence of
`Fin n`. -/
@[expose] def Perm.ofEquiv (e : Fin n ≃ Fin n) : Perm n :=
  Perm.ofFn e (fun _ _ h => e.injective h)
    (fun i => ⟨e.symm i, e.apply_symm_apply i⟩)

@[simp] theorem Perm.get_ofEquiv (e : Fin n ≃ Fin n) (i : Fin n) :
    (Perm.ofEquiv e).get i = e i :=
  Perm.get_ofFn ..

namespace Perm

@[simp] theorem ofEquiv_toEquiv (p : Perm n) : ofEquiv p.toEquiv = p := by
  ext i
  simp [toEquiv]

@[simp] theorem toEquiv_ofEquiv (e : Equiv.Perm (Fin n)) : (ofEquiv e).toEquiv = e := by
  ext i
  simp [toEquiv]

@[simp] theorem toEquiv_id : (Perm.id n).toEquiv = 1 := by
  ext i
  simp

@[simp] theorem toEquiv_comp (p q : Perm n) :
    (p.comp q).toEquiv = p.toEquiv * q.toEquiv := by
  ext i
  simp [toEquiv]

@[simp] theorem toEquiv_inv (p : Perm n) : p.inv.toEquiv = p.toEquiv⁻¹ := by
  ext i
  simp [toEquiv]

@[simp] theorem ofEquiv_one : ofEquiv (1 : Equiv.Perm (Fin n)) = Perm.id n := by
  ext i
  simp

@[simp] theorem ofEquiv_mul (p q : Equiv.Perm (Fin n)) :
    ofEquiv (p * q) = (ofEquiv p).comp (ofEquiv q) := by
  ext i
  simp

@[simp] theorem ofEquiv_inv (p : Equiv.Perm (Fin n)) :
    ofEquiv p⁻¹ = (ofEquiv p).inv := by
  have hi : Function.Injective (@toEquiv n) := fun p q h => by
    simpa only [ofEquiv_toEquiv] using congrArg ofEquiv h
  apply hi
  simp

end Perm

end Hex

namespace Hex.PermGroup

/-- A Mathlib permutation from literal images. Invalid lists return the identity,
as in `Perm.ofImages`. -/
@[expose] def permOfImages (n : Nat) (l : List Nat) : Equiv.Perm (Fin n) :=
  (Perm.ofImages n l).toEquiv

end Hex.PermGroup
