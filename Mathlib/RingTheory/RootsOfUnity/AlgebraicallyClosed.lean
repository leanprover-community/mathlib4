/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Instances for HasEnoughRootsOfUnity

We provide an instance for `HasEnoughRootsOfUnity F n` when `F` is an algebraically closed field
and `n` is not divisible by the characteristic. In particular, when `F` has characteristic zero,
this hold for all `n ≠ 0`.

### TODO

Add an instance `HasEnoughRootsOfUnity Circle n` for all `n ≠ 0`.
This is probably easiest via setting up an isomorphism
`rootsOfUnity n Circle ≃* rootsOfUnity n ℂ`.
-/

namespace IsAlgClosed

/-- An algebraically closed field `F` satisfies `HasEnoughRootsOfUnity F n` for all `n`
that are not divisible by the characteristic of `F`. -/
instance hasEnoughRootsOfUnity (F : Type*) [Field F] [IsAlgClosed F] (n : ℕ) [i : NeZero (n : F)] :
    HasEnoughRootsOfUnity F n where
  prim := by
    have : NeZero n := .of_neZero_natCast F
    have := isCyclotomicExtension {⟨n, NeZero.pos n⟩} F fun _ h ↦ Set.mem_singleton_iff.mp h ▸ i
    exact IsCyclotomicExtension.exists_prim_root (S := {(⟨n, NeZero.pos n⟩ : ℕ+)}) F rfl
  cyc :=
    have : NeZero n := .of_neZero_natCast F
    rootsOfUnity.isCyclic F n

end IsAlgClosed

variable (n : ℕ) [NeZero n]

#check ((rootsOfUnityUnitsMulEquiv ℂ n).toMonoidHom.comp (restrictRootsOfUnity Circle.toUnits n) :
  ((rootsOfUnity n Circle) →* (rootsOfUnity n ℂ)))

#check ((rootsOfUnityUnitsMulEquiv ℂ n) : rootsOfUnity n ℂˣ ≃* rootsOfUnity n ℂ)

#check ((restrictRootsOfUnity Circle.toUnits n) : ((rootsOfUnity n Circle) →* (rootsOfUnity n ℂˣ)))

variable (z : rootsOfUnity n ℂ)

#check z.val.val

#check Complex.norm_eq_one_of_mem_rootsOfUnity z.prop

lemma n1 : ‖z.val.val‖=1 := Complex.norm_eq_one_of_mem_rootsOfUnity z.prop

@[simps]
noncomputable def rootsOfUnitytoCircle : (rootsOfUnity n ℂ) →* Circle where
  toFun := fun z => ⟨z.val.val,
    mem_sphere_zero_iff_norm.2 (Complex.norm_eq_one_of_mem_rootsOfUnity z.prop)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

#check (rootsOfUnitytoCircle n).toHomUnits


noncomputable def rootsOfUnityCircleUnitsEquiv : rootsOfUnity n Circle ≃* rootsOfUnity n ℂ where
  __ := (rootsOfUnityUnitsMulEquiv ℂ n).toMonoidHom.comp (restrictRootsOfUnity Circle.toUnits n)
  invFun z := ⟨MonoidHom.toHomUnits (rootsOfUnitytoCircle n) z, by
    rw [mem_rootsOfUnity']
    rw [MonoidHom.coe_toHomUnits]
    rw [← MonoidHom.map_pow]
    rw [← (rootsOfUnitytoCircle n).map_one]
    congr
    aesop⟩
  left_inv := sorry
  right_inv := sorry

variable (w : rootsOfUnity n ℂˣ)

#check w.2

#check Units.liftRight

#check (toUnits (G := ℂˣ) : ℂˣ ≃* ℂˣˣ)

#check (MulEquiv.restrictRootsOfUnity (toUnits (G := ℂˣ)) n :
   (rootsOfUnity n ℂˣ) ≃* (rootsOfUnity n ℂˣˣ))

noncomputable def rootsOfUnityCircleUnitsEquiv2 : rootsOfUnity n Circle ≃* rootsOfUnity n ℂˣ where
  __ := restrictRootsOfUnity Circle.toUnits n
  invFun := fun z => ⟨z.val,sorry⟩
  left_inv := sorry
  right_inv := sorry
