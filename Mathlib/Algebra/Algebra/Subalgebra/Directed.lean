/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Data.Set.UnionLift

#align_import algebra.algebra.subalgebra.basic from "leanprover-community/mathlib"@"b915e9392ecb2a861e1e766f0e1df6ac481188ca"

/-!
# Subalgebras and directed Unions of sets

## Main results

 * `Subalgebra.coe_iSup_of_directed`: a directed supremum consists of the union of the algebras
 * `Subalgebra.iSupLift`: define an algebra homomorphism on a directed supremum of subalgebras by
   defining it on each subalgebra, and proving that it agrees on the intersection of subalgebras.
-/

namespace Subalgebra

open Algebra

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable (S : Subalgebra R A)

variable {ι : Type*} [Nonempty ι] {K : ι → Subalgebra R A} (dir : Directed (· ≤ ·) K)

theorem coe_iSup_of_directed : ↑(iSup K) = ⋃ i, (K i : Set A) :=
  let s : Subalgebra R A :=
    { __ := Subsemiring.copy _ _ (Subsemiring.coe_iSup_of_directed dir).symm
      algebraMap_mem' := fun _ ↦ Set.mem_iUnion.2
        ⟨Classical.arbitrary ι, Subalgebra.algebraMap_mem _ _⟩ }
  have : iSup K = s := le_antisymm
    (iSup_le fun i ↦ le_iSup (fun i ↦ (K i : Set A)) i) (Set.iUnion_subset fun _ ↦ le_iSup K _)
  this.symm ▸ rfl
#align subalgebra.coe_supr_of_directed Subalgebra.coe_iSup_of_directed

variable (K)
variable (f : ∀ i, K i →ₐ[R] B) (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h))
  (T : Subalgebra R A) (hT : T = iSup K)

-- Porting note (#11215): TODO: turn `hT` into an assumption `T ≤ iSup K`.
-- That's what `Set.iUnionLift` needs
-- Porting note: the proofs of `map_{zero,one,add,mul}` got a bit uglier, probably unification trbls
/-- Define an algebra homomorphism on a directed supremum of subalgebras by defining
it on each subalgebra, and proving that it agrees on the intersection of subalgebras. -/
noncomputable def iSupLift : ↥T →ₐ[R] B :=
  { toFun := Set.iUnionLift (fun i => ↑(K i)) (fun i x => f i x)
        (fun i j x hxi hxj => by
          let ⟨k, hik, hjk⟩ := dir i j
          dsimp
          rw [hf i k hik, hf j k hjk]
          rfl)
        T (by rw [hT, coe_iSup_of_directed dir])
    map_one' := by apply Set.iUnionLift_const _ (fun _ => 1) <;> simp
    map_zero' := by dsimp; apply Set.iUnionLift_const _ (fun _ => 0) <;> simp
    map_mul' := by
      subst hT; dsimp
      apply Set.iUnionLift_binary (coe_iSup_of_directed dir) dir _ (fun _ => (· * ·))
      on_goal 3 => rw [coe_iSup_of_directed dir]
      all_goals simp
    map_add' := by
      subst hT; dsimp
      apply Set.iUnionLift_binary (coe_iSup_of_directed dir) dir _ (fun _ => (· + ·))
      on_goal 3 => rw [coe_iSup_of_directed dir]
      all_goals simp
    commutes' := fun r => by
      dsimp
      apply Set.iUnionLift_const _ (fun _ => algebraMap R _ r) <;> simp }
#align subalgebra.supr_lift Subalgebra.iSupLift

variable {K dir f hf T hT}

@[simp]
theorem iSupLift_inclusion {i : ι} (x : K i) (h : K i ≤ T) :
    iSupLift K dir f hf T hT (inclusion h x) = f i x := by
  dsimp [iSupLift, inclusion]
  rw [Set.iUnionLift_inclusion]
#align subalgebra.supr_lift_inclusion Subalgebra.iSupLift_inclusion

@[simp]
theorem iSupLift_comp_inclusion {i : ι} (h : K i ≤ T) :
    (iSupLift K dir f hf T hT).comp (inclusion h) = f i := by ext; simp
#align subalgebra.supr_lift_comp_inclusion Subalgebra.iSupLift_comp_inclusion

@[simp]
theorem iSupLift_mk {i : ι} (x : K i) (hx : (x : A) ∈ T) :
    iSupLift K dir f hf T hT ⟨x, hx⟩ = f i x := by
  dsimp [iSupLift, inclusion]
  rw [Set.iUnionLift_mk]
#align subalgebra.supr_lift_mk Subalgebra.iSupLift_mk

theorem iSupLift_of_mem {i : ι} (x : T) (hx : (x : A) ∈ K i) :
    iSupLift K dir f hf T hT x = f i ⟨x, hx⟩ := by
  dsimp [iSupLift, inclusion]
  rw [Set.iUnionLift_of_mem]
#align subalgebra.supr_lift_of_mem Subalgebra.iSupLift_of_mem

end Subalgebra
