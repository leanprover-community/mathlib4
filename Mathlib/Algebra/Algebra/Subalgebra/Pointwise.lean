/-
Copyright (c) 2021 Eric Weiser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Ring.Subring.Pointwise

/-!
# Pointwise actions on subalgebras.

If `R'` acts on an `R`-algebra `A` (so that `R'` and `R` actions commute)
then we get an `R'` action on the collection of `R`-subalgebras.
-/


namespace Subalgebra

section Pointwise

variable {R : Type*} {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem mul_toSubmodule_le (S T : Subalgebra R A) :
    (Subalgebra.toSubmodule S)* (Subalgebra.toSubmodule T) ≤ Subalgebra.toSubmodule (S ⊔ T) := by
  rw [Submodule.mul_le]
  intro y hy z hz
  change y * z ∈ S ⊔ T
  exact mul_mem (Algebra.mem_sup_left hy) (Algebra.mem_sup_right hz)

/-- As submodules, subalgebras are idempotent. -/
@[simp]
theorem isIdempotentElem_toSubmodule (S : Subalgebra R A) :
    IsIdempotentElem S.toSubmodule := by
  apply le_antisymm
  · refine (mul_toSubmodule_le _ _).trans_eq ?_
    rw [sup_idem]
  · intro x hx1
    rw [← mul_one x]
    exact Submodule.mul_mem_mul hx1 (show (1 : A) ∈ S from one_mem S)

/-- When `A` is commutative, `Subalgebra.mul_toSubmodule_le` is strict. -/
theorem mul_toSubmodule {R : Type*} {A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S T : Subalgebra R A) : (Subalgebra.toSubmodule S) * (Subalgebra.toSubmodule T)
        = Subalgebra.toSubmodule (S ⊔ T) := by
  refine le_antisymm (mul_toSubmodule_le _ _) ?_
  rintro x (hx : x ∈ Algebra.adjoin R (S ∪ T : Set A))
  refine
    Algebra.adjoin_induction (fun x hx => ?_) (fun r => ?_) (fun _ _ _ _ => Submodule.add_mem _)
      (fun x y _ _ hx hy => ?_) hx
  · rcases hx with hxS | hxT
    · rw [← mul_one x]
      exact Submodule.mul_mem_mul hxS (show (1 : A) ∈ T from one_mem T)
    · rw [← one_mul x]
      exact Submodule.mul_mem_mul (show (1 : A) ∈ S from one_mem S) hxT
  · rw [← one_mul (algebraMap _ _ _)]
    exact Submodule.mul_mem_mul (show (1 : A) ∈ S from one_mem S) (algebraMap_mem T _)
  have := Submodule.mul_mem_mul hx hy
  rwa [mul_assoc, mul_comm _ (Subalgebra.toSubmodule T), ← mul_assoc _ _ (Subalgebra.toSubmodule S),
    isIdempotentElem_toSubmodule, mul_comm T.toSubmodule, ← mul_assoc,
    isIdempotentElem_toSubmodule] at this

variable {R' : Type*} [Semiring R'] [MulSemiringAction R' A] [SMulCommClass R' R A]

/-- The action on a subalgebra corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
protected def pointwiseMulAction : MulAction R' (Subalgebra R A) where
  smul a S := S.map (MulSemiringAction.toAlgHom _ _ a)
  one_smul S := (congr_arg (fun f => S.map f) (AlgHom.ext <| one_smul R')).trans S.map_id
  mul_smul _a₁ _a₂ S :=
    (congr_arg (fun f => S.map f) (AlgHom.ext <| mul_smul _ _)).trans (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Subalgebra.pointwiseMulAction

open Pointwise

@[simp]
theorem coe_pointwise_smul (m : R') (S : Subalgebra R A) : ↑(m • S) = m • (S : Set A) :=
  rfl

@[simp]
theorem pointwise_smul_toSubsemiring (m : R') (S : Subalgebra R A) :
    (m • S).toSubsemiring = m • S.toSubsemiring :=
  rfl

@[simp]
theorem pointwise_smul_toSubmodule (m : R') (S : Subalgebra R A) :
    Subalgebra.toSubmodule (m • S) = m • Subalgebra.toSubmodule S :=
  rfl

@[simp]
theorem pointwise_smul_toSubring {R' R A : Type*} [Semiring R'] [CommRing R] [Ring A]
    [MulSemiringAction R' A] [Algebra R A] [SMulCommClass R' R A] (m : R') (S : Subalgebra R A) :
    (m • S).toSubring = m • S.toSubring :=
  rfl

theorem smul_mem_pointwise_smul (m : R') (r : A) (S : Subalgebra R A) : r ∈ S → m • r ∈ m • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ m • (S : Set A))

instance : CovariantClass R' (Subalgebra R A) HSMul.hSMul LE.le :=
  ⟨fun _ _ => map_mono⟩

end Pointwise

end Subalgebra
