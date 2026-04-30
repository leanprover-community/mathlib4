/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Flat

/-!
# Weakly étale algebras

In this file we define weakly étale algebras. An `R`-algebra `S` is weakly étale if
`S` is `R`-flat and the multiplication map `S ⊗[R] S → S` is flat.

## TODOs

- Show that a weakly étale algebra is formally unramified and in particular that
  a weakly étale algebra of finite presentation is étale (@chrisflav).
-/

@[expose] public section

universe u u₁ u₂ u₃ u₄ u₅

open TensorProduct

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- `S` is a weakly-étale `R`-algebra if both `R → S` and `S ⊗[R] S → R` are flat. -/
@[stacks 092B, mk_iff]
class WeaklyEtale (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] where
  flat : Module.Flat R S := by infer_instance
  flat_lmul' (R S) : (Algebra.TensorProduct.lmul' R (S := S)).Flat

attribute [instance] WeaklyEtale.flat

namespace WeaklyEtale

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] ULift.algebra' in
lemma ulift_iff : WeaklyEtale (ULift.{u₁} R) (ULift.{u₂} S) ↔ WeaklyEtale R S := by
  rw [weaklyEtale_iff, weaklyEtale_iff, Module.Flat.ulift_left_iff, Module.Flat.ulift_right_iff]
  congr!
  conv_rhs => rw [← RingHom.Flat.ulift_iff.{u₁, u₂}]
  rw [TensorProduct.lmul'_ulift, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom]
  exact RingHom.Flat.comp_iff_of_bijective_right (Equiv.bijective _)

@[stacks 092N "(2)"]
instance (priority := low) [Etale R S] : WeaklyEtale R S where
  flat_lmul' := by
    algebraize [Algebra.TensorProduct.lmul' R (S := S) |>.toRingHom]
    have : IsScalarTower R (S ⊗[R] S) S := .of_algHom (Algebra.TensorProduct.lmul' R (S := S))
    have : Etale R (S ⊗[R] S) := .comp _ S _
    have : Etale (S ⊗[R] S) S := .of_restrictScalars R _ _
    exact Smooth.flat (S ⊗[R] S) S

@[stacks 092H]
instance {T : Type*} [CommRing T] [Algebra R T] [WeaklyEtale R S] :
    WeaklyEtale T (T ⊗[R] S) where
  flat_lmul' := by
    let e : T ⊗[R] S ⊗[T] (T ⊗[R] S) ≃ₐ[T] T ⊗[R] (S ⊗[R] S) :=
      (Algebra.TensorProduct.cancelBaseChange _ _ T _ _).trans
        (TensorProduct.assoc _ _ _ _ _ _)
    have : TensorProduct.lmul' T (S := T ⊗[R] S) =
        (TensorProduct.map (.id T T) (TensorProduct.lmul' R)).comp e.toAlgHom := by
      ext <;> simp [e, TensorProduct.one_def]
    rw [this]
    refine .comp (.of_bijective e.bijective) (.tensorProductMap ?_ ?_)
    · exact .of_bijective Function.bijective_id
    · exact WeaklyEtale.flat_lmul' R S

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] TensorProduct.rightAlgebra ULift.algebra' in
@[stacks 092J]
lemma trans (R : Type u₁) (S : Type u₂) [CommRing R] [CommRing S] [Algebra R S]
    (T : Type u₃) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [WeaklyEtale R S] [WeaklyEtale S T] : WeaklyEtale R T := by
  rw [← ulift_iff.{max u₁ u₂ u₃, max u₁ u₂ u₃}] at *
  refine ⟨.trans _ (ULift.{max u₁ u₂ u₃} S) _, ?_⟩
  · have heq : TensorProduct.lmul' (S := ULift.{max u₁ u₂ u₃} T) (ULift R) =
        AlgHom.comp ((TensorProduct.lmul' (S := ULift.{max u₁ u₂ u₃} T)
          (ULift.{max u₁ u₂ u₃} S)).restrictScalars (ULift.{max u₁ u₂ u₃} R))
          (TensorProduct.mapOfCompatibleSMul _ _ _ _ _) := by
      ext <;> simp
    rw [heq]
    refine .comp ?_ ?_
    · exact (flat_lmul' (ULift R) (ULift S)).mapOfCompatibleSMul
        (ULift.{max u₁ u₂ u₃} T) (ULift.{max u₁ u₂ u₃} T)
    · exact WeaklyEtale.flat_lmul' (ULift S) (ULift T)

end WeaklyEtale

end Algebra
