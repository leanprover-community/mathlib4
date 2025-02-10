/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Algebraic independence persists to the algebraic closure

## Main results

* `AlgebraicIndependent.extendScalars`: if A/S/R is a tower of algebras with S/R algebraic,
then a family of elements in A that are algebraically independent over R remains algebraically
independent over S, provided that S has no zero divisors.

* `AlgebraicIndependent.algebraicClosure`: an algebraically independent family remains
algebraically independent over the algebraic closure.
-/

open Function Algebra

namespace AlgebraicIndependent

variable {ι R S A : Type*} {x : ι → A}
variable [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [NoZeroDivisors S] (hx : AlgebraicIndependent R x)
include hx

theorem extendScalars [alg : Algebra.IsAlgebraic R S]
    (inj : Injective (algebraMap S A)) : AlgebraicIndependent S x := by
  nontriviality S
  have := inj.nontrivial
  refine algebraicIndependent_of_finite_type' inj fun t fin ind i hi ↦ ?_
  let Rt := adjoin R (x '' t)
  let St := adjoin S (x '' t)
  let _ : Algebra Rt St :=
    (Rt.inclusion (T := St.restrictScalars R) <| adjoin_le <| by exact subset_adjoin).toAlgebra
  have : IsScalarTower Rt St A := .of_algebraMap_eq fun ⟨y, _⟩ ↦ show y = y from rfl
  have : NoZeroDivisors St := (Set.image_eq_range _ _ ▸ ind.aevalEquiv)
    |>.symm.injective.noZeroDivisors _ (map_zero _) (map_mul _)
  have : NoZeroDivisors Rt := (Subalgebra.inclusion_injective _).noZeroDivisors
    (algebraMap Rt St) (map_zero _) (map_mul _)
  have : Algebra.IsAlgebraic Rt St := ⟨fun ⟨y, hy⟩ ↦ by
    rw [← isAlgebraic_algHom_iff (IsScalarTower.toAlgHom Rt St A) Subtype.val_injective]
    show IsAlgebraic Rt y
    exact adjoin_induction (fun _ h ↦ isAlgebraic_algebraMap (⟨_, subset_adjoin h⟩ : Rt))
      (fun z ↦ ((alg.1 z).algHom (IsScalarTower.toAlgHom R S A)).extendScalars fun _ _ eq ↦ by
        exact hx.algebraMap_injective congr($eq.1)) (fun _ _ _ _ ↦ .add) (fun _ _ _ _ ↦ .mul) hy⟩
  show Transcendental St (x i)
  exact (hx.transcendental_adjoin hi).extendScalars Subtype.val_injective

theorem extendScalars_of_isSimpleRing [Algebra.IsAlgebraic R S] [IsSimpleRing S] :
    AlgebraicIndependent S x :=
  hx.extendScalars <|
    have := Module.nontrivial R S
    have := hx.algebraMap_injective.nontrivial
    RingHom.injective _

theorem extendScalars_of_isIntegral [Algebra.IsIntegral R S]
    (inj : Injective (algebraMap S A)) : AlgebraicIndependent S x := by
  nontriviality S
  have := Module.nontrivial R S
  exact hx.extendScalars inj

protected theorem subalgebra (S : Subalgebra R A) [NoZeroDivisors A] [Algebra.IsAlgebraic R S] :
    AlgebraicIndependent S x :=
  hx.extendScalars Subtype.val_injective

theorem subalgebra_of_isIntegral (S : Subalgebra R A) [NoZeroDivisors A] [Algebra.IsIntegral R S] :
    AlgebraicIndependent S x :=
  hx.extendScalars_of_isIntegral Subtype.val_injective

theorem subalgebraAlgebraicClosure [IsDomain R] [NoZeroDivisors A] :
    AlgebraicIndependent (Subalgebra.algebraicClosure R A) x :=
  hx.subalgebra _

protected theorem integralClosure [NoZeroDivisors A] :
    AlgebraicIndependent (integralClosure R A) x :=
  hx.subalgebra_of_isIntegral _

omit hx in
protected theorem algebraicClosure {F E : Type*} [Field F] [Field E] [Algebra F E] {x : ι → E}
    (hx : AlgebraicIndependent F x) : AlgebraicIndependent (algebraicClosure F E) x :=
  hx.extendScalars_of_isSimpleRing

end AlgebraicIndependent
