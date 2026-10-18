/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.Coalgebra.Quotient
public import Mathlib.RingTheory.Congruence.Hom
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Bialgebra structure on quotients

If the counit and comultiplication of an `R`-bialgebra `A` descend along a ring congruence `c`,
then `c.Quotient` is again an `R`-bialgebra. A *biideal* `I` of `A`, a two-sided ideal whose
underlying `R`-submodule is a coideal, induces such a congruence, so `A ⧸ I` is an `R`-bialgebra.

## Main definitions

* `RingCon.IsBialgebraCon R c` : the counit and comultiplication descend to `c.Quotient`.
* `RingCon.mkBialgHom` : `c.mkₐ` as a bialgebra homomorphism.
* `Bialgebra.Quotient.mkBialgHom` : `Ideal.Quotient.mkₐ` as a bialgebra homomorphism.

## Main results

* `Bialgebra R c.Quotient` instance when `[c.IsBialgebraCon R]`.
* `Bialgebra R (A ⧸ I)` instance when `[I.IsTwoSided]` and `[(I.restrictScalars R).IsCoideal]`.
-/

@[expose] public section

open Coalgebra TensorProduct

section RingCon

variable {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]

variable (R) in
/-- A ring congruence `c` on an `R`-bialgebra is a bialgebra congruence if the counit and
comultiplication descend to `c.Quotient`. -/
@[mk_iff]
class RingCon.IsBialgebraCon (c : RingCon A) : Prop where
  counit_eq : ∀ ⦃x y : A⦄, c x y → counit (R := R) x = counit y
  comul_eq : ∀ ⦃x y : A⦄, c x y →
    TensorProduct.map (c.mkₐ R).toLinearMap (c.mkₐ R).toLinearMap (comul x) =
      TensorProduct.map (c.mkₐ R).toLinearMap (c.mkₐ R).toLinearMap (comul y)

namespace Bialgebra.Quotient

variable (c : RingCon A) [hc : c.IsBialgebraCon R]

/-- The counit on `c.Quotient`, as an `R`-algebra homomorphism. -/
def counitAlgHom : c.Quotient →ₐ[R] R :=
  c.liftₐ (Bialgebra.counitAlgHom R A) hc.counit_eq

/-- The comultiplication on `c.Quotient`, as an `R`-algebra homomorphism. -/
def comulAlgHom : c.Quotient →ₐ[R] c.Quotient ⊗[R] c.Quotient :=
  c.liftₐ ((Algebra.TensorProduct.map (c.mkₐ R) (c.mkₐ R)).comp (Bialgebra.comulAlgHom R A))
    hc.comul_eq

lemma counit_comp_mkₐ : (counitAlgHom c).toLinearMap ∘ₗ (c.mkₐ R).toLinearMap = counit := rfl

lemma comul_comp_mkₐ : (comulAlgHom c).toLinearMap ∘ₗ (c.mkₐ R).toLinearMap =
    map (c.mkₐ R).toLinearMap (c.mkₐ R).toLinearMap ∘ₗ comul := rfl

/-- The bialgebra structure on `c.Quotient` when `c` is a bialgebra congruence. -/
instance : Bialgebra R c.Quotient := by
  refine .ofAlgHom (comulAlgHom c) (counitAlgHom c) ?_ ?_ ?_ <;>
    refine RingCon.Quotient.hom_extₐ (AlgHom.toLinearMap_injective ?_) <;>
    simp only [coassoc_simps, AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      comul_comp_mkₐ, counit_comp_mkₐ]
  · simp [coassoc_simps]
  · rw [CoassocSimps.map_counit_comp_comul_left]; rfl
  · rw [CoassocSimps.map_counit_comp_comul_right]; rfl

@[simp] lemma counit_coe (a : A) : counit (R := R) (a : c.Quotient) = counit a := rfl

@[simp] lemma comul_coe (a : A) :
    comul (R := R) (a : c.Quotient) = map (c.mkₐ R).toLinearMap (c.mkₐ R).toLinearMap (comul a) :=
  rfl

end Bialgebra.Quotient

variable (R) in
/-- `c.mkₐ` as a bialgebra homomorphism. -/
def RingCon.mkBialgHom (c : RingCon A) [c.IsBialgebraCon R] : A →ₐc[R] c.Quotient :=
  .ofAlgHom (c.mkₐ R) rfl rfl

@[simp] lemma RingCon.mkBialgHom_apply (c : RingCon A) [c.IsBialgebraCon R] (a : A) :
    c.mkBialgHom R a = a := rfl

end RingCon

section Ideal

variable {R A : Type*} [CommRing R] [Ring A] [Bialgebra R A] (I : Ideal A) [I.IsTwoSided]
  [(I.restrictScalars R).IsCoideal]

/-- The ring congruence of a biideal is a bialgebra congruence. -/
instance : (Ideal.Quotient.ringCon I).IsBialgebraCon R where
  counit_eq _ _ h := sub_eq_zero.mp <| by
    rw [← map_sub]
    exact Submodule.IsCoideal.counit_eq_zero (I := I.restrictScalars R)
      (Ideal.Quotient.eq.mp (Quotient.sound h))
  comul_eq _ _ h := sub_eq_zero.mp <| by
    rw [← map_sub, ← map_sub]
    exact Submodule.IsCoideal.map_mkQ_comul_eq_zero (I := I.restrictScalars R)
      (Ideal.Quotient.eq.mp (Quotient.sound h))

namespace Bialgebra.Quotient

/-- The bialgebra structure on `A ⧸ I` when `I` is a biideal. -/
instance : Bialgebra R (A ⧸ I) :=
  -- Transporting the `RingCon` instance wholesale would give an algebra structure that is only
  -- defeq to `Ideal.Quotient.algebra` at default transparency, creating a diamond.
  { Ideal.Quotient.algebra R,
    (inferInstance : Bialgebra R (Ideal.Quotient.ringCon I).Quotient) with }

@[simp] lemma counit_mk (a : A) : counit (R := R) (Ideal.Quotient.mk I a) = counit a := rfl

@[simp] lemma comul_mk (a : A) :
    comul (R := R) (Ideal.Quotient.mk I a) =
      map (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ R I).toLinearMap (comul a) :=
  rfl

/-- `Ideal.Quotient.mkₐ` as a bialgebra homomorphism. -/
def mkBialgHom : A →ₐc[R] A ⧸ I := .ofAlgHom (Ideal.Quotient.mkₐ R I) rfl rfl

@[simp] lemma mkBialgHom_apply (a : A) :
    mkBialgHom (R := R) I a = Ideal.Quotient.mk I a := rfl

end Bialgebra.Quotient

end Ideal
