/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap

/-!
# Integral closure of a subring.

Let `A` be an `R`-algebra. We prove that integral elements form a sub-`R`-algebra of `A`.

## Main definitions

Let `R` be a `CommRing` and let `A` be an R-algebra.

* `integralClosure R A` : the integral closure of `R` in an `R`-algebra `A`.
-/


open Polynomial Submodule

section

variable {R A B S : Type*}
variable [CommRing R] [CommRing A] [Ring B] [CommRing S]
variable [Algebra R A] [Algebra R B] (f : R →+* S)

theorem Subalgebra.isIntegral_iff (S : Subalgebra R A) :
    Algebra.IsIntegral R S ↔ ∀ x ∈ S, IsIntegral R x :=
  Algebra.isIntegral_def.trans <| .trans
    (forall_congr' fun _ ↦ (isIntegral_algHom_iff S.val Subtype.val_injective).symm) Subtype.forall

instance Module.End.isIntegral {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Algebra.IsIntegral R (Module.End R M) :=
  ⟨LinearMap.exists_monic_and_aeval_eq_zero R⟩

variable (R)
theorem IsIntegral.of_finite [Module.Finite R B] (x : B) : IsIntegral R x :=
  (isIntegral_algHom_iff (Algebra.lmul R B) Algebra.lmul_injective).mp
    (Algebra.IsIntegral.isIntegral _)

variable (B)
instance Algebra.IsIntegral.of_finite [Module.Finite R B] : Algebra.IsIntegral R B :=
  ⟨.of_finite R⟩

variable {R B}

/-- If `S` is a sub-`R`-algebra of `A` and `S` is finitely-generated as an `R`-module,
  then all elements of `S` are integral over `R`. -/
theorem IsIntegral.of_mem_of_fg (S : Subalgebra R B)
    (HS : S.toSubmodule.FG) (x : B) (hx : x ∈ S) : IsIntegral R x :=
  have : Module.Finite R S := ⟨(fg_top _).mpr HS⟩
  (isIntegral_algHom_iff S.val Subtype.val_injective).mpr (.of_finite R (⟨x, hx⟩ : S))

theorem RingHom.IsIntegralElem.of_mem_closure {x y z : S} (hx : f.IsIntegralElem x)
    (hy : f.IsIntegralElem y) (hz : z ∈ Subring.closure ({x, y} : Set S)) : f.IsIntegralElem z := by
  letI : Algebra R S := f.toAlgebra
  have := (IsIntegral.fg_adjoin_singleton hx).mul (IsIntegral.fg_adjoin_singleton hy)
  rw [← Algebra.adjoin_union_coe_submodule, Set.singleton_union] at this
  exact
    IsIntegral.of_mem_of_fg (Algebra.adjoin R {x, y}) this z
      (Algebra.mem_adjoin_iff.2 <| Subring.closure_mono Set.subset_union_right hz)

nonrec theorem IsIntegral.of_mem_closure {x y z : A} (hx : IsIntegral R x) (hy : IsIntegral R y)
    (hz : z ∈ Subring.closure ({x, y} : Set A)) : IsIntegral R z :=
  hx.of_mem_closure (algebraMap R A) hy hz

variable (f : R →+* B)

theorem RingHom.IsIntegralElem.add (f : R →+* S) {x y : S}
    (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) :
    f.IsIntegralElem (x + y) :=
  hx.of_mem_closure f hy <|
    Subring.add_mem _ (Subring.subset_closure (Or.inl rfl)) (Subring.subset_closure (Or.inr rfl))

nonrec theorem IsIntegral.add {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) :
    IsIntegral R (x + y) :=
  hx.add (algebraMap R A) hy

variable (f : R →+* S)

-- can be generalized to noncommutative S.
theorem RingHom.IsIntegralElem.neg {x : S} (hx : f.IsIntegralElem x) : f.IsIntegralElem (-x) :=
  hx.of_mem_closure f hx (Subring.neg_mem _ (Subring.subset_closure (Or.inl rfl)))

theorem IsIntegral.neg {x : B} (hx : IsIntegral R x) : IsIntegral R (-x) :=
  .of_mem_of_fg _ hx.fg_adjoin_singleton _ (Subalgebra.neg_mem _ <| Algebra.subset_adjoin rfl)

theorem RingHom.IsIntegralElem.sub {x y : S} (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) :
    f.IsIntegralElem (x - y) := by
  simpa only [sub_eq_add_neg] using hx.add f (hy.neg f)

nonrec theorem IsIntegral.sub {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) :
    IsIntegral R (x - y) :=
  hx.sub (algebraMap R A) hy

theorem RingHom.IsIntegralElem.mul {x y : S} (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) :
    f.IsIntegralElem (x * y) :=
  hx.of_mem_closure f hy
    (Subring.mul_mem _ (Subring.subset_closure (Or.inl rfl)) (Subring.subset_closure (Or.inr rfl)))

nonrec theorem IsIntegral.mul {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) :
    IsIntegral R (x * y) :=
  hx.mul (algebraMap R A) hy

theorem IsIntegral.smul {R} [CommSemiring R] [CommRing S] [Algebra R B] [Algebra S B] [Algebra R S]
    [IsScalarTower R S B] {x : B} (r : R) (hx : IsIntegral S x) : IsIntegral S (r • x) :=
  .of_mem_of_fg _ hx.fg_adjoin_singleton _ <| by
    rw [← algebraMap_smul S]; apply Subalgebra.smul_mem; exact Algebra.subset_adjoin rfl

section inv

open Algebra

variable {R S : Type*}

/-- A nonzero element in a domain integral over a field is a unit. -/
theorem IsIntegral.isUnit [Field R] [Ring S] [IsDomain S] [Algebra R S] {x : S}
    (int : IsIntegral R x) (h0 : x ≠ 0) : IsUnit x :=
  have : FiniteDimensional R (adjoin R {x}) := ⟨(Submodule.fg_top _).mpr int.fg_adjoin_singleton⟩
  (FiniteDimensional.isUnit R (K := adjoin R {x})
    (x := ⟨x, subset_adjoin rfl⟩) <| mt Subtype.ext_iff.mp h0).map (adjoin R {x}).val

/-- A commutative domain that is an integral algebra over a field is a field. -/
theorem isField_of_isIntegral_of_isField' [CommRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [Algebra.IsIntegral R S] (hR : IsField R) : IsField S where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel {x} hx := by
    letI := hR.toField
    obtain ⟨y, rfl⟩ := (Algebra.IsIntegral.isIntegral (R := R) x).isUnit hx
    exact ⟨y.inv, y.val_inv⟩

variable [Field R] [DivisionRing S] [Algebra R S] {x : S} {A : Subalgebra R S}

theorem IsIntegral.inv_mem_adjoin (int : IsIntegral R x) : x⁻¹ ∈ adjoin R {x} := by
  obtain rfl | h0 := eq_or_ne x 0
  · rw [inv_zero]; exact Subalgebra.zero_mem _
  have : FiniteDimensional R (adjoin R {x}) := ⟨(Submodule.fg_top _).mpr int.fg_adjoin_singleton⟩
  obtain ⟨⟨y, hy⟩, h1⟩ := FiniteDimensional.exists_mul_eq_one R
    (K := adjoin R {x}) (x := ⟨x, subset_adjoin rfl⟩) (mt Subtype.ext_iff.mp h0)
  rwa [← mul_left_cancel₀ h0 ((Subtype.ext_iff.mp h1).trans (mul_inv_cancel h0).symm)]

/-- The inverse of an integral element in a subalgebra of a division ring over a field
  also lies in that subalgebra. -/
theorem IsIntegral.inv_mem (int : IsIntegral R x) (hx : x ∈ A) : x⁻¹ ∈ A :=
  adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hx) int.inv_mem_adjoin

/-- An integral subalgebra of a division ring over a field is closed under inverses. -/
theorem Algebra.IsIntegral.inv_mem [Algebra.IsIntegral R A] (hx : x ∈ A) : x⁻¹ ∈ A :=
  ((isIntegral_algHom_iff A.val Subtype.val_injective).mpr <|
    Algebra.IsIntegral.isIntegral (⟨x, hx⟩ : A)).inv_mem hx

/-- The inverse of an integral element in a division ring over a field is also integral. -/
theorem IsIntegral.inv (int : IsIntegral R x) : IsIntegral R x⁻¹ :=
  .of_mem_of_fg _ int.fg_adjoin_singleton _ int.inv_mem_adjoin

theorem IsIntegral.mem_of_inv_mem (int : IsIntegral R x) (inv_mem : x⁻¹ ∈ A) : x ∈ A := by
  rw [← inv_inv x]; exact int.inv.inv_mem inv_mem

end inv

variable (R A)

/-- The integral closure of R in an R-algebra A. -/
def integralClosure : Subalgebra R A where
  carrier := { r | IsIntegral R r }
  zero_mem' := isIntegral_zero
  one_mem' := isIntegral_one
  add_mem' := IsIntegral.add
  mul_mem' := IsIntegral.mul
  algebraMap_mem' _ := isIntegral_algebraMap

end
