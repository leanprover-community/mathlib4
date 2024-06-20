/-
Copyright (c) 2023 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey, Eric Wieser
-/
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Coalgebras

In this file we define `Coalgebra`, and provide instances for:

* Commutative semirings: `CommSemiring.toCoalgebra`
* Binary products: `Prod.instCoalgebra`
* Finitely supported functions: `Finsupp.instCoalgebra`

## References

* <https://en.wikipedia.org/wiki/Coalgebra>
-/

suppress_compilation

universe u v w

open scoped TensorProduct

/-- Data fields for `Coalgebra`, to allow API to be constructed before proving `Coalgebra.coassoc`.

See `Coalgebra` for documentation. -/
class CoalgebraStruct (R : Type u) (A : Type v)
    [CommSemiring R] [AddCommMonoid A] [Module R A] where
  /-- The comultiplication of the coalgebra -/
  comul : A →ₗ[R] A ⊗[R] A
  /-- The counit of the coalgebra -/
  counit : A →ₗ[R] R

namespace Coalgebra
export CoalgebraStruct (comul counit)
end Coalgebra

/-- A coalgebra over a commutative (semi)ring `R` is an `R`-module equipped with a coassociative
comultiplication `Δ` and a counit `ε` obeying the left and right counitality laws. -/
class Coalgebra (R : Type u) (A : Type v)
    [CommSemiring R] [AddCommMonoid A] [Module R A] extends CoalgebraStruct R A where
  /-- The comultiplication is coassociative -/
  coassoc : TensorProduct.assoc R A A A ∘ₗ comul.rTensor A ∘ₗ comul = comul.lTensor A ∘ₗ comul
  /-- The counit satisfies the left counitality law -/
  rTensor_counit_comp_comul : counit.rTensor A ∘ₗ comul = TensorProduct.mk R _ _ 1
  /-- The counit satisfies the right counitality law -/
  lTensor_counit_comp_comul : counit.lTensor A ∘ₗ comul = (TensorProduct.mk R _ _).flip 1

namespace Coalgebra
variable {R : Type u} {A : Type v}
variable [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]

@[simp]
theorem coassoc_apply (a : A) :
    TensorProduct.assoc R A A A (comul.rTensor A (comul a)) = comul.lTensor A (comul a) :=
  LinearMap.congr_fun coassoc a

@[simp]
theorem coassoc_symm_apply (a : A) :
    (TensorProduct.assoc R A A A).symm (comul.lTensor A (comul a)) = comul.rTensor A (comul a) := by
  rw [(TensorProduct.assoc R A A A).symm_apply_eq, coassoc_apply a]

@[simp]
theorem coassoc_symm :
    (TensorProduct.assoc R A A A).symm ∘ₗ comul.lTensor A ∘ₗ comul =
    comul.rTensor A ∘ₗ (comul (R := R)) :=
  LinearMap.ext coassoc_symm_apply

@[simp]
theorem rTensor_counit_comul (a : A) : counit.rTensor A (comul a) = 1 ⊗ₜ[R] a :=
  LinearMap.congr_fun rTensor_counit_comp_comul a

@[simp]
theorem lTensor_counit_comul (a : A) : counit.lTensor A (comul a) = a ⊗ₜ[R] 1 :=
  LinearMap.congr_fun lTensor_counit_comp_comul a

end Coalgebra
section CommSemiring

open Coalgebra

namespace CommSemiring
variable (R : Type u) [CommSemiring R]

/-- Every commutative (semi)ring is a coalgebra over itself, with `Δ r = 1 ⊗ₜ r`. -/
instance toCoalgebra : Coalgebra R R where
  comul := (TensorProduct.mk R R R) 1
  counit := .id
  coassoc := rfl
  rTensor_counit_comp_comul := by ext; rfl
  lTensor_counit_comp_comul := by ext; rfl

@[simp]
theorem comul_apply (r : R) : comul r = 1 ⊗ₜ[R] r := rfl

@[simp]
theorem counit_apply (r : R) : counit r = r := rfl

end CommSemiring

namespace Prod
variable (R : Type u) (A : Type v) (B : Type w)
variable [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
variable [Coalgebra R A] [Coalgebra R B]

open LinearMap

instance instCoalgebraStruct : CoalgebraStruct R (A × B) where
  comul := .coprod
    (TensorProduct.map (.inl R A B) (.inl R A B) ∘ₗ comul)
    (TensorProduct.map (.inr R A B) (.inr R A B) ∘ₗ comul)
  counit := .coprod counit counit

@[simp]
theorem comul_apply (r : A × B) :
    comul r =
      TensorProduct.map (.inl R A B) (.inl R A B) (comul r.1) +
      TensorProduct.map (.inr R A B) (.inr R A B) (comul r.2) := rfl

@[simp]
theorem counit_apply (r : A × B) : (counit r : R) = counit r.1 + counit r.2 := rfl

theorem comul_comp_inl :
    comul ∘ₗ inl R A B = TensorProduct.map (.inl R A B) (.inl R A B) ∘ₗ comul := by
  ext; simp

theorem comul_comp_inr :
    comul ∘ₗ inr R A B = TensorProduct.map (.inr R A B) (.inr R A B) ∘ₗ comul := by
  ext; simp

theorem comul_comp_fst :
    comul ∘ₗ .fst R A B = TensorProduct.map (.fst R A B) (.fst R A B) ∘ₗ comul := by
  ext : 1
  · rw [comp_assoc, fst_comp_inl, comp_id, comp_assoc, comul_comp_inl, ← comp_assoc,
      ← TensorProduct.map_comp, fst_comp_inl, TensorProduct.map_id, id_comp]
  · rw [comp_assoc, fst_comp_inr, comp_zero, comp_assoc, comul_comp_inr, ← comp_assoc,
      ← TensorProduct.map_comp, fst_comp_inr, TensorProduct.map_zero_left, zero_comp]

theorem comul_comp_snd :
    comul ∘ₗ .snd R A B = TensorProduct.map (.snd R A B) (.snd R A B) ∘ₗ comul := by
  ext : 1
  · rw [comp_assoc, snd_comp_inl, comp_zero, comp_assoc, comul_comp_inl, ← comp_assoc,
      ← TensorProduct.map_comp, snd_comp_inl, TensorProduct.map_zero_left, zero_comp]
  · rw [comp_assoc, snd_comp_inr, comp_id, comp_assoc, comul_comp_inr, ← comp_assoc,
      ← TensorProduct.map_comp, snd_comp_inr, TensorProduct.map_id, id_comp]

@[simp] theorem counit_comp_inr : counit ∘ₗ inr R A B = counit := by ext; simp

@[simp] theorem counit_comp_inl : counit ∘ₗ inl R A B = counit := by ext; simp

instance instCoalgebra : Coalgebra R (A × B) where
  rTensor_counit_comp_comul := by
    ext : 1
    · rw [comp_assoc, comul_comp_inl, ← comp_assoc, rTensor_comp_map, counit_comp_inl,
        ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul, lTensor_comp_mk]
    · rw [comp_assoc, comul_comp_inr, ← comp_assoc, rTensor_comp_map, counit_comp_inr,
        ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul, lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    · rw [comp_assoc, comul_comp_inl, ← comp_assoc, lTensor_comp_map, counit_comp_inl,
        ← rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul, rTensor_comp_flip_mk]
    · rw [comp_assoc, comul_comp_inr, ← comp_assoc, lTensor_comp_map, counit_comp_inr,
        ← rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul, rTensor_comp_flip_mk]
  coassoc := by
    dsimp only [instCoalgebraStruct]
    ext x : 2 <;> dsimp only [comp_apply, LinearEquiv.coe_coe, coe_inl, coe_inr, coprod_apply]
    · simp only [map_zero, add_zero]
      simp_rw [← comp_apply, ← comp_assoc, rTensor_comp_map, lTensor_comp_map, coprod_inl,
        ← map_comp_rTensor, ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq, comp_apply, LinearEquiv.coe_coe]
    · simp only [map_zero, zero_add]
      simp_rw [← comp_apply, ← comp_assoc, rTensor_comp_map, lTensor_comp_map, coprod_inr,
        ← map_comp_rTensor, ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq, comp_apply, LinearEquiv.coe_coe]

end Prod

namespace Finsupp
variable (R : Type u) (ι : Type v) (A : Type w)
variable [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]

open LinearMap

instance instCoalgebraStruct : CoalgebraStruct R (ι →₀ A) where
  comul := Finsupp.lsum R fun i =>
    TensorProduct.map (Finsupp.lsingle i) (Finsupp.lsingle i) ∘ₗ comul
  counit := Finsupp.lsum R fun _ => counit

@[simp]
theorem comul_single (i : ι) (a : A) :
    comul (R := R) (Finsupp.single i a) =
      (TensorProduct.map (Finsupp.lsingle i) (Finsupp.lsingle i) : _ →ₗ[R] _) (comul a) :=
  lsum_single _ _ _ _

@[simp]
theorem counit_single (i : ι) (a : A) : counit (Finsupp.single i a) = counit (R := R) a :=
  lsum_single _ _ _ _

theorem comul_comp_lsingle (i : ι) :
    comul ∘ₗ (lsingle i : A →ₗ[R] _) = TensorProduct.map (lsingle i) (lsingle i) ∘ₗ comul := by
  ext; simp

theorem comul_comp_lapply (i : ι) :
    comul ∘ₗ (lapply i : _ →ₗ[R] A) = TensorProduct.map (lapply i) (lapply i) ∘ₗ comul := by
  ext j : 1
  conv_rhs => rw [comp_assoc, comul_comp_lsingle, ← comp_assoc, ← TensorProduct.map_comp]
  obtain rfl | hij := eq_or_ne i j
  · rw [comp_assoc, lapply_comp_lsingle_same, comp_id,  TensorProduct.map_id, id_comp]
  · rw [comp_assoc, lapply_comp_lsingle_of_ne _ _ hij, comp_zero, TensorProduct.map_zero_left,
      zero_comp]

@[simp] theorem counit_comp_lsingle (i : ι) : counit ∘ₗ (lsingle i : A →ₗ[R] _) = counit := by
  ext; simp

/-- The `R`-module whose elements are functions `ι → A` which are zero on all but finitely many
elements of `ι` has a coalgebra structure. The coproduct `Δ` is given by `Δ(fᵢ a) = fᵢ a₁ ⊗ fᵢ a₂`
where `Δ(a) = a₁ ⊗ a₂` and the counit `ε` by `ε(fᵢ a) = ε(a)`, where `fᵢ a` is the function sending
`i` to `a` and all other elements of `ι` to zero. -/
instance instCoalgebra : Coalgebra R (ι →₀ A) where
  rTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc, comul_comp_lsingle, ← comp_assoc, rTensor_comp_map, counit_comp_lsingle,
      ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul, lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc, comul_comp_lsingle, ← comp_assoc, lTensor_comp_map, counit_comp_lsingle,
      ← rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul, rTensor_comp_flip_mk]
  coassoc := by
    ext i : 1
    simp_rw [comp_assoc, comul_comp_lsingle, ← comp_assoc, lTensor_comp_map, comul_comp_lsingle,
      comp_assoc, ← comp_assoc comul, rTensor_comp_map, comul_comp_lsingle, ← map_comp_rTensor,
      ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc comul, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq]

end Finsupp

end CommSemiring
