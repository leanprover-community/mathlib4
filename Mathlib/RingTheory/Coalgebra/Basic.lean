/-
Copyright (c) 2023 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Coalgebras

In this file we define `Coalgebra`, and provide instances for:

* Commutative semirings: `CommSemiring.toCoalgebra`
* Binary products: `Prod.instCoalgebra`
* Finitely supported functions: `DFinsupp.instCoalgebra`, `Finsupp.instCoalgebra`
* Finite pi functions: `Pi.instCoalgebra`

## References

* <https://en.wikipedia.org/wiki/Coalgebra>
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

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

@[inherit_doc] scoped[RingTheory.LinearMap] notation "ε" => CoalgebraStruct.counit
@[inherit_doc] scoped[RingTheory.LinearMap] notation "δ" => CoalgebraStruct.comul

/--
A representation of an element `a` of a coalgebra `A` is a finite sum of pure tensors `∑ xᵢ ⊗ yᵢ`
that is equal to `comul a`.
-/
structure Coalgebra.Repr (R : Type u) {A : Type v}
    [CommSemiring R] [AddCommMonoid A] [Module R A] [CoalgebraStruct R A] (a : A) where
  /-- the indexing type of a representation of `comul a` -/
  {ι : Type*}
  /-- the finite indexing set of a representation of `comul a` -/
  (index : Finset ι)
  /-- the first coordinate of a representation of `comul a` -/
  (left : ι → A)
  /-- the second coordinate of a representation of `comul a` -/
  (right : ι → A)
  /-- `comul a` is equal to a finite sum of some pure tensors -/
  (eq : ∑ i ∈ index, left i ⊗ₜ[R] right i = CoalgebraStruct.comul a)

/-- An arbitrarily chosen representation. -/
noncomputable def Coalgebra.Repr.arbitrary (R : Type u) {A : Type v}
    [CommSemiring R] [AddCommMonoid A] [Module R A] [CoalgebraStruct R A] (a : A) :
    Coalgebra.Repr R a where
  left := Prod.fst
  right := Prod.snd
  index := TensorProduct.exists_finset (R := R) (CoalgebraStruct.comul a) |>.choose
  eq := TensorProduct.exists_finset (R := R) (CoalgebraStruct.comul a) |>.choose_spec.symm

@[inherit_doc Coalgebra.Repr.arbitrary]
scoped[Coalgebra] notation "ℛ" => Coalgebra.Repr.arbitrary

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
variable [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A] {a : A}

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

@[simp]
lemma sum_counit_tmul_eq {a : A} (repr : Coalgebra.Repr R a) :
    ∑ i ∈ repr.index, counit (R := R) (repr.left i) ⊗ₜ (repr.right i) = 1 ⊗ₜ[R] a := by
  simpa [← repr.eq, map_sum] using congr($(rTensor_counit_comp_comul (R := R) (A := A)) a)

@[simp]
lemma sum_tmul_counit_eq {a : A} (repr : Coalgebra.Repr R a) :
    ∑ i ∈ repr.index, (repr.left i) ⊗ₜ counit (R := R) (repr.right i) = a ⊗ₜ[R] 1 := by
  simpa [← repr.eq, map_sum] using congr($(lTensor_counit_comp_comul (R := R) (A := A)) a)

-- Cannot be @[simp] because `a₂` cannot be inferred by `simp`.
lemma sum_tmul_tmul_eq {a : A} (repr : Repr R a)
    (a₁ : (i : repr.ι) → Repr R (repr.left i)) (a₂ : (i : repr.ι) → Repr R (repr.right i)) :
    ∑ i ∈ repr.index, ∑ j ∈ (a₁ i).index,
      (a₁ i).left j ⊗ₜ[R] ((a₁ i).right j ⊗ₜ[R] repr.right i)
      = ∑ i ∈ repr.index, ∑ j ∈ (a₂ i).index,
      repr.left i ⊗ₜ[R] ((a₂ i).left j ⊗ₜ[R] (a₂ i).right j) := by
  simpa [(a₂ _).eq, ← (a₁ _).eq, ← TensorProduct.tmul_sum,
    TensorProduct.sum_tmul, ← repr.eq] using congr($(coassoc (R := R)) a)

@[simp]
theorem sum_counit_tmul_map_eq {B : Type*} [AddCommMonoid B] [Module R B]
    {F : Type*} [FunLike F A B] [LinearMapClass F R A B] (f : F) (a : A) {repr : Repr R a} :
    ∑ i ∈ repr.index, counit (R := R) (repr.left i) ⊗ₜ f (repr.right i) = 1 ⊗ₜ[R] f a := by
  have := sum_counit_tmul_eq repr
  apply_fun LinearMap.lTensor R (f : A →ₗ[R] B) at this
  simp_all only [map_sum, LinearMap.lTensor_tmul, LinearMap.coe_coe]

@[simp]
theorem sum_map_tmul_counit_eq {B : Type*} [AddCommMonoid B] [Module R B]
    {F : Type*} [FunLike F A B] [LinearMapClass F R A B] (f : F) (a : A) {repr : Repr R a} :
    ∑ i ∈ repr.index, f (repr.left i) ⊗ₜ counit (R := R) (repr.right i) = f a ⊗ₜ[R] 1 := by
  have := sum_tmul_counit_eq repr
  apply_fun LinearMap.rTensor R (f : A →ₗ[R] B) at this
  simp_all only [map_sum, LinearMap.rTensor_tmul, LinearMap.coe_coe]

-- Cannot be @[simp] because `a₁` cannot be inferred by `simp`.
theorem sum_map_tmul_tmul_eq {B : Type*} [AddCommMonoid B] [Module R B]
    {F : Type*} [FunLike F A B] [LinearMapClass F R A B] (f g h : F) (a : A) {repr : Repr R a}
    {a₁ : (i : repr.ι) → Repr R (repr.left i)} {a₂ : (i : repr.ι) → Repr R (repr.right i)} :
    ∑ i ∈ repr.index, ∑ j ∈ (a₂ i).index,
      f (repr.left i) ⊗ₜ (g ((a₂ i).left j) ⊗ₜ h ((a₂ i).right j)) =
    ∑ i ∈ repr.index, ∑ j ∈ (a₁ i).index,
      f ((a₁ i).left j) ⊗ₜ[R] (g ((a₁ i).right j) ⊗ₜ[R] h (repr.right i)) := by
  have := sum_tmul_tmul_eq repr a₁ a₂
  apply_fun TensorProduct.map (f : A →ₗ[R] B)
    (TensorProduct.map (g : A →ₗ[R] B) (h : A →ₗ[R] B)) at this
  simp_all only [map_sum, TensorProduct.map_tmul, LinearMap.coe_coe]

lemma sum_counit_smul (𝓡 : Repr R a) :
    ∑ x ∈ 𝓡.index, counit (R := R) (𝓡.left x) • 𝓡.right x = a := by
  simpa only [map_sum, TensorProduct.lift.tmul, LinearMap.lsmul_apply, one_smul]
    using congr(TensorProduct.lift (LinearMap.lsmul R A) $(sum_counit_tmul_eq (R := R) 𝓡))

lemma lift_lsmul_comp_counit_comp_comul :
    TensorProduct.lift (.lsmul R A ∘ₗ counit) ∘ₗ comul = .id := by
  have := rTensor_counit_comp_comul (R := R) (A := A)
  apply_fun (TensorProduct.lift (LinearMap.lsmul R A) ∘ₗ ·) at this
  rw [LinearMap.rTensor, ← LinearMap.comp_assoc, TensorProduct.lift_comp_map, LinearMap.compl₂_id]
    at this
  ext
  simp [this]

variable (R A) in
/-- A coalgebra `A` is cocommutative if its comultiplication `δ : A → A ⊗ A` commutes with the
swapping `β : A ⊗ A ≃ A ⊗ A` of the factors in the tensor product. -/
class IsCocomm where
  protected comm_comp_comul : (TensorProduct.comm R A A).comp comul = comul

variable [IsCocomm R A]

variable (R A) in
@[simp] lemma comm_comp_comul : (TensorProduct.comm R A A).comp comul = comul :=
  IsCocomm.comm_comp_comul

variable (R) in
@[simp] lemma comm_comul (a : A) : TensorProduct.comm R A A (comul a) = comul a :=
  congr($(comm_comp_comul R A) a)

end Coalgebra

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

instance : IsCocomm R R where comm_comp_comul := by ext; simp

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
    dsimp +instances only [instCoalgebraStruct]
    ext x : 2 <;> dsimp only [comp_apply, LinearEquiv.coe_coe, coe_inl, coe_inr, coprod_apply]
    · simp only [map_zero, add_zero]
      simp_rw [← comp_apply, ← comp_assoc, rTensor_comp_map, lTensor_comp_map, coprod_inl,
        ← map_comp_rTensor, ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq, comp_apply, LinearEquiv.coe_coe]
    · simp only [map_zero, zero_add]
      simp_rw [← comp_apply, ← comp_assoc, rTensor_comp_map, lTensor_comp_map, coprod_inr,
        ← map_comp_rTensor, ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc,
        TensorProduct.map_map_comp_assoc_eq, comp_apply, LinearEquiv.coe_coe]

instance [IsCocomm R A] [IsCocomm R B] : IsCocomm R (A × B) where
  comm_comp_comul := by ext <;> simp [← TensorProduct.map_comm]

end Prod

namespace DFinsupp
variable (R : Type u) (ι : Type v) (A : ι → Type w)
variable [DecidableEq ι]
variable [CommSemiring R] [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]

open LinearMap

section coalgebraStruct
variable [∀ i, CoalgebraStruct R (A i)]

instance instCoalgebraStruct : CoalgebraStruct R (Π₀ i, A i) where
  comul := DFinsupp.lsum R fun i =>
    TensorProduct.map (DFinsupp.lsingle i) (DFinsupp.lsingle i) ∘ₗ comul
  counit := DFinsupp.lsum R fun _ => counit

@[simp]
theorem comul_single (i : ι) (a : A i) :
    comul (R := R) (DFinsupp.single i a) =
      (TensorProduct.map (DFinsupp.lsingle i) (DFinsupp.lsingle i) : _ →ₗ[R] _) (comul a) :=
  lsum_single _ _ _ _

@[simp]
theorem counit_single (i : ι) (a : A i) : counit (DFinsupp.single i a) = counit (R := R) a :=
  lsum_single _ _ _ _

theorem comul_comp_lsingle (i : ι) :
    comul ∘ₗ (lsingle i : A i →ₗ[R] _) = TensorProduct.map (lsingle i) (lsingle i) ∘ₗ comul := by
  ext; simp

theorem comul_comp_lapply (i : ι) :
    comul ∘ₗ (lapply i : _ →ₗ[R] A i) = TensorProduct.map (lapply i) (lapply i) ∘ₗ comul := by
  ext j
  have := eq_or_ne i j
  aesop (add simp [TensorProduct.map_map, proj_comp_single, diag])

@[simp] theorem counit_comp_lsingle (i : ι) : counit ∘ₗ (lsingle i : A i →ₗ[R] _) = counit := by
  ext; simp

end coalgebraStruct

variable [∀ i, Coalgebra R (A i)]

/-- The `R`-module whose elements are dependent functions `(i : ι) → A i` which are zero on all but
finitely many elements of `ι` has a coalgebra structure.

The coproduct `Δ` is given by `Δ(fᵢ a) = fᵢ a₁ ⊗ fᵢ a₂` where `Δ(a) = a₁ ⊗ a₂` and the counit `ε`
by `ε(fᵢ a) = ε(a)`, where `fᵢ a` is the function sending `i` to `a` and all other elements of `ι`
to zero. -/
instance instCoalgebra : Coalgebra R (Π₀ i, A i) where
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

instance instIsCocomm [∀ i, IsCocomm R (A i)] : IsCocomm R (Π₀ i, A i) where
  comm_comp_comul := by ext; simp [← TensorProduct.map_comm]

end DFinsupp

namespace Finsupp
variable (R : Type u) (ι : Type v) (A : Type w)
variable [CommSemiring R] [AddCommMonoid A] [Module R A]

open LinearMap

section coalgebraStruct
variable [CoalgebraStruct R A]

noncomputable instance instCoalgebraStruct : CoalgebraStruct R (ι →₀ A) where
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
  ext j; have := eq_or_ne i j
  aesop (add simp [TensorProduct.map_map, proj_comp_single, diag])

@[simp] theorem counit_comp_lsingle (i : ι) : counit ∘ₗ (lsingle i : A →ₗ[R] _) = counit := by
  ext; simp

end coalgebraStruct

variable [Coalgebra R A]

/-- The `R`-module whose elements are functions `ι → A` which are zero on all but finitely many
elements of `ι` has a coalgebra structure. The coproduct `Δ` is given by `Δ(fᵢ a) = fᵢ a₁ ⊗ fᵢ a₂`
where `Δ(a) = a₁ ⊗ a₂` and the counit `ε` by `ε(fᵢ a) = ε(a)`, where `fᵢ a` is the function sending
`i` to `a` and all other elements of `ι` to zero. -/
noncomputable instance instCoalgebra : Coalgebra R (ι →₀ A) where
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

instance instIsCocomm [IsCocomm R A] : IsCocomm R (ι →₀ A) where
  comm_comp_comul := by ext; simp [← TensorProduct.map_comm]

end Finsupp

namespace Pi
variable {R n : Type*} [CommSemiring R] [Fintype n] [DecidableEq n]
  {A : n → Type*} [Π i, AddCommMonoid (A i)] [Π i, Module R (A i)]

open TensorProduct LinearMap

section coalgebraStruct
variable [Π i, CoalgebraStruct R (A i)]

instance instCoalgebraStruct : CoalgebraStruct R (Π i, A i) where
  comul := .lsum R _ R fun i ↦ map (.single R _ i) (.single R _ i) ∘ₗ comul
  counit := .lsum R _ R fun _ ↦ counit

@[simp] theorem comul_single (i : n) (a : A i) :
    comul (single i a) = map (.single R _ i) (.single R _ i) (comul a) :=
  lsum_piSingle _ _ _ _ _ _

@[simp] theorem counit_single (i : n) (a : A i) : counit (single i a) = counit (R := R) a :=
  lsum_piSingle _ _ _ _ _ _

theorem comul_comp_single (i : n) :
    comul ∘ₗ .single R _ i = map (.single R A i) (.single R A i) ∘ₗ comul := by
  ext; simp

theorem comul_comp_proj (i : n) :
    comul ∘ₗ (proj i : (Π i, A i) →ₗ[R] A i) = map (proj i) (proj i) ∘ₗ comul := by
  ext j; have := eq_or_ne i j
  aesop (add simp [map_map, proj_comp_single, diag])

@[simp] theorem counit_comp_single (i : n) : counit ∘ₗ .single R A i = counit := by ext; simp

theorem counit_comp_dFinsuppCoeFnLinearMap :
    counit (R := R) (A := Π i, A i) ∘ₗ DFinsupp.coeFnLinearMap _ = counit := by
  apply LinearMap.ext fun x ↦ ?_
  have (i : n) (x : A i) : Decidable (x ≠ 0) := Classical.propDecidable _
  rw [← DFinsupp.sum_single (f := x)]
  simp [DFinsupp.single_eq_pi_single]

@[simp] theorem counit_coe_dFinsupp (x : Π₀ i, A i) :
    counit (R := R) ⇑x = counit x := congr($counit_comp_dFinsuppCoeFnLinearMap x)

open DFinsupp in
theorem comul_comp_dFinsuppCoeFnLinearMap :
    comul (R := R) (A := Π i, A i) ∘ₗ coeFnLinearMap _ =
      map (coeFnLinearMap _) (coeFnLinearMap _) ∘ₗ comul := by
  apply LinearMap.ext fun x ↦ ?_
  have (i : n) (x : A i) : Decidable (x ≠ 0) := Classical.propDecidable _
  rw [← DFinsupp.sum_single (f := x)]
  aesop (add simp [map_map, DFinsupp.single_eq_pi_single])

open DFinsupp in
@[simp] theorem comul_coe_dFinsupp (x : Π₀ i, A i) :
    comul (R := R) ⇑x = map (coeFnLinearMap _) (coeFnLinearMap _) (comul x) :=
  congr($comul_comp_dFinsuppCoeFnLinearMap x)

variable {M : Type*} [AddCommMonoid M] [Module R M] [CoalgebraStruct R M]

theorem counit_comp_finsuppLcoeFun :
    counit (R := R) (A := n → M) ∘ₗ Finsupp.lcoeFun = counit := by
  apply LinearMap.ext fun x ↦ ?_
  rw [← Finsupp.univ_sum_single x]
  simp [-Finsupp.univ_sum_single, Finsupp.lcoeFun, Finsupp.single_eq_pi_single]

@[simp] theorem counit_coe_finsupp (x : n →₀ M) :
    counit (R := R) ⇑x = counit x := congr($counit_comp_finsuppLcoeFun x)

open Finsupp in
theorem comul_comp_finsuppLcoeFun :
    comul (R := R) (A := n → M) ∘ₗ lcoeFun = map lcoeFun lcoeFun ∘ₗ comul := by
  apply LinearMap.ext fun x ↦ ?_
  rw [← Finsupp.univ_sum_single x]
  simp [-univ_sum_single, single_eq_pi_single, map_map]

open Finsupp in
@[simp] theorem comul_coe_finsupp (x : n →₀ M) :
    comul (R := R) ⇑x = map lcoeFun lcoeFun (comul x) :=
  congr($comul_comp_finsuppLcoeFun x)

end coalgebraStruct

variable [Π i, Coalgebra R (A i)]

/-- The `R`-module whose elements are functions `Π i, A i` for finite `n` has a coalgebra structure.
The coproduct `Δ` is given by `Δ(fᵢ a) = fᵢ a₁ ⊗ fᵢ a₂` where `Δ(a) = a₁ ⊗ a₂` and
the counit `ε` by `ε(fᵢ a) = ε(a)`, where `fᵢ a` is the function sending `i` to `a` and all
other elements of `ι` to zero. -/
instance instCoalgebra : Coalgebra R (Π i, A i) where
  rTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc, comul_comp_single, ← comp_assoc, rTensor_comp_map, counit_comp_single,
      ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul, lTensor_comp_mk]
  lTensor_counit_comp_comul := by
    ext : 1
    rw [comp_assoc, comul_comp_single, ← comp_assoc, lTensor_comp_map, counit_comp_single,
      ← rTensor_comp_lTensor, comp_assoc, lTensor_counit_comp_comul, rTensor_comp_flip_mk]
  coassoc := by
    ext : 1
    simp_rw [comp_assoc, comul_comp_single, ← comp_assoc, lTensor_comp_map, comul_comp_single,
      comp_assoc, ← comp_assoc comul, rTensor_comp_map, comul_comp_single, ← map_comp_rTensor,
      ← map_comp_lTensor, comp_assoc, ← coassoc, ← comp_assoc comul, ← comp_assoc,
      map_map_comp_assoc_eq]

instance instIsCocomm [∀ i, IsCocomm R (A i)] : IsCocomm R (Π i, A i) where
  comm_comp_comul := by ext; simp [← map_comm]

end Pi

namespace Equiv
variable {R A B : Type*} [CommSemiring R]

variable (R) in
/-- Transfer `CoalgebraStruct` across an `Equiv`. -/
abbrev coalgebraStruct [AddCommMonoid B] [Module R B] [CoalgebraStruct R B] (e : A ≃ B) :
    letI := e.addCommMonoid
    letI := e.module R
    CoalgebraStruct R A :=
  letI := e.addCommMonoid
  letI := e.module R
  { comul :=
      TensorProduct.map (e.linearEquiv R).symm.toLinearMap (e.linearEquiv R).symm.toLinearMap ∘ₗ
        comul ∘ₗ (e.linearEquiv R).toLinearMap
    counit := counit ∘ₗ (e.linearEquiv R).toLinearMap }

variable (R) in
/-- Transfer `Coalgebra` across an `Equiv`. -/
abbrev coalgebra [AddCommMonoid B] [Module R B] [Coalgebra R B] (e : A ≃ B) :
    letI := e.addCommMonoid
    letI := e.module R
    Coalgebra R A :=
  letI := e.addCommMonoid
  letI := e.module R
  { __ := e.coalgebraStruct R
    rTensor_counit_comp_comul := by
      ext
      apply (TensorProduct.map_bijective (f := .id) Function.bijective_id
        (e.linearEquiv R).bijective).injective
      simpa +instances [coalgebraStruct, LinearMap.comp_assoc, TensorProduct.map_map,
        LinearMap.rTensor] using Coalgebra.rTensor_counit_comul _
    lTensor_counit_comp_comul := by
      ext
      apply (TensorProduct.map_bijective (g := .id) (e.linearEquiv R).bijective
        Function.bijective_id).injective
      simpa +instances [coalgebraStruct, LinearMap.comp_assoc, TensorProduct.map_map,
        LinearMap.lTensor] using Coalgebra.lTensor_counit_comul _
    coassoc := by
      ext
      apply (TensorProduct.map_bijective (e.linearEquiv R).bijective <|
        TensorProduct.map_bijective (e.linearEquiv R).bijective
        (e.linearEquiv R).bijective).injective
      simp +instances [coalgebraStruct, e.tensorProductAssoc_def R, TensorProduct.congr,
        ← LinearMap.comp_assoc, TensorProduct.map_map, ← TensorProduct.map_comp]
      simpa [LinearMap.comp_assoc, -coassoc_apply] using coassoc_apply (R := R) (A := B) _ }

variable (R) in
/-- Transfer `Coalgebra.IsCocomm` across an `Equiv`. -/
lemma coalgebraIsCocomm [AddCommMonoid B] [Module R B] [Coalgebra R B] [IsCocomm R B] (e : A ≃ B) :
    letI := e.addCommMonoid
    letI := e.module R
    letI := e.coalgebra R
    IsCocomm R A :=
  letI := e.addCommMonoid
  letI := e.module R
  letI := e.coalgebra R
  { comm_comp_comul := by ext; simp [comul, ← TensorProduct.map_comm] }

end Equiv
