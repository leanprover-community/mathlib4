/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.Multilinear.Basic

#align_import linear_algebra.tensor_algebra.basic from "leanprover-community/mathlib"@"b8d2eaa69d69ce8f03179a5cda774fc0cde984e4"

/-!
# Tensor Algebras

Given a commutative semiring `R`, and an `R`-module `M`, we construct the tensor algebra of `M`.
This is the free `R`-algebra generated (`R`-linearly) by the module `M`.

## Notation

1. `TensorAlgebra R M` is the tensor algebra itself. It is endowed with an R-algebra structure.
2. `TensorAlgebra.ι R` is the canonical R-linear map `M → TensorAlgebra R M`.
3. Given a linear map `f : M → A` to an R-algebra `A`, `lift R f` is the lift of `f` to an
  `R`-algebra morphism `TensorAlgebra R M → A`.

## Theorems

1. `ι_comp_lift` states that the composition `(lift R f) ∘ (ι R)` is identical to `f`.
2. `lift_unique` states that whenever an R-algebra morphism `g : TensorAlgebra R M → A` is
  given whose composition with `ι R` is `f`, then one has `g = lift R f`.
3. `hom_ext` is a variant of `lift_unique` in the form of an extensionality theorem.
4. `lift_comp_ι` is a combination of `ι_comp_lift` and `lift_unique`. It states that the lift
  of the composition of an algebra morphism with `ι` is the algebra morphism itself.

## Implementation details

As noted above, the tensor algebra of `M` is constructed as the free `R`-algebra generated by `M`,
modulo the additional relations making the inclusion of `M` into an `R`-linear map.
-/


variable (R : Type*) [CommSemiring R]

variable (M : Type*) [AddCommMonoid M] [Module R M]

namespace TensorAlgebra

/-- An inductively defined relation on `Pre R M` used to force the initial algebra structure on
the associated quotient.
-/
inductive Rel : FreeAlgebra R M → FreeAlgebra R M → Prop
  -- force `ι` to be linear
  | add {a b : M} : Rel (FreeAlgebra.ι R (a + b)) (FreeAlgebra.ι R a + FreeAlgebra.ι R b)
  | smul {r : R} {a : M} :
    Rel (FreeAlgebra.ι R (r • a)) (algebraMap R (FreeAlgebra R M) r * FreeAlgebra.ι R a)
#align tensor_algebra.rel TensorAlgebra.Rel

end TensorAlgebra

/-- The tensor algebra of the module `M` over the commutative semiring `R`.
-/
def TensorAlgebra :=
  RingQuot (TensorAlgebra.Rel R M)
#align tensor_algebra TensorAlgebra

-- Porting note: Expanded `deriving Inhabited, Semiring, Algebra`
instance : Inhabited (TensorAlgebra R M) := RingQuot.instInhabited _
instance : Semiring (TensorAlgebra R M) := RingQuot.instSemiring _

-- `IsScalarTower` is not needed, but the instance isn't really canonical without it.
@[nolint unusedArguments]
instance instAlgebra {R A M} [CommSemiring R] [AddCommMonoid M] [CommSemiring A]
    [Algebra R A] [Module R M] [Module A M]
    [IsScalarTower R A M] :
    Algebra R (TensorAlgebra A M) :=
  RingQuot.instAlgebra _

-- verify there is no diamond
-- but doesn't work at `reducible_and_instances` #10906
example : (algebraNat : Algebra ℕ (TensorAlgebra R M)) = instAlgebra := rfl

instance {R S A M} [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [CommSemiring A]
    [Algebra R A] [Algebra S A] [Module R M] [Module S M] [Module A M]
    [IsScalarTower R A M] [IsScalarTower S A M] :
    SMulCommClass R S (TensorAlgebra A M) :=
  RingQuot.instSMulCommClass _

instance {R S A M} [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [CommSemiring A]
    [SMul R S] [Algebra R A] [Algebra S A] [Module R M] [Module S M] [Module A M]
    [IsScalarTower R A M] [IsScalarTower S A M] [IsScalarTower R S A] :
    IsScalarTower R S (TensorAlgebra A M) :=
  RingQuot.instIsScalarTower _

namespace TensorAlgebra

instance {S : Type*} [CommRing S] [Module S M] : Ring (TensorAlgebra S M) :=
  RingQuot.instRing (Rel S M)

-- verify there is no diamond
-- but doesn't work at `reducible_and_instances` #10906
variable (S M : Type) [CommRing S] [AddCommGroup M] [Module S M] in
example : (algebraInt _ : Algebra ℤ (TensorAlgebra S M)) = instAlgebra := rfl

variable {M}

/-- The canonical linear map `M →ₗ[R] TensorAlgebra R M`.
-/
irreducible_def ι : M →ₗ[R] TensorAlgebra R M :=
  { toFun := fun m => RingQuot.mkAlgHom R _ (FreeAlgebra.ι R m)
    map_add' := fun x y => by
      rw [← (RingQuot.mkAlgHom R (Rel R M)).map_add]
      exact RingQuot.mkAlgHom_rel R Rel.add
    map_smul' := fun r x => by
      rw [← (RingQuot.mkAlgHom R (Rel R M)).map_smul]
      exact RingQuot.mkAlgHom_rel R Rel.smul }
#align tensor_algebra.ι TensorAlgebra.ι

theorem ringQuot_mkAlgHom_freeAlgebra_ι_eq_ι (m : M) :
    RingQuot.mkAlgHom R (Rel R M) (FreeAlgebra.ι R m) = ι R m := by
  rw [ι]
  rfl
#align tensor_algebra.ring_quot_mk_alg_hom_free_algebra_ι_eq_ι TensorAlgebra.ringQuot_mkAlgHom_freeAlgebra_ι_eq_ι

-- Porting note: Changed `irreducible_def` to `def` to get `@[simps symm_apply]` to work
/-- Given a linear map `f : M → A` where `A` is an `R`-algebra, `lift R f` is the unique lift
of `f` to a morphism of `R`-algebras `TensorAlgebra R M → A`.
-/
@[simps symm_apply]
def lift {A : Type*} [Semiring A] [Algebra R A] : (M →ₗ[R] A) ≃ (TensorAlgebra R M →ₐ[R] A) :=
  { toFun :=
      RingQuot.liftAlgHom R ∘ fun f =>
        ⟨FreeAlgebra.lift R (⇑f), fun x y (h : Rel R M x y) => by
          induction h <;>
            simp only [Algebra.smul_def, FreeAlgebra.lift_ι_apply, LinearMap.map_smulₛₗ,
              RingHom.id_apply, map_mul, AlgHom.commutes, map_add]⟩
    invFun := fun F => F.toLinearMap.comp (ι R)
    left_inv := fun f => by
      rw [ι]
      ext1 x
      exact (RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _).trans (FreeAlgebra.lift_ι_apply f x)
    right_inv := fun F =>
      RingQuot.ringQuot_ext' _ _ _ <|
        FreeAlgebra.hom_ext <|
          funext fun x => by
            rw [ι]
            exact
              (RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _).trans (FreeAlgebra.lift_ι_apply _ _) }
#align tensor_algebra.lift TensorAlgebra.lift

variable {R}

@[simp]
theorem ι_comp_lift {A : Type*} [Semiring A] [Algebra R A] (f : M →ₗ[R] A) :
    (lift R f).toLinearMap.comp (ι R) = f := by
  convert (lift R).symm_apply_apply f
#align tensor_algebra.ι_comp_lift TensorAlgebra.ι_comp_lift

@[simp]
theorem lift_ι_apply {A : Type*} [Semiring A] [Algebra R A] (f : M →ₗ[R] A) (x) :
    lift R f (ι R x) = f x := by
  conv_rhs => rw [← ι_comp_lift f]
#align tensor_algebra.lift_ι_apply TensorAlgebra.lift_ι_apply

@[simp]
theorem lift_unique {A : Type*} [Semiring A] [Algebra R A] (f : M →ₗ[R] A)
    (g : TensorAlgebra R M →ₐ[R] A) : g.toLinearMap.comp (ι R) = f ↔ g = lift R f := by
  rw [← (lift R).symm_apply_eq]
  simp only [lift, Equiv.coe_fn_symm_mk]
#align tensor_algebra.lift_unique TensorAlgebra.lift_unique

-- Marking `TensorAlgebra` irreducible makes `Ring` instances inaccessible on quotients.
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/algebra.2Esemiring_to_ring.20breaks.20semimodule.20typeclass.20lookup/near/212580241
-- For now, we avoid this by not marking it irreducible.
@[simp]
theorem lift_comp_ι {A : Type*} [Semiring A] [Algebra R A] (g : TensorAlgebra R M →ₐ[R] A) :
    lift R (g.toLinearMap.comp (ι R)) = g := by
  rw [← lift_symm_apply]
  exact (lift R).apply_symm_apply g
#align tensor_algebra.lift_comp_ι TensorAlgebra.lift_comp_ι

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem hom_ext {A : Type*} [Semiring A] [Algebra R A] {f g : TensorAlgebra R M →ₐ[R] A}
    (w : f.toLinearMap.comp (ι R) = g.toLinearMap.comp (ι R)) : f = g := by
  rw [← lift_symm_apply, ← lift_symm_apply] at w
  exact (lift R).symm.injective w
#align tensor_algebra.hom_ext TensorAlgebra.hom_ext

-- This proof closely follows `FreeAlgebra.induction`
/-- If `C` holds for the `algebraMap` of `r : R` into `TensorAlgebra R M`, the `ι` of `x : M`,
and is preserved under addition and muliplication, then it holds for all of `TensorAlgebra R M`.
-/
@[elab_as_elim]
theorem induction {C : TensorAlgebra R M → Prop}
    (algebraMap : ∀ r, C (algebraMap R (TensorAlgebra R M) r)) (ι : ∀ x, C (ι R x))
    (mul : ∀ a b, C a → C b → C (a * b)) (add : ∀ a b, C a → C b → C (a + b))
    (a : TensorAlgebra R M) : C a := by
  -- the arguments are enough to construct a subalgebra, and a mapping into it from M
  let s : Subalgebra R (TensorAlgebra R M) :=
    { carrier := C
      mul_mem' := @mul
      add_mem' := @add
      algebraMap_mem' := algebraMap }
  -- porting note: Added `h`. `h` is needed for `of`.
  let h : AddCommMonoid s := inferInstanceAs (AddCommMonoid (Subalgebra.toSubmodule s))
  let of : M →ₗ[R] s := (TensorAlgebra.ι R).codRestrict (Subalgebra.toSubmodule s) ι
  -- the mapping through the subalgebra is the identity
  have of_id : AlgHom.id R (TensorAlgebra R M) = s.val.comp (lift R of) := by
    ext
    simp only [AlgHom.toLinearMap_id, LinearMap.id_comp, AlgHom.comp_toLinearMap,
      LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, lift_ι_apply,
      Subalgebra.coe_val]
    erw [LinearMap.codRestrict_apply]
  -- finding a proof is finding an element of the subalgebra
  rw [← AlgHom.id_apply (R := R) a, of_id]
  exact Subtype.prop (lift R of a)
#align tensor_algebra.induction TensorAlgebra.induction

/-- The left-inverse of `algebraMap`. -/
def algebraMapInv : TensorAlgebra R M →ₐ[R] R :=
  lift R (0 : M →ₗ[R] R)
#align tensor_algebra.algebra_map_inv TensorAlgebra.algebraMapInv

variable (M)

theorem algebraMap_leftInverse :
    Function.LeftInverse algebraMapInv (algebraMap R <| TensorAlgebra R M) := fun x => by
  simp [algebraMapInv]
#align tensor_algebra.algebra_map_left_inverse TensorAlgebra.algebraMap_leftInverse

@[simp]
theorem algebraMap_inj (x y : R) :
    algebraMap R (TensorAlgebra R M) x = algebraMap R (TensorAlgebra R M) y ↔ x = y :=
  (algebraMap_leftInverse M).injective.eq_iff
#align tensor_algebra.algebra_map_inj TensorAlgebra.algebraMap_inj

@[simp]
theorem algebraMap_eq_zero_iff (x : R) : algebraMap R (TensorAlgebra R M) x = 0 ↔ x = 0 :=
  map_eq_zero_iff (algebraMap _ _) (algebraMap_leftInverse _).injective
#align tensor_algebra.algebra_map_eq_zero_iff TensorAlgebra.algebraMap_eq_zero_iff

@[simp]
theorem algebraMap_eq_one_iff (x : R) : algebraMap R (TensorAlgebra R M) x = 1 ↔ x = 1 :=
  map_eq_one_iff (algebraMap _ _) (algebraMap_leftInverse _).injective
#align tensor_algebra.algebra_map_eq_one_iff TensorAlgebra.algebraMap_eq_one_iff

/-- A `TensorAlgebra` over a nontrivial semiring is nontrivial. -/
instance [Nontrivial R] : Nontrivial (TensorAlgebra R M) :=
  (algebraMap_leftInverse M).injective.nontrivial

variable {M}

/-- The canonical map from `TensorAlgebra R M` into `TrivSqZeroExt R M` that sends
`TensorAlgebra.ι` to `TrivSqZeroExt.inr`. -/
def toTrivSqZeroExt [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    TensorAlgebra R M →ₐ[R] TrivSqZeroExt R M :=
  lift R (TrivSqZeroExt.inrHom R M)
#align tensor_algebra.to_triv_sq_zero_ext TensorAlgebra.toTrivSqZeroExt

@[simp]
theorem toTrivSqZeroExt_ι (x : M) [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    toTrivSqZeroExt (ι R x) = TrivSqZeroExt.inr x :=
  lift_ι_apply _ _
#align tensor_algebra.to_triv_sq_zero_ext_ι TensorAlgebra.toTrivSqZeroExt_ι

/-- The left-inverse of `ι`.

As an implementation detail, we implement this using `TrivSqZeroExt` which has a suitable
algebra structure. -/
def ιInv : TensorAlgebra R M →ₗ[R] M := by
  letI : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  haveI : IsCentralScalar R M := ⟨fun r m => rfl⟩
  exact (TrivSqZeroExt.sndHom R M).comp toTrivSqZeroExt.toLinearMap
#align tensor_algebra.ι_inv TensorAlgebra.ιInv

theorem ι_leftInverse : Function.LeftInverse ιInv (ι R : M → TensorAlgebra R M) := fun x => by
  -- porting note: needs the last two `simp` lemmas explicitly in order to use them
  simp [ιInv, (AlgHom.toLinearMap_apply), toTrivSqZeroExt_ι _]
#align tensor_algebra.ι_left_inverse TensorAlgebra.ι_leftInverse

variable (R)

@[simp]
theorem ι_inj (x y : M) : ι R x = ι R y ↔ x = y :=
  ι_leftInverse.injective.eq_iff
#align tensor_algebra.ι_inj TensorAlgebra.ι_inj

@[simp]
theorem ι_eq_zero_iff (x : M) : ι R x = 0 ↔ x = 0 := by rw [← ι_inj R x 0, LinearMap.map_zero]
#align tensor_algebra.ι_eq_zero_iff TensorAlgebra.ι_eq_zero_iff

variable {R}

@[simp]
theorem ι_eq_algebraMap_iff (x : M) (r : R) : ι R x = algebraMap R _ r ↔ x = 0 ∧ r = 0 := by
  refine' ⟨fun h => _, _⟩
  · letI : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
    haveI : IsCentralScalar R M := ⟨fun r m => rfl⟩
    have hf0 : toTrivSqZeroExt (ι R x) = (0, x) := lift_ι_apply _ _
    rw [h, AlgHom.commutes] at hf0
    have : r = 0 ∧ 0 = x := Prod.ext_iff.1 hf0
    exact this.symm.imp_left Eq.symm
  · rintro ⟨rfl, rfl⟩
    rw [LinearMap.map_zero, RingHom.map_zero]
#align tensor_algebra.ι_eq_algebra_map_iff TensorAlgebra.ι_eq_algebraMap_iff

@[simp]
theorem ι_ne_one [Nontrivial R] (x : M) : ι R x ≠ 1 := by
  rw [← (algebraMap R (TensorAlgebra R M)).map_one, Ne.def, ι_eq_algebraMap_iff]
  exact one_ne_zero ∘ And.right
#align tensor_algebra.ι_ne_one TensorAlgebra.ι_ne_one

/-- The generators of the tensor algebra are disjoint from its scalars. -/
theorem ι_range_disjoint_one :
    Disjoint (LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M))
      (1 : Submodule R (TensorAlgebra R M)) := by
  rw [Submodule.disjoint_def]
  rintro _ ⟨x, hx⟩ ⟨r, rfl⟩
  rw [Algebra.linearMap_apply, ι_eq_algebraMap_iff] at hx
  rw [hx.2, map_zero]
#align tensor_algebra.ι_range_disjoint_one TensorAlgebra.ι_range_disjoint_one

variable (R M)

/-- Construct a product of `n` elements of the module within the tensor algebra.

See also `PiTensorProduct.tprod`. -/
def tprod (n : ℕ) : MultilinearMap R (fun _ : Fin n => M) (TensorAlgebra R M) :=
  (MultilinearMap.mkPiAlgebraFin R n (TensorAlgebra R M)).compLinearMap fun _ => ι R
#align tensor_algebra.tprod TensorAlgebra.tprod

@[simp]
theorem tprod_apply {n : ℕ} (x : Fin n → M) : tprod R M n x = (List.ofFn fun i => ι R (x i)).prod :=
  rfl
#align tensor_algebra.tprod_apply TensorAlgebra.tprod_apply

variable {R M}

end TensorAlgebra

namespace FreeAlgebra

variable {R M}

/-- The canonical image of the `FreeAlgebra` in the `TensorAlgebra`, which maps
`FreeAlgebra.ι R x` to `TensorAlgebra.ι R x`. -/
def toTensor : FreeAlgebra R M →ₐ[R] TensorAlgebra R M :=
  FreeAlgebra.lift R (TensorAlgebra.ι R)
#align free_algebra.to_tensor FreeAlgebra.toTensor

@[simp]
theorem toTensor_ι (m : M) : FreeAlgebra.toTensor (FreeAlgebra.ι R m) = TensorAlgebra.ι R m := by
  simp [toTensor]
#align free_algebra.to_tensor_ι FreeAlgebra.toTensor_ι

end FreeAlgebra
