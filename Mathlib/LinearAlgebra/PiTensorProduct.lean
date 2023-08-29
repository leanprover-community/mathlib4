/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Eric Wieser
-/
import Mathlib.GroupTheory.Congruence
import Mathlib.LinearAlgebra.Multilinear.TensorProduct
import Mathlib.Tactic.LibrarySearch

#align_import linear_algebra.pi_tensor_product from "leanprover-community/mathlib"@"ce11c3c2a285bbe6937e26d9792fda4e51f3fe1a"

/-!
# Tensor product of an indexed family of modules over commutative semirings

We define the tensor product of an indexed family `s : ι → Type*` of modules over commutative
semirings. We denote this space by `⨂[R] i, s i` and define it as `FreeAddMonoid (R × ∀ i, s i)`
quotiented by the appropriate equivalence relation. The treatment follows very closely that of the
binary tensor product in `LinearAlgebra/TensorProduct.lean`.

## Main definitions

* `PiTensorProduct R s` with `R` a commutative semiring and `s : ι → Type*` is the tensor product
  of all the `s i`'s. This is denoted by `⨂[R] i, s i`.
* `tprod R f` with `f : ∀ i, s i` is the tensor product of the vectors `f i` over all `i : ι`.
  This is bundled as a multilinear map from `∀ i, s i` to `⨂[R] i, s i`.
* `liftAddHom` constructs an `AddMonoidHom` from `(⨂[R] i, s i)` to some space `F` from a
  function `φ : (R × ∀ i, s i) → F` with the appropriate properties.
* `lift φ` with `φ : MultilinearMap R s E` is the corresponding linear map
  `(⨂[R] i, s i) →ₗ[R] E`. This is bundled as a linear equivalence.
* `PiTensorProduct.reindex e` re-indexes the components of `⨂[R] i : ι, M` along `e : ι ≃ ι₂`.
* `PiTensorProduct.tmulEquiv` equivalence between a `TensorProduct` of `PiTensorProduct`s and
  a single `PiTensorProduct`.

## Notations

* `⨂[R] i, s i` is defined as localized notation in locale `TensorProduct`.
* `⨂ₜ[R] i, f i` with `f : ∀ i, f i` is defined globally as the tensor product of all the `f i`'s.

## Implementation notes

* We define it via `FreeAddMonoid (R × ∀ i, s i)` with the `R` representing a "hidden" tensor
  factor, rather than `FreeAddMonoid (∀ i, s i)` to ensure that, if `ι` is an empty type,
  the space is isomorphic to the base ring `R`.
* We have not restricted the index type `ι` to be a `Fintype`, as nothing we do here strictly
  requires it. However, problems may arise in the case where `ι` is infinite; use at your own
  caution.
* Instead of requiring `DecidableEq ι` as an argument to `PiTensorProduct` itself, we include it
  as an argument in the constructors of the relation. A decidability instance still has to come
  from somewhere due to the use of `Function.update`, but this hides it from the downstream user.
  See the implementation notes for `MultilinearMap` for an extended discussion of this choice.

## TODO

* Define tensor powers, symmetric subspace, etc.
* API for the various ways `ι` can be split into subsets; connect this with the binary
  tensor product.
* Include connection with holors.
* Port more of the API from the binary tensor product over to this case.

## Tags

multilinear, tensor, tensor product
-/


open Function

section Semiring

variable {ι ι₂ ι₃ : Type*}

variable {R : Type*} [CommSemiring R]

variable {R₁ R₂ : Type*}

variable {s : ι → Type*} [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable {E : Type*} [AddCommMonoid E] [Module R E]

variable {F : Type*} [AddCommMonoid F]

namespace PiTensorProduct

variable (R) (s)

/-- The relation on `FreeAddMonoid (R × ∀ i, s i)` that generates a congruence whose quotient is
the tensor product. -/
inductive Eqv : FreeAddMonoid (R × ∀ i, s i) → FreeAddMonoid (R × ∀ i, s i) → Prop
  | of_zero : ∀ (r : R) (f : ∀ i, s i) (i : ι) (_ : f i = 0), Eqv (FreeAddMonoid.of (r, f)) 0
  | of_zero_scalar : ∀ f : ∀ i, s i, Eqv (FreeAddMonoid.of (0, f)) 0
  | of_add : ∀ (_ : DecidableEq ι) (r : R) (f : ∀ i, s i) (i : ι) (m₁ m₂ : s i),
      Eqv (FreeAddMonoid.of (r, update f i m₁) + FreeAddMonoid.of (r, update f i m₂))
        (FreeAddMonoid.of (r, update f i (m₁ + m₂)))
  | of_add_scalar : ∀ (r r' : R) (f : ∀ i, s i),
      Eqv (FreeAddMonoid.of (r, f) + FreeAddMonoid.of (r', f)) (FreeAddMonoid.of (r + r', f))
  | of_smul : ∀ (_ : DecidableEq ι) (r : R) (f : ∀ i, s i) (i : ι) (r' : R),
      Eqv (FreeAddMonoid.of (r, update f i (r' • f i))) (FreeAddMonoid.of (r' * r, f))
  | add_comm : ∀ x y, Eqv (x + y) (y + x)
#align pi_tensor_product.eqv PiTensorProduct.Eqv

end PiTensorProduct

variable (R) (s)

/-- `PiTensorProduct R s` with `R` a commutative semiring and `s : ι → Type*` is the tensor
  product of all the `s i`'s. This is denoted by `⨂[R] i, s i`. -/
def PiTensorProduct : Type _ :=
  (addConGen (PiTensorProduct.Eqv R s)).Quotient
#align pi_tensor_product PiTensorProduct

variable {R}

-- This enables the notation `⨂[R] i : ι, s i` for the pi tensor product, given `s : ι → Type*`.
--scoped[TensorProduct] -- Porting note: `scoped` caused an error, so I commented it out.
/-- notation for tensor product over some indexed type -/
notation3:100"⨂["R"] "(...)", "r:(scoped f => PiTensorProduct R f) => r

open TensorProduct

namespace PiTensorProduct

section Module

instance : AddCommMonoid (⨂[R] i, s i) :=
  { (addConGen (PiTensorProduct.Eqv R s)).addMonoid with
    add_comm := fun x y ↦
      AddCon.induction_on₂ x y fun _ _ ↦
        Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.add_comm _ _ }

instance : Inhabited (⨂[R] i, s i) := ⟨0⟩

variable (R) {s}

/-- `tprodCoeff R r f` with `r : R` and `f : ∀ i, s i` is the tensor product of the vectors `f i`
over all `i : ι`, multiplied by the coefficient `r`. Note that this is meant as an auxiliary
definition for this file alone, and that one should use `tprod` defined below for most purposes. -/
def tprodCoeff (r : R) (f : ∀ i, s i) : ⨂[R] i, s i :=
  AddCon.mk' _ <| FreeAddMonoid.of (r, f)
#align pi_tensor_product.tprod_coeff PiTensorProduct.tprodCoeff

variable {R}

theorem zero_tprodCoeff (f : ∀ i, s i) : tprodCoeff R 0 f = 0 :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_zero_scalar _
#align pi_tensor_product.zero_tprod_coeff PiTensorProduct.zero_tprodCoeff

theorem zero_tprodCoeff' (z : R) (f : ∀ i, s i) (i : ι) (hf : f i = 0) : tprodCoeff R z f = 0 :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_zero _ _ i hf
#align pi_tensor_product.zero_tprod_coeff' PiTensorProduct.zero_tprodCoeff'

theorem add_tprodCoeff [DecidableEq ι] (z : R) (f : ∀ i, s i) (i : ι) (m₁ m₂ : s i) :
    tprodCoeff R z (update f i m₁) + tprodCoeff R z (update f i m₂) =
      tprodCoeff R z (update f i (m₁ + m₂)) :=
  Quotient.sound' <| AddConGen.Rel.of _ _ (Eqv.of_add _ z f i m₁ m₂)
#align pi_tensor_product.add_tprod_coeff PiTensorProduct.add_tprodCoeff

theorem add_tprodCoeff' (z₁ z₂ : R) (f : ∀ i, s i) :
    tprodCoeff R z₁ f + tprodCoeff R z₂ f = tprodCoeff R (z₁ + z₂) f :=
  Quotient.sound' <| AddConGen.Rel.of _ _ (Eqv.of_add_scalar z₁ z₂ f)
#align pi_tensor_product.add_tprod_coeff' PiTensorProduct.add_tprodCoeff'

theorem smul_tprodCoeff_aux [DecidableEq ι] (z : R) (f : ∀ i, s i) (i : ι) (r : R) :
    tprodCoeff R z (update f i (r • f i)) = tprodCoeff R (r * z) f :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_smul _ _ _ _ _
#align pi_tensor_product.smul_tprod_coeff_aux PiTensorProduct.smul_tprodCoeff_aux

theorem smul_tprodCoeff [DecidableEq ι] (z : R) (f : ∀ i, s i) (i : ι) (r : R₁) [SMul R₁ R]
    [IsScalarTower R₁ R R] [SMul R₁ (s i)] [IsScalarTower R₁ R (s i)] :
    tprodCoeff R z (update f i (r • f i)) = tprodCoeff R (r • z) f := by
  have h₁ : r • z = r • (1 : R) * z := by rw [smul_mul_assoc, one_mul]
  -- ⊢ tprodCoeff R z (update f i (r • f i)) = tprodCoeff R (r • z) f
  have h₂ : r • f i = (r • (1 : R)) • f i := (smul_one_smul _ _ _).symm
  -- ⊢ tprodCoeff R z (update f i (r • f i)) = tprodCoeff R (r • z) f
  rw [h₁, h₂]
  -- ⊢ tprodCoeff R z (update f i ((r • 1) • f i)) = tprodCoeff R (r • 1 * z) f
  exact smul_tprodCoeff_aux z f i _
  -- 🎉 no goals
#align pi_tensor_product.smul_tprod_coeff PiTensorProduct.smul_tprodCoeff

/-- Construct an `AddMonoidHom` from `(⨂[R] i, s i)` to some space `F` from a function
`φ : (R × ∀ i, s i) → F` with the appropriate properties. -/
def liftAddHom (φ : (R × ∀ i, s i) → F)
    (C0 : ∀ (r : R) (f : ∀ i, s i) (i : ι) (_ : f i = 0), φ (r, f) = 0)
    (C0' : ∀ f : ∀ i, s i, φ (0, f) = 0)
    (C_add : ∀ [DecidableEq ι] (r : R) (f : ∀ i, s i) (i : ι) (m₁ m₂ : s i),
      φ (r, update f i m₁) + φ (r, update f i m₂) = φ (r, update f i (m₁ + m₂)))
    (C_add_scalar : ∀ (r r' : R) (f : ∀ i, s i), φ (r, f) + φ (r', f) = φ (r + r', f))
    (C_smul : ∀ [DecidableEq ι] (r : R) (f : ∀ i, s i) (i : ι) (r' : R),
      φ (r, update f i (r' • f i)) = φ (r' * r, f)) :
    (⨂[R] i, s i) →+ F :=
  (addConGen (PiTensorProduct.Eqv R s)).lift (FreeAddMonoid.lift φ) <|
    AddCon.addConGen_le fun x y hxy ↦
      match hxy with
      | Eqv.of_zero r' f i hf =>
        (AddCon.ker_rel _).2 <| by simp [FreeAddMonoid.lift_eval_of, C0 r' f i hf]
                                   -- 🎉 no goals
      | Eqv.of_zero_scalar f =>
        (AddCon.ker_rel _).2 <| by simp [FreeAddMonoid.lift_eval_of, C0']
                                   -- 🎉 no goals
      | Eqv.of_add inst z f i m₁ m₂ =>
        (AddCon.ker_rel _).2 <| by simp [FreeAddMonoid.lift_eval_of, @C_add inst]
                                   -- 🎉 no goals
      | Eqv.of_add_scalar z₁ z₂ f =>
        (AddCon.ker_rel _).2 <| by simp [FreeAddMonoid.lift_eval_of, C_add_scalar]
                                   -- 🎉 no goals
      | Eqv.of_smul inst z f i r' =>
        (AddCon.ker_rel _).2 <| by simp [FreeAddMonoid.lift_eval_of, @C_smul inst]
                                   -- 🎉 no goals
      | Eqv.add_comm x y =>
        (AddCon.ker_rel _).2 <| by simp_rw [AddMonoidHom.map_add, add_comm]
                                   -- 🎉 no goals
#align pi_tensor_product.lift_add_hom PiTensorProduct.liftAddHom

@[elab_as_elim]
protected theorem induction_on' {C : (⨂[R] i, s i) → Prop} (z : ⨂[R] i, s i)
    (C1 : ∀ {r : R} {f : ∀ i, s i}, C (tprodCoeff R r f)) (Cp : ∀ {x y}, C x → C y → C (x + y)) :
    C z := by
  have C0 : C 0 := by
    have h₁ := @C1 0 0
    rwa [zero_tprodCoeff] at h₁
  refine' AddCon.induction_on z fun x ↦ FreeAddMonoid.recOn x C0 _
  -- ⊢ ∀ (x : R × ((i : ι) → (fun i => s i) i)) (xs : FreeAddMonoid (R × ((i : ι) → …
  simp_rw [AddCon.coe_add]
  -- ⊢ ∀ (x : R × ((i : ι) → (fun i => s i) i)) (xs : FreeAddMonoid (R × ((i : ι) → …
  refine' fun f y ih ↦ Cp _ ih
  -- ⊢ C ↑(FreeAddMonoid.of f)
  convert@C1 f.1 f.2
  -- 🎉 no goals
#align pi_tensor_product.induction_on' PiTensorProduct.induction_on'

section DistribMulAction

variable [Monoid R₁] [DistribMulAction R₁ R] [SMulCommClass R₁ R R]

variable [Monoid R₂] [DistribMulAction R₂ R] [SMulCommClass R₂ R R]

-- Most of the time we want the instance below this one, which is easier for typeclass resolution
-- to find.
instance hasSMul' : SMul R₁ (⨂[R] i, s i) :=
  ⟨fun r ↦
    liftAddHom (fun f : R × ∀ i, s i ↦ tprodCoeff R (r • f.1) f.2)
      (fun r' f i hf ↦ by simp_rw [zero_tprodCoeff' _ f i hf])
                          -- 🎉 no goals
      (fun f ↦ by simp [zero_tprodCoeff]) (fun r' f i m₁ m₂ ↦ by simp [add_tprodCoeff])
                  -- 🎉 no goals
                                                                 -- 🎉 no goals
      (fun r' r'' f ↦ by simp [add_tprodCoeff', mul_add]) fun z f i r' ↦ by
                         -- 🎉 no goals
      simp [smul_tprodCoeff, mul_smul_comm]⟩
      -- 🎉 no goals
#align pi_tensor_product.has_smul' PiTensorProduct.hasSMul'

instance : SMul R (⨂[R] i, s i) :=
  PiTensorProduct.hasSMul'

theorem smul_tprodCoeff' (r : R₁) (z : R) (f : ∀ i, s i) :
    r • tprodCoeff R z f = tprodCoeff R (r • z) f := rfl
#align pi_tensor_product.smul_tprod_coeff' PiTensorProduct.smul_tprodCoeff'

protected theorem smul_add (r : R₁) (x y : ⨂[R] i, s i) : r • (x + y) = r • x + r • y :=
  AddMonoidHom.map_add _ _ _
#align pi_tensor_product.smul_add PiTensorProduct.smul_add

instance distribMulAction' : DistribMulAction R₁ (⨂[R] i, s i) where
  smul := (· • ·)
  smul_add r x y := AddMonoidHom.map_add _ _ _
  mul_smul r r' x :=
    PiTensorProduct.induction_on' x (fun {r'' f} ↦ by simp [smul_tprodCoeff', smul_smul])
                                                      -- 🎉 no goals
      fun {x y} ihx ihy ↦ by simp_rw [PiTensorProduct.smul_add, ihx, ihy]
                             -- 🎉 no goals
                                                    -- 🎉 no goals
  one_smul x :=
                             -- 🎉 no goals
    PiTensorProduct.induction_on' x (fun {r f} ↦ by rw [smul_tprodCoeff', one_smul])
      fun {z y} ihz ihy ↦ by simp_rw [PiTensorProduct.smul_add, ihz, ihy]
  smul_zero r := AddMonoidHom.map_zero _
#align pi_tensor_product.distrib_mul_action' PiTensorProduct.distribMulAction'

instance smulCommClass' [SMulCommClass R₁ R₂ R] : SMulCommClass R₁ R₂ (⨂[R] i, s i) :=
  ⟨fun {r' r''} x ↦
    PiTensorProduct.induction_on' x (fun {xr xf} ↦ by simp only [smul_tprodCoeff', smul_comm])
                                                      -- 🎉 no goals
      fun {z y} ihz ihy ↦ by simp_rw [PiTensorProduct.smul_add, ihz, ihy]⟩
                             -- 🎉 no goals
#align pi_tensor_product.smul_comm_class' PiTensorProduct.smulCommClass'

instance isScalarTower' [SMul R₁ R₂] [IsScalarTower R₁ R₂ R] :
    IsScalarTower R₁ R₂ (⨂[R] i, s i) :=
  ⟨fun {r' r''} x ↦
    PiTensorProduct.induction_on' x (fun {xr xf} ↦ by simp only [smul_tprodCoeff', smul_assoc])
                                                      -- 🎉 no goals
      fun {z y} ihz ihy ↦ by simp_rw [PiTensorProduct.smul_add, ihz, ihy]⟩
                             -- 🎉 no goals
#align pi_tensor_product.is_scalar_tower' PiTensorProduct.isScalarTower'

end DistribMulAction

-- Most of the time we want the instance below this one, which is easier for typeclass resolution
-- to find.
instance module' [Semiring R₁] [Module R₁ R] [SMulCommClass R₁ R R] : Module R₁ (⨂[R] i, s i) :=
  { PiTensorProduct.distribMulAction' with
    smul := (· • ·)
    add_smul := fun r r' x ↦
      PiTensorProduct.induction_on' x
        (fun {r f} ↦ by simp_rw [smul_tprodCoeff', add_smul, add_tprodCoeff'])
                        -- 🎉 no goals
        fun {x y} ihx ihy ↦ by simp_rw [PiTensorProduct.smul_add, ihx, ihy, add_add_add_comm]
                               -- 🎉 no goals
    zero_smul := fun x ↦
      PiTensorProduct.induction_on' x
        (fun {r f} ↦ by simp_rw [smul_tprodCoeff', zero_smul, zero_tprodCoeff])
                        -- 🎉 no goals
        fun {x y} ihx ihy ↦ by simp_rw [PiTensorProduct.smul_add, ihx, ihy, add_zero] }
                               -- 🎉 no goals
#align pi_tensor_product.module' PiTensorProduct.module'

-- shortcut instances
instance : Module R (⨂[R] i, s i) :=
  PiTensorProduct.module'

instance : SMulCommClass R R (⨂[R] i, s i) :=
  PiTensorProduct.smulCommClass'

instance : IsScalarTower R R (⨂[R] i, s i) :=
  PiTensorProduct.isScalarTower'

variable (R)

/-- The canonical `MultilinearMap R s (⨂[R] i, s i)`. -/
def tprod : MultilinearMap R s (⨂[R] i, s i) where
  toFun := tprodCoeff R 1
  map_add' {_ f} i x y := (add_tprodCoeff (1 : R) f i x y).symm
  map_smul' {_ f} i r x := by
    rw [smul_tprodCoeff', ← smul_tprodCoeff (1 : R) _ i, update_idem, update_same]
    -- 🎉 no goals
#align pi_tensor_product.tprod PiTensorProduct.tprod

variable {R}

/-- pure tensor in tensor product over some index type -/
-- Porting note: use `FunLike.coe` as an explicit coercion to help `notation3` pretty print,
-- was just `tprod R f`.
notation3:100 "⨂ₜ["R"] "(...)", "r:(scoped f => FunLike.coe (tprod R) f) => r

--Porting note: new theorem
theorem tprod_eq_tprodCoeff_one :
  ⇑(tprod R : MultilinearMap R s (⨂[R] i, s i)) = tprodCoeff R 1 := rfl

@[simp]
theorem tprodCoeff_eq_smul_tprod (z : R) (f : ∀ i, s i) : tprodCoeff R z f = z • tprod R f := by
  have : z = z • (1 : R) := by simp only [mul_one, Algebra.id.smul_eq_mul]
  -- ⊢ tprodCoeff R z f = z • ↑(tprod R) f
  conv_lhs => rw [this]
  -- 🎉 no goals
#align pi_tensor_product.tprod_coeff_eq_smul_tprod PiTensorProduct.tprodCoeff_eq_smul_tprod

@[elab_as_elim]
protected theorem induction_on {C : (⨂[R] i, s i) → Prop} (z : ⨂[R] i, s i)
    (C1 : ∀ {r : R} {f : ∀ i, s i}, C (r • tprod R f)) (Cp : ∀ {x y}, C x → C y → C (x + y)) :
    C z := by
  simp_rw [← tprodCoeff_eq_smul_tprod] at C1
  -- ⊢ C z
  exact PiTensorProduct.induction_on' z @C1 @Cp
  -- 🎉 no goals
#align pi_tensor_product.induction_on PiTensorProduct.induction_on

@[ext]
theorem ext {φ₁ φ₂ : (⨂[R] i, s i) →ₗ[R] E}
    (H : φ₁.compMultilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂ := by
  refine' LinearMap.ext _
  -- ⊢ ∀ (x : ⨂[R] (i : ι), s i), ↑φ₁ x = ↑φ₂ x
  refine' fun z ↦
    PiTensorProduct.induction_on' z _ fun {x y} hx hy ↦ by rw [φ₁.map_add, φ₂.map_add, hx, hy]
  · intro r f
    -- ⊢ ↑φ₁ (tprodCoeff R r f) = ↑φ₂ (tprodCoeff R r f)
    rw [tprodCoeff_eq_smul_tprod, φ₁.map_smul, φ₂.map_smul]
    -- ⊢ r • ↑φ₁ (↑(tprod R) f) = r • ↑φ₂ (↑(tprod R) f)
    apply _root_.congr_arg
    -- ⊢ ↑φ₁ (↑(tprod R) f) = ↑φ₂ (↑(tprod R) f)
    exact MultilinearMap.congr_fun H f
    -- 🎉 no goals
#align pi_tensor_product.ext PiTensorProduct.ext

end Module

section Multilinear

open MultilinearMap

variable {s}

/-- Auxiliary function to constructing a linear map `(⨂[R] i, s i) → E` given a
`MultilinearMap R s E` with the property that its composition with the canonical
`MultilinearMap R s (⨂[R] i, s i)` is the given multilinear map. -/
def liftAux (φ : MultilinearMap R s E) : (⨂[R] i, s i) →+ E :=
  liftAddHom (fun p : R × ∀ i, s i ↦ p.1 • φ p.2)
    (fun z f i hf ↦ by simp_rw [map_coord_zero φ i hf, smul_zero])
                       -- 🎉 no goals
    (fun f ↦ by simp_rw [zero_smul])
                -- 🎉 no goals
    (fun z f i m₁ m₂ ↦ by simp_rw [← smul_add, φ.map_add])
                          -- 🎉 no goals
    (fun z₁ z₂ f ↦ by rw [← add_smul])
                      -- 🎉 no goals
    fun z f i r ↦ by simp [φ.map_smul, smul_smul, mul_comm]
                     -- 🎉 no goals
#align pi_tensor_product.lift_aux PiTensorProduct.liftAux

theorem liftAux_tprod (φ : MultilinearMap R s E) (f : ∀ i, s i) : liftAux φ (tprod R f) = φ f := by
  simp only [liftAux, liftAddHom, tprod_eq_tprodCoeff_one, tprodCoeff, AddCon.coe_mk']
  -- ⊢ ↑(AddCon.lift (addConGen (Eqv R fun i => s i)) (↑FreeAddMonoid.lift fun p => …
  rw [FreeAddMonoid.of, FreeAddMonoid.ofList, Equiv.refl_apply, AddCon.lift_coe]
  -- ⊢ ↑(↑FreeAddMonoid.lift fun p => p.fst • ↑φ p.snd) [(1, f)] = ↑φ f
  dsimp [FreeAddMonoid.lift, FreeAddMonoid.sumAux]
  -- ⊢ (FreeAddMonoid.sumAux.match_1 (fun x => E) [1 • ↑φ f] (fun _ => 0) fun x xs  …
  show _ • _ = _
  -- ⊢ 1 • ↑φ f = ↑φ f
  rw [one_smul]
  -- 🎉 no goals
#align pi_tensor_product.lift_aux_tprod PiTensorProduct.liftAux_tprod

theorem liftAux_tprodCoeff (φ : MultilinearMap R s E) (z : R) (f : ∀ i, s i) :
    liftAux φ (tprodCoeff R z f) = z • φ f := rfl
#align pi_tensor_product.lift_aux_tprod_coeff PiTensorProduct.liftAux_tprodCoeff

theorem liftAux.smul {φ : MultilinearMap R s E} (r : R) (x : ⨂[R] i, s i) :
    liftAux φ (r • x) = r • liftAux φ x := by
  refine' PiTensorProduct.induction_on' x _ _
  -- ⊢ ∀ {r_1 : R} {f : (i : ι) → s i}, ↑(liftAux φ) (r • tprodCoeff R r_1 f) = r • …
  · intro z f
    -- ⊢ ↑(liftAux φ) (r • tprodCoeff R z f) = r • ↑(liftAux φ) (tprodCoeff R z f)
    rw [smul_tprodCoeff' r z f, liftAux_tprodCoeff, liftAux_tprodCoeff, smul_assoc]
    -- 🎉 no goals
  · intro z y ihz ihy
    -- ⊢ ↑(liftAux φ) (r • (z + y)) = r • ↑(liftAux φ) (z + y)
    rw [smul_add, (liftAux φ).map_add, ihz, ihy, (liftAux φ).map_add, smul_add]
    -- 🎉 no goals
#align pi_tensor_product.lift_aux.smul PiTensorProduct.liftAux.smul

/-- Constructing a linear map `(⨂[R] i, s i) → E` given a `MultilinearMap R s E` with the
property that its composition with the canonical `MultilinearMap R s E` is
the given multilinear map `φ`. -/
def lift : MultilinearMap R s E ≃ₗ[R] (⨂[R] i, s i) →ₗ[R] E where
  toFun φ := { liftAux φ with map_smul' := liftAux.smul }
  invFun φ' := φ'.compMultilinearMap (tprod R)
  left_inv φ := by
    ext
    -- ⊢ ↑((fun φ' => LinearMap.compMultilinearMap φ' (tprod R))
    simp [liftAux_tprod, LinearMap.compMultilinearMap]
    -- 🎉 no goals
  right_inv φ := by
    ext
    -- ⊢ ↑(LinearMap.compMultilinearMap
    -- ⊢ ↑(LinearMap.compMultilinearMap
    simp [liftAux_tprod]
    -- 🎉 no goals
    -- 🎉 no goals
  map_add' φ₁ φ₂ := by
    -- ⊢ ↑(LinearMap.compMultilinearMap
    ext
    -- 🎉 no goals
    simp [liftAux_tprod]
  map_smul' r φ₂ := by
    ext
    simp [liftAux_tprod]
#align pi_tensor_product.lift PiTensorProduct.lift

variable {φ : MultilinearMap R s E}

@[simp]
theorem lift.tprod (f : ∀ i, s i) : lift φ (tprod R f) = φ f :=
  liftAux_tprod φ f
#align pi_tensor_product.lift.tprod PiTensorProduct.lift.tprod

theorem lift.unique' {φ' : (⨂[R] i, s i) →ₗ[R] E}
    (H : φ'.compMultilinearMap (PiTensorProduct.tprod R) = φ) : φ' = lift φ :=
  ext <| H.symm ▸ (lift.symm_apply_apply φ).symm
#align pi_tensor_product.lift.unique' PiTensorProduct.lift.unique'

theorem lift.unique {φ' : (⨂[R] i, s i) →ₗ[R] E} (H : ∀ f, φ' (PiTensorProduct.tprod R f) = φ f) :
    φ' = lift φ :=
  lift.unique' (MultilinearMap.ext H)
#align pi_tensor_product.lift.unique PiTensorProduct.lift.unique

@[simp]
theorem lift_symm (φ' : (⨂[R] i, s i) →ₗ[R] E) : lift.symm φ' = φ'.compMultilinearMap (tprod R) :=
  rfl
#align pi_tensor_product.lift_symm PiTensorProduct.lift_symm

@[simp]
theorem lift_tprod : lift (tprod R : MultilinearMap R s _) = LinearMap.id :=
  Eq.symm <| lift.unique' rfl
#align pi_tensor_product.lift_tprod PiTensorProduct.lift_tprod

section

variable (R M)

/-- Re-index the components of the tensor power by `e`.

For simplicity, this is defined only for homogeneously- (rather than dependently-) typed components.
-/
def reindex (e : ι ≃ ι₂) : (⨂[R] _ : ι, M) ≃ₗ[R] ⨂[R] _ : ι₂, M :=
  LinearEquiv.ofLinear (lift (domDomCongr e.symm (tprod R : MultilinearMap R _ (⨂[R] _ : ι₂, M))))
    (lift (domDomCongr e (tprod R : MultilinearMap R _ (⨂[R] _ : ι, M))))
    (by
      ext
      -- ⊢ ↑(LinearMap.compMultilinearMap (LinearMap.comp (↑lift (domDomCongr e.symm (t …
      simp only [LinearMap.comp_apply, LinearMap.id_apply, lift_tprod,
        LinearMap.compMultilinearMap_apply, lift.tprod, domDomCongr_apply]
      congr
      -- ⊢ (fun i => x✝ (↑e (↑e.symm i))) = x✝
      ext
      -- ⊢ x✝¹ (↑e (↑e.symm x✝)) = x✝¹ x✝
      rw [e.apply_symm_apply])
      -- 🎉 no goals
    (by
      ext
      -- ⊢ ↑(LinearMap.compMultilinearMap (LinearMap.comp (↑lift (domDomCongr e (tprod  …
      simp only [LinearMap.comp_apply, LinearMap.id_apply, lift_tprod,
        LinearMap.compMultilinearMap_apply, lift.tprod, domDomCongr_apply]
      congr
      -- ⊢ (fun i => x✝ (↑e.symm (↑e i))) = x✝
      ext
      -- ⊢ x✝¹ (↑e.symm (↑e x✝)) = x✝¹ x✝
      rw [e.symm_apply_apply])
      -- 🎉 no goals
#align pi_tensor_product.reindex PiTensorProduct.reindex

end

@[simp]
theorem reindex_tprod (e : ι ≃ ι₂) (f : ∀ _, M) :
    reindex R M e (tprod R f) = tprod R fun i ↦ f (e.symm i) := by
  dsimp [reindex]
  -- ⊢ ↑(↑lift (domDomCongr e.symm (tprod R))) (↑(tprod R) f) = ⨂ₜ[R] (i : ι₂), f ( …
  exact liftAux_tprod _ f
  -- 🎉 no goals
#align pi_tensor_product.reindex_tprod PiTensorProduct.reindex_tprod

@[simp]
theorem reindex_comp_tprod (e : ι ≃ ι₂) :
    (reindex R M e : (⨂[R] _ : ι, M) →ₗ[R] ⨂[R] _ : ι₂, M).compMultilinearMap (tprod R) =
      (tprod R : MultilinearMap R (fun _ ↦ M) _).domDomCongr e.symm :=
  MultilinearMap.ext <| reindex_tprod e
#align pi_tensor_product.reindex_comp_tprod PiTensorProduct.reindex_comp_tprod

@[simp]
theorem lift_comp_reindex (e : ι ≃ ι₂) (φ : MultilinearMap R (fun _ : ι₂ ↦ M) E) :
    lift φ ∘ₗ ↑(reindex R M e) = lift (φ.domDomCongr e.symm) := by
  ext
  -- ⊢ ↑(LinearMap.compMultilinearMap (LinearMap.comp (↑lift φ) ↑(reindex R M e)) ( …
  simp
  -- 🎉 no goals
#align pi_tensor_product.lift_comp_reindex PiTensorProduct.lift_comp_reindex

@[simp]
theorem lift_reindex (e : ι ≃ ι₂) (φ : MultilinearMap R (fun _ ↦ M) E) (x : ⨂[R] _, M) :
    lift φ (reindex R M e x) = lift (φ.domDomCongr e.symm) x :=
  LinearMap.congr_fun (lift_comp_reindex e φ) x
#align pi_tensor_product.lift_reindex PiTensorProduct.lift_reindex

@[simp]
theorem reindex_trans (e : ι ≃ ι₂) (e' : ι₂ ≃ ι₃) :
    (reindex R M e).trans (reindex R M e') = reindex R M (e.trans e') := by
  apply LinearEquiv.toLinearMap_injective
  -- ⊢ ↑(LinearEquiv.trans (reindex R M e) (reindex R M e')) = ↑(reindex R M (e.tra …
  ext f
  -- ⊢ ↑(LinearMap.compMultilinearMap (↑(LinearEquiv.trans (reindex R M e) (reindex …
  simp only [LinearEquiv.trans_apply, LinearEquiv.coe_coe, reindex_tprod,
    LinearMap.coe_compMultilinearMap, Function.comp_apply, MultilinearMap.domDomCongr_apply,
    reindex_comp_tprod]
  congr
  -- 🎉 no goals
#align pi_tensor_product.reindex_trans PiTensorProduct.reindex_trans

@[simp]
theorem reindex_reindex (e : ι ≃ ι₂) (e' : ι₂ ≃ ι₃) (x : ⨂[R] _, M) :
    reindex R M e' (reindex R M e x) = reindex R M (e.trans e') x :=
  LinearEquiv.congr_fun (reindex_trans e e' : _ = reindex R M (e.trans e')) x
#align pi_tensor_product.reindex_reindex PiTensorProduct.reindex_reindex

@[simp]
theorem reindex_symm (e : ι ≃ ι₂) : (reindex R M e).symm = reindex R M e.symm := rfl
#align pi_tensor_product.reindex_symm PiTensorProduct.reindex_symm

@[simp]
theorem reindex_refl : reindex R M (Equiv.refl ι) = LinearEquiv.refl R _ := by
  apply LinearEquiv.toLinearMap_injective
  -- ⊢ ↑(reindex R M (Equiv.refl ι)) = ↑(LinearEquiv.refl R (⨂[R] (x : ι), M))
  ext
  -- ⊢ ↑(LinearMap.compMultilinearMap (↑(reindex R M (Equiv.refl ι))) (tprod R)) x✝ …
  rw [reindex_comp_tprod, LinearEquiv.refl_toLinearMap, Equiv.refl_symm]
  -- ⊢ ↑(domDomCongr (Equiv.refl ι) (tprod R)) x✝ = ↑(LinearMap.compMultilinearMap  …
  rfl
  -- 🎉 no goals
#align pi_tensor_product.reindex_refl PiTensorProduct.reindex_refl

variable (ι)

/-- The tensor product over an empty index type `ι` is isomorphic to the base ring. -/
@[simps symm_apply]
def isEmptyEquiv [IsEmpty ι] : (⨂[R] _ : ι, M) ≃ₗ[R] R where
  toFun := lift (constOfIsEmpty R _ 1)
  invFun r := r • tprod R (@isEmptyElim _ _ _)
  left_inv x := by
    refine x.induction_on ?_ ?_
    -- ⊢ ∀ {r : R} {f : ι → M}, (fun r => r • ↑(tprod R) isEmptyElim) (AddHom.toFun { …
    · intro x y
      -- ⊢ (fun r => r • ↑(tprod R) isEmptyElim) (AddHom.toFun { toAddHom := { toFun := …
      simp only [map_smulₛₗ, RingHom.id_apply, lift.tprod, constOfIsEmpty_apply, const_apply,
        smul_eq_mul, mul_one]
      congr
      -- ⊢ isEmptyElim = y
      aesop
      -- 🎉 no goals
    · simp only
      -- ⊢ ∀ {x y : ⨂[R] (i : ι), M}, ↑(↑lift (constOfIsEmpty R (fun i => M) 1)) x • ↑( …
      intro x y hx hy
    -- ⊢ ↑(↑lift (constOfIsEmpty R (fun i => M) 1)) (r • x) = ↑(RingHom.id R) r • ↑(↑ …
      -- ⊢ ↑(↑lift (constOfIsEmpty R (fun i => M) 1)) (x + y) • ↑(tprod R) isEmptyElim  …
    -- 🎉 no goals
      rw [map_add, add_smul, hx, hy]
      -- 🎉 no goals
  right_inv t := by simp
                    -- 🎉 no goals
  map_add' := LinearMap.map_add _
  map_smul' := fun r x => by
    simp only
    exact LinearMap.map_smul _ r x
#align pi_tensor_product.is_empty_equiv PiTensorProduct.isEmptyEquiv

@[simp]
theorem isEmptyEquiv_apply_tprod [IsEmpty ι] (f : ι → M) : isEmptyEquiv ι (tprod R f) = 1 :=
  lift.tprod _
#align pi_tensor_product.is_empty_equiv_apply_tprod PiTensorProduct.isEmptyEquiv_apply_tprod

variable {ι}

/--
Tensor product of `M` over a singleton set is equivalent to `M`
-/
@[simps symm_apply]
def subsingletonEquiv [Subsingleton ι] (i₀ : ι) : (⨂[R] _ : ι, M) ≃ₗ[R] M where
  toFun := lift (MultilinearMap.ofSubsingleton R M i₀)
  invFun m := tprod R fun _ ↦ m
  left_inv x := by
    dsimp only
    -- ⊢ (⨂ₜ[R] (x_1 : ι), ↑(↑lift (ofSubsingleton R M i₀)) x) = x
    have : ∀ (f : ι → M) (z : M), (fun _ : ι ↦ z) = update f i₀ z := by
      intro f z
      ext i
      rw [Subsingleton.elim i i₀, Function.update_same]
    refine x.induction_on ?_ ?_
    -- ⊢ ∀ {r : R} {f : ι → M}, (⨂ₜ[R] (x : ι), ↑(↑lift (ofSubsingleton R M i₀)) (r • …
    · intro r f
      -- ⊢ (⨂ₜ[R] (x : ι), ↑(↑lift (ofSubsingleton R M i₀)) (r • ↑(tprod R) f)) = r • ↑ …
      simp only [LinearMap.map_smul, lift.tprod, ofSubsingleton_apply, Function.eval, this f,
        MultilinearMap.map_smul, update_eq_self]
    · intro x y hx hy
      -- ⊢ (⨂ₜ[R] (x_1 : ι), ↑(↑lift (ofSubsingleton R M i₀)) (x + y)) = x + y
      rw [LinearMap.map_add, this 0 (_ + _), MultilinearMap.map_add, ← this 0 (lift _ _), hx,
        ← this 0 (lift _ _), hy]
    -- ⊢ ↑(↑lift (ofSubsingleton R M i₀)) (r • x) = ↑(RingHom.id R) r • ↑(↑lift (ofSu …
  right_inv t := by simp only [ofSubsingleton_apply, lift.tprod, Function.eval_apply]
    -- 🎉 no goals
                    -- 🎉 no goals
  map_add' := LinearMap.map_add _
  map_smul' := fun r x => by
    simp only
    exact LinearMap.map_smul _ r x
#align pi_tensor_product.subsingleton_equiv PiTensorProduct.subsingletonEquiv

@[simp]
theorem subsingletonEquiv_apply_tprod [Subsingleton ι] (i : ι) (f : ι → M) :
    subsingletonEquiv i (tprod R f) = f i :=
  lift.tprod _
#align pi_tensor_product.subsingleton_equiv_apply_tprod PiTensorProduct.subsingletonEquiv_apply_tprod

section Tmul

/-- Collapse a `TensorProduct` of `PiTensorProduct`s. -/
private def tmul : ((⨂[R] _ : ι, M) ⊗[R] ⨂[R] _ : ι₂, M) →ₗ[R] ⨂[R] _ : Sum ι ι₂, M :=
  TensorProduct.lift
    { toFun := fun a ↦
        PiTensorProduct.lift <|
          PiTensorProduct.lift (MultilinearMap.currySumEquiv R _ _ M _ (tprod R)) a
      map_add' := fun a b ↦ by simp only [LinearEquiv.map_add, LinearMap.map_add]
                               -- 🎉 no goals
      map_smul' := fun r a ↦ by
        simp only [LinearEquiv.map_smul, LinearMap.map_smul, RingHom.id_apply] }
        -- 🎉 no goals

private theorem tmul_apply (a : ι → M) (b : ι₂ → M) :
    tmul ((⨂ₜ[R] i, a i) ⊗ₜ[R] ⨂ₜ[R] i, b i) = ⨂ₜ[R] i, Sum.elim a b i := by
  erw [TensorProduct.lift.tmul, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
  -- ⊢ (↑(↑(↑(currySumEquiv R ι (⨂[R] (i : ι ⊕ ι₂), M) M ι₂) (tprod R)) fun i => a  …
  rfl
  -- 🎉 no goals

/-- Expand `PiTensorProduct` into a `TensorProduct` of two factors. -/
private def tmulSymm : (⨂[R] _ : Sum ι ι₂, M) →ₗ[R] (⨂[R] _ : ι, M) ⊗[R] ⨂[R] _ : ι₂, M :=
  -- by using tactic mode, we avoid the need for a lot of `@`s and `_`s
  PiTensorProduct.lift <| MultilinearMap.domCoprod (tprod R) (tprod R)

private theorem tmulSymm_apply (a : Sum ι ι₂ → M) :
    tmulSymm (⨂ₜ[R] i, a i) = (⨂ₜ[R] i, a (Sum.inl i)) ⊗ₜ[R] ⨂ₜ[R] i, a (Sum.inr i) :=
  PiTensorProduct.lift.tprod _

variable (R M)

attribute [local ext] TensorProduct.ext

/-- Equivalence between a `TensorProduct` of `PiTensorProduct`s and a single
`PiTensorProduct` indexed by a `Sum` type.

For simplicity, this is defined only for homogeneously- (rather than dependently-) typed components.
-/
def tmulEquiv : ((⨂[R] _ : ι, M) ⊗[R] ⨂[R] _ : ι₂, M) ≃ₗ[R] ⨂[R] _ : Sum ι ι₂, M :=
  LinearEquiv.ofLinear tmul tmulSymm
    (by
      ext x
      -- ⊢ ↑(LinearMap.compMultilinearMap (LinearMap.comp PiTensorProduct.tmul PiTensor …
      show tmul (tmulSymm (tprod R x)) = tprod R x -- Speed up the call to `simp`.
      -- ⊢ ↑PiTensorProduct.tmul (↑PiTensorProduct.tmulSymm (↑(tprod R) x)) = ↑(tprod R …
      simp only [tmulSymm_apply, tmul_apply]
      -- ⊢ (⨂ₜ[R] (i : ι ⊕ ι₂), Sum.elim (fun i => x (Sum.inl i)) (fun i => x (Sum.inr  …
      -- Porting note (https://github.com/leanprover-community/mathlib4/issues/5026):
      -- was part of `simp only` above
      erw [Sum.elim_comp_inl_inr])
      -- 🎉 no goals
    (by
      ext x y
      -- ⊢ ↑(LinearMap.compMultilinearMap (↑(LinearMap.compMultilinearMap (LinearMap.co …
      show tmulSymm (tmul (tprod R x ⊗ₜ[R] tprod R y)) = tprod R x ⊗ₜ[R] tprod R y
      -- ⊢ ↑PiTensorProduct.tmulSymm (↑PiTensorProduct.tmul (↑(tprod R) x ⊗ₜ[R] ↑(tprod …
      simp only [tmul_apply, tmulSymm_apply, Sum.elim_inl, Sum.elim_inr])
      -- 🎉 no goals
#align pi_tensor_product.tmul_equiv PiTensorProduct.tmulEquiv

@[simp]
theorem tmulEquiv_apply (a : ι → M) (b : ι₂ → M) :
    tmulEquiv (ι := ι) (ι₂ := ι₂) R M ((⨂ₜ[R] i, a i) ⊗ₜ[R] ⨂ₜ[R] i, b i) =
    ⨂ₜ[R] i, Sum.elim a b i :=
  tmul_apply a b
#align pi_tensor_product.tmul_equiv_apply PiTensorProduct.tmulEquiv_apply

@[simp]
theorem tmulEquiv_symm_apply (a : Sum ι ι₂ → M) :
    (tmulEquiv (ι := ι) (ι₂ := ι₂) R M).symm (⨂ₜ[R] i, a i) =
    (⨂ₜ[R] i, a (Sum.inl i)) ⊗ₜ[R] ⨂ₜ[R] i, a (Sum.inr i) :=
  tmulSymm_apply a
#align pi_tensor_product.tmul_equiv_symm_apply PiTensorProduct.tmulEquiv_symm_apply

end Tmul

end Multilinear

end PiTensorProduct

end Semiring

section Ring

namespace PiTensorProduct

open PiTensorProduct

open TensorProduct

variable {ι : Type*} {R : Type*} [CommRing R]

variable {s : ι → Type*} [∀ i, AddCommGroup (s i)] [∀ i, Module R (s i)]

/- Unlike for the binary tensor product, we require `R` to be a `CommRing` here, otherwise
this is false in the case where `ι` is empty. -/
instance : AddCommGroup (⨂[R] i, s i) :=
  Module.addCommMonoidToAddCommGroup R

end PiTensorProduct

end Ring
