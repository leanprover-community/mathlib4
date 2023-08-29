/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Andrew Yang
-/
import Mathlib.RingTheory.Adjoin.Basic

#align_import ring_theory.derivation.basic from "leanprover-community/mathlib"@"b608348ffaeb7f557f2fd46876037abafd326ff3"

/-!
# Derivations

This file defines derivation. A derivation `D` from the `R`-algebra `A` to the `A`-module `M` is an
`R`-linear map that satisfy the Leibniz rule `D (a * b) = a * D b + D a * b`.

## Main results

- `Derivation`: The type of `R`-derivations from `A` to `M`. This has an `A`-module structure.
- `Derivation.llcomp`: We may compose linear maps and derivations to obtain a derivation,
  and the composition is bilinear.

See `RingTheory.Derivation.Lie` for
- `derivation.lie_algebra`: The `R`-derivations from `A` to `A` form a lie algebra over `R`.

and `RingTheory.Derivation.ToSquareZero` for
- `derivation_to_square_zero_equiv_lift`: The `R`-derivations from `A` into a square-zero ideal `I`
  of `B` corresponds to the lifts `A →ₐ[R] B` of the map `A →ₐ[R] B ⧸ I`.

## Future project

- Generalize derivations into bimodules.

-/

open Algebra
open scoped BigOperators

/-- `D : Derivation R A M` is an `R`-linear map from `A` to `M` that satisfies the `leibniz`
equality. We also require that `D 1 = 0`. See `Derivation.mk'` for a constructor that deduces this
assumption from the Leibniz rule when `M` is cancellative.

TODO: update this when bimodules are defined. -/
structure Derivation (R : Type*) (A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A]
    (M : Type*) [AddCommMonoid M] [Module A M] [Module R M] extends A →ₗ[R] M where
  protected map_one_eq_zero' : toLinearMap 1 = 0
  protected leibniz' (a b : A) : toLinearMap (a * b) = a • toLinearMap b + b • toLinearMap a
#align derivation Derivation

/-- The `LinearMap` underlying a `Derivation`. -/
add_decl_doc Derivation.toLinearMap

namespace Derivation

section

variable {R : Type*} [CommSemiring R]

variable {A : Type*} [CommSemiring A] [Algebra R A]

variable {M : Type*} [AddCommMonoid M] [Module A M] [Module R M]

variable (D : Derivation R A M) {D1 D2 : Derivation R A M} (r : R) (a b : A)

instance : AddMonoidHomClass (Derivation R A M) A M where
  coe D := D.toFun
  coe_injective' D1 D2 h := by cases D1; cases D2; congr; exact FunLike.coe_injective h
                               -- ⊢ { toLinearMap := toLinearMap✝, map_one_eq_zero' := map_one_eq_zero'✝, leibni …
                                         -- ⊢ { toLinearMap := toLinearMap✝¹, map_one_eq_zero' := map_one_eq_zero'✝¹, leib …
                                                   -- ⊢ toLinearMap✝¹ = toLinearMap✝
                                                          -- 🎉 no goals
  map_add D := D.toLinearMap.map_add'
  map_zero D := D.toLinearMap.map_zero

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (Derivation R A M) fun _ => A → M :=
  ⟨FunLike.coe⟩

-- Not a simp lemma because it can be proved via `coeFn_coe` + `toLinearMap_eq_coe`
theorem toFun_eq_coe : D.toFun = ⇑D :=
  rfl
#align derivation.to_fun_eq_coe Derivation.toFun_eq_coe

attribute [coe] toLinearMap

instance hasCoeToLinearMap : Coe (Derivation R A M) (A →ₗ[R] M) :=
  ⟨fun D => D.toLinearMap⟩
#align derivation.has_coe_to_linear_map Derivation.hasCoeToLinearMap

#noalign derivation.to_linear_map_eq_coe -- porting note: not needed anymore

@[simp]
theorem mk_coe (f : A →ₗ[R] M) (h₁ h₂) : ((⟨f, h₁, h₂⟩ : Derivation R A M) : A → M) = f :=
  rfl
#align derivation.mk_coe Derivation.mk_coe

@[simp, norm_cast]
theorem coeFn_coe (f : Derivation R A M) : ⇑(f : A →ₗ[R] M) = f :=
  rfl
#align derivation.coe_fn_coe Derivation.coeFn_coe

theorem coe_injective : @Function.Injective (Derivation R A M) (A → M) FunLike.coe :=
  FunLike.coe_injective
#align derivation.coe_injective Derivation.coe_injective

@[ext]
theorem ext (H : ∀ a, D1 a = D2 a) : D1 = D2 :=
  FunLike.ext _ _ H
#align derivation.ext Derivation.ext

theorem congr_fun (h : D1 = D2) (a : A) : D1 a = D2 a :=
  FunLike.congr_fun h a
#align derivation.congr_fun Derivation.congr_fun

protected theorem map_add : D (a + b) = D a + D b :=
  map_add D a b
#align derivation.map_add Derivation.map_add

protected theorem map_zero : D 0 = 0 :=
  map_zero D
#align derivation.map_zero Derivation.map_zero

@[simp]
theorem map_smul : D (r • a) = r • D a :=
  D.toLinearMap.map_smul r a
#align derivation.map_smul Derivation.map_smul

@[simp]
theorem leibniz : D (a * b) = a • D b + b • D a :=
  D.leibniz' _ _
#align derivation.leibniz Derivation.leibniz

theorem map_sum {ι : Type*} (s : Finset ι) (f : ι → A) : D (∑ i in s, f i) = ∑ i in s, D (f i) :=
  D.toLinearMap.map_sum
#align derivation.map_sum Derivation.map_sum

@[simp]
theorem map_smul_of_tower {S : Type*} [SMul S A] [SMul S M] [LinearMap.CompatibleSMul A M S R]
    (D : Derivation R A M) (r : S) (a : A) : D (r • a) = r • D a :=
  D.toLinearMap.map_smul_of_tower r a
#align derivation.map_smul_of_tower Derivation.map_smul_of_tower

@[simp]
theorem map_one_eq_zero : D 1 = 0 :=
  D.map_one_eq_zero'
#align derivation.map_one_eq_zero Derivation.map_one_eq_zero

@[simp]
theorem map_algebraMap : D (algebraMap R A r) = 0 := by
  rw [← mul_one r, RingHom.map_mul, RingHom.map_one, ← smul_def, map_smul, map_one_eq_zero,
    smul_zero]
#align derivation.map_algebra_map Derivation.map_algebraMap

@[simp]
theorem map_coe_nat (n : ℕ) : D (n : A) = 0 := by
  rw [← nsmul_one, D.map_smul_of_tower n, map_one_eq_zero, smul_zero]
  -- 🎉 no goals
#align derivation.map_coe_nat Derivation.map_coe_nat

@[simp]
theorem leibniz_pow (n : ℕ) : D (a ^ n) = n • a ^ (n - 1) • D a := by
  induction' n with n ihn
  -- ⊢ ↑D (a ^ Nat.zero) = Nat.zero • a ^ (Nat.zero - 1) • ↑D a
  · rw [Nat.zero_eq, pow_zero, map_one_eq_zero, zero_smul]
    -- 🎉 no goals
  · rcases (zero_le n).eq_or_lt with (rfl | hpos)
    -- ⊢ ↑D (a ^ Nat.succ 0) = Nat.succ 0 • a ^ (Nat.succ 0 - 1) • ↑D a
    · erw [pow_one, one_smul, pow_zero, one_smul]
      -- 🎉 no goals
    · have : a * a ^ (n - 1) = a ^ n := by rw [← pow_succ, Nat.sub_add_cancel hpos]
      -- ⊢ ↑D (a ^ Nat.succ n) = Nat.succ n • a ^ (Nat.succ n - 1) • ↑D a
      simp only [pow_succ, leibniz, ihn, smul_comm a n (_ : M), smul_smul a, add_smul, this,
        Nat.succ_eq_add_one, Nat.add_succ_sub_one, add_zero, one_nsmul]
#align derivation.leibniz_pow Derivation.leibniz_pow

theorem eqOn_adjoin {s : Set A} (h : Set.EqOn D1 D2 s) : Set.EqOn D1 D2 (adjoin R s) := fun x hx =>
  Algebra.adjoin_induction hx h (fun r => (D1.map_algebraMap r).trans (D2.map_algebraMap r).symm)
    (fun x y hx hy => by simp only [map_add, *]) fun x y hx hy => by simp only [leibniz, *]
                         -- 🎉 no goals
                                                                     -- 🎉 no goals
#align derivation.eq_on_adjoin Derivation.eqOn_adjoin

/-- If adjoin of a set is the whole algebra, then any two derivations equal on this set are equal
on the whole algebra. -/
theorem ext_of_adjoin_eq_top (s : Set A) (hs : adjoin R s = ⊤) (h : Set.EqOn D1 D2 s) : D1 = D2 :=
  ext fun _ => eqOn_adjoin h <| hs.symm ▸ trivial
#align derivation.ext_of_adjoin_eq_top Derivation.ext_of_adjoin_eq_top

-- Data typeclasses
instance : Zero (Derivation R A M) :=
  ⟨{  toLinearMap := 0
      map_one_eq_zero' := rfl
      leibniz' := fun a b => by simp only [add_zero, LinearMap.zero_apply, smul_zero] }⟩
                                -- 🎉 no goals

@[simp]
theorem coe_zero : ⇑(0 : Derivation R A M) = 0 :=
  rfl
#align derivation.coe_zero Derivation.coe_zero

@[simp]
theorem coe_zero_linearMap : ↑(0 : Derivation R A M) = (0 : A →ₗ[R] M) :=
  rfl
#align derivation.coe_zero_linear_map Derivation.coe_zero_linearMap

theorem zero_apply (a : A) : (0 : Derivation R A M) a = 0 :=
  rfl
#align derivation.zero_apply Derivation.zero_apply

instance : Add (Derivation R A M) :=
  ⟨fun D1 D2 =>
    { toLinearMap := D1 + D2
      map_one_eq_zero' := by simp
                             -- 🎉 no goals
      leibniz' := fun a b => by
        simp only [leibniz, LinearMap.add_apply, coeFn_coe, smul_add, add_add_add_comm] }⟩
        -- 🎉 no goals

@[simp]
theorem coe_add (D1 D2 : Derivation R A M) : ⇑(D1 + D2) = D1 + D2 :=
  rfl
#align derivation.coe_add Derivation.coe_add

@[simp]
theorem coe_add_linearMap (D1 D2 : Derivation R A M) : ↑(D1 + D2) = (D1 + D2 : A →ₗ[R] M) :=
  rfl
#align derivation.coe_add_linear_map Derivation.coe_add_linearMap

theorem add_apply : (D1 + D2) a = D1 a + D2 a :=
  rfl
#align derivation.add_apply Derivation.add_apply

instance : Inhabited (Derivation R A M) :=
  ⟨0⟩

section Scalar

variable {S T : Type*}

variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M] [SMulCommClass S A M]

variable [Monoid T] [DistribMulAction T M] [SMulCommClass R T M] [SMulCommClass T A M]

instance : SMul S (Derivation R A M) :=
  ⟨fun r D =>
    { toLinearMap := r • D.1
      map_one_eq_zero' := by rw [LinearMap.smul_apply, coeFn_coe, D.map_one_eq_zero, smul_zero]
                             -- 🎉 no goals
      leibniz' := fun a b => by simp only [LinearMap.smul_apply, coeFn_coe, leibniz, smul_add,
        smul_comm r (_ : A) (_ : M)] }⟩

@[simp]
theorem coe_smul (r : S) (D : Derivation R A M) : ⇑(r • D) = r • ⇑D :=
  rfl
#align derivation.coe_smul Derivation.coe_smul

@[simp]
theorem coe_smul_linearMap (r : S) (D : Derivation R A M) : ↑(r • D) = r • (D : A →ₗ[R] M) :=
  rfl
#align derivation.coe_smul_linear_map Derivation.coe_smul_linearMap

theorem smul_apply (r : S) (D : Derivation R A M) : (r • D) a = r • D a :=
  rfl
#align derivation.smul_apply Derivation.smul_apply

instance : AddCommMonoid (Derivation R A M) :=
  coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

/-- `coe_fn` as an `AddMonoidHom`. -/
def coeFnAddMonoidHom : Derivation R A M →+ A → M where
  toFun := (↑)
  map_zero' := coe_zero
  map_add' := coe_add
#align derivation.coe_fn_add_monoid_hom Derivation.coeFnAddMonoidHom

instance : DistribMulAction S (Derivation R A M) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

instance [DistribMulAction Sᵐᵒᵖ M] [IsCentralScalar S M] : IsCentralScalar S (Derivation R A M)
    where op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

instance [SMul S T] [IsScalarTower S T M] : IsScalarTower S T (Derivation R A M) :=
  ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩

instance [SMulCommClass S T M] : SMulCommClass S T (Derivation R A M) :=
  ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩

end Scalar

instance instModule {S : Type*} [Semiring S] [Module S M] [SMulCommClass R S M]
    [SMulCommClass S A M] : Module S (Derivation R A M) :=
  Function.Injective.module S coeFnAddMonoidHom coe_injective coe_smul

section PushForward

variable {N : Type*} [AddCommMonoid N] [Module A N] [Module R N] [IsScalarTower R A M]
  [IsScalarTower R A N]

variable (f : M →ₗ[A] N) (e : M ≃ₗ[A] N)

/-- We can push forward derivations using linear maps, i.e., the composition of a derivation with a
linear map is a derivation. Furthermore, this operation is linear on the spaces of derivations. -/
def _root_.LinearMap.compDer : Derivation R A M →ₗ[R] Derivation R A N where
  toFun D :=
    { toLinearMap := (f : M →ₗ[R] N).comp (D : A →ₗ[R] M)
      map_one_eq_zero' := by simp only [LinearMap.comp_apply, coeFn_coe, map_one_eq_zero, map_zero]
                             -- 🎉 no goals
      leibniz' := fun a b => by
        simp only [coeFn_coe, LinearMap.comp_apply, LinearMap.map_add, leibniz,
          LinearMap.coe_restrictScalars, LinearMap.map_smul] }
  map_add' D₁ D₂ := by ext; exact LinearMap.map_add _ _ _
                       -- ⊢ ↑((fun D => { toLinearMap := LinearMap.comp (↑R f) ↑D, map_one_eq_zero' := ( …
                            -- 🎉 no goals
  map_smul' r D := by dsimp; ext; exact LinearMap.map_smul (f : M →ₗ[R] N) _ _
                      -- ⊢ { toLinearMap := LinearMap.comp (↑R f) (r • ↑D), map_one_eq_zero' := (_ : ↑f …
                             -- ⊢ ↑{ toLinearMap := LinearMap.comp (↑R f) (r • ↑D), map_one_eq_zero' := (_ : ↑ …
                                  -- 🎉 no goals
#align linear_map.comp_der LinearMap.compDer

@[simp]
theorem coe_to_linearMap_comp : (f.compDer D : A →ₗ[R] N) = (f : M →ₗ[R] N).comp (D : A →ₗ[R] M) :=
  rfl
#align derivation.coe_to_linear_map_comp Derivation.coe_to_linearMap_comp

@[simp]
theorem coe_comp : (f.compDer D : A → N) = (f : M →ₗ[R] N).comp (D : A →ₗ[R] M) :=
  rfl
#align derivation.coe_comp Derivation.coe_comp

/-- The composition of a derivation with a linear map as a bilinear map -/
@[simps]
def llcomp : (M →ₗ[A] N) →ₗ[A] Derivation R A M →ₗ[R] Derivation R A N where
  toFun f := f.compDer
  map_add' f₁ f₂ := by ext; rfl
                       -- ⊢ ↑(↑((fun f => LinearMap.compDer f) (f₁ + f₂)) x✝) a✝ = ↑(↑((fun f => LinearM …
                            -- 🎉 no goals
  map_smul' r D := by ext; rfl
                      -- ⊢ ↑(↑(AddHom.toFun { toFun := fun f => LinearMap.compDer f, map_add' := (_ : ∀ …
                           -- 🎉 no goals
#align derivation.llcomp Derivation.llcomp

/-- Pushing a derivation forward through a linear equivalence is an equivalence. -/
def _root_.LinearEquiv.compDer : Derivation R A M ≃ₗ[R] Derivation R A N :=
  { e.toLinearMap.compDer with
    invFun := e.symm.toLinearMap.compDer
    left_inv := fun D => by ext a; exact e.symm_apply_apply (D a)
                            -- ⊢ ↑(↑(LinearMap.compDer ↑(LinearEquiv.symm e)) (AddHom.toFun { toAddHom := src …
                                   -- 🎉 no goals
    right_inv := fun D => by ext a; exact e.apply_symm_apply (D a) }
                             -- ⊢ ↑(AddHom.toFun { toAddHom := src✝.toAddHom, map_smul' := (_ : ∀ (r : R) (x : …
                                    -- 🎉 no goals
#align linear_equiv.comp_der LinearEquiv.compDer

end PushForward

section RestrictScalars

variable {S : Type*} [CommSemiring S]

variable [Algebra S A] [Module S M] [LinearMap.CompatibleSMul A M R S]

variable (R)

/-- If `A` is both an `R`-algebra and an `S`-algebra; `M` is both an `R`-module and an `S`-module,
then an `S`-derivation `A → M` is also an `R`-derivation if it is also `R`-linear. -/
protected def restrictScalars (d : Derivation S A M) : Derivation R A M where
  map_one_eq_zero' := d.map_one_eq_zero
  leibniz' := d.leibniz
  toLinearMap := d.toLinearMap.restrictScalars R
#align derivation.restrict_scalars Derivation.restrictScalars

end RestrictScalars

end

section Cancel

variable {R : Type*} [CommSemiring R] {A : Type*} [CommSemiring A] [Algebra R A] {M : Type*}
  [AddCancelCommMonoid M] [Module R M] [Module A M]

/-- Define `Derivation R A M` from a linear map when `M` is cancellative by verifying the Leibniz
rule. -/
def mk' (D : A →ₗ[R] M) (h : ∀ a b, D (a * b) = a • D b + b • D a) : Derivation R A M where
  toLinearMap := D
  map_one_eq_zero' := add_right_eq_self.1 <| by simpa only [one_smul, one_mul] using (h 1 1).symm
                                                -- 🎉 no goals
  leibniz' := h
#align derivation.mk' Derivation.mk'

@[simp]
theorem coe_mk' (D : A →ₗ[R] M) (h) : ⇑(mk' D h) = D :=
  rfl
#align derivation.coe_mk' Derivation.coe_mk'

@[simp]
theorem coe_mk'_linearMap (D : A →ₗ[R] M) (h) : (mk' D h : A →ₗ[R] M) = D :=
  rfl
#align derivation.coe_mk'_linear_map Derivation.coe_mk'_linearMap

end Cancel

section

variable {R : Type*} [CommRing R]

variable {A : Type*} [CommRing A] [Algebra R A]

section

variable {M : Type*} [AddCommGroup M] [Module A M] [Module R M]

variable (D : Derivation R A M) {D1 D2 : Derivation R A M} (r : R) (a b : A)

protected theorem map_neg : D (-a) = -D a :=
  map_neg D a
#align derivation.map_neg Derivation.map_neg

protected theorem map_sub : D (a - b) = D a - D b :=
  map_sub D a b
#align derivation.map_sub Derivation.map_sub

@[simp]
theorem map_coe_int (n : ℤ) : D (n : A) = 0 := by
  rw [← zsmul_one, D.map_smul_of_tower n, map_one_eq_zero, smul_zero]
  -- 🎉 no goals
#align derivation.map_coe_int Derivation.map_coe_int

theorem leibniz_of_mul_eq_one {a b : A} (h : a * b = 1) : D a = -a ^ 2 • D b := by
  rw [neg_smul]
  -- ⊢ ↑D a = -(a ^ 2 • ↑D b)
  refine' eq_neg_of_add_eq_zero_left _
  -- ⊢ ↑D a + a ^ 2 • ↑D b = 0
  calc
    D a + a ^ 2 • D b = a • b • D a + a • a • D b := by simp only [smul_smul, h, one_smul, sq]
    _ = a • D (a * b) := by rw [leibniz, smul_add, add_comm]
    _ = 0 := by rw [h, map_one_eq_zero, smul_zero]

#align derivation.leibniz_of_mul_eq_one Derivation.leibniz_of_mul_eq_one

theorem leibniz_invOf [Invertible a] : D (⅟ a) = -⅟ a ^ 2 • D a :=
  D.leibniz_of_mul_eq_one <| invOf_mul_self a
#align derivation.leibniz_inv_of Derivation.leibniz_invOf

theorem leibniz_inv {K : Type*} [Field K] [Module K M] [Algebra R K] (D : Derivation R K M)
    (a : K) : D a⁻¹ = -a⁻¹ ^ 2 • D a := by
  rcases eq_or_ne a 0 with (rfl | ha)
  -- ⊢ ↑D 0⁻¹ = -0⁻¹ ^ 2 • ↑D 0
  · simp
    -- 🎉 no goals
  · exact D.leibniz_of_mul_eq_one (inv_mul_cancel ha)
    -- 🎉 no goals
#align derivation.leibniz_inv Derivation.leibniz_inv

instance : Neg (Derivation R A M) :=
  ⟨fun D =>
    mk' (-D) fun a b => by
      simp only [LinearMap.neg_apply, smul_neg, neg_add_rev, leibniz, coeFn_coe, add_comm]⟩
      -- 🎉 no goals

@[simp]
theorem coe_neg (D : Derivation R A M) : ⇑(-D) = -D :=
  rfl
#align derivation.coe_neg Derivation.coe_neg

@[simp]
theorem coe_neg_linearMap (D : Derivation R A M) : ↑(-D) = (-D : A →ₗ[R] M) :=
  rfl
#align derivation.coe_neg_linear_map Derivation.coe_neg_linearMap

theorem neg_apply : (-D) a = -D a :=
  rfl
#align derivation.neg_apply Derivation.neg_apply

instance : Sub (Derivation R A M) :=
  ⟨fun D1 D2 =>
    mk' (D1 - D2 : A →ₗ[R] M) fun a b => by
      simp only [LinearMap.sub_apply, leibniz, coeFn_coe, smul_sub, add_sub_add_comm]⟩
      -- 🎉 no goals

@[simp]
theorem coe_sub (D1 D2 : Derivation R A M) : ⇑(D1 - D2) = D1 - D2 :=
  rfl
#align derivation.coe_sub Derivation.coe_sub

@[simp]
theorem coe_sub_linearMap (D1 D2 : Derivation R A M) : ↑(D1 - D2) = (D1 - D2 : A →ₗ[R] M) :=
  rfl
#align derivation.coe_sub_linear_map Derivation.coe_sub_linearMap

theorem sub_apply : (D1 - D2) a = D1 a - D2 a :=
  rfl
#align derivation.sub_apply Derivation.sub_apply

instance : AddCommGroup (Derivation R A M) :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

end

end

end Derivation
