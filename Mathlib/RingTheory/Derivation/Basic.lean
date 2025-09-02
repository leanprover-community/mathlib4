/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Andrew Yang
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative

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
- `derivationToSquareZeroEquivLift`: The `R`-derivations from `A` into a square-zero ideal `I`
  of `B` corresponds to the lifts `A →ₐ[R] B` of the map `A →ₐ[R] B ⧸ I`.

## Future project

- Generalize derivations into bimodules.

-/

open Algebra

/-- `D : Derivation R A M` is an `R`-linear map from `A` to `M` that satisfies the `leibniz`
equality. We also require that `D 1 = 0`. See `Derivation.mk'` for a constructor that deduces this
assumption from the Leibniz rule when `M` is cancellative.

TODO: update this when bimodules are defined. -/
structure Derivation (R : Type*) (A : Type*) (M : Type*)
    [CommSemiring R] [CommSemiring A] [AddCommMonoid M] [Algebra R A] [Module A M] [Module R M]
    extends A →ₗ[R] M where
  protected map_one_eq_zero' : toLinearMap 1 = 0
  protected leibniz' (a b : A) : toLinearMap (a * b) = a • toLinearMap b + b • toLinearMap a

/-- The `LinearMap` underlying a `Derivation`. -/
add_decl_doc Derivation.toLinearMap

namespace Derivation

section

variable {R : Type*} {A : Type*} {B : Type*} {M : Type*}
variable [CommSemiring R] [CommSemiring A] [CommSemiring B] [AddCommMonoid M]
variable [Algebra R A] [Algebra R B]
variable [Module A M] [Module B M] [Module R M]


variable (D : Derivation R A M) {D1 D2 : Derivation R A M} (r : R) (a b : A)

instance : FunLike (Derivation R A M) A M where
  coe D := D.toFun
  coe_injective' D1 D2 h := by cases D1; cases D2; congr; exact DFunLike.coe_injective h

instance : AddMonoidHomClass (Derivation R A M) A M where
  map_add D := D.toLinearMap.map_add'
  map_zero D := D.toLinearMap.map_zero

-- Not a simp lemma because it can be proved via `coeFn_coe` + `toLinearMap_eq_coe`
theorem toFun_eq_coe : D.toFun = ⇑D :=
  rfl

/-- See Note [custom simps projection] -/
def Simps.apply (D : Derivation R A M) : A → M := D

initialize_simps_projections Derivation (toFun → apply)

attribute [coe] toLinearMap

instance hasCoeToLinearMap : Coe (Derivation R A M) (A →ₗ[R] M) :=
  ⟨fun D => D.toLinearMap⟩

@[simp]
theorem mk_coe (f : A →ₗ[R] M) (h₁ h₂) : ((⟨f, h₁, h₂⟩ : Derivation R A M) : A → M) = f :=
  rfl

@[simp, norm_cast]
theorem coeFn_coe (f : Derivation R A M) : ⇑(f : A →ₗ[R] M) = f :=
  rfl

theorem coe_injective : @Function.Injective (Derivation R A M) (A → M) DFunLike.coe :=
  DFunLike.coe_injective

@[ext]
theorem ext (H : ∀ a, D1 a = D2 a) : D1 = D2 :=
  DFunLike.ext _ _ H

theorem congr_fun (h : D1 = D2) (a : A) : D1 a = D2 a :=
  DFunLike.congr_fun h a

protected theorem map_add : D (a + b) = D a + D b :=
  map_add D a b

protected theorem map_zero : D 0 = 0 :=
  map_zero D

@[simp]
theorem map_smul : D (r • a) = r • D a :=
  D.toLinearMap.map_smul r a

@[simp]
theorem leibniz : D (a * b) = a • D b + b • D a :=
  D.leibniz' _ _

@[simp]
theorem map_smul_of_tower {S : Type*} [SMul S A] [SMul S M] [LinearMap.CompatibleSMul A M S R]
    (D : Derivation R A M) (r : S) (a : A) : D (r • a) = r • D a :=
  D.toLinearMap.map_smul_of_tower r a

@[simp]
theorem map_one_eq_zero : D 1 = 0 :=
  D.map_one_eq_zero'

@[simp]
theorem map_algebraMap : D (algebraMap R A r) = 0 := by
  rw [← mul_one r, RingHom.map_mul, RingHom.map_one, ← smul_def, map_smul, map_one_eq_zero,
    smul_zero]

@[simp]
theorem map_natCast (n : ℕ) : D (n : A) = 0 := by
  rw [← nsmul_one, D.map_smul_of_tower n, map_one_eq_zero, smul_zero]

@[simp]
theorem leibniz_pow (n : ℕ) : D (a ^ n) = n • a ^ (n - 1) • D a := by
  induction' n with n ihn
  · rw [pow_zero, map_one_eq_zero, zero_smul]
  · rcases (zero_le n).eq_or_lt with (rfl | hpos)
    · simp
    · have : a * a ^ (n - 1) = a ^ n := by rw [← pow_succ', Nat.sub_add_cancel hpos]
      simp only [pow_succ', leibniz, ihn, smul_comm a n (_ : M), smul_smul a, add_smul, this,
        Nat.add_succ_sub_one, add_zero, one_nsmul]

open Polynomial in
@[simp]
theorem map_aeval (P : R[X]) (x : A) :
    D (aeval x P) = aeval x (derivative P) • D x := by
  induction P using Polynomial.induction_on
  · simp
  · simp [add_smul, *]
  · simp [mul_smul, ← Nat.cast_smul_eq_nsmul A]

theorem eqOn_adjoin {s : Set A} (h : Set.EqOn D1 D2 s) : Set.EqOn D1 D2 (adjoin R s) := fun _ hx =>
  Algebra.adjoin_induction (hx := hx) h
    (fun r => (D1.map_algebraMap r).trans (D2.map_algebraMap r).symm)
    (fun x y _ _ hx hy => by simp only [map_add, *]) fun x y _ _ hx hy => by simp only [leibniz, *]

/-- If adjoin of a set is the whole algebra, then any two derivations equal on this set are equal
on the whole algebra. -/
theorem ext_of_adjoin_eq_top (s : Set A) (hs : adjoin R s = ⊤) (h : Set.EqOn D1 D2 s) : D1 = D2 :=
  ext fun _ => eqOn_adjoin h <| hs.symm ▸ trivial

-- Data typeclasses
instance : Zero (Derivation R A M) :=
  ⟨{  toLinearMap := 0
      map_one_eq_zero' := rfl
      leibniz' := fun a b => by simp only [add_zero, LinearMap.zero_apply, smul_zero] }⟩

@[simp]
theorem coe_zero : ⇑(0 : Derivation R A M) = 0 :=
  rfl

@[simp]
theorem coe_zero_linearMap : ↑(0 : Derivation R A M) = (0 : A →ₗ[R] M) :=
  rfl

theorem zero_apply (a : A) : (0 : Derivation R A M) a = 0 :=
  rfl

instance : Add (Derivation R A M) :=
  ⟨fun D1 D2 =>
    { toLinearMap := D1 + D2
      map_one_eq_zero' := by simp
      leibniz' := fun a b => by
        simp only [leibniz, LinearMap.add_apply, coeFn_coe, smul_add, add_add_add_comm] }⟩

@[simp]
theorem coe_add (D1 D2 : Derivation R A M) : ⇑(D1 + D2) = D1 + D2 :=
  rfl

@[simp]
theorem coe_add_linearMap (D1 D2 : Derivation R A M) : ↑(D1 + D2) = (D1 + D2 : A →ₗ[R] M) :=
  rfl

theorem add_apply : (D1 + D2) a = D1 a + D2 a :=
  rfl

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
      leibniz' := fun a b => by simp only [LinearMap.smul_apply, coeFn_coe, leibniz, smul_add,
        smul_comm r (_ : A) (_ : M)] }⟩

@[simp]
theorem coe_smul (r : S) (D : Derivation R A M) : ⇑(r • D) = r • ⇑D :=
  rfl

@[simp]
theorem coe_smul_linearMap (r : S) (D : Derivation R A M) : ↑(r • D) = r • (D : A →ₗ[R] M) :=
  rfl

theorem smul_apply (r : S) (D : Derivation R A M) : (r • D) a = r • D a :=
  rfl

instance : AddCommMonoid (Derivation R A M) :=
  coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

/-- `coeFn` as an `AddMonoidHom`. -/
def coeFnAddMonoidHom : Derivation R A M →+ A → M where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
lemma coeFnAddMonoidHom_apply (D : Derivation R A M) : coeFnAddMonoidHom D = D := rfl

instance : DistribMulAction S (Derivation R A M) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

instance [DistribMulAction Sᵐᵒᵖ M] [IsCentralScalar S M] :
    IsCentralScalar S (Derivation R A M) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

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
      leibniz' := fun a b => by
        simp only [coeFn_coe, LinearMap.comp_apply, LinearMap.map_add, leibniz,
          LinearMap.coe_restrictScalars, LinearMap.map_smul] }
  map_add' D₁ D₂ := by ext; exact LinearMap.map_add _ _ _
  map_smul' r D := by dsimp; ext; exact LinearMap.map_smul (f : M →ₗ[R] N) _ _

@[simp]
theorem coe_to_linearMap_comp : (f.compDer D : A →ₗ[R] N) = (f : M →ₗ[R] N).comp (D : A →ₗ[R] M) :=
  rfl

@[simp]
theorem coe_comp : (f.compDer D : A → N) = (f : M →ₗ[R] N).comp (D : A →ₗ[R] M) :=
  rfl

/-- The composition of a derivation with a linear map as a bilinear map -/
@[simps]
def llcomp : (M →ₗ[A] N) →ₗ[A] Derivation R A M →ₗ[R] Derivation R A N where
  toFun f := f.compDer
  map_add' f₁ f₂ := by ext; rfl
  map_smul' r D := by ext; rfl

/-- Pushing a derivation forward through a linear equivalence is an equivalence. -/
def _root_.LinearEquiv.compDer : Derivation R A M ≃ₗ[R] Derivation R A N :=
  { e.toLinearMap.compDer with
    invFun := e.symm.toLinearMap.compDer
    left_inv := fun D => by ext a; exact e.symm_apply_apply (D a)
    right_inv := fun D => by ext a; exact e.apply_symm_apply (D a) }

@[simp]
theorem linearEquiv_coe_to_linearMap_comp :
    (e.compDer D : A →ₗ[R] N) = (e.toLinearMap : M →ₗ[R] N).comp (D : A →ₗ[R] M) :=
  rfl

@[simp]
theorem linearEquiv_coe_comp :
    (e.compDer D : A → N) = (e.toLinearMap : M →ₗ[R] N).comp (D : A →ₗ[R] M) :=
  rfl

end PushForward

variable (A) in
/-- For a tower `R → A → B` and an `R`-derivation `B → M`, we may compose with `A → B` to obtain an
`R`-derivation `A → M`. -/
@[simps!]
def compAlgebraMap [Algebra A B] [IsScalarTower R A B] [IsScalarTower A B M]
    (d : Derivation R B M) : Derivation R A M where
  map_one_eq_zero' := by simp
  leibniz' a b := by simp
  toLinearMap := d.toLinearMap.comp (IsScalarTower.toAlgHom R A B).toLinearMap

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

lemma coe_restrictScalars (d : Derivation S A M) : ⇑(d.restrictScalars R) = ⇑d := rfl

@[simp]
lemma restrictScalars_apply (d : Derivation S A M) (x : A) : d.restrictScalars R x = d x := rfl

end RestrictScalars

end

section Lift

variable {R : Type*} {A : Type*} {M : Type*}
variable [CommSemiring R] [CommRing A] [CommRing M]
variable [Algebra R A] [Algebra R M]
variable {F : Type*} [FunLike F A M] [AlgHomClass F R A M]

/--
Lift a derivation via an algebra homomorphism `f` with a right inverse such that
`f(x) = 0 → f(d(x)) = 0`. This gives the derivation `f ∘ d ∘ f⁻¹`.
This is needed for an argument in [Rosenlicht, M. Integration in finite terms][Rosenlicht_1972].
-/
def liftOfRightInverse {f : F} {f_inv : M → A} (hf : Function.RightInverse f_inv f)
    ⦃d : Derivation R A A⦄ (hd : ∀ x, f x = 0 → f (d x) = 0) : Derivation R M M where
  toFun x := f (d (f_inv x))
  map_add' x y := by
    suffices f (d (f_inv (x + y) - (f_inv x + f_inv y))) = 0 by simpa [sub_eq_zero]
    apply hd
    simp [hf _]
  map_smul' x y := by
    suffices f (d (f_inv (x • y) - x • f_inv y)) = 0 by simpa [sub_eq_zero]
    apply hd
    simp [hf _]
  map_one_eq_zero' := by
    suffices f (d (f_inv 1 - 1)) = 0 by simpa [sub_eq_zero]
    apply hd
    simp [hf _]
  leibniz' x y := by
    suffices f (d (f_inv (x * y) - f_inv x * f_inv y)) = 0 by simpa [sub_eq_zero, hf _]
    apply hd
    simp [hf _]

@[simp]
lemma liftOfRightInverse_apply {f : F} {f_inv : M → A} (hf : Function.RightInverse f_inv f)
    {d : Derivation R A A} (hd : ∀ x, f x = 0 → f (d x) = 0) (x : A) :
    Derivation.liftOfRightInverse hf hd (f x) = f (d x) := by
  suffices f (d (f_inv (f x) - x)) = 0 by simpa [sub_eq_zero]
  apply hd
  simp [hf _]

lemma liftOfRightInverse_eq {f : F} {f_inv₁ f_inv₂ : M → A} (hf₁ : Function.RightInverse f_inv₁ f)
    (hf₂ : Function.RightInverse f_inv₂ f) :
    liftOfRightInverse hf₁ = liftOfRightInverse hf₂ := by
  ext _ _ x
  obtain ⟨x, rfl⟩ := hf₁.surjective x
  simp

/--
A noncomputable version of `liftOfRightInverse` for surjective homomorphisms.
-/
noncomputable abbrev liftOfSurjective {f : F} (hf : Function.Surjective f)
    ⦃d : Derivation R A A⦄ (hd : ∀ x, f x = 0 → f (d x) = 0) : Derivation R M M :=
  d.liftOfRightInverse (Function.rightInverse_surjInv hf) hd

lemma liftOfSurjective_apply {f : F} (hf : Function.Surjective f)
    {d : Derivation R A A} (hd : ∀ x, f x = 0 → f (d x) = 0) (x : A) :
    Derivation.liftOfSurjective hf hd (f x) = f (d x) := by simp

end Lift

section Cancel

variable {R : Type*} [CommSemiring R] {A : Type*} [CommSemiring A] [Algebra R A] {M : Type*}
  [AddCancelCommMonoid M] [Module R M] [Module A M]

/-- Define `Derivation R A M` from a linear map when `M` is cancellative by verifying the Leibniz
rule. -/
def mk' (D : A →ₗ[R] M) (h : ∀ a b, D (a * b) = a • D b + b • D a) : Derivation R A M where
  toLinearMap := D
  map_one_eq_zero' := (add_eq_left (a := D 1)).1 <| by
    simpa only [one_smul, one_mul] using (h 1 1).symm
  leibniz' := h

@[simp]
theorem coe_mk' (D : A →ₗ[R] M) (h) : ⇑(mk' D h) = D :=
  rfl

@[simp]
theorem coe_mk'_linearMap (D : A →ₗ[R] M) (h) : (mk' D h : A →ₗ[R] M) = D :=
  rfl

end Cancel

section

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]

section

variable {M : Type*} [AddCommGroup M] [Module A M] [Module R M]
variable (D : Derivation R A M) {D1 D2 : Derivation R A M} (r : R) (a b : A)

protected theorem map_neg : D (-a) = -D a :=
  map_neg D a

protected theorem map_sub : D (a - b) = D a - D b :=
  map_sub D a b

@[simp]
theorem map_intCast (n : ℤ) : D (n : A) = 0 := by
  rw [← zsmul_one, D.map_smul_of_tower n, map_one_eq_zero, smul_zero]

theorem leibniz_of_mul_eq_one {a b : A} (h : a * b = 1) : D a = -a ^ 2 • D b := by
  rw [neg_smul]
  refine eq_neg_of_add_eq_zero_left ?_
  calc
    D a + a ^ 2 • D b = a • b • D a + a • a • D b := by simp only [smul_smul, h, one_smul, sq]
    _ = a • D (a * b) := by rw [leibniz, smul_add, add_comm]
    _ = 0 := by rw [h, map_one_eq_zero, smul_zero]

theorem leibniz_invOf [Invertible a] : D (⅟a) = -⅟a ^ 2 • D a :=
  D.leibniz_of_mul_eq_one <| invOf_mul_self a

section Field

variable {K : Type*} [Field K] [Module K M] [Algebra R K] (D : Derivation R K M)

theorem leibniz_inv (a : K) : D a⁻¹ = -a⁻¹ ^ 2 • D a := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  · exact D.leibniz_of_mul_eq_one (inv_mul_cancel₀ ha)

theorem leibniz_div (a b : K) : D (a / b) = b⁻¹ ^ 2 • (b • D a - a • D b) := by
  simp only [div_eq_mul_inv, leibniz, leibniz_inv, inv_pow, neg_smul, smul_neg, smul_smul, add_comm,
    sub_eq_add_neg, smul_add]
  rw [← inv_mul_mul_self b⁻¹, inv_inv]
  ring_nf

theorem leibniz_div_const (a b : K) (h : D b = 0) : D (a / b) = b⁻¹ • D a := by
  simp only [leibniz_div, inv_pow, h, smul_zero, sub_zero, smul_smul]
  rw [← mul_self_mul_inv b⁻¹, inv_inv]
  ring_nf

lemma leibniz_zpow (a : K) (n : ℤ) : D (a ^ n) = n • a ^ (n - 1) • D a := by
  by_cases hn : n = 0
  · simp [hn]
  by_cases ha : a = 0
  · simp [ha, zero_zpow n hn]
  rcases Int.natAbs_eq n with h | h
  · rw [h]
    simp only [zpow_natCast, leibniz_pow, natCast_zsmul]
    rw [← zpow_natCast]
    congr
    omega
  · rw [h, zpow_neg, zpow_natCast, leibniz_inv, leibniz_pow, inv_pow, ← pow_mul, ← zpow_natCast,
      ← zpow_natCast, ← Nat.cast_smul_eq_nsmul K, ← Int.cast_smul_eq_zsmul K, smul_smul, smul_smul,
      smul_smul]
    trans (-n.natAbs * (a ^ ((n.natAbs - 1 : ℕ) : ℤ) / (a ^ ((n.natAbs * 2 : ℕ) : ℤ)))) • D a
    · ring_nf
    rw [← zpow_sub₀ ha]
    congr 3
    · norm_cast
    omega

end Field

instance : Neg (Derivation R A M) :=
  ⟨fun D =>
    mk' (-D) fun a b => by
      simp only [LinearMap.neg_apply, smul_neg, neg_add_rev, leibniz, coeFn_coe, add_comm]⟩

@[simp]
theorem coe_neg (D : Derivation R A M) : ⇑(-D) = -D :=
  rfl

@[simp]
theorem coe_neg_linearMap (D : Derivation R A M) : ↑(-D) = (-D : A →ₗ[R] M) :=
  rfl

theorem neg_apply : (-D) a = -D a :=
  rfl

instance : Sub (Derivation R A M) :=
  ⟨fun D1 D2 =>
    mk' (D1 - D2 : A →ₗ[R] M) fun a b => by
      simp only [LinearMap.sub_apply, leibniz, coeFn_coe, smul_sub, add_sub_add_comm]⟩

@[simp]
theorem coe_sub (D1 D2 : Derivation R A M) : ⇑(D1 - D2) = D1 - D2 :=
  rfl

@[simp]
theorem coe_sub_linearMap (D1 D2 : Derivation R A M) : ↑(D1 - D2) = (D1 - D2 : A →ₗ[R] M) :=
  rfl

theorem sub_apply : (D1 - D2) a = D1 a - D2 a :=
  rfl

instance : AddCommGroup (Derivation R A M) :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

end

end

end Derivation
