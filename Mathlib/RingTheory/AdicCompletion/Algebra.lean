/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Algebra.Module.Torsion

/-!
# Algebra instance on adic completion

In this file we provide an algebra instance on the adic completion of a ring. Then the adic
completion of any module is a module over the adic completion of the ring.

## Implementation details

We do not make a separate adic completion type in algebra case, to not duplicate all module
theoretic results on adic completions. This choice does cause some trouble though,
since `I ^ n • ⊤` is not defeq to `I ^ n`. We try to work around most of the trouble by
providing as much API as possible.

-/

open Submodule

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]

namespace AdicCompletion

attribute [-simp] smul_eq_mul Algebra.id.smul_eq_mul

@[local simp]
theorem transitionMap_ideal_mk {m n : ℕ} (hmn : m ≤ n) (x : R) :
    transitionMap I R hmn (Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) x) =
      Ideal.Quotient.mk (I ^ m • ⊤ : Ideal R) x :=
  rfl

@[local simp]
theorem transitionMap_map_one {m n : ℕ} (hmn : m ≤ n) : transitionMap I R hmn 1 = 1 :=
  rfl

@[local simp]
theorem transitionMap_map_mul {m n : ℕ} (hmn : m ≤ n) (x y : R ⧸ (I ^ n • ⊤ : Ideal R)) :
    transitionMap I R hmn (x * y) = transitionMap I R hmn x * transitionMap I R hmn y :=
  Quotient.inductionOn₂' x y (fun _ _ ↦ rfl)

/-- `AdicCompletion.transitionMap` as an algebra homomorphism. -/
def transitionMapₐ {m n : ℕ} (hmn : m ≤ n) :
    R ⧸ (I ^ n • ⊤ : Ideal R) →ₐ[R] R ⧸ (I ^ m • ⊤ : Ideal R) :=
  AlgHom.ofLinearMap (transitionMap I R hmn) rfl (transitionMap_map_mul I hmn)

/-- `AdicCompletion I R` is an `R`-subalgebra of `∀ n, R ⧸ (I ^ n • ⊤ : Ideal R)`. -/
def subalgebra : Subalgebra R (∀ n, R ⧸ (I ^ n • ⊤ : Ideal R)) :=
  Submodule.toSubalgebra (submodule I R) (fun _ ↦ by simp)
    (fun x y hx hy m n hmn ↦ by simp [hx hmn, hy hmn])

/-- `AdicCompletion I R` is a subring of `∀ n, R ⧸ (I ^ n • ⊤ : Ideal R)`. -/
def subring : Subring (∀ n, R ⧸ (I ^ n • ⊤ : Ideal R)) :=
  Subalgebra.toSubring (subalgebra I)

instance : CommRing (AdicCompletion I R) :=
  inferInstanceAs <| CommRing (subring I)

instance : Algebra R (AdicCompletion I R) :=
  inferInstanceAs <| Algebra R (subalgebra I)

@[simp]
theorem val_one (n : ℕ) : (1 : AdicCompletion I R).val n = 1 :=
  rfl

@[simp]
theorem val_mul (n : ℕ) (x y : AdicCompletion I R) : (x * y).val n = x.val n * y.val n :=
  rfl

/-- The canonical algebra map from the adic completion to `R ⧸ I ^ n`.

This is `AdicCompletion.eval` postcomposed with the algebra isomorphism
`R ⧸ (I ^ n • ⊤) ≃ₐ[R] R ⧸ I ^ n`. -/
def evalₐ (n : ℕ) : AdicCompletion I R →ₐ[R] R ⧸ I ^ n :=
  have h : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext x; simp
  AlgHom.comp
    (Ideal.quotientEquivAlgOfEq R h)
    (AlgHom.ofLinearMap (eval I R n) rfl (fun _ _ ↦ rfl))

@[simp]
theorem evalₐ_mk (n : ℕ) (x : AdicCauchySequence I R) :
    evalₐ I n (mk I R x) = Ideal.Quotient.mk (I ^ n) (x.val n) := by
  simp [evalₐ]

/-- `AdicCauchySequence I R` is an `R`-subalgebra of `ℕ → R`. -/
def AdicCauchySequence.subalgebra : Subalgebra R (ℕ → R) :=
  Submodule.toSubalgebra (AdicCauchySequence.submodule I R)
    (fun {m n} _ ↦ by simp; rfl)
    (fun x y hx hy {m n} hmn ↦ by
      simp only [Pi.mul_apply]
      exact SModEq.mul (hx hmn) (hy hmn))

/-- `AdicCauchySequence I R` is a subring of `ℕ → R`. -/
def AdicCauchySequence.subring : Subring (ℕ → R) :=
  Subalgebra.toSubring (AdicCauchySequence.subalgebra I)

instance : CommRing (AdicCauchySequence I R) :=
  inferInstanceAs <| CommRing (AdicCauchySequence.subring I)

instance : Algebra R (AdicCauchySequence I R) :=
  inferInstanceAs <| Algebra R (AdicCauchySequence.subalgebra I)

@[simp]
theorem one_apply (n : ℕ) : (1 : AdicCauchySequence I R) n = 1 :=
  rfl

@[simp]
theorem mul_apply (n : ℕ) (f g : AdicCauchySequence I R) : (f * g) n = f n * g n :=
  rfl

/-- The canonical algebra map from adic cauchy sequences to the adic completion. -/
@[simps!]
def mkₐ : AdicCauchySequence I R →ₐ[R] AdicCompletion I R :=
  AlgHom.ofLinearMap (mk I R) rfl (fun _ _ ↦ rfl)

@[simp]
theorem evalₐ_mkₐ (n : ℕ) (x : AdicCauchySequence I R) :
    evalₐ I n (mkₐ I x) = Ideal.Quotient.mk (I ^ n) (x.val n) := by
  simp [mkₐ]

theorem Ideal.mk_eq_mk {m n : ℕ} (hmn : m ≤ n) (r : AdicCauchySequence I R) :
    Ideal.Quotient.mk (I ^ m) (r.val n) = Ideal.Quotient.mk (I ^ m) (r.val m) := by
  have h : I ^ m = I ^ m • ⊤ := by simp
  rw [h, ← Ideal.Quotient.mk_eq_mk, ← Ideal.Quotient.mk_eq_mk]
  exact (r.property hmn).symm

theorem smul_mk {m n : ℕ} (hmn : m ≤ n) (r : AdicCauchySequence I R)
    (x : AdicCauchySequence I M) :
    r.val n • Submodule.Quotient.mk (p := (I ^ m • ⊤ : Submodule R M)) (x.val n) =
      r.val m • Submodule.Quotient.mk (p := (I ^ m • ⊤ : Submodule R M)) (x.val m) := by
  rw [← Submodule.Quotient.mk_smul, ← Module.Quotient.mk_smul_mk,
    AdicCauchySequence.mk_eq_mk hmn, Ideal.mk_eq_mk I hmn, Module.Quotient.mk_smul_mk,
    Submodule.Quotient.mk_smul]

/-- Scalar multiplication of `R ⧸ (I • ⊤)` on `M ⧸ (I • ⊤)`. This is used in order to have
good definitional behaviour for the module instance on adic completions -/
instance : SMul (R ⧸ (I • ⊤ : Ideal R)) (M ⧸ (I • ⊤ : Submodule R M)) where
  smul r x :=
    Quotient.liftOn r (· • x) fun b₁ b₂ (h : Setoid.Rel _ b₁ b₂) ↦ by
      refine Quotient.inductionOn' x (fun x ↦ ?_)
      have h : b₁ - b₂ ∈ (I : Submodule R R) := by
        rwa [show I = I • ⊤ by simp, ← Submodule.quotientRel_r_def]
      rw [← sub_eq_zero, ← sub_smul, Submodule.Quotient.mk''_eq_mk,
        ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul h mem_top

@[local simp]
theorem mk_smul_mk (r : R) (x : M) :
    Ideal.Quotient.mk (I • ⊤) r • Submodule.Quotient.mk (p := (I • ⊤ : Submodule R M)) x
      = r • Submodule.Quotient.mk (p := (I • ⊤ : Submodule R M)) x :=
  rfl

theorem val_smul_eq_evalₐ_smul (n : ℕ) (r : AdicCompletion I R)
    (x : M ⧸ (I ^ n • ⊤ : Submodule R M)) : r.val n • x = evalₐ I n r • x := by
  apply induction_on I R r (fun r ↦ ?_)
  exact Quotient.inductionOn' x (fun x ↦ rfl)

instance : Module (R ⧸ (I • ⊤ : Ideal R)) (M ⧸ (I • ⊤ : Submodule R M)) :=
  Function.Surjective.moduleLeft (Ideal.Quotient.mk (I • ⊤ : Ideal R))
    Ideal.Quotient.mk_surjective (fun _ _ ↦ rfl)

instance : IsScalarTower R (R ⧸ (I • ⊤ : Ideal R)) (M ⧸ (I • ⊤ : Submodule R M)) where
  smul_assoc r s x := by
    refine Quotient.inductionOn' s (fun s ↦ ?_)
    refine Quotient.inductionOn' x (fun x ↦ ?_)
    simp only [Submodule.Quotient.mk''_eq_mk]
    rw [← Submodule.Quotient.mk_smul, Ideal.Quotient.mk_eq_mk, mk_smul_mk, smul_assoc]
    rfl

instance smul : SMul (AdicCompletion I R) (AdicCompletion I M) where
  smul r x := {
    val := fun n ↦ eval I R n r • eval I M n x
    property := fun {m n} hmn ↦ by
      apply induction_on I R r (fun r ↦ ?_)
      apply induction_on I M x (fun x ↦ ?_)
      simp only [coe_eval, mk_apply_coe, mkQ_apply, Ideal.Quotient.mk_eq_mk,
        mk_smul_mk, LinearMapClass.map_smul, transitionMap_mk]
      rw [smul_mk I hmn]
  }

@[simp]
theorem smul_eval (n : ℕ) (r : AdicCompletion I R) (x : AdicCompletion I M) :
    (r • x).val n = r.val n • x.val n :=
  rfl

/-- `AdicCompletion I M` is naturally an `AdicCompletion I R` module. -/
instance module : Module (AdicCompletion I R) (AdicCompletion I M) where
  one_smul b := by
    ext n
    simp only [smul_eval, val_one, one_smul]
  mul_smul r s x := by
    ext n
    simp only [smul_eval, val_mul, mul_smul]
  smul_zero r := by
    ext n
    rw [smul_eval, val_zero, smul_zero]
  smul_add r x y := by
    ext n
    simp only [smul_eval, val_add, smul_add]
  add_smul r s x := by
    ext n
    simp only [coe_eval, smul_eval, map_add, add_smul, val_add]
  zero_smul x := by
    ext n
    simp only [smul_eval, _root_.map_zero, zero_smul, val_zero]

instance : IsScalarTower R (AdicCompletion I R) (AdicCompletion I M) where
  smul_assoc r s x := by
    ext n
    rw [smul_eval, val_smul, val_smul, smul_eval, smul_assoc]

/-- A priori `AdicCompletion I R` has two `AdicCompletion I R`-module instances.
Both agree definitionally. -/
example : module I = @Algebra.toModule (AdicCompletion I R)
    (AdicCompletion I R) _ _ (Algebra.id _) := by
  with_reducible_and_instances rfl
