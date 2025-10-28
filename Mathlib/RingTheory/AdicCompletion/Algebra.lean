/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.Algebra.Module.Torsion
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Algebra instance on adic completion

In this file we provide an algebra instance on the adic completion of a ring. Then the adic
completion of any module is a module over the adic completion of the ring.

## Implementation details

We do not make a separate adic completion type in algebra case, to not duplicate all
module-theoretic results on adic completions. This choice does cause some trouble though,
since `I ^ n • ⊤` is not defeq to `I ^ n`. We try to work around most of the trouble by
providing as much API as possible.

-/

suppress_compilation

open Submodule

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R)
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

@[local simp]
theorem transitionMap_map_pow {m n a : ℕ} (hmn : m ≤ n) (x : R ⧸ (I ^ n • ⊤ : Ideal R)) :
    transitionMap I R hmn (x ^ a) = transitionMap I R hmn x ^ a :=
  Quotient.inductionOn' x (fun _ ↦ rfl)

/-- `AdicCompletion.transitionMap` as an algebra homomorphism. -/
def transitionMapₐ {m n : ℕ} (hmn : m ≤ n) :
    R ⧸ (I ^ n • ⊤ : Ideal R) →ₐ[R] R ⧸ (I ^ m • ⊤ : Ideal R) :=
  AlgHom.ofLinearMap (transitionMap I R hmn) rfl (transitionMap_map_mul I hmn)

/-- `AdicCompletion I R` is an `R`-subalgebra of `∀ n, R ⧸ (I ^ n • ⊤ : Ideal R)`. -/
def subalgebra : Subalgebra R (∀ n, R ⧸ (I ^ n • ⊤ : Ideal R)) :=
  Submodule.toSubalgebra (submodule I R) (fun _ ↦ by simp [transitionMap_map_one I])
    (fun x y hx hy m n hmn ↦ by simp [hx hmn, hy hmn, transitionMap_map_mul I hmn])

/-- `AdicCompletion I R` is a subring of `∀ n, R ⧸ (I ^ n • ⊤ : Ideal R)`. -/
def subring : Subring (∀ n, R ⧸ (I ^ n • ⊤ : Ideal R)) :=
  Subalgebra.toSubring (subalgebra I)

instance : Mul (AdicCompletion I R) where
  mul x y := ⟨x.val * y.val, fun hmn ↦ by
    simp [x.property, y.property, transitionMap_map_mul I hmn]⟩

instance : One (AdicCompletion I R) where
  one := ⟨1, by simp [transitionMap_map_one I]⟩

instance : NatCast (AdicCompletion I R) where
  natCast n := ⟨n, fun _ ↦ rfl⟩

instance : IntCast (AdicCompletion I R) where
  intCast n := ⟨n, fun _ ↦ rfl⟩

instance : Pow (AdicCompletion I R) ℕ where
  pow x n := ⟨x.val ^ n, fun hmn ↦ by simp [x.property, transitionMap_map_pow I hmn]⟩

instance : CommRing (AdicCompletion I R) :=
  let f : AdicCompletion I R → ∀ n, R ⧸ (I ^ n • ⊤ : Ideal R) := Subtype.val
  Subtype.val_injective.commRing f rfl rfl
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

instance [Algebra S R] : Algebra S (AdicCompletion I R) where
  algebraMap :=
  { toFun r := ⟨algebraMap S (∀ n, R ⧸ (I ^ n • ⊤ : Ideal R)) r, fun hmn ↦ by
      simp only [Pi.algebraMap_apply,
        IsScalarTower.algebraMap_apply S R (R ⧸ (I ^ _ • ⊤ : Ideal R)),
        Ideal.Quotient.algebraMap_eq, mapQ_eq_factor]
      rfl⟩
    map_one' := Subtype.ext <| map_one _
    map_mul' x y := Subtype.ext <| map_mul _ x y
    map_zero' := Subtype.ext <| map_zero _
    map_add' x y := Subtype.ext <| map_add _ x y }
  commutes' r x := Subtype.ext <| Algebra.commutes' r x.val
  smul_def' r x := Subtype.ext <| Algebra.smul_def' r x.val

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

instance : Mul (AdicCauchySequence I R) where
  mul x y := ⟨x.val * y.val, fun hmn ↦ SModEq.mul (x.property hmn) (y.property hmn)⟩

instance : One (AdicCauchySequence I R) where
  one := ⟨1, fun _ ↦ rfl⟩

instance : NatCast (AdicCauchySequence I R) where
  natCast n := ⟨n, fun _ ↦ rfl⟩

instance : IntCast (AdicCauchySequence I R) where
  intCast n := ⟨n, fun _ ↦ rfl⟩

instance : Pow (AdicCauchySequence I R) ℕ where
  pow x n := ⟨x.val ^ n, fun hmn ↦ SModEq.pow n (x.property hmn)⟩

instance : CommRing (AdicCauchySequence I R) :=
  let f : AdicCauchySequence I R → (ℕ → R) := Subtype.val
  Subtype.val_injective.commRing f rfl rfl
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

instance : Algebra R (AdicCauchySequence I R) where
  algebraMap :=
  { toFun r := ⟨algebraMap R (∀ _, R) r, fun _ ↦ rfl⟩
    map_one' := Subtype.ext <| map_one _
    map_mul' x y := Subtype.ext <| map_mul _ x y
    map_zero' := Subtype.ext <| map_zero _
    map_add' x y := Subtype.ext <| map_add _ x y }
  commutes' r x := Subtype.ext <| Algebra.commutes' r x.val
  smul_def' r x := Subtype.ext <| Algebra.smul_def' r x.val

@[simp]
theorem one_apply (n : ℕ) : (1 : AdicCauchySequence I R) n = 1 :=
  rfl

@[simp]
theorem mul_apply (n : ℕ) (f g : AdicCauchySequence I R) : (f * g) n = f n * g n :=
  rfl

/-- The canonical algebra map from adic Cauchy sequences to the adic completion. -/
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
  rw [← Ideal.Quotient.mk_eq_mk, ← Ideal.Quotient.mk_eq_mk, h]
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
    Quotient.liftOn r (· • x) fun b₁ b₂ h ↦ by
      refine Quotient.inductionOn' x (fun x ↦ ?_)
      have h : b₁ - b₂ ∈ (I : Submodule R R) := by
        rwa [show I = I • ⊤ by simp, ← Submodule.quotientRel_def]
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
      simp only [coe_eval, mapQ_eq_factor, mk_apply_coe, mkQ_apply, Ideal.Quotient.mk_eq_mk,
        mk_smul_mk, map_smul, mapQ_apply, LinearMap.id_coe, id_eq]
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
  smul_zero r := by ext n; simp
  smul_add r x y := by ext n; simp
  add_smul r s x := by ext n; simp [add_smul]
  zero_smul x := by ext n; simp

instance : IsScalarTower R (AdicCompletion I R) (AdicCompletion I M) where
  smul_assoc r s x := by
    ext n
    rw [smul_eval, val_smul_apply, val_smul_apply, smul_eval, smul_assoc]

/-- A priori `AdicCompletion I R` has two `AdicCompletion I R`-module instances.
Both agree definitionally. -/
example : module I = @Algebra.toModule (AdicCompletion I R)
    (AdicCompletion I R) _ _ (Algebra.id _) := by
  with_reducible_and_instances rfl

end AdicCompletion
