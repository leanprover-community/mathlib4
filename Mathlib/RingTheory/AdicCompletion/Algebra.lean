/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Algebra instance on adic completion

In this file we provide an algebra instance on the adic completion of a ring. Then the adic
completion of any module is a module over the adic completion of the ring.

## Main definitions

- `evalₐ`: the canonical algebra map from the adic completion to `R ⧸ I ^ n`.

- `AdicCompletion.liftRingHom`: given a compatible family of ring maps
  `R →+* S ⧸ I ^ n`, the lift ring map `R →+* AdicCompletion I S`.

## Implementation details

We do not make a separate adic completion type in algebra case, to not duplicate all
module-theoretic results on adic completions. This choice does cause some trouble though,
since `I ^ n • ⊤` is not defeq to `I ^ n`. We try to work around most of the trouble by
providing as much API as possible.

-/

@[expose] public section

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

theorem factor_evalₐ_eq_eval {n : ℕ} (x : AdicCompletion I R) (h : I ^ n ≤ I ^ n • ⊤) :
    Ideal.Quotient.factor h (evalₐ I n x) = eval I R n x := by
  simp [evalₐ]

theorem factor_eval_eq_evalₐ {n : ℕ} (x : AdicCompletion I R) (h : I ^ n • ⊤ ≤ I ^ n) :
    factor h (eval I R n x) = evalₐ I n x := by
  simp [evalₐ]

/--
The composition map `R →+* AdicCompletion I R →+* R ⧸ I ^ n` equals to the natural quotient map.
-/
@[simp]
theorem evalₐ_of (n : ℕ) (x : R) :
    evalₐ I n (of I R x) = Ideal.Quotient.mk _ x := by
  simp [evalₐ]

theorem surjective_evalₐ (n : ℕ) : Function.Surjective (evalₐ I n) := by
  simp only [evalₐ, smul_eq_mul, Ideal.quotientEquivAlgOfEq_coe_eq_factorₐ,
    AlgHom.coe_comp]
  apply Function.Surjective.comp
  · exact factor_surjective Ideal.mul_le_right
  · exact eval_surjective I R n

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

section liftRingHom

open Ideal Quotient

variable {R S : Type*} [NonAssocSemiring R] [CommRing S] (I : Ideal S)

/--
The universal property of `AdicCompletion` for rings.
The lift ring map `R →+* AdicCompletion I S` of a compatible family of
ring maps `R →+* S ⧸ I ^ n`.
-/
def liftRingHom (f : (n : ℕ) → R →+* S ⧸ I ^ n)
    (hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m) :
    R →+* AdicCompletion I S where
  toFun := fun x ↦ ⟨fun n ↦ (factor (le_of_eq (Ideal.mul_top _).symm)) (f n x),
    fun hkl ↦ by simp [transitionMap, Submodule.factorPow, ← hf hkl]⟩
  map_add' x y := by
    simp only [map_add]
    ext; simp
  map_zero' := by
    simp only [map_zero]
    ext; simp
  map_mul' x y := by
    simp only [mapQ_eq_factor, factor_eq_factor, map_mul]
    ext; simp
  map_one' := by
    simp only [map_one]
    ext; simp

variable (f : (n : ℕ) → R →+* S ⧸ I ^ n)
  (hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m)

theorem factor_eval_liftRingHom (n : ℕ) (x : R) (h : I ^ n • ⊤ ≤ I ^ n) :
    factor h (eval I S n (liftRingHom I f hf x)) = f n x := by
  simp [liftRingHom, eval]

@[simp]
theorem evalₐ_liftRingHom (n : ℕ) (x : R) :
    evalₐ I n (liftRingHom I f hf x) = f n x := by
  rw [← factor_eval_eq_evalₐ I _ (le_of_eq (Ideal.mul_top _))]
  simp [liftRingHom, eval]

@[simp]
theorem evalₐ_comp_liftRingHom (n : ℕ) :
    (evalₐ I n : _ →+* _).comp (liftRingHom I f hf) = f n := by
  ext; simp

variable [IsAdicComplete I S]

/--
When `S` is `I`-adic complete, the canonical map from `S` to
its `I`-adic completion is an `S`-algebra isomorphism.
-/
noncomputable def ofAlgEquiv : S ≃ₐ[S] AdicCompletion I S where
  __ := ofLinearEquiv I S
  map_mul' _ _ := by ext; simp
  commutes' _ := rfl

@[simp]
theorem ofAlgEquiv_apply (x : S) : ofAlgEquiv I x = of I S x := by
  rfl

@[simp]
theorem of_ofAlgEquiv_symm (x : AdicCompletion I S) :
    of I S ((ofAlgEquiv I).symm x) = x := by
  simp [ofAlgEquiv]

@[simp]
theorem ofAlgEquiv_symm_of (x : S) :
    (ofAlgEquiv I).symm (of I S x) = x := by
  simp [ofAlgEquiv]

theorem mk_smul_top_ofAlgEquiv_symm (n : ℕ) (x : AdicCompletion I S) :
    Ideal.Quotient.mk (I ^ n • ⊤) ((ofAlgEquiv I).symm x) = eval I S n x := by
  nth_rw 2 [← of_ofAlgEquiv_symm I x]
  simp [-of_ofAlgEquiv_symm, eval]

@[simp]
theorem mk_ofAlgEquiv_symm (n : ℕ) (x : AdicCompletion I S) :
    Ideal.Quotient.mk (I ^ n) ((ofAlgEquiv I).symm x) = evalₐ I n x := by
  simp only [evalₐ, AlgHom.coe_comp, Function.comp_apply, AlgHom.ofLinearMap_apply]
  rw [← mk_smul_top_ofAlgEquiv_symm I n x]
  simp

end liftRingHom

end AdicCompletion
