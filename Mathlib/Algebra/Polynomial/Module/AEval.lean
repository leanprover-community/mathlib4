/-
Copyright (c) 2022 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard M. Hill
-/
import Mathlib.Algebra.Module.Submodule.Invariant
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Maps

/-!
# Action of the polynomial ring on module induced by an algebra element.

Given an element `a` in an `R`-algebra `A` and an `A`-module `M` we define an
`R[X]`-module `Module.AEval R M a`, which is a type synonym of `M` with the
action of a polynomial `f` given by `f • m = Polynomial.aeval a f • m`.
In particular `X • m = a • m`.

In the special case that `A = M →ₗ[R] M` and `φ : M →ₗ[R] M`, the module `Module.AEval R M a` is
abbreviated `Module.AEval' φ`. In this module we have `X • m = ↑φ m`.
-/

open Set Function Polynomial

namespace Module
/--
Suppose `a` is an element of an `R`-algebra `A` and `M` is an `A`-module.
Loosely speaking, `Module.AEval R M a` is the `R[X]`-module with elements `m : M`,
where the action of a polynomial $f$ is given by $f • m = f(a) • m$.

More precisely, `Module.AEval R M a` has elements `Module.AEval.of R M a m` for `m : M`,
and the action of `f` is `f • (of R M a m) = of R M a ((aeval a f) • m)`.
-/
@[nolint unusedArguments]
def AEval (R M : Type*) {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M] (_ : A) := M

instance AEval.instAddCommGroup {R A M} [CommSemiring R] [Semiring A] (a : A) [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] :
    AddCommGroup <| AEval R M a := inferInstanceAs (AddCommGroup M)

variable {R A M} [CommSemiring R] [Semiring A] (a : A) [Algebra R A] [AddCommMonoid M] [Module A M]
  [Module R M] [IsScalarTower R A M]

namespace AEval

instance instAddCommMonoid : AddCommMonoid <| AEval R M a := inferInstanceAs (AddCommMonoid M)

instance instModuleOrig : Module R <| AEval R M a := inferInstanceAs (Module R M)

instance instFiniteOrig [Module.Finite R M] : Module.Finite R <| AEval R M a :=
  ‹Module.Finite R M›

instance instModulePolynomial : Module R[X] <| AEval R M a := compHom M (aeval a).toRingHom

variable (R M)
/--
The canonical linear equivalence between `M` and `Module.AEval R M a` as an `R`-module.
-/
def of : M ≃ₗ[R] AEval R M a :=
  LinearEquiv.refl _ _

variable {R M}

lemma of_aeval_smul (f : R[X]) (m : M) : of R M a (aeval a f • m) = f • of R M a m := rfl

@[simp] lemma of_symm_smul (f : R[X]) (m : AEval R M a) :
    (of R M a).symm (f • m) = aeval a f • (of R M a).symm m := rfl

@[simp] lemma C_smul (t : R) (m : AEval R M a) : C t • m = t • m :=
  (of R M a).symm.injective <| by simp

lemma X_smul_of (m : M) : (X : R[X]) • (of R M a m) = of R M a (a • m) := by
  rw [← of_aeval_smul, aeval_X]

lemma X_pow_smul_of (m : M) (n : ℕ) : (X ^ n : R[X]) • (of R M a m) = of R M a (a ^ n • m) := by
  rw [← of_aeval_smul, aeval_X_pow]

lemma of_symm_X_smul (m : AEval R M a) :
    (of R M a).symm ((X : R[X]) • m) = a • (of R M a).symm m := by
  rw [of_symm_smul, aeval_X]

instance instIsScalarTowerOrigPolynomial : IsScalarTower R R[X] <| AEval R M a where
  smul_assoc r f m := by
    apply (of R M a).symm.injective
    rw [of_symm_smul, map_smul, smul_assoc, map_smul, of_symm_smul]

instance instFinitePolynomial [Module.Finite R M] : Module.Finite R[X] <| AEval R M a :=
  Finite.of_restrictScalars_finite R _ _

/-- Construct an `R[X]`-linear map out of `AEval R M a` from a `R`-linear map out of `M`. -/
def _root_.LinearMap.ofAEval {N} [AddCommMonoid N] [Module R N] [Module R[X] N]
    [IsScalarTower R R[X] N] (f : M →ₗ[R] N) (hf : ∀ m : M, f (a • m) = (X : R[X]) • f m) :
    AEval R M a →ₗ[R[X]] N where
  __ := f ∘ₗ (of R M a).symm
  map_smul' p := p.induction_on (fun k m ↦ by simp [C_eq_algebraMap])
    (fun p q hp hq m ↦ by simp_all [add_smul]) fun n k h m ↦ by
      simp_rw [RingHom.id_apply, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
        LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at h ⊢
      simp_rw [pow_succ, ← mul_assoc, mul_smul _ X, ← hf, ← of_symm_X_smul, ← h]

/-- Construct an `R[X]`-linear equivalence out of `AEval R M a` from a `R`-linear map out of `M`. -/
def _root_.LinearEquiv.ofAEval {N} [AddCommMonoid N] [Module R N] [Module R[X] N]
    [IsScalarTower R R[X] N] (f : M ≃ₗ[R] N) (hf : ∀ m : M, f (a • m) = (X : R[X]) • f m) :
    AEval R M a ≃ₗ[R[X]] N where
  __ := LinearMap.ofAEval a f hf
  invFun := (of R M a) ∘ f.symm
  left_inv x := by simp [LinearMap.ofAEval]
  right_inv x := by simp [LinearMap.ofAEval]

lemma annihilator_eq_ker_aeval [FaithfulSMul A M] :
    annihilator R[X] (AEval R M a) = RingHom.ker (aeval a) := by
  ext p
  simp_rw [mem_annihilator, RingHom.mem_ker]
  change (∀ m : M, aeval a p • m = 0) ↔ _
  exact ⟨fun h ↦ eq_of_smul_eq_smul (α := M) <| by simp [h], fun h ↦ by simp [h]⟩

@[simp]
lemma annihilator_top_eq_ker_aeval [FaithfulSMul A M] :
    (⊤ : Submodule R[X] <| AEval R M a).annihilator = RingHom.ker (aeval a) := by
  ext p
  simp only [Submodule.mem_annihilator, Submodule.mem_top, forall_true_left, RingHom.mem_ker]
  change (∀ m : M, aeval a p • m = 0) ↔ _
  exact ⟨fun h ↦ eq_of_smul_eq_smul (α := M) <| by simp [h], fun h ↦ by simp [h]⟩

section Submodule

variable (R M)

/-- The natural order isomorphism between the two ways to represent invariant submodules. -/
def mapSubmodule :
    (Algebra.lsmul R R M a).invtSubmodule ≃o Submodule R[X] (AEval R M a) where
  toFun p :=
    { toAddSubmonoid := (p : Submodule R M).toAddSubmonoid.map (of R M a)
      smul_mem' := by
        rintro f - ⟨m : M, h : m ∈ (p : Submodule R M), rfl⟩
        simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
          AddSubmonoid.mem_map, Submodule.mem_toAddSubmonoid]
        exact ⟨aeval a f • m, aeval_apply_smul_mem_of_le_comap' h f a p.2, of_aeval_smul a f m⟩ }
  invFun q := ⟨(Submodule.orderIsoMapComap (of R M a)).symm (q.restrictScalars R), fun m hm ↦ by
    simpa [← X_smul_of] using q.smul_mem (X : R[X]) hm⟩
  left_inv p := by ext; simp
  right_inv q := by ext; aesop
  map_rel_iff' {p p'} := ⟨fun h x hx ↦ by aesop (rule_sets := [SetLike!]), fun h x hx ↦ by aesop⟩

@[simp] lemma mem_mapSubmodule_apply {p : (Algebra.lsmul R R M a).invtSubmodule} {m : AEval R M a} :
    m ∈ mapSubmodule R M a p ↔ (of R M a).symm m ∈ (p : Submodule R M) :=
  ⟨fun ⟨_, hm, hm'⟩ ↦ hm'.symm ▸ hm, fun hm ↦ ⟨(of R M a).symm m, hm, rfl⟩⟩

@[simp] lemma mem_mapSubmodule_symm_apply {q : Submodule R[X] (AEval R M a)} {m : M} :
    m ∈ ((mapSubmodule R M a).symm q : Submodule R M) ↔ of R M a m ∈ q :=
  Iff.rfl

variable {R M}
variable (p : Submodule R M) (hp : p ∈ (Algebra.lsmul R R M a).invtSubmodule)

/-- The natural `R`-linear equivalence between the two ways to represent an invariant submodule. -/
def equiv_mapSubmodule :
    p ≃ₗ[R] mapSubmodule R M a ⟨p, hp⟩ where
  toFun x := ⟨of R M a x, by simp⟩
  invFun x := ⟨((of R M _).symm (x : AEval R M a)), by obtain ⟨x, hx⟩ := x; simpa using hx⟩
  map_add' x y := rfl
  map_smul' t x := rfl

/-- The natural `R[X]`-linear equivalence between the two ways to represent an invariant submodule.
-/
noncomputable def restrict_equiv_mapSubmodule :
    (AEval R p <| (Algebra.lsmul R R M a).restrict hp) ≃ₗ[R[X]] mapSubmodule R M a ⟨p, hp⟩ :=
  LinearEquiv.ofAEval ((Algebra.lsmul R R M a).restrict hp) (equiv_mapSubmodule a p hp)
    (fun x ↦ by simp [equiv_mapSubmodule, X_smul_of])

end Submodule

end AEval

variable (φ : M →ₗ[R] M)
/--
Given and `R`-module `M` and a linear map `φ : M →ₗ[R] M`, `Module.AEval' φ` is loosely speaking
the `R[X]`-module with elements `m : M`, where the action of a polynomial $f$ is given by
$f • m = f(a) • m$.

More precisely, `Module.AEval' φ` has elements `Module.AEval'.of φ m` for `m : M`,
and the action of `f` is `f • (of φ m) = of φ ((aeval φ f) • m)`.

`Module.AEval'` is defined as a special case of `Module.AEval` in which the `R`-algebra is
`M →ₗ[R] M`. Lemmas involving `Module.AEval` may be applied to `Module.AEval'`.
-/
abbrev AEval' := AEval R M φ
/--
The canonical linear equivalence between `M` and `Module.AEval' φ` as an `R`-module,
where `φ : M →ₗ[R] M`.
-/
abbrev AEval'.of : M ≃ₗ[R] AEval' φ := AEval.of R M φ

lemma AEval'_def : AEval' φ = AEval R M φ := rfl

lemma AEval'.X_smul_of (m : M) : (X : R[X]) • AEval'.of φ m = AEval'.of φ (φ m) :=
  AEval.X_smul_of _ _

lemma AEval'.X_pow_smul_of (m : M) (n : ℕ) : (X ^ n : R[X]) • AEval'.of φ m = .of φ (φ ^ n • m) :=
  AEval.X_pow_smul_of ..

lemma AEval'.of_symm_X_smul (m : AEval' φ) :
    (AEval'.of φ).symm ((X : R[X]) • m) = φ ((AEval'.of φ).symm m) := AEval.of_symm_X_smul _ _

instance [Module.Finite R M] : Module.Finite R[X] <| AEval' φ := inferInstance

end Module
