/-
Copyright (c) 2022 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard M. Hill
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Finiteness

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

instance instFiniteOrig [Finite R M] : Finite R <| AEval R M a := inferInstanceAs (Finite R M)

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

lemma of_symm_X_smul (m : AEval R M a) :
    (of R M a).symm ((X : R[X]) • m) = a • (of R M a).symm m := by
  rw [of_symm_smul, aeval_X]

instance instIsScalarTowerOrigPolynomial : IsScalarTower R R[X] <| AEval R M a where
  smul_assoc r f m := by
    apply (of R M a).symm.injective
    rw [of_symm_smul, map_smul, smul_assoc, map_smul, of_symm_smul]

instance instFinitePolynomial [Finite R M] : Finite R[X] <| AEval R M a :=
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

variable {p : Submodule R M} (hp : p ≤ p.comap (Algebra.lsmul R R M a))
  {q : Submodule R[X] <| AEval R M a}

variable (R M) in
/-- We can turn an `R[X]`-submodule into an `R`-submodule by forgetting the action of `X`. -/
def comapSubmodule :
    CompleteLatticeHom (Submodule R[X] <| AEval R M a) (Submodule R M) :=
  (Submodule.orderIsoMapComap (of R M a)).symm.toCompleteLatticeHom.comp <|
    Submodule.restrictScalarsLatticeHom R R[X] (AEval R M a)

@[simp] lemma mem_comapSubmodule {x : M} :
    x ∈ comapSubmodule R M a q ↔ of R M a x ∈ q :=
  Iff.rfl

@[simp] lemma comapSubmodule_le_comap :
    comapSubmodule R M a q ≤ (comapSubmodule R M a q).comap (Algebra.lsmul R R M a) := by
  intro m hm
  simpa only [Submodule.mem_comap, Algebra.lsmul_coe, mem_comapSubmodule, ← X_smul_of] using
    q.smul_mem (X : R[X]) hm

/-- An `R`-submodule which is stable under the action of `a` can be promoted to an
`R[X]`-submodule. -/
def mapSubmodule : Submodule R[X] <| AEval R M a :=
  { toAddSubmonoid := p.toAddSubmonoid.map (of R M a)
    smul_mem' := by
      rintro f - ⟨m : M, h : m ∈ p, rfl⟩
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup, AddSubmonoid.mem_map,
        Submodule.mem_toAddSubmonoid]
      exact ⟨aeval a f • m, aeval_apply_smul_mem_of_le_comap' h f a hp, of_aeval_smul a f m⟩ }

@[simp] lemma mem_mapSubmodule {m : AEval R M a} :
    m ∈ mapSubmodule a hp ↔ (of R M a).symm m ∈ p :=
  ⟨fun ⟨_, hm, hm'⟩ ↦ hm'.symm ▸ hm, fun hm ↦ ⟨(of R M a).symm m, hm, rfl⟩⟩

@[simp] lemma mapSubmodule_comapSubmodule (h := comapSubmodule_le_comap a) :
    mapSubmodule a (p := comapSubmodule R M a q) h = q := by
  ext; simp

@[simp] lemma comapSubmodule_mapSubmodule :
    comapSubmodule R M a (mapSubmodule a hp) = p := by
  ext; simp

variable (R M)

lemma injective_comapSubmodule : Injective (comapSubmodule R M a) := by
  intro q₁ q₂ hq
  rw [← mapSubmodule_comapSubmodule (q := q₁), ← mapSubmodule_comapSubmodule (q := q₂)]
  simp_rw [hq]

lemma range_comapSubmodule :
    range (comapSubmodule R M a) = {p | p ≤ p.comap (Algebra.lsmul R R M a)} :=
  le_antisymm (fun _ ⟨_, hq⟩ ↦ hq ▸ comapSubmodule_le_comap a)
    (fun _ hp ↦ ⟨mapSubmodule a hp, comapSubmodule_mapSubmodule a hp⟩)

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
lemma AEval'.of_symm_X_smul (m : AEval' φ) :
    (AEval'.of φ).symm ((X : R[X]) • m) = φ ((AEval'.of φ).symm m) := AEval.of_symm_X_smul _ _

instance [Finite R M] : Finite R[X] <| AEval' φ := inferInstance

end Module
