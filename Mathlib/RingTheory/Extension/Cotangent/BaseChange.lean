/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Ideal.CotangentBaseChange
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.Algebra.FiveLemma
import Mathlib.RingTheory.Kaehler.TensorProduct

/-!
# Base change for the naive cotangent complex

This file shows that the cotangent space and first homology of the naive cotangent complex
commute with base change.

## Main results

- `Algebra.Extension.tensorCotangentSpace`: If `T` is an `R`-algebra, there is a `T`-linear
  isomorphism `T ⊗[R] P.CotangentSpace ≃ₗ[T] (P.baseChange).CotangentSpace`.
- `Algebra.Extension.tensorCotangent'`: If `T` is flat over `R`, there is a `T`-linear
  isomorphism `T ⊗[R] P.Cotangent ≃ₗ[T] (P.baseChange).Cotangent`.
- `Algebra.Extension.tensorH1Cotangent'`: If `T` is flat over `R`, there is a `T`-linear
  isomorphism `T ⊗[R] P.H1Cotangent ≃ₗ[T] (P.baseChange).H1Cotangent`.
- `Algebra.tensorH1CotangentOfFlat`: Flat base change commutes with `H1Cotangent`.

-/

suppress_compilation

universe u

open TensorProduct

@[simps]
def AddEquiv.linearEquiv {α : Type*} {β : Type*} (A : Type*) [Semiring A] [AddCommMonoid α]
    [AddCommMonoid β] [Module A β] (e : α ≃+ β) :
    letI := e.module A
    α ≃ₗ[A] β :=
  letI := e.module A
  { __ := e
    map_smul' _ _ := e.apply_symm_apply _ }

/-

`(M₁ ⊗[R] M₂) ⊗[A] M₃ ≃ₗ[B] M₁ ⊗[R] (M₂ ⊗[A] M₃)`

-/

section

variable {R S : Type*} [CommSemiring R] [CommSemiring S]
 [Algebra R S]
 {M₁ M₂ M₃ M₁₂ M₂₃ M'' : Type*}
 [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
 [AddCommMonoid M₁₂] [AddCommMonoid M₂₃] [AddCommMonoid M'']
 [Module R M₁]
 [Module R M₂] [Module S M₂] [IsScalarTower R S M₂]
 [Module R M₃] [Module S M₃] [IsScalarTower R S M₃]
 [Module R M₁₂] [Module S M₁₂] [IsScalarTower R S M₁₂]
 [Module R M₂₃] [Module S M₂₃] [IsScalarTower R S M₂₃]
 [Module R M''] [Module S M''] [IsScalarTower R S M'']

/-- (Implementation): Use the more linear `IsTensorProduct.assoc`. -/
def IsTensorProduct.assocAux
    (f : M₁ →ₗ[R] M₂ →ₗ[S] M₁₂) (hf : IsTensorProduct (f.restrictScalars₁₂ R R))
    (g : M₂ →ₗ[S] M₃ →ₗ[S] M₂₃) (hg : IsTensorProduct g) :
    M₁₂ ⊗[S] M₃ ≃ₗ[R] M₁ ⊗[R] M₂₃ :=
  letI : Module S (M₁ ⊗[R] M₂) :=
    AddEquiv.module S hf.equiv.toAddEquiv
  haveI heq (s : S) (y : M₁) (x : M₂) : s • y ⊗ₜ[R] x = y ⊗ₜ[R] (s • x) := by
    change hf.equiv.symm (s • _) = _
    dsimp
    rw [← map_smul]
    apply hf.equiv_symm_apply
  haveI : IsScalarTower R S (M₁ ⊗[R] M₂) := hf.equiv.isScalarTower S
  letI e₀ : M₂ ⊗[R] M₁ ≃ₗ[S] M₁ ⊗[R] M₂ :=
    { __ := TensorProduct.comm R M₂ M₁
      map_smul' s x := by induction x <;> simp_all [TensorProduct.smul_tmul'] }
  LinearEquiv.symm <|
    TensorProduct.congr (.refl _ _) (hg.equiv.symm.restrictScalars R) ≪≫ₗ
    TensorProduct.comm _ _ _ ≪≫ₗ
    (AlgebraTensorModule.congr (TensorProduct.comm _ _ _) (.refl _ _)).restrictScalars R ≪≫ₗ
    (AlgebraTensorModule.assoc R S S M₃ M₂ M₁).restrictScalars R ≪≫ₗ
    (TensorProduct.comm _ _ _).restrictScalars R ≪≫ₗ
    (TensorProduct.congr e₀ (.refl _ _)).restrictScalars R ≪≫ₗ
    (TensorProduct.congr (hf.equiv.linearEquiv S) (.refl _ _)).restrictScalars R

variable (f : M₁ →ₗ[R] M₂ →ₗ[S] M₁₂) (hf : IsTensorProduct (f.restrictScalars₁₂ R R))
  (g : M₂ →ₗ[S] M₃ →ₗ[S] M₂₃) (hg : IsTensorProduct g)

@[simp]
lemma IsTensorProduct.assocAux_symm_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    (IsTensorProduct.assocAux f hf g hg).symm (x₁ ⊗ₜ g x₂ x₃) = f x₁ x₂ ⊗ₜ x₃ := by
  simp [IsTensorProduct.assocAux]

@[simp]
lemma IsTensorProduct.assocAux_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    IsTensorProduct.assocAux f hf g hg (f x₁ x₂ ⊗ₜ x₃) = x₁ ⊗ₜ g x₂ x₃ := by
  have : hf.equiv.symm (f x₁ x₂) = x₁ ⊗ₜ x₂ := hf.equiv_symm_apply _ _
  simp [IsTensorProduct.assocAux, this]

/-- This is the canonical isomorphism `(M₁ ⊗[R] M₂) ⊗[S] M₃ ≃ₗ[T] M₁ ⊗[R] (M₂ ⊗[S] M₃)`.
For the version where `R` and `S` are flipped, see `TensorProduct.AlgebraTensorModule.assoc`. -/
def IsTensorProduct.assoc {T : Type*} [CommSemiring T] [Algebra R T]
    [Module T M₁] [IsScalarTower R T M₁] [Module T M₁₂] [SMulCommClass S T M₁₂]
    [IsScalarTower R T M₁₂]
    (f : M₁ →ₗ[T] M₂ →ₗ[S] M₁₂) (hf : IsTensorProduct (f.restrictScalars₁₂ R R))
    (g : M₂ →ₗ[S] M₃ →ₗ[S] M₂₃) (hg : IsTensorProduct g) :
    M₁₂ ⊗[S] M₃ ≃ₗ[T] M₁ ⊗[R] M₂₃ where
  toAddEquiv := IsTensorProduct.assocAux (f.restrictScalars₁₂ R S) hf g hg
  map_smul' t x := by
    induction x with
    | zero => simp
    | add x y _ _ => simp_all
    | tmul x y =>
    obtain ⟨x, rfl⟩ := hf.equiv.surjective x
    induction x with
    | zero => simp
    | add x y _ _ => simp_all [add_tmul]
    | tmul x z =>
      have : t • (f x) z = f (t • x) z := by simp
      dsimp
      rw [smul_tmul', this, ← f.restrictScalars₁₂_apply_apply R S,
        ← f.restrictScalars₁₂_apply_apply R S, IsTensorProduct.assocAux_tmul,
        IsTensorProduct.assocAux_tmul, TensorProduct.smul_tmul']

variable {T : Type*} [CommSemiring T] [Algebra R T]
  [Module T M₁] [IsScalarTower R T M₁] [Module T M₁₂] [SMulCommClass S T M₁₂]
  [IsScalarTower R T M₁₂]
  (f : M₁ →ₗ[T] M₂ →ₗ[S] M₁₂) (hf : IsTensorProduct (f.restrictScalars₁₂ R R))
  (g : M₂ →ₗ[S] M₃ →ₗ[S] M₂₃) (hg : IsTensorProduct g)

@[simp]
lemma IsTensorProduct.assoc_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    IsTensorProduct.assoc f hf g hg (f x₁ x₂ ⊗ₜ x₃) = x₁ ⊗ₜ g x₂ x₃ :=
  IsTensorProduct.assocAux_tmul (f.restrictScalars₁₂ R S) hf g hg _ _ _

@[simp]
lemma IsTensorProduct.assoc_symm_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    (IsTensorProduct.assoc f hf g hg).symm (x₁ ⊗ₜ g x₂ x₃) = f x₁ x₂ ⊗ₜ x₃ :=
  IsTensorProduct.assocAux_symm_tmul (f.restrictScalars₁₂ R S) hf g hg _ _ _

/-- This is the canonical isomorphism `(M₁ ⊗[R] M₂) ⊗[S] M₃ ≃ₗ[T] M₁ ⊗[R] (M₂ ⊗[S] M₃)`.
For the version where `R` and `S` are flipped, see `TensorProduct.AlgebraTensorModule.assoc`. -/
def IsTensorProduct.assocOfMapSMul {T : Type*} [CommSemiring T] [Algebra R T]
    [Module T M₁] [IsScalarTower R T M₁] [Module T M₁₂] [SMulCommClass S T M₁₂]
    [IsScalarTower R T M₁₂]
    (f : M₁ →ₗ[R] M₂ →ₗ[R] M₁₂) (hf : IsTensorProduct f)
    (g : M₂ →ₗ[S] M₃ →ₗ[S] M₂₃) (hg : IsTensorProduct g)
    (h₁ : ∀ (t : T) (x : M₁) (y : M₂), f (t • x) y = t • f x y)
    (h₂ : ∀ (s : S) (x : M₁) (y : M₂), f x (s • y) = s • f x y) :
    M₁₂ ⊗[S] M₃ ≃ₗ[T] M₁ ⊗[R] M₂₃ :=
  IsTensorProduct.assoc (.mk₂' _ _ (f ·) (by simp) (by simp [h₁]) (by simp) (by simp [h₂])) hf g hg

variable
  (f : M₁ →ₗ[R] M₂ →ₗ[R] M₁₂) (hf : IsTensorProduct f)
  (g : M₂ →ₗ[S] M₃ →ₗ[S] M₂₃) (hg : IsTensorProduct g)
  (h₁ : ∀ (t : T) (x : M₁) (y : M₂), f (t • x) y = t • f x y)
  (h₂ : ∀ (s : S) (x : M₁) (y : M₂), f x (s • y) = s • f x y)

@[simp]
lemma IsTensorProduct.assocOfMapSMul_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    IsTensorProduct.assocOfMapSMul f hf g hg h₁ h₂ (f x₁ x₂ ⊗ₜ x₃) = x₁ ⊗ₜ g x₂ x₃ :=
  IsTensorProduct.assoc_tmul ..

@[simp]
lemma IsTensorProduct.assocOfMapSMul_symm_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    (IsTensorProduct.assocOfMapSMul f hf g hg h₁ h₂).symm (x₁ ⊗ₜ g x₂ x₃) = f x₁ x₂ ⊗ₜ x₃ :=
  IsTensorProduct.assoc_symm_tmul ..

end

namespace Algebra

/-!
### Auxiliary lemmas to be moved

The following lemma belongs in `Mathlib.RingTheory.Extension.Cotangent.Basic`.
-/

namespace Extension

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (P : Extension R S)

/-- The sequence `H¹(L_{S/R}) → P.Cotangent → P.CotangentSpace` is exact. -/
lemma exact_hCotangentι_cotangentComplex :
    Function.Exact h1Cotangentι P.cotangentComplex := by
  rw [LinearMap.exact_iff]
  symm
  apply Submodule.range_subtype

end Extension

/-!
### Part 1: Cotangent space base change

This section establishes the base change isomorphism for the cotangent space and conormal space
of a presentation.
-/

namespace Extension

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (P : Extension R S)
variable (T : Type*) [CommRing T] [Algebra R T]

end Extension

namespace Extension

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (P : Extension.{u, u, u} R S)
variable (T : Type u) [CommRing T] [Algebra R T]

noncomputable
def tensorCotangentSpace : T ⊗[R] P.CotangentSpace ≃ₗ[T] (P.baseChange (T := T)).CotangentSpace :=
  letI := P.algebraBaseChange T
  letI : Algebra S (T ⊗[R] S) := TensorProduct.rightAlgebra
  letI : Algebra P.Ring (T ⊗[R] S) := Algebra.compHom _ (algebraMap P.Ring S)
  haveI : IsScalarTower R P.Ring (T ⊗[R] S) :=
    .of_algebraMap_eq fun x ↦ by
      rw [TensorProduct.algebraMap_apply, RingHom.algebraMap_toAlgebra,
        Algebra.TensorProduct.tmul_one_eq_one_tmul, IsScalarTower.algebraMap_apply R P.Ring]
      rfl
  letI PT : Extension T (T ⊗[R] S) := P.baseChange
  haveI : IsPushout R T P.Ring PT.Ring := by
    convert TensorProduct.isPushout (R := R) (T := P.Ring) (S := T)
    exact Algebra.algebra_ext _ _ fun _ ↦ rfl
  haveI : IsScalarTower P.Ring PT.Ring (T ⊗[R] S) := .of_algebraMap_eq' rfl
  (IsTensorProduct.assocOfMapSMul (TensorProduct.mk R T S) (isTensorProduct _ _ _)
    (TensorProduct.mk _ _ _) (isTensorProduct _ _ _) (by simp [Algebra.smul_def])
    (by simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra])).symm ≪≫ₗ
  (AlgebraTensorModule.cancelBaseChange _ PT.Ring PT.Ring _ _).symm.restrictScalars T ≪≫ₗ
  (AlgebraTensorModule.congr (LinearEquiv.refl PT.Ring (T ⊗[R] S))
    (KaehlerDifferential.tensorKaehlerEquiv R T P.Ring PT.Ring)).restrictScalars T

attribute [local instance] algebraBaseChange in
@[simp]
lemma tensorCotangentSpace_tmul_tmul (t : T) (s : S) (x : Ω[P.Ring⁄R]) :
    P.tensorCotangentSpace T (t ⊗ₜ (s ⊗ₜ x)) = t ⊗ₜ s ⊗ₜ KaehlerDifferential.map _ _ _ _ x := by
  simp only [tensorCotangentSpace, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    ← mk_apply s x, IsTensorProduct.assocOfMapSMul_symm_tmul]
  simp only [mk_apply, AlgebraTensorModule.cancelBaseChange_symm_tmul,
    AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply]
  have this : x ∈ Submodule.span P.Ring (Set.range (KaehlerDifferential.D R P.Ring)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction this using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => simp [tmul_add, hx, hy]
  | mem y hy =>
    obtain ⟨y, rfl⟩ := hy
    simp
  | smul a x _ hx =>
    rw [tmul_smul, ← algebraMap_smul (P.baseChange (T := T)).Ring a, LinearEquiv.map_smul,
      tmul_smul, hx, LinearMap.map_smul, ← algebraMap_smul (P.baseChange (T := T)).Ring a,
      tmul_smul]

lemma CotangentSpace.map_tmul' {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {P : Extension R S} {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S']
    [Algebra R' S'] {P' : Extension R' S'} [Algebra R R'] [Algebra S S'] [Algebra R S']
    [IsScalarTower R R' S'] (f : P.Hom P') (x : S) (y : Ω[P.Ring⁄R]) :
    letI : Algebra P.Ring P'.Ring := f.toAlgHom.toAlgebra
    (CotangentSpace.map f) (x ⊗ₜ[P.Ring] y) =
      (algebraMap S S') x ⊗ₜ[P'.Ring] KaehlerDifferential.map _ _ _ _ y := by
  rw [CotangentSpace.map, LinearMap.liftBaseChange_tmul, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.restrictScalars_apply, mk_apply, smul_tmul', Algebra.smul_def, mul_one]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
lemma tensorCotangentSpace_tmul (t : T) (x : P.CotangentSpace) :
    P.tensorCotangentSpace T (t ⊗ₜ x) = t • CotangentSpace.map (P.toBaseChange T) x := by
  dsimp only [CotangentSpace] at x
  induction x with
  | zero => rw [tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero, smul_zero]
  | add x y hx hy => rw [tmul_add, LinearEquiv.map_add, LinearMap.map_add, smul_add, hx, hy]
  | tmul s y =>
  simp [tensorCotangentSpace_tmul_tmul,
    CotangentSpace.map_tmul', smul_tmul', Algebra.smul_def, RingHom.algebraMap_toAlgebra]

end Extension

end Algebra

/-!
### Auxiliary lemma to be moved

The following lemma belongs in `Mathlib.RingTheory.Ideal.Cotangent`.
-/

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (T : Type*) [CommRing T] [Algebra R T]
variable (I : Ideal S)

/-- A linear isomorphism between cotangent spaces induced by an equality of ideals. -/
def Cotangent.equivOfEq (I J : Ideal S) (hIJ : I = J) :
    I.Cotangent ≃ₗ[S] J.Cotangent where
  __ := Cotangent.lift (J.toCotangent ∘ₗ LinearEquiv.ofEq I J hIJ) <| fun x y ↦ by
    simp [toCotangent_eq_zero, ← hIJ, sq, mul_mem_mul]
  invFun := Cotangent.lift (I.toCotangent ∘ₗ LinearEquiv.ofEq J I hIJ.symm) <| fun x y ↦ by
    simp [toCotangent_eq_zero, hIJ, sq, mul_mem_mul]
  left_inv x := by
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, lift_toCotangent, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply]
    rfl
  right_inv x := by
    obtain ⟨x, rfl⟩ := J.toCotangent_surjective x
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, lift_toCotangent, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply]
    rfl

@[simp]
lemma Cotangent.equivOfEq_toCotangent (I J : Ideal S) (hIJ : I = J) (x : I) :
    Cotangent.equivOfEq I J hIJ (I.toCotangent x) = J.toCotangent (LinearEquiv.ofEq I J hIJ x) :=
  rfl

end Ideal

namespace Algebra

namespace Generators

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type*}
variable (P : Generators R S ι)
variable (T : Type u) [CommRing T] [Algebra R T]

/-- The canonical hom from the base change of `P.toExtension` to the extension
corresponding to `P.baseChange`. -/
noncomputable
def baseChangeFromBaseChange :
    (P.toExtension.baseChange (T := T)).Hom (P.baseChange (T := T)).toExtension where
  toRingHom := (MvPolynomial.algebraTensorAlgEquiv R T).toRingHom
  toRingHom_algebraMap x := by
    simp only [toExtension_Ring, Extension.baseChange,
      AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
      TensorProduct.algebraMap_apply, algebraMap_self, RingHom.id_apply, MvPolynomial.algebraMap_eq]
    change (MvPolynomial.algebraTensorAlgEquiv R T) (x ⊗ₜ[R] 1) = MvPolynomial.C x
    simp only [MvPolynomial.algebraTensorAlgEquiv_tmul, map_one, smul_def,
      MvPolynomial.algebraMap_eq, mul_one]
  algebraMap_toRingHom x := by
    simp only [Extension.baseChange, toExtension_Ring,
      AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
      algebraMap_apply, algebraMap_self, RingHomCompTriple.comp_apply] at x ⊢
    change (MvPolynomial.aeval (P.baseChange T).val) (MvPolynomial.algebraTensorAlgEquiv R T x) = _
    induction x with
    | zero => simp
    | add x y hx hy =>
      rw [map_add, RingHom.map_add, map_add, hx, hy]
    | tmul t x =>
      simp only [MvPolynomial.algebraTensorAlgEquiv_tmul, map_smul]
      rw [Algebra.smul_def]
      simp only [TensorProduct.algebraMap_apply, algebraMap_self, RingHom.id_apply, baseChange,
        ofSurjective, AlgHom.toRingHom_eq_coe, MvPolynomial.aeval_map_algebraMap]
      induction x using MvPolynomial.induction_on with
      | C r =>
        simp only [MvPolynomial.algHom_C, TensorProduct.algebraMap_apply,
          TensorProduct.tmul_mul_tmul, mul_one, RingHom.algebraMap_toAlgebra,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        rw [mul_comm, ← Algebra.smul_def, ← smul_tmul', ← tmul_smul, Algebra.smul_def, mul_one]
        simp
      | mul_X p i hp =>
        simp only [map_mul, MvPolynomial.aeval_X]
        rw [← mul_assoc, hp]
        simp [RingHom.algebraMap_toAlgebra]
      | add p q hp hq =>
        simp only [map_add, mul_add, hp, hq]
        rw [tmul_add, RingHom.map_add]

set_option maxHeartbeats 0 in
-- The proof requires substantial heartbeats due to the complex computation
-- with `MvPolynomial.algebraTensorAlgEquiv`.
noncomputable
def baseChangeToBaseChange :
    (P.baseChange (T := T)).toExtension.Hom (P.toExtension.baseChange (T := T)) where
  toRingHom := (MvPolynomial.algebraTensorAlgEquiv R T).symm.toRingHom
  algebraMap_toRingHom x := by
    have := (P.baseChangeFromBaseChange T).algebraMap_toRingHom <|
      (MvPolynomial.algebraTensorAlgEquiv R T).symm.toRingHom x
    simp only [toExtension_Ring,
      baseChangeFromBaseChange, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom, AlgEquiv.symm_toRingEquiv, RingHom.coe_coe, algebraMap_apply,
      algebraMap_self, RingHomCompTriple.comp_apply] at this
    convert this.symm
    change _ = (MvPolynomial.aeval (P.baseChange T).val)
      ((MvPolynomial.algebraTensorAlgEquiv R T) (((MvPolynomial.algebraTensorAlgEquiv R T)).symm x))
    simp only [algebraMap_self, toExtension_Ring,
      algebraMap_apply, MvPolynomial.map_aeval, RingHomCompTriple.comp_eq, baseChange_val,
      RingHom.id_apply, MvPolynomial.coe_eval₂Hom, AlgEquiv.apply_symm_apply]
    rfl
  toRingHom_algebraMap x := by
    simp only [toExtension_Ring, AlgEquiv.toRingEquiv_eq_coe,
      AlgEquiv.symm_toRingEquiv, RingEquiv.toRingHom_eq_coe, MvPolynomial.algebraMap_eq,
      algebraMap_self, RingHom.id_apply]
    change (MvPolynomial.algebraTensorAlgEquiv R T).symm _ = _
    rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    rfl

end Generators

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (P : Extension.{u, u, u} R S)
variable (T : Type u) [CommRing T] [Algebra R T]

namespace Extension

attribute [local instance] SMulCommClass.of_commMonoid

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- `Cotangent.val` as a linear isomorphism. -/
@[simps]
def valEquiv : P.Cotangent ≃ₗ[P.Ring] P.ker.Cotangent where
  toFun := Cotangent.val
  invFun := Cotangent.of
  map_add' x y := by simp
  map_smul' x y := by simp
  left_inv x := rfl
  right_inv x := rfl

/-- If `T` is flat over `R`, there is a `T`-linear isomorphism
`T ⊗[R] P.Cotangent ≃ₗ[T] (P.baseChange).Cotangent`. -/
noncomputable def tensorCotangent' [Module.Flat R T] :
    T ⊗[R] P.Cotangent ≃ₗ[T] (P.baseChange (T := T)).Cotangent :=
  let e₀ : T ⊗[R] P.Cotangent ≃ₗ[T] T ⊗[R] P.ker.Cotangent :=
    AlgebraTensorModule.congr (LinearEquiv.refl T T) (P.valEquiv.restrictScalars R)
  let e₁ := P.ker.tensorCotangentEquiv R T
  have : (Ideal.map (algebraMap P.Ring (T ⊗[R] P.Ring)) P.ker) = (P.baseChange (T := T)).ker := by
    simp only [Extension.ker, RingHom.algebraMap_toAlgebra]
    symm
    exact Algebra.TensorProduct.lTensor_ker (A := T) (IsScalarTower.toAlgHom R P.Ring S)
      P.algebraMap_surjective
  let e₂ : (Ideal.map (algebraMap P.Ring (T ⊗[R] P.Ring)) P.ker).Cotangent ≃ₗ[T]
      (P.baseChange (T := T)).ker.Cotangent :=
    (Ideal.Cotangent.equivOfEq _ _ this).restrictScalars T
  let e₃ : (P.baseChange (T := T)).ker.Cotangent ≃ₗ[T] (P.baseChange (T := T)).Cotangent :=
    (P.baseChange (T := T)).valEquiv.symm.restrictScalars T
  e₀ ≪≫ₗ e₁ ≪≫ₗ e₂ ≪≫ₗ e₃

@[simp]
lemma tensorCotangent'_tmul [Module.Flat R T] (t : T) (x : P.Cotangent) :
    P.tensorCotangent' T (t ⊗ₜ x) = t • Cotangent.map (P.toBaseChange T) x := by
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  simp only [tensorCotangent', LinearEquiv.trans_apply, AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, LinearEquiv.restrictScalars_apply, valEquiv_apply, Cotangent.val_mk,
    Ideal.tensorCotangentEquiv_tmul, map_smul, valEquiv_symm_apply, Cotangent.map_mk,
    Hom.toAlgHom_apply]
  rfl

/-!
### Part 2: H1Cotangent base change

This section establishes that `H1Cotangent` commutes with flat base change.
-/

/-- The canonical map `T ⊗[R] P.H1Cotangent →ₗ[T] (P.baseChange).H1Cotangent`. -/
noncomputable
def tensorToH1Cotangent :
    T ⊗[R] P.H1Cotangent →ₗ[T] (P.baseChange (T := T)).H1Cotangent :=
  let _ : Algebra S (T ⊗[R] S) := TensorProduct.includeRight.toRingHom.toAlgebra
  LinearMap.liftBaseChange T <|
    (Extension.H1Cotangent.map (P.toBaseChange T)).restrictScalars R

@[simp]
lemma tensorToH1Cotangent_tmul (t : T) (x : P.H1Cotangent) :
    (P.tensorToH1Cotangent T (t ⊗ₜ x)).val = t • Cotangent.map (P.toBaseChange T) x.val :=
  rfl

lemma tensorToH1Cotangent_bijective_of_flat [Module.Flat R T] :
    Function.Bijective (P.tensorToH1Cotangent T) := by
  apply LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective (M₁ := Unit)
      (N₁ := Unit) (M₂ := Unit) (N₂ := Unit)
      (M₄ := T ⊗[R] P.Cotangent) (N₄ := (P.baseChange (T := T)).Cotangent)
      (M₅ := T ⊗[R] P.CotangentSpace) (N₅ := (P.baseChange (T := T)).CotangentSpace)
    0
    0
    (((h1Cotangentι (P := P)).restrictScalars R).lTensor T)
    ((P.cotangentComplex.restrictScalars R).lTensor T)
    0
    0
    (h1Cotangentι.restrictScalars R)
    ((P.baseChange (T := T)).cotangentComplex.restrictScalars R)
    0
    0
    ((P.tensorToH1Cotangent T).restrictScalars R)
    ((P.tensorCotangent' T).restrictScalars R)
    ((P.tensorCotangentSpace T).restrictScalars R)
  · simp
  · simp
  · ext t x
    simp
  · ext t x
    simp [CotangentSpace.map_cotangentComplex]
  · tauto
  · simp only [LinearMap.exact_zero_iff_injective]
    apply Module.Flat.lTensor_preserves_injective_linearMap
    simp only [LinearMap.coe_restrictScalars]
    exact h1Cotangentι_injective
  · apply Module.Flat.lTensor_exact
    simp only [LinearMap.coe_restrictScalars]
    exact P.exact_hCotangentι_cotangentComplex
  · tauto
  · rw [LinearMap.exact_zero_iff_injective]
    simp only [LinearMap.coe_restrictScalars]
    exact h1Cotangentι_injective
  · simp only [LinearMap.coe_restrictScalars]
    apply exact_hCotangentι_cotangentComplex
  · tauto
  · simp
  · exact (P.tensorCotangent' T).bijective
  · exact (P.tensorCotangentSpace T).injective

/-- If `T` is flat over `R`, there is a `T`-linear isomorphism
`T ⊗[R] P.H1Cotangent ≃ₗ[T] (P.baseChange).H1Cotangent`. -/
noncomputable def tensorH1Cotangent' [Module.Flat R T] :
    T ⊗[R] P.H1Cotangent ≃ₗ[T] (P.baseChange (T := T)).H1Cotangent :=
  LinearEquiv.ofBijective (P.tensorToH1Cotangent T)
    (P.tensorToH1Cotangent_bijective_of_flat T)

end Extension

end

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Flat base change commutes with `H1Cotangent`. -/
noncomputable def tensorH1CotangentOfFlat (T : Type u) [CommRing T] [Algebra R T]
    [Module.Flat R T] :
    T ⊗[R] H1Cotangent R S ≃ₗ[T] H1Cotangent T (T ⊗[R] S) :=
  let P : Extension R S := (Generators.self R S).toExtension
  let e : T ⊗[R] P.H1Cotangent ≃ₗ[T] (P.baseChange (T := T)).H1Cotangent :=
    P.tensorH1Cotangent' T
  let PT : Extension T (T ⊗[R] S) := P.baseChange
  let PT' : Extension T (T ⊗[R] S) := ((Generators.self R S).baseChange T).toExtension
  let f₁ : PT.Hom PT' := (Generators.self R S).baseChangeFromBaseChange T
  let f₂ : PT'.Hom PT := (Generators.self R S).baseChangeToBaseChange T
  let e₂ : PT.H1Cotangent ≃ₗ[T] PT'.H1Cotangent :=
    (Extension.H1Cotangent.equiv f₁ f₂).restrictScalars T
  e ≪≫ₗ e₂ ≪≫ₗ ((Generators.self R S).baseChange (T := T)).equivH1Cotangent.restrictScalars T

end Algebra
