/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Smooth.Kaehler
import Mathlib.RingTheory.Flat.Localization

/-!
# The differential module and etale algebras

## Main results
- `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`:
  The canonical isomorphism `T ⊗[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R]` for `T` a formally etale `S`-algebra.
- `Algebra.tensorH1CotangentOfIsLocalization`:
  The canonical isomorphism `T ⊗[S] H¹(L_{S⁄R}) ≃ₗ[T] H¹(L_{T⁄R})` for `T` a localization of `S`.
-/

universe u

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

open TensorProduct

/--
The canonical isomorphism `T ⊗[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R]` for `T` a formally etale `S`-algebra.
Also see `S ⊗[R] Ω[A⁄R] ≃ₗ[S] Ω[S ⊗[R] A⁄S]` at `KaehlerDifferential.tensorKaehlerEquiv`.
-/
@[simps! apply] noncomputable
def KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale [Algebra.FormallyEtale S T] :
    T ⊗[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R] := by
  refine LinearEquiv.ofBijective (mapBaseChange R S T)
    ⟨?_, fun x ↦ (KaehlerDifferential.exact_mapBaseChange_map R S T x).mp (Subsingleton.elim _ _)⟩
  rw [injective_iff_map_eq_zero]
  intros x hx
  obtain ⟨x, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T x).mp hx
  rw [Subsingleton.elim x 0, map_zero]

lemma KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap
    [Algebra.FormallyEtale S T] (s : S) :
    (tensorKaehlerEquivOfFormallyEtale R S T).symm (D R T (algebraMap S T s)) = 1 ⊗ₜ D R S s := by
  rw [LinearEquiv.symm_apply_eq, tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul,
    one_smul, map_D]

lemma KaehlerDifferential.isBaseChange_of_formallyEtale [Algebra.FormallyEtale S T] :
    IsBaseChange T (map R R S T) := by
  show Function.Bijective _
  convert (tensorKaehlerEquivOfFormallyEtale R S T).bijective using 1
  show _ = ((tensorKaehlerEquivOfFormallyEtale
    R S T).toLinearMap.restrictScalars S : T ⊗[S] Ω[S⁄R] → _)
  congr!
  ext
  simp

instance KaehlerDifferential.isLocalizedModule_map (M : Submonoid S) [IsLocalization M T] :
    IsLocalizedModule M (map R R S T) :=
  have := Algebra.FormallyEtale.of_isLocalization (Rₘ := T) M
  (isLocalizedModule_iff_isBaseChange M T _).mpr (isBaseChange_of_formallyEtale R S T)

namespace Algebra.Extension

open KaehlerDifferential

attribute [local instance] SMulCommClass.of_commMonoid

variable {R S T}

/-!
Suppose we have a morphism of extensions of `R`-algebras
```
0 → J → Q → T → 0
    ↑   ↑   ↑
0 → I → P → S → 0
```
-/
variable {P : Extension.{u} R S} {Q : Extension.{u} R T} (f : P.Hom Q)

/-- If `P → Q` is formally etale, then `T ⊗ₛ (S ⊗ₚ Ω[P/R]) ≃ T ⊗_Q Ω[Q/R]`. -/
noncomputable
def tensorCotangentSpace
    (H : letI := f.toRingHom.toAlgebra; FormallyEtale P.Ring Q.Ring) :
    T ⊗[S] P.CotangentSpace ≃ₗ[T] Q.CotangentSpace :=
  letI := f.toRingHom.toAlgebra
  haveI : IsScalarTower R P.Ring Q.Ring :=
    .of_algebraMap_eq fun r ↦ (f.toRingHom_algebraMap r).symm
  letI := ((algebraMap S T).comp (algebraMap P.Ring S)).toAlgebra
  haveI : IsScalarTower P.Ring S T := .of_algebraMap_eq' rfl
  haveI : IsScalarTower P.Ring Q.Ring T :=
    .of_algebraMap_eq fun r ↦ (f.algebraMap_toRingHom r).symm
  haveI : FormallyEtale P.Ring Q.Ring := ‹_›
  { __ := (CotangentSpace.map f).liftBaseChange T
    invFun := LinearMap.liftBaseChange T (by
      refine LinearMap.liftBaseChange _ ?_ ∘ₗ
        (tensorKaehlerEquivOfFormallyEtale R P.Ring Q.Ring).symm.toLinearMap
      exact (TensorProduct.mk _ _ _ 1).restrictScalars P.Ring ∘ₗ
        (TensorProduct.mk _ _ _ 1).restrictScalars P.Ring)
    left_inv x := by
      show (LinearMap.liftBaseChange _ _ ∘ₗ LinearMap.liftBaseChange _ _) x =
        LinearMap.id (R := T) x
      congr 1
      ext : 4
      refine Derivation.liftKaehlerDifferential_unique
        (R := R) (S := P.Ring) (M := T ⊗[S] P.CotangentSpace) _ _ ?_
      ext a
      have : (tensorKaehlerEquivOfFormallyEtale R P.Ring Q.Ring).symm
          ((D R Q.Ring) (f.toRingHom a)) = 1 ⊗ₜ D _ _ a :=
        tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap R P.Ring Q.Ring a
      simp [this]
    right_inv x := by
      show (LinearMap.liftBaseChange _ _ ∘ₗ LinearMap.liftBaseChange _ _) x =
        LinearMap.id (R := T) x
      congr 1
      ext a
      dsimp
      obtain ⟨x, hx⟩ := (tensorKaehlerEquivOfFormallyEtale R P.Ring _).surjective (D R Q.Ring a)
      simp only [one_smul, ← hx, LinearEquiv.symm_apply_apply]
      show (((CotangentSpace.map f).liftBaseChange T).restrictScalars Q.Ring ∘ₗ
        LinearMap.liftBaseChange _ _) x = ((TensorProduct.mk _ _ _ 1) ∘ₗ
          (tensorKaehlerEquivOfFormallyEtale R P.Ring Q.Ring).toLinearMap) x
      congr 1
      ext a
      simp; rfl }

/-- A map between extensions induce a map between kernels -/
def Hom.mapKer {R R' S S' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R' S'] [Algebra R R'] [Algebra S S']
    {P : Extension R S} {P' : Extension R' S'} (f : P.Hom P')
    [alg : Algebra P.Ring P'.Ring] (halg : alg = f.toRingHom.toAlgebra) :
    P.ker →ₗ[P.Ring] P'.ker :=
  (Algebra.linearMap P.Ring P'.Ring).restrict (q := P'.ker.restrictScalars P.Ring) fun x hx ↦ by
    subst halg
    show (algebraMap P'.Ring S' (f.toRingHom x)) = 0
    simp [show algebraMap P.Ring S x = 0 from hx]

set_option maxHeartbeats 220000 in
/-- If `J ≃ Q ⊗ₚ I` (e.g. when `T = Q ⊗ₚ S` and `P → Q` is flat), then `T ⊗ₛ I/I² ≃ J/J²`. -/
noncomputable
def tensorCotangent [alg : Algebra P.Ring Q.Ring] (halg : alg = f.toRingHom.toAlgebra)
    (H : Function.Bijective ((f.mapKer halg).liftBaseChange Q.Ring)) :
    T ⊗[S] P.Cotangent ≃ₗ[T] Q.Cotangent :=
  haveI : IsScalarTower R P.Ring Q.Ring := by
    subst halg
    letI := f.toRingHom.toAlgebra
    exact .of_algebraMap_eq fun r ↦ (f.toRingHom_algebraMap r).symm
  letI := ((algebraMap S T).comp (algebraMap P.Ring S)).toAlgebra
  haveI : IsScalarTower P.Ring S T := .of_algebraMap_eq' rfl
  haveI : IsScalarTower P.Ring Q.Ring T := by
    subst halg
    letI := f.toRingHom.toAlgebra
    exact .of_algebraMap_eq fun r ↦ (f.algebraMap_toRingHom r).symm
  letI e := LinearEquiv.ofBijective _ H
  letI f' : Q.ker →ₗ[Q.Ring] T ⊗[S] P.Cotangent :=
    (LinearMap.liftBaseChange _
      ((TensorProduct.mk _ _ _ 1).restrictScalars _ ∘ₗ Cotangent.mk)) ∘ₗ e.symm.toLinearMap
  { __ := (Cotangent.map f).liftBaseChange T
    invFun :=
      QuotientAddGroup.lift _ f' <| by
        intro x hx
        refine Submodule.smul_induction_on hx ?_ fun _ _ ↦ add_mem
        clear x hx
        rintro a ha b -
        obtain ⟨x, hx⟩ := e.surjective ⟨a, ha⟩
        obtain rfl : (e x).1 = a := congr_arg Subtype.val hx
        obtain ⟨y, rfl⟩ := e.surjective b
        simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_coe, map_smul,
          LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
          LinearEquiv.symm_apply_apply, f']
        clear hx ha
        induction x with
        | zero => simp only [LinearEquiv.map_zero, ZeroMemClass.coe_zero, zero_smul]
        | add x y _ _ =>
          simp only [LinearEquiv.map_add, Submodule.coe_add, add_smul, zero_add, *]
        | tmul a b =>
          induction y with
          | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero, smul_zero]
          | add x y hx hy => simp only [LinearMap.map_add, smul_add, hx, hy, zero_add]
          | tmul c d =>
            simp only [LinearMap.liftBaseChange_tmul, LinearMap.coe_comp, SetLike.val_smul,
              LinearMap.coe_restrictScalars, Function.comp_apply, mk_apply, smul_eq_mul, e,
              LinearMap.liftBaseChange_tmul, LinearEquiv.ofBijective_apply]
            have h₁ : (f.mapKer halg b).1 = algebraMap _ _ b.1 := rfl
            have h₂ : b.1 • Cotangent.mk d = 0 := by ext; simp [Cotangent.smul_eq_zero_of_mem _ b.2]
            rw [TensorProduct.smul_tmul', mul_smul, h₁,
              algebraMap_smul, ← TensorProduct.tmul_smul, h₂, tmul_zero, smul_zero]
    left_inv x := by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      induction x with
      | zero => simp only [map_zero]
      | add x y _ _ => simp only [map_add, *]
      | tmul a b =>
        obtain ⟨b, rfl⟩ := Cotangent.mk_surjective b
        obtain ⟨a, rfl⟩ := Q.algebraMap_surjective a
        simp only [LinearMap.liftBaseChange_tmul, Cotangent.map_mk, Hom.toAlgHom_apply,
          algebraMap_smul, ← map_smul]
        subst halg
        letI := f.toRingHom.toAlgebra
        show f' (e (a ⊗ₜ b)) = _
        simp [f', algebraMap_eq_smul_one, TensorProduct.smul_tmul']
    right_inv x := by
      obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
      obtain ⟨x, rfl⟩ := e.surjective x
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      show (Cotangent.map f).liftBaseChange T (f' (e x)) = _
      induction x with
      | zero => simp only [map_zero]
      | add x y _ _ => simp only [map_add, *]
      | tmul a b =>
        subst halg
        letI := f.toRingHom.toAlgebra
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars,
          LinearEquiv.symm_apply_apply, LinearMap.liftBaseChange_tmul, Function.comp_apply,
          mk_apply, LinearMap.map_smul_of_tower, Cotangent.map_mk, Hom.toAlgHom_apply, one_smul, f']
        simp only [LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, map_smul, e]
        rfl }

/-- If `J ≃ Q ⊗ₚ I`, `S → T` is flat, and `P → Q` is formaly etale, then `T ⊗ H¹(L_P) ≃ H¹(L_Q)`. -/
noncomputable
def tensorH1Cotangent [alg : Algebra P.Ring Q.Ring] (halg : alg = f.toRingHom.toAlgebra)
    [Module.Flat S T]
    (H₁ : letI := f.toRingHom.toAlgebra; FormallyEtale P.Ring Q.Ring)
    (H₂ : Function.Bijective ((f.mapKer halg).liftBaseChange Q.Ring)) :
    T ⊗[S] P.H1Cotangent ≃ₗ[T] Q.H1Cotangent := by
  refine .ofBijective ((H1Cotangent.map f).liftBaseChange T) ?_
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    apply Module.Flat.lTensor_preserves_injective_linearMap _ h1Cotangentι_injective
    apply (Extension.tensorCotangent f halg H₂).injective
    simp only [map_zero]
    rw [← h1Cotangentι.map_zero, ← hx]
    show ((Cotangent.map f).liftBaseChange T ∘ₗ h1Cotangentι.baseChange T) x =
      (h1Cotangentι ∘ₗ _) x
    congr 1
    ext x
    simp
  · intro x
    have : Function.Exact (h1Cotangentι.baseChange T) (P.cotangentComplex.baseChange T) :=
      Module.Flat.lTensor_exact T (LinearMap.exact_subtype_ker_map _)
    obtain ⟨a, ha⟩ := (this ((Extension.tensorCotangent f halg H₂).symm x.1)).mp (by
      apply (Extension.tensorCotangentSpace f H₁).injective
      rw [map_zero, ← x.2]
      have : (CotangentSpace.map f).liftBaseChange T ∘ₗ P.cotangentComplex.baseChange T =
          Q.cotangentComplex ∘ₗ (Cotangent.map f).liftBaseChange T := by
        ext x; obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x; dsimp
        simp only [CotangentSpace.map_tmul,
          map_one, Hom.toAlgHom_apply, one_smul, cotangentComplex_mk]
      exact (DFunLike.congr_fun this _).trans (DFunLike.congr_arg Q.cotangentComplex
        ((tensorCotangent f halg H₂).apply_symm_apply x.1)))
    refine ⟨a, Subtype.ext (.trans ?_ ((LinearEquiv.eq_symm_apply _).mp ha))⟩
    show (h1Cotangentι ∘ₗ (H1Cotangent.map f).liftBaseChange T) _ =
      ((Cotangent.map f).liftBaseChange T ∘ₗ h1Cotangentι.baseChange T) _
    congr 1
    ext; simp

variable (R T) in
/-- let `p` be a submonoid of an `R`-algebra `S`. Then `Sₚ ⊗ H¹(L_{S/R}) ≃ H¹(L_{Sₚ/R})`. -/
noncomputable
def _root_.Algebra.tensorH1CotangentOfIsLocalization (M : Submonoid S) [IsLocalization M T] :
    T ⊗[S] H1Cotangent R S ≃ₗ[T] H1Cotangent R T := by
  letI P : Extension R S := (Generators.self R S).toExtension
  letI M' := M.comap (algebraMap P.Ring S)
  letI fQ : Localization M' →ₐ[R] T := IsLocalization.liftAlgHom (M := M')
    (f := (IsScalarTower.toAlgHom R S T).comp (IsScalarTower.toAlgHom R P.Ring S)) (fun ⟨y, hy⟩ ↦
    by simpa using IsLocalization.map_units T ⟨algebraMap P.Ring S y, hy⟩)
  letI Q : Extension R T := .ofSurjective fQ (by
    intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    obtain ⟨x, rfl⟩ := P.algebraMap_surjective x
    obtain ⟨s, rfl⟩ := P.algebraMap_surjective s
    refine ⟨IsLocalization.mk' _ x ⟨s, show s ∈ M' from hs⟩, ?_⟩
    simp only [fQ, IsLocalization.coe_liftAlgHom, AlgHom.toRingHom_eq_coe]
    rw [IsLocalization.lift_mk'_spec]
    simp)
  letI f : P.Hom Q :=
  { toRingHom := algebraMap P.Ring (Localization M')
    toRingHom_algebraMap x := (IsScalarTower.algebraMap_apply R P.Ring (Localization M') _).symm
    algebraMap_toRingHom x := @IsLocalization.lift_eq .. }
  haveI : FormallySmooth R P.Ring := inferInstanceAs (FormallySmooth R (MvPolynomial _ _))
  haveI : FormallySmooth P.Ring (Localization M') := .of_isLocalization M'
  haveI : FormallySmooth R Q.Ring := .comp R P.Ring (Localization M')
  haveI : Module.Flat S T := IsLocalization.flat T M
  letI : Algebra P.Ring Q.Ring := inferInstanceAs (Algebra P.Ring (Localization M'))
  letI := ((algebraMap S T).comp (algebraMap P.Ring S)).toAlgebra
  letI := fQ.toRingHom.toAlgebra
  haveI : IsScalarTower P.Ring S T := .of_algebraMap_eq' rfl
  haveI : IsScalarTower P.Ring (Localization M') T :=
    .of_algebraMap_eq fun r ↦ (f.algebraMap_toRingHom r).symm
  haveI : IsLocalizedModule M' (IsScalarTower.toAlgHom P.Ring S T).toLinearMap := by
    rw [isLocalizedModule_iff_isLocalization]
    convert ‹IsLocalization M T› using 1
    exact Submonoid.map_comap_eq_of_surjective P.algebraMap_surjective _
  refine tensorH1Cotangent f ?_ ?_ ?_ ≪≫ₗ equivH1CotangentOfFormallySmooth _
  · exact Algebra.algebra_ext _ _ fun _ ↦ rfl
  · convert FormallyEtale.of_isLocalization (M := M') (Rₘ := Localization M')
    exact Algebra.algebra_ext _ _ fun _ ↦ rfl
  · let F : P.ker →ₗ[P.Ring] RingHom.ker fQ := f.mapKer (Algebra.algebra_ext _ _ fun _ ↦ rfl)
    refine (isLocalizedModule_iff_isBaseChange M' (Localization M') F).mp ?_
    have : (Algebra.linearMap P.Ring S).ker.localized' (Localization M') M'
        (Algebra.linearMap P.Ring (Localization M')) = RingHom.ker fQ := by
      rw [LinearMap.localized'_ker_eq_ker_localizedMap (Localization M') M'
        (Algebra.linearMap P.Ring (Localization M'))
        (f' := (IsScalarTower.toAlgHom P.Ring S T).toLinearMap)]
      ext x
      obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective M' x
      simp only [LinearMap.mem_ker, LinearMap.extendScalarsOfIsLocalization_apply', RingHom.mem_ker,
        IsLocalization.coe_liftAlgHom, AlgHom.toRingHom_eq_coe, IsLocalization.lift_mk'_spec,
        RingHom.coe_coe, AlgHom.coe_comp, IsScalarTower.coe_toAlgHom', Function.comp_apply,
        mul_zero, fQ]
      have : IsLocalization.mk' (Localization M') x ⟨s, hs⟩ =
          IsLocalizedModule.mk' (Algebra.linearMap P.Ring (Localization M')) x ⟨s, hs⟩ := by
        rw [IsLocalization.mk'_eq_iff_eq_mul, mul_comm, ← Algebra.smul_def, ← Submonoid.smul_def,
          IsLocalizedModule.mk'_cancel']
        rfl
      simp [this, ← IsScalarTower.algebraMap_apply]
    have : F = ((LinearEquiv.ofEq _ _ this).restrictScalars P.Ring).toLinearMap ∘ₗ
      P.ker.toLocalized' (Localization M') M' (Algebra.linearMap P.Ring (Localization M')) := by
      ext; rfl
    rw [this]
    exact IsLocalizedModule.of_linearEquiv _ _ _

variable (R T) in
lemma _root_.Algebra.tensorH1CotangentOfIsLocalization_toLinearMap
    (M : Submonoid S) [IsLocalization M T] :
    (tensorH1CotangentOfIsLocalization R T M).toLinearMap =
      (Algebra.H1Cotangent.map R R S T).liftBaseChange T := by
  ext x : 3
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, LinearMap.liftBaseChange_tmul, one_smul]
  simp only [tensorH1CotangentOfIsLocalization, Generators.toExtension_Ring,
    Generators.toExtension_commRing, Generators.self_vars, Generators.toExtension_algebra₂,
    Generators.self_algebra, AlgHom.toRingHom_eq_coe, tensorH1Cotangent, LinearEquiv.trans_apply,
    LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul,
    equivH1CotangentOfFormallySmooth]
  letI P : Extension R S := (Generators.self R S).toExtension
  letI M' := M.comap (algebraMap P.Ring S)
  letI fQ : Localization M' →ₐ[R] T := IsLocalization.liftAlgHom (M := M')
    (f := (IsScalarTower.toAlgHom R S T).comp (IsScalarTower.toAlgHom R P.Ring S)) (fun ⟨y, hy⟩ ↦
    by simpa using IsLocalization.map_units T ⟨algebraMap P.Ring S y, hy⟩)
  letI Q : Extension R T := .ofSurjective fQ (by
    intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    obtain ⟨x, rfl⟩ := P.algebraMap_surjective x
    obtain ⟨s, rfl⟩ := P.algebraMap_surjective s
    refine ⟨IsLocalization.mk' _ x ⟨s, show s ∈ M' from hs⟩, ?_⟩
    simp only [fQ, IsLocalization.coe_liftAlgHom, AlgHom.toRingHom_eq_coe]
    rw [IsLocalization.lift_mk'_spec]
    simp)
  letI f : (Generators.self R T).toExtension.Hom Q :=
  { toRingHom := (MvPolynomial.aeval Q.σ).toRingHom
    toRingHom_algebraMap := (MvPolynomial.aeval Q.σ).commutes
    algebraMap_toRingHom := by
      have : (IsScalarTower.toAlgHom R Q.Ring T).comp (MvPolynomial.aeval Q.σ) =
          IsScalarTower.toAlgHom _ (Generators.self R T).toExtension.Ring _ := by
        ext i
        show _ = algebraMap (Generators.self R T).Ring _ (.X i)
        simp
      exact DFunLike.congr_fun this }
  rw [← H1Cotangent.equivOfFormallySmooth_symm, LinearEquiv.symm_apply_eq,
    @H1Cotangent.equivOfFormallySmooth_apply (f := f),
    Algebra.H1Cotangent.map, ← (H1Cotangent.map f).coe_restrictScalars S,
    ← LinearMap.comp_apply, ← H1Cotangent.map_comp, H1Cotangent.map_eq]

variable (R T) in
instance _root_.Algebra.H1Cotangent.isLocalizedModule
    (M : Submonoid S) [IsLocalization M T] :
    IsLocalizedModule M (Algebra.H1Cotangent.map R R S T) := by
  rw [isLocalizedModule_iff_isBaseChange M T]
  show Function.Bijective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T)
  rw [← tensorH1CotangentOfIsLocalization_toLinearMap R T M]
  exact (tensorH1CotangentOfIsLocalization R T M).bijective

end Algebra.Extension
