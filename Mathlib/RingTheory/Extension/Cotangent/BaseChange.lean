import Mathlib.RingTheory.Ideal.CotangentBaseChange
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.Algebra.FiveLemma
import Mathlib.RingTheory.Kaehler.TensorProduct

suppress_compilation

universe u

open TensorProduct

namespace Algebra

namespace TensorProduct

variable {R S T A : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T]
  [CommRing A] [Algebra R A]

attribute [local instance] rightAlgebra

variable {M : Type*} [AddCommGroup M] [Module R M] [Algebra A T]
  [Module A M] [Algebra R A] [IsScalarTower R A M]
  [Algebra R T] [IsScalarTower R A T]
  [SMulCommClass R A T]

end TensorProduct

namespace Extension

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (P : Extension R S)
variable (T : Type*) [CommRing T] [Algebra R T]

lemma exact_hCotangentι_cotangentComplex :
    Function.Exact h1Cotangentι P.cotangentComplex := by
  rw [LinearMap.exact_iff]
  symm
  apply Submodule.range_subtype

attribute [local instance] Algebra.TensorProduct.rightAlgebra

noncomputable
def toBaseChange : P.Hom (P.baseChange (T := T)) where
  toRingHom := TensorProduct.includeRight.toRingHom
  toRingHom_algebraMap x := by simp [baseChange]
  algebraMap_toRingHom x := rfl

end Extension

namespace Extension

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (P : Extension.{u, u, u} R S)
variable (T : Type u) [CommRing T] [Algebra R T]

attribute [local instance] SMulCommClass.of_commMonoid

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance : Algebra P.Ring (T ⊗[R] S) :=
  (algebraMap _ _).comp (algebraMap P.Ring S) |>.toAlgebra

def commTensorProd : S ⊗[R] T ≃ₗ[P.Ring] T ⊗[R] S :=
  (_root_.TensorProduct.comm ..).toAddEquiv.toLinearEquiv <| by
    intro c x
    induction x with
    | zero => simp
    | add x y hx hy =>
        simp only [LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply] at hx hy
        simp [hx, hy]
    | tmul s t =>
        simp only [LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply, comm_tmul]
        change (_root_.TensorProduct.comm R S T) ((c • s) ⊗ₜ[R] t) = c • t ⊗ₜ[R] s
        simp [comm_tmul, Algebra.smul_def, RingHom.algebraMap_toAlgebra]

instance : IsScalarTower P.Ring S (T ⊗[R] S) :=
  IsScalarTower.of_algebraMap_eq' rfl

instance : IsScalarTower R P.Ring (T ⊗[R] S) :=
  IsScalarTower.of_algebraMap_eq <| fun x ↦ by
    simp only [TensorProduct.algebraMap_apply, RingHom.algebraMap_toAlgebra]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      TensorProduct.includeRight_apply]
    rw [← IsScalarTower.algebraMap_apply, ← mul_one (algebraMap R T x), ← smul_eq_mul, ← smul_tmul']
    conv_rhs => rw [← mul_one (algebraMap R S x), ← Algebra.smul_def]
    simp

def myAssoc : T ⊗[R] (S ⊗[P.Ring] Ω[P.Ring⁄R]) ≃ₗ[R] (T ⊗[R] S) ⊗[P.Ring] Ω[P.Ring⁄R] :=
  let e₁ : T ⊗[R] (S ⊗[P.Ring] Ω[P.Ring⁄R]) ≃ₗ[R] (S ⊗[P.Ring] Ω[P.Ring⁄R]) ⊗[R] T :=
    _root_.TensorProduct.comm ..
  let e₂ : (S ⊗[P.Ring] Ω[P.Ring⁄R]) ⊗[R] T ≃ₗ[R] (Ω[P.Ring⁄R] ⊗[P.Ring] S) ⊗[R] T :=
    AlgebraTensorModule.congr
      ((_root_.TensorProduct.comm ..).restrictScalars R) (LinearEquiv.refl R T)
  let e₃ : (Ω[P.Ring⁄R] ⊗[P.Ring] S) ⊗[R] T ≃ₗ[P.Ring] Ω[P.Ring⁄R] ⊗[P.Ring] (S ⊗[R] T) :=
    AlgebraTensorModule.assoc ..
  let e₄ : Ω[P.Ring⁄R] ⊗[P.Ring] (S ⊗[R] T) ≃ₗ[R] (S ⊗[R] T) ⊗[P.Ring] Ω[P.Ring⁄R] :=
    (_root_.TensorProduct.comm ..).restrictScalars R
  let eaux : S ⊗[R] T ≃ₗ[P.Ring] T ⊗[R] S := commTensorProd ..
  let e₅ : (S ⊗[R] T) ⊗[P.Ring] Ω[P.Ring⁄R] ≃ₗ[P.Ring] (T ⊗[R] S) ⊗[P.Ring] Ω[P.Ring⁄R] :=
    AlgebraTensorModule.congr eaux (LinearEquiv.refl _ _)
  e₁ ≪≫ₗ e₂ ≪≫ₗ e₃.restrictScalars R ≪≫ₗ e₄ ≪≫ₗ e₅.restrictScalars R

lemma myAssoc_tmul (t : T) (s : S) (x : Ω[P.Ring⁄R]) :
    P.myAssoc T (t ⊗ₜ (s ⊗ₜ x)) = (t ⊗ₜ s) ⊗ₜ x :=
  rfl

def myAssocE : T ⊗[R] (S ⊗[P.Ring] Ω[P.Ring⁄R]) ≃ₗ[T] (T ⊗[R] S) ⊗[P.Ring] Ω[P.Ring⁄R] :=
  (myAssoc ..).toAddEquiv.toLinearEquiv <| fun c x ↦ by
    induction x with
    | zero => rw [smul_zero, AddEquiv.map_zero, smul_zero]
    | add x y hx hy =>
    dsimp only [LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply] at hx hy ⊢
    rw [smul_add, LinearEquiv.map_add, LinearEquiv.map_add, hx, hy, smul_add]
    | tmul t x =>
    induction x with
    | zero => rw [tmul_zero, smul_zero, AddEquiv.map_zero, smul_zero]
    | add x y hx hy =>
    dsimp only [LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply] at hx hy ⊢
    rw [tmul_add, smul_add, LinearEquiv.map_add, hx, hy, LinearEquiv.map_add, smul_add]
    | tmul s x =>
    dsimp only [LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply]
    have : c • t ⊗ₜ[R] (s ⊗ₜ[P.Ring] x) = (c • t) ⊗ₜ[R] (s ⊗ₜ[P.Ring] x) := rfl
    rw [this, myAssoc_tmul, myAssoc_tmul]
    rfl

@[simp]
lemma myAssocE_tmul (t : T) (s : S) (x : Ω[P.Ring⁄R]) :
    P.myAssocE T (t ⊗ₜ (s ⊗ₜ x)) = (t ⊗ₜ s) ⊗ₜ x :=
  rfl

set_option maxHeartbeats 0 in
noncomputable
def tensorCotangentSpace' :
    T ⊗[R] P.CotangentSpace ≃ₗ[T] (P.baseChange (T := T)).CotangentSpace := by
  let PT : Extension T (T ⊗[R] S) := P.baseChange
  let _ : Algebra P.Ring PT.Ring :=
    inferInstanceAs <| Algebra P.Ring (T ⊗[R] P.Ring)
  have : IsScalarTower R P.Ring PT.Ring :=
    IsScalarTower.of_algebraMap_eq <| fun x ↦ by
      simp only [baseChange, RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        AlgHom.commutes, TensorProduct.algebraMap_apply, PT]
      rfl
  have : IsPushout R T P.Ring PT.Ring := by
    rw [IsPushout.comm]
    dsimp [PT, baseChange]
    sorry
    --convert _root_.TensorProduct.isPushout_rightAlgebra' R P.Ring T
    --ext x (y : T ⊗[R] P.Ring)
    --rw [Algebra.smul_def]
    --simp only [TensorProduct.algebraMap_apply]
    --rw [Algebra.compHom_smul_def]
    --rw [Algebra.smul_def]
    --simp
  have : IsScalarTower P.Ring PT.Ring (T ⊗[R] S) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower T PT.Ring (T ⊗[R] S) :=
    IsScalarTower.of_algebraMap_eq <| fun x ↦ by
      simp [PT, baseChange, RingHom.algebraMap_toAlgebra]
  let e : PT.Ring ⊗[P.Ring] Ω[P.Ring⁄R] ≃ₗ[PT.Ring] Ω[PT.Ring⁄T] :=
    KaehlerDifferential.tensorKaehlerEquiv _ _ _ _
  dsimp only [CotangentSpace]
  let e' :
      (T ⊗[R] S) ⊗[PT.Ring] (PT.Ring ⊗[P.Ring] Ω[P.Ring⁄R]) ≃ₗ[PT.Ring]
      (T ⊗[R] S) ⊗[PT.Ring] Ω[PT.Ring⁄T] :=
    AlgebraTensorModule.congr (LinearEquiv.refl _ _) e
  let e₂ : T ⊗[R] (S ⊗[P.Ring] Ω[P.Ring⁄R]) ≃ₗ[T] (T ⊗[R] S) ⊗[P.Ring] Ω[P.Ring⁄R] :=
    myAssocE ..
  let e₃ : (T ⊗[R] S) ⊗[P.Ring] Ω[P.Ring⁄R] ≃ₗ[T]
      (T ⊗[R] S) ⊗[PT.Ring] (PT.Ring ⊗[P.Ring] Ω[P.Ring⁄R]) :=
    (AlgebraTensorModule.cancelBaseChange _ PT.Ring PT.Ring _ _).symm.restrictScalars T
  let e'' : T ⊗[R] (S ⊗[P.Ring] Ω[P.Ring⁄R]) ≃ₗ[T]
      (T ⊗[R] S) ⊗[PT.Ring] (PT.Ring ⊗[P.Ring] Ω[P.Ring⁄R]) :=
    e₂ ≪≫ₗ e₃
  exact e'' ≪≫ₗ e'.restrictScalars T

noncomputable local instance : Algebra P.Ring (P.baseChange (T := T)).Ring :=
  TensorProduct.includeRight.toRingHom.toAlgebra

set_option maxHeartbeats 0 in
@[simp]
lemma tensorCotangentSpace'_tmul (t : T) (x : P.CotangentSpace) :
    P.tensorCotangentSpace' T (t ⊗ₜ x) = t • CotangentSpace.map (P.toBaseChange T) x := by
  dsimp only [CotangentSpace] at x
  induction (x : S ⊗[P.Ring] Ω[P.Ring⁄R]) with
  | zero => rw [tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero, smul_zero]
  | add x y hx hy => rw [tmul_add, LinearEquiv.map_add, LinearMap.map_add, smul_add, hx, hy]
  | tmul s y =>
  simp [tensorCotangentSpace']
  have : y ∈ Submodule.span P.Ring (Set.range (KaehlerDifferential.D R P.Ring)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction this using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨y, rfl⟩ := hy
    rw [CotangentSpace.map_tmul, KaehlerDifferential.tensorKaehlerEquiv_tmul_D]
    rw [one_smul, smul_tmul', Algebra.smul_def, RingHom.algebraMap_toAlgebra,
      RingHom.algebraMap_toAlgebra]
    simp
    rfl
  | smul a x _ hx =>
    have h1 : a • (1 : (P.baseChange (T := T)).Ring) ⊗ₜ[P.Ring] x =
        algebraMap P.Ring (P.baseChange (T := T)).Ring a • 1 ⊗ₜ x :=
      rfl
    have h2 : a • s ⊗ₜ[P.Ring] x = algebraMap P.Ring S a • s ⊗ₜ x := by
      rw [smul_tmul', Algebra.smul_def, ← smul_eq_mul, smul_tmul']
    rw [tmul_smul, tmul_smul, h1, LinearEquiv.map_smul, tmul_smul, hx, h2, LinearMap.map_smul,
      smul_comm]
    rfl
  | add x y _ _ hx hy =>
    rw [tmul_add, LinearEquiv.map_add, tmul_add, tmul_add, LinearMap.map_add, smul_add, hx, hy]
  | zero =>
    rw [tmul_zero, tmul_zero, LinearEquiv.map_zero, tmul_zero, LinearMap.map_zero, smul_zero]

end Extension

end Algebra

open TensorProduct

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (T : Type*) [CommRing T] [Algebra R T]
variable (I : Ideal S)

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

noncomputable
def baseChangeFromBaseChange :
    (P.toExtension.baseChange (T := T)).Hom (P.baseChange (T := T)).toExtension where
  toRingHom := (MvPolynomial.algebraTensorAlgEquiv R T).toRingHom
  toRingHom_algebraMap x := by
    simp only [toExtension_Ring, Extension.baseChange, toExtension_commRing,
      AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
      TensorProduct.algebraMap_apply, algebraMap_self, RingHom.id_apply, MvPolynomial.algebraMap_eq]
    show (MvPolynomial.algebraTensorAlgEquiv R T) (x ⊗ₜ[R] 1) = MvPolynomial.C x
    simp only [MvPolynomial.algebraTensorAlgEquiv_tmul, map_one, smul_def,
      MvPolynomial.algebraMap_eq, mul_one]
  algebraMap_toRingHom x := by
    simp only [Extension.baseChange, toExtension_Ring, toExtension_commRing, toExtension_algebra₂,
      AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
      algebraMap_apply, algebraMap_self, RingHomCompTriple.comp_apply] at x ⊢
    show (MvPolynomial.aeval (P.baseChange T).val) (MvPolynomial.algebraTensorAlgEquiv R T x) = _
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
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
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
noncomputable
def baseChangeToBaseChange :
    (P.baseChange (T := T)).toExtension.Hom (P.toExtension.baseChange (T := T)) where
  toRingHom := (MvPolynomial.algebraTensorAlgEquiv R T).symm.toRingHom
  algebraMap_toRingHom x := by
    have := (P.baseChangeFromBaseChange T).algebraMap_toRingHom <|
      (MvPolynomial.algebraTensorAlgEquiv R T).symm.toRingHom x
    simp only [toExtension_Ring, toExtension_commRing, toExtension_algebra₂,
      baseChangeFromBaseChange, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom, AlgEquiv.symm_toRingEquiv, RingHom.coe_coe, algebraMap_apply,
      algebraMap_self, RingHomCompTriple.comp_apply] at this
    convert this.symm
    show _ = (MvPolynomial.aeval (P.baseChange T).val)
      ((MvPolynomial.algebraTensorAlgEquiv R T) (((MvPolynomial.algebraTensorAlgEquiv R T)).symm x))
    simp only [algebraMap_self, toExtension_Ring, toExtension_commRing, toExtension_algebra₂,
      algebraMap_apply, MvPolynomial.map_aeval, RingHomCompTriple.comp_eq, baseChange_val,
      RingHom.id_apply, MvPolynomial.coe_eval₂Hom, AlgEquiv.apply_symm_apply]
    rfl
  toRingHom_algebraMap x := by
    simp only [toExtension_Ring, toExtension_commRing, AlgEquiv.toRingEquiv_eq_coe,
      AlgEquiv.symm_toRingEquiv, RingEquiv.toRingHom_eq_coe, MvPolynomial.algebraMap_eq,
      algebraMap_self, RingHom.id_apply]
    show (MvPolynomial.algebraTensorAlgEquiv R T).symm _ = _
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

noncomputable def tensorCotangent' [Module.Flat R T] :
    T ⊗[R] P.Cotangent ≃ₗ[T] (P.baseChange (T := T)).Cotangent :=
  let e₀ : T ⊗[R] P.Cotangent ≃ₗ[T] T ⊗[R] P.ker.Cotangent :=
    AlgebraTensorModule.congr (LinearEquiv.refl T T) (P.valEquiv.restrictScalars R)
  let e₁ := P.ker.tensorCotangentEquiv R T
  have : (Ideal.map (algebraMap P.Ring (T ⊗[R] P.Ring)) P.ker) = (P.baseChange (T := T)).ker := by
    simp [Extension.ker, RingHom.algebraMap_toAlgebra]
    symm
    exact Algebra.TensorProduct.lTensor_ker _ P.algebraMap_surjective
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

set_option maxHeartbeats 0 in
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
    ((P.tensorCotangentSpace' T).restrictScalars R)
  · simp
  · simp
  · ext t x
    simp
  · ext t x
    simp [CotangentSpace.map_cotangentComplex]
  · tauto
  · simp
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
  · exact (P.tensorCotangentSpace' T).injective

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
