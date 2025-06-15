/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Extension.Presentation.Basic

/-!

# Naive cotangent complex associated to a presentation.

Given a presentation `0 → I → R[x₁,...,xₙ] → S → 0` (or equivalently a closed embedding `S ↪ Aⁿ`
defined by `I`), we may define the (naive) cotangent complex `I/I² → ⨁ᵢ S dxᵢ → Ω[S/R] → 0`.

## Main results
- `Algebra.Extension.Cotangent`: The conormal space `I/I²`. (Defined in `Generators/Basic`)
- `Algebra.Extension.CotangentSpace`: The cotangent space `⨁ᵢ S dxᵢ`.
- `Algebra.Generators.cotangentSpaceBasis`: The canonical basis on `⨁ᵢ S dxᵢ`.
- `Algebra.Extension.CotangentComplex`: The map `I/I² → ⨁ᵢ S dxᵢ`.
- `Algebra.Extension.toKaehler`: The projection `⨁ᵢ S dxᵢ → Ω[S/R]`.
- `Algebra.Extension.toKaehler_surjective`: The map `⨁ᵢ S dxᵢ → Ω[S/R]` is surjective.
- `Algebra.Extension.exact_cotangentComplex_toKaehler`: `I/I² → ⨁ᵢ S dxᵢ → Ω[S/R]` is exact.
- `Algebra.Extension.Hom.Sub`: If `f` and `g` are two maps between presentations, `f - g` induces
  a map `⨁ᵢ S dxᵢ → I/I²` that makes `f` and `g` homotopic.
- `Algebra.Extension.H1Cotangent`: The first homology of the (naive) cotangent complex
  of `S` over `R`, induced by a given presentation.
- `Algebra.H1Cotangent`: `H¹(L_{S/R})`,
  the first homology of the (naive) cotangent complex of `S` over `R`.

## Implementation detail
We actually develop these material for general extensions (i.e. surjection `P → S`) so that we can
apply them to infinitesimal smooth (or versal) extensions later.

-/

open KaehlerDifferential TensorProduct MvPolynomial

namespace Algebra

universe w u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

namespace Extension

variable (P : Extension.{w} R S)

/--
The cotangent space on `P = R[X]`.
This is isomorphic to `Sⁿ` with `n` being the number of variables of `P`.
-/
abbrev CotangentSpace : Type _ := S ⊗[P.Ring] Ω[P.Ring⁄R]

/-- The cotangent complex given by a presentation `R[X] → S` (i.e. a closed embedding `S ↪ Aⁿ`). -/
noncomputable
def cotangentComplex : P.Cotangent →ₗ[S] P.CotangentSpace :=
  letI f : P.Cotangent ≃ₗ[P.Ring] P.ker.Cotangent :=
    { __ := AddEquiv.refl _, map_smul' := Cotangent.val_smul' }
  (kerCotangentToTensor R P.Ring S ∘ₗ f).extendScalarsOfSurjective P.algebraMap_surjective

@[simp]
lemma cotangentComplex_mk (x) : P.cotangentComplex (.mk x) = 1 ⊗ₜ .D _ _ x :=
  kerCotangentToTensor_toCotangent _ _ _ _

universe w' u' v'

variable {R' : Type u'} {S' : Type v'} [CommRing R'] [CommRing S'] [Algebra R' S']
variable (P' : Extension.{w'} R' S')
variable [Algebra R R'] [Algebra S S'] [Algebra R S'] [IsScalarTower R R' S']

attribute [local instance] SMulCommClass.of_commMonoid

variable {P P'}

universe w'' u'' v''

variable {R'' : Type u''} {S'' : Type v''} [CommRing R''] [CommRing S''] [Algebra R'' S'']
variable {P'' : Extension.{w''} R'' S''}
variable [Algebra R R''] [Algebra S S''] [Algebra R S'']
  [IsScalarTower R R'' S'']
variable [Algebra R' R''] [Algebra S' S''] [Algebra R' S'']
  [IsScalarTower R' R'' S'']
variable [IsScalarTower R R' R''] [IsScalarTower S S' S'']

namespace CotangentSpace

/--
This is the map on the cotangent space associated to a map of presentation.
The matrix associated to this map is the Jacobian matrix. See `CotangentSpace.repr_map`.
-/
protected noncomputable
def map (f : Hom P P') : P.CotangentSpace →ₗ[S] P'.CotangentSpace := by
  letI := ((algebraMap S S').comp (algebraMap P.Ring S)).toAlgebra
  haveI : IsScalarTower P.Ring S S' := IsScalarTower.of_algebraMap_eq' rfl
  letI := f.toAlgHom.toAlgebra
  haveI : IsScalarTower P.Ring P'.Ring S' :=
    IsScalarTower.of_algebraMap_eq (fun x ↦ (f.algebraMap_toRingHom x).symm)
  apply LinearMap.liftBaseChange
  refine (TensorProduct.mk _ _ _ 1).restrictScalars _ ∘ₗ KaehlerDifferential.map R R' P.Ring P'.Ring

@[simp]
lemma map_tmul (f : Hom P P') (x y) :
    CotangentSpace.map f (x ⊗ₜ .D _ _ y) = (algebraMap _ _ x) ⊗ₜ .D _ _ (f.toAlgHom y) := by
  simp only [CotangentSpace.map, AlgHom.toRingHom_eq_coe, LinearMap.liftBaseChange_tmul,
    LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, map_D, mk_apply]
  rw [smul_tmul', ← Algebra.algebraMap_eq_smul_one]
  rfl

@[simp]
lemma map_id :
    CotangentSpace.map (.id P) = LinearMap.id := by ext; simp

lemma map_comp (f : Hom P P') (g : Hom P' P'') :
    CotangentSpace.map (g.comp f) =
      (CotangentSpace.map g).restrictScalars S ∘ₗ CotangentSpace.map f := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply]
  | add =>
    simp only [map_add, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, *]
  | tmul x y =>
    obtain ⟨y, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective _ _ y
    induction y with
    | zero => simp only [map_zero, tmul_zero, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
        Function.comp_apply]
    | add => simp only [map_add, tmul_add, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Function.comp_apply, *]
    | tmul => simp only [Derivation.tensorProductTo_tmul, tmul_smul, smul_tmul', map_tmul,
        Hom.toAlgHom_apply, Hom.comp_toRingHom, RingHom.coe_comp, Function.comp_apply,
        LinearMap.coe_comp, LinearMap.coe_restrictScalars,
        ← IsScalarTower.algebraMap_apply S S' S'']

lemma map_comp_apply (f : Hom P P') (g : Hom P' P'') (x) :
    CotangentSpace.map (g.comp f) x = .map g (.map f x) :=
  DFunLike.congr_fun (map_comp f g) x

lemma map_cotangentComplex (f : Hom P P') (x) :
    CotangentSpace.map f (P.cotangentComplex x) = P'.cotangentComplex (.map f x) := by
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  rw [cotangentComplex_mk, map_tmul, map_one, Cotangent.map_mk, cotangentComplex_mk]

lemma map_comp_cotangentComplex (f : Hom P P') :
    CotangentSpace.map f ∘ₗ P.cotangentComplex =
      P'.cotangentComplex.restrictScalars S ∘ₗ Cotangent.map f := by
  ext x; exact map_cotangentComplex f x

end CotangentSpace

lemma Hom.sub_aux (f g : Hom P P') (x y) :
    letI := ((algebraMap S S').comp (algebraMap P.Ring S)).toAlgebra
    f.toAlgHom (x * y) - g.toAlgHom (x * y) -
        (P'.σ ((algebraMap P.Ring S') x) * (f.toAlgHom y - g.toAlgHom y) +
          P'.σ ((algebraMap P.Ring S') y) * (f.toAlgHom x - g.toAlgHom x)) ∈
      P'.ker ^ 2 := by
  letI := ((algebraMap S S').comp (algebraMap P.Ring S)).toAlgebra
  have :
      (f.toAlgHom x - P'.σ (algebraMap P.Ring S' x)) * (f.toAlgHom y - g.toAlgHom y) +
      (g.toAlgHom y - P'.σ (algebraMap P.Ring S' y)) * (f.toAlgHom x - g.toAlgHom x)
        ∈ P'.ker ^ 2 := by
    rw [pow_two]
    refine Ideal.add_mem _ (Ideal.mul_mem_mul ?_ ?_) (Ideal.mul_mem_mul ?_ ?_) <;>
      simp only [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_comp,
        RingHom.coe_coe, Function.comp_apply, map_aeval, ← IsScalarTower.algebraMap_eq,
        coe_eval₂Hom, ← aeval_def, ker, RingHom.mem_ker, map_sub, algebraMap_toRingHom,
        algebraMap_σ, sub_self, toAlgHom_apply]
  convert this using 1
  simp only [map_mul]
  ring

/--
If `f` and `g` are two maps `P → P'` between presentations,
then the image of `f - g` is in the kernel of `P' → S`.
-/
@[simps! apply_coe]
noncomputable
def Hom.subToKer (f g : Hom P P') : P.Ring →ₗ[R] P'.ker := by
  refine ((f.toAlgHom.toLinearMap - g.toAlgHom.toLinearMap).codRestrict
    (P'.ker.restrictScalars R) ?_)
  intro x
  simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, ker, algebraMap_eq,
    Submodule.restrictScalars_mem, RingHom.mem_ker, map_sub, RingHom.coe_coe, algebraMap_toRingHom,
    map_aeval, coe_eval₂Hom, sub_self, toAlgHom_apply]

variable [IsScalarTower R S S'] in
/--
If `f` and `g` are two maps `P → P'` between presentations,
their difference induces a map `P.CotangentSpace →ₗ[S] P'.Cotangent` that makes two maps
between the cotangent complexes homotopic.
-/
noncomputable
def Hom.sub (f g : Hom P P') : P.CotangentSpace →ₗ[S] P'.Cotangent := by
  letI := ((algebraMap S S').comp (algebraMap P.Ring S)).toAlgebra
  haveI : IsScalarTower P.Ring S S' := IsScalarTower.of_algebraMap_eq' rfl
  letI := f.toAlgHom.toAlgebra
  haveI : IsScalarTower P.Ring P'.Ring S' :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (f.algebraMap_toRingHom x).symm
  haveI : IsScalarTower R P.Ring S' :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      show algebraMap R S' x = algebraMap S S' (algebraMap P.Ring S (algebraMap R P.Ring x)) by
        rw [← IsScalarTower.algebraMap_apply R P.Ring S, ← IsScalarTower.algebraMap_apply]
  refine (Derivation.liftKaehlerDifferential ?_).liftBaseChange S
  refine
  { __ := Cotangent.mk.restrictScalars R ∘ₗ f.subToKer g
    map_one_eq_zero' := ?_
    leibniz' := ?_ }
  · ext
    simp [Ideal.toCotangent_eq_zero]
  · intro x y
    ext
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      Cotangent.val_mk, Cotangent.val_add, Cotangent.val_smul''', ← map_smul, ← map_add,
      Ideal.toCotangent_eq, AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid,
      SetLike.val_smul, smul_eq_mul]
    exact Hom.sub_aux f g x y

variable [IsScalarTower R S S']

lemma Hom.sub_one_tmul (f g : Hom P P') (x) :
    f.sub g (1 ⊗ₜ .D _ _ x) = Cotangent.mk (f.subToKer g x) := by
  simp only [sub, LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D,
    Derivation.mk_coe, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    one_smul]

@[simp]
lemma Hom.sub_tmul (f g : Hom P P') (r x) :
    f.sub g (r ⊗ₜ .D _ _ x) = r • Cotangent.mk (f.subToKer g x) := by
  simp only [sub, LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D,
    Derivation.mk_coe, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply]

lemma CotangentSpace.map_sub_map (f g : Hom P P') :
    CotangentSpace.map f - CotangentSpace.map g =
      P'.cotangentComplex.restrictScalars S ∘ₗ (f.sub g) := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply]
  | add =>
    simp only [map_add, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, *]
  | tmul x y =>
    obtain ⟨y, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective _ _ y
    induction y with
    | zero => simp only [map_zero, tmul_zero, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
        Function.comp_apply]
    | add => simp only [map_add, tmul_add, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Function.comp_apply, *]
    | tmul =>
      simp only [Derivation.tensorProductTo_tmul, tmul_smul, smul_tmul', LinearMap.sub_apply,
        map_tmul, Hom.toAlgHom_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
        Function.comp_apply, Hom.sub_tmul, LinearMap.map_smul_of_tower, cotangentComplex_mk,
        Hom.subToKer_apply_coe, map_sub, ← algebraMap_eq_smul_one, tmul_sub, smul_sub]

lemma Cotangent.map_sub_map (f g : Hom P P') :
    map f - map g = (f.sub g) ∘ₗ P.cotangentComplex := by
  ext x
  obtain ⟨x, rfl⟩ := mk_surjective x
  simp only [LinearMap.sub_apply, map_mk, LinearMap.coe_comp, Function.comp_apply,
    cotangentComplex_mk, Hom.sub_tmul, one_smul, val_mk]
  apply (Ideal.cotangentEquivIdeal _).injective
  ext
  simp only [val_sub, val_mk, map_sub, AddSubgroupClass.coe_sub, Ideal.cotangentEquivIdeal_apply,
    Ideal.toCotangent_to_quotient_square, Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk,
    Hom.subToKer_apply_coe, Hom.toAlgHom_apply]

variable (P) in
/-- The projection map from the relative cotangent space to the module of differentials. -/
noncomputable
abbrev toKaehler : P.CotangentSpace →ₗ[S] Ω[S⁄R] := mapBaseChange _ _ _

lemma toKaehler_surjective : Function.Surjective P.toKaehler :=
  mapBaseChange_surjective _ _ _ P.algebraMap_surjective

lemma exact_cotangentComplex_toKaehler : Function.Exact P.cotangentComplex P.toKaehler :=
  exact_kerCotangentToTensor_mapBaseChange _ _ _ P.algebraMap_surjective

variable (P) in
/--
The first homology of the (naive) cotangent complex of `S` over `R`,
induced by a given presentation `0 → I → P → R → 0`,
defined as the kernel of `I/I² → S ⊗[P] Ω[P⁄R]`.
-/
protected noncomputable
def H1Cotangent : Type _ := LinearMap.ker P.cotangentComplex

variable {P : Extension R S}

noncomputable
instance : AddCommGroup P.H1Cotangent := by delta Extension.H1Cotangent; infer_instance

noncomputable
instance {R₀} [CommRing R₀] [Algebra R₀ S] [Module R₀ P.Cotangent]
    [IsScalarTower R₀ S P.Cotangent] : Module R₀ P.H1Cotangent := by
  delta Extension.H1Cotangent; infer_instance

@[simp] lemma H1Cotangent.val_add (x y : P.H1Cotangent) : (x + y).1 = x.1 + y.1 := rfl
@[simp] lemma H1Cotangent.val_zero : (0 : P.H1Cotangent).1 = 0 := rfl
@[simp] lemma H1Cotangent.val_smul {R₀} [CommRing R₀] [Algebra R₀ S] [Module R₀ P.Cotangent]
    [IsScalarTower R₀ S P.Cotangent] (r : R₀) (x : P.H1Cotangent) : (r • x).1 = r • x.1 := rfl

noncomputable
instance {R₁ R₂} [CommRing R₁] [CommRing R₂] [Algebra R₁ R₂]
    [Algebra R₁ S] [Algebra R₂ S]
    [Module R₁ P.Cotangent] [IsScalarTower R₁ S P.Cotangent]
    [Module R₂ P.Cotangent] [IsScalarTower R₂ S P.Cotangent]
    [IsScalarTower R₁ R₂ P.Cotangent] :
    IsScalarTower R₁ R₂ P.H1Cotangent := by
  delta Extension.H1Cotangent; infer_instance

lemma subsingleton_h1Cotangent (P : Extension R S) :
    Subsingleton P.H1Cotangent ↔ Function.Injective P.cotangentComplex := by
  delta Extension.H1Cotangent
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff, subsingleton_iff_forall_eq 0, Subtype.forall']
  simp only [Subtype.ext_iff, Submodule.coe_zero]

/-- The inclusion of `H¹(L_{S/R})` into the conormal space of a presentation. -/
@[simps!] noncomputable def h1Cotangentι : P.H1Cotangent →ₗ[S] P.Cotangent := Submodule.subtype _

lemma h1Cotangentι_injective : Function.Injective P.h1Cotangentι := Subtype.val_injective

@[ext] lemma h1Cotangentι_ext (x y : P.H1Cotangent) (e : x.1 = y.1) : x = y := Subtype.ext e

/--
The induced map on the first homology of the (naive) cotangent complex.
-/
@[simps!]
noncomputable
def H1Cotangent.map (f : Hom P P') : P.H1Cotangent →ₗ[S] P'.H1Cotangent := by
  refine (Cotangent.map f).restrict (p := LinearMap.ker P.cotangentComplex)
    (q := (LinearMap.ker P'.cotangentComplex).restrictScalars S) fun x hx ↦ ?_
  simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem] at hx ⊢
  apply_fun (CotangentSpace.map f) at hx
  rw [CotangentSpace.map_cotangentComplex] at hx
  rw [hx]
  exact LinearMap.map_zero _

lemma H1Cotangent.map_eq (f g : Hom P P') : map f = map g := by
  ext x
  simp only [map_apply_coe]
  rw [← sub_eq_zero, ← Cotangent.val_sub, ← LinearMap.sub_apply, Cotangent.map_sub_map]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.map_coe_ker, map_zero,
    Cotangent.val_zero]

@[simp] lemma H1Cotangent.map_id : map (.id P) = LinearMap.id := by ext; simp

omit [IsScalarTower R S S'] in
lemma H1Cotangent.map_comp
    (f : Hom P P') (g : Hom P' P'') :
    map (g.comp f) = (map g).restrictScalars S ∘ₗ map f := by
  ext; simp [Cotangent.map_comp]

/-- Maps `P₁ → P₂` and `P₂ → P₁` between extensions
induce an isomorphism between `H¹(L_P₁)` and `H¹(L_P₂)`. -/
@[simps! apply]
noncomputable
def H1Cotangent.equiv {P₁ P₂ : Extension R S} (f₁ : P₁.Hom P₂) (f₂ : P₂.Hom P₁) :
    P₁.H1Cotangent ≃ₗ[S] P₂.H1Cotangent where
  __ := map f₁
  invFun := map f₂
  left_inv x :=
    show (map f₂ ∘ₗ map f₁) x = LinearMap.id x by
    rw [← Extension.H1Cotangent.map_id, eq_comm, map_eq _ (f₂.comp f₁),
      Extension.H1Cotangent.map_comp]; rfl
  right_inv x :=
    show (map f₁ ∘ₗ map f₂) x = LinearMap.id x by
    rw [← Extension.H1Cotangent.map_id, eq_comm, map_eq _ (f₁.comp f₂),
      Extension.H1Cotangent.map_comp]; rfl

end Extension

namespace Generators

variable {ι : Type w} (P : Generators R S ι)

/-- The canonical basis on the `CotangentSpace`. -/
noncomputable
def cotangentSpaceBasis : Basis ι S P.toExtension.CotangentSpace :=
  (mvPolynomialBasis _ _).baseChange (R := P.Ring) _

@[simp]
lemma cotangentSpaceBasis_repr_tmul (r x i) :
    P.cotangentSpaceBasis.repr (r ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x : _) i =
      r * aeval P.val (pderiv i x) := by
  classical
  simp only [cotangentSpaceBasis, Basis.baseChange_repr_tmul, mvPolynomialBasis_repr_apply,
    Algebra.smul_def, mul_comm r, algebraMap_apply, toExtension]

lemma cotangentSpaceBasis_repr_one_tmul (x i) :
    P.cotangentSpaceBasis.repr (1 ⊗ₜ .D _ _ x) i = aeval P.val (pderiv i x) := by
  simp

lemma cotangentSpaceBasis_apply (i) :
    P.cotangentSpaceBasis i = ((1 : S) ⊗ₜ[P.Ring] D R P.Ring (.X i) :) := by
  simp [cotangentSpaceBasis, toExtension]

instance (P : Generators R S ι) : Module.Free S P.toExtension.CotangentSpace :=
  .of_basis P.cotangentSpaceBasis

universe w' u' v'

variable {R' : Type u'} {S' : Type v'} {ι' : Type w'} [CommRing R'] [CommRing S'] [Algebra R' S']
variable (P' : Generators R' S' ι')
variable [Algebra R R'] [Algebra S S'] [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']

attribute [local instance] SMulCommClass.of_commMonoid

variable {P P'}

universe w'' u'' v''

variable {R'' : Type u''} {S'' : Type v''} {ι'' : Type w''}
  [CommRing R''] [CommRing S''] [Algebra R'' S''] {P'' : Generators R'' S'' ι''}
variable [Algebra R R''] [Algebra S S''] [Algebra R S'']
  [IsScalarTower R R'' S''] [IsScalarTower R S S'']
variable [Algebra R' R''] [Algebra S' S''] [Algebra R' S'']
  [IsScalarTower R' R'' S''] [IsScalarTower R' S' S'']
variable [IsScalarTower S S' S'']

open Extension

@[simp]
lemma repr_CotangentSpaceMap (f : Hom P P') (i j) :
    P'.cotangentSpaceBasis.repr (CotangentSpace.map f.toExtensionHom (P.cotangentSpaceBasis i)) j =
      aeval P'.val (pderiv j (f.val i)) := by
  rw [cotangentSpaceBasis_apply]
  simp only [toExtension]
  rw [CotangentSpace.map_tmul, map_one]
  erw [cotangentSpaceBasis_repr_one_tmul, Hom.toAlgHom_X]

@[simp]
lemma toKaehler_cotangentSpaceBasis (i) :
    P.toExtension.toKaehler (P.cotangentSpaceBasis i) = D R S (P.val i) := by
  rw [cotangentSpaceBasis_apply]
  exact (KaehlerDifferential.mapBaseChange_tmul ..).trans (by simp)

end Generators

-- TODO: generalize to essentially of finite presentation algebras
open KaehlerDifferential in
attribute [local instance] Module.finitePresentation_of_projective in
instance [Algebra.FinitePresentation R S] : Module.FinitePresentation S (Ω[S⁄R]) := by
  let P := Algebra.Presentation.ofFinitePresentation R S
  have : Algebra.FiniteType R P.toExtension.Ring := .mvPolynomial _ _
  refine Module.finitePresentation_of_surjective _ P.toExtension.toKaehler_surjective ?_
  rw [LinearMap.exact_iff.mp P.toExtension.exact_cotangentComplex_toKaehler, ← Submodule.map_top]
  exact (Extension.Cotangent.finite P.fg_ker).1.map P.toExtension.cotangentComplex

variable {ι : Type w} {ι' : Type*} {P : Generators R S ι}

open Extension.H1Cotangent in
/-- `H¹(L_{S/R})` is independent of the presentation chosen. -/
@[simps! apply]
noncomputable
def Generators.H1Cotangent.equiv (P : Generators R S ι) (P' : Generators R S ι') :
    P.toExtension.H1Cotangent ≃ₗ[S] P'.toExtension.H1Cotangent :=
  Extension.H1Cotangent.equiv
    (Generators.defaultHom P P').toExtensionHom (Generators.defaultHom P' P).toExtensionHom

variable {S' : Type*} [CommRing S'] [Algebra R S']
variable {T : Type w} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable [Algebra S' T] [IsScalarTower R S' T]

variable (R S S' T)

/-- `H¹(L_{S/R})`, the first homology of the (naive) cotangent complex of `S` over `R`. -/
abbrev H1Cotangent : Type _ := (Generators.self R S).toExtension.H1Cotangent

/-- The induced map on the first homology of the (naive) cotangent complex of `S` over `R`. -/
noncomputable
def H1Cotangent.map : H1Cotangent R S' →ₗ[S'] H1Cotangent S T :=
  Extension.H1Cotangent.map (Generators.defaultHom _ _).toExtensionHom

/-- Isomorphic algebras induce isomorphic `H¹(L_{S/R})`. -/
noncomputable
def H1Cotangent.mapEquiv (e : S ≃ₐ[R] S') :
    H1Cotangent R S ≃ₗ[R] H1Cotangent R S' :=
  -- we are constructing data, so we do not use `algebraize`
  letI := e.toRingHom.toAlgebra
  letI := e.symm.toRingHom.toAlgebra
  have : IsScalarTower R S S' := .of_algebraMap_eq' e.toAlgHom.comp_algebraMap.symm
  have : IsScalarTower R S' S := .of_algebraMap_eq' e.symm.toAlgHom.comp_algebraMap.symm
  have : IsScalarTower S S' S := .of_algebraMap_eq fun _ ↦ (e.symm_apply_apply _).symm
  have : IsScalarTower S' S S' := .of_algebraMap_eq fun _ ↦ (e.apply_symm_apply _).symm
  { toFun := map R R S S'
    invFun := map R R S' S
    left_inv x := by
      show ((map R R S' S).restrictScalars S ∘ₗ map R R S S') x = x
      rw [map, map, ← Extension.H1Cotangent.map_comp, Extension.H1Cotangent.map_eq,
        Extension.H1Cotangent.map_id, LinearMap.id_apply]
    right_inv x := by
      show ((map R R S S').restrictScalars S' ∘ₗ map R R S' S) x = x
      rw [map, map, ← Extension.H1Cotangent.map_comp, Extension.H1Cotangent.map_eq,
        Extension.H1Cotangent.map_id, LinearMap.id_apply]
    map_add' := LinearMap.map_add (map R R S S')
    map_smul' := LinearMap.CompatibleSMul.map_smul (map R R S S') }

variable {R S S' T}

/-- `H¹(L_{S/R})` is independent of the presentation chosen. -/
noncomputable
abbrev Generators.equivH1Cotangent (P : Generators R S ι) :
    P.toExtension.H1Cotangent ≃ₗ[S] H1Cotangent R S :=
  Generators.H1Cotangent.equiv _ _

attribute [local instance] Module.finitePresentation_of_projective in
instance [FinitePresentation R S] [Module.Projective S (Ω[S⁄R])] :
    Module.Finite S (H1Cotangent R S) := by
  let P := Algebra.Presentation.ofFinitePresentation R S
  have : Algebra.FiniteType R P.toExtension.Ring := FiniteType.mvPolynomial R _
  suffices Module.Finite S P.toExtension.H1Cotangent from
    .of_surjective P.equivH1Cotangent.toLinearMap P.equivH1Cotangent.surjective
  rw [Module.finite_def, Submodule.fg_top, ← LinearMap.ker_rangeRestrict]
  have := Extension.Cotangent.finite P.fg_ker
  have : Module.FinitePresentation S (LinearMap.range P.toExtension.cotangentComplex) := by
    rw [← LinearMap.exact_iff.mp P.toExtension.exact_cotangentComplex_toKaehler]
    exact Module.finitePresentation_of_projective_of_exact
      _ _ (Subtype.val_injective) P.toExtension.toKaehler_surjective
      (LinearMap.exact_subtype_ker_map _)
  exact Module.FinitePresentation.fg_ker (N := LinearMap.range P.toExtension.cotangentComplex)
    _ P.toExtension.cotangentComplex.surjective_rangeRestrict

end Algebra
