/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Generators

/-!

# Naive cotangent complex associated to a presentation.

Given a presentation `0 → I → R[x₁,...,xₙ] → S → 0` (or equivalently a closed embedding `S ↪ Aⁿ`
defined by `I`), we may define the (naive) cotangent complex `I/I² → ⨁ᵢ S dxᵢ → Ω[S/R] → 0`.

## Main results
- `Algebra.Generators.Cotangent`: The conormal space `I/I²`. (Defined in `Generators/Basic`)
- `Algebra.Generators.CotangentSpace`: The cotangent space `⨁ᵢ S dxᵢ`.
- `Algebra.Generators.CotangentComplex`: The map `I/I² → ⨁ᵢ S dxᵢ`.
- `Algebra.Generators.toKaehler`: The projection `⨁ᵢ S dxᵢ → Ω[S/R]`.
- `Algebra.Generators.toKaehler_surjective`: The map `⨁ᵢ S dxᵢ → Ω[S/R]` is surjective.
- `Algebra.Generators.exact_cotangentComplex_toKaehler`: `I/I² → ⨁ᵢ S dxᵢ → Ω[S/R]` is exact.
- `Algebra.Generators.Hom.Sub`: If `f` and `g` are two maps between presentations, `f - g` induces
  a map `⨁ᵢ S dxᵢ → I/I²` that makes `f` and `g` homotopic.
- `Algebra.Generators.H1Cotangent`: The first homology of the (naive) cotangent complex
  of `S` over `R`, induced by a given presentation.
- `Algebra.H1Cotangent`: `H¹(L_{S/R})`,
  the first homology of the (naive) cotangent complex of `S` over `R`.
-/

open KaehlerDifferential TensorProduct MvPolynomial

namespace Algebra

universe w u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

namespace Generators

variable (P : Generators.{w} R S)

/--
The cotangent space on `P = R[X]`.
This is isomorphic to `Sⁿ` with `n` being the number of variables of `P`.
-/
abbrev CotangentSpace : Type _ := S ⊗[P.Ring] Ω[P.Ring⁄R]

/-- The canonical basis on the `CotangentSpace`. -/
noncomputable
def cotangentSpaceBasis : Basis P.vars S P.CotangentSpace :=
  (mvPolynomialBasis _ _).baseChange _

@[simp]
lemma cotangentSpaceBasis_repr_tmul (r x i) :
    P.cotangentSpaceBasis.repr (r ⊗ₜ .D _ _ x) i = r * aeval P.val (pderiv i x) := by
  classical
  simp only [cotangentSpaceBasis, Basis.baseChange_repr_tmul, mvPolynomialBasis_repr_apply,
    Algebra.smul_def, mul_comm r, algebraMap_apply]

lemma cotangentSpaceBasis_repr_one_tmul (x i) :
    P.cotangentSpaceBasis.repr (1 ⊗ₜ .D _ _ x) i = aeval P.val (pderiv i x) := by
  rw [cotangentSpaceBasis_repr_tmul, one_mul]

lemma cotangentSpaceBasis_apply i :
    P.cotangentSpaceBasis i = 1 ⊗ₜ .D _ _ (.X i) := by
  simp [cotangentSpaceBasis]

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
variable (P' : Generators.{w'} R' S')
variable [Algebra R R'] [Algebra S S'] [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']

attribute [local instance] SMulCommClass.of_commMonoid

variable {P P'}

universe w'' u'' v''

variable {R'' : Type u''} {S'' : Type v''} [CommRing R''] [CommRing S''] [Algebra R'' S'']
variable {P'' : Generators.{w''} R'' S''}
variable [Algebra R R''] [Algebra S S''] [Algebra R S'']
  [IsScalarTower R R'' S''] [IsScalarTower R S S'']
variable [Algebra R' R''] [Algebra S' S''] [Algebra R' S'']
  [IsScalarTower R' R'' S''] [IsScalarTower R' S' S'']
variable [IsScalarTower S S' S'']

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
    IsScalarTower.of_algebraMap_eq (fun x ↦ (f.algebraMap_toAlgHom x).symm)
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
lemma repr_map (f : Hom P P') (i j) :
    P'.cotangentSpaceBasis.repr (CotangentSpace.map f (P.cotangentSpaceBasis i)) j =
      aeval P'.val (pderiv j (f.val i)) := by
  simp only [cotangentSpaceBasis_apply, map_tmul, map_one, Hom.toAlgHom_X,
    cotangentSpaceBasis_repr_one_tmul]

@[simp]
lemma map_id :
    CotangentSpace.map (.id P) = LinearMap.id := by
  apply P.cotangentSpaceBasis.ext
  intro i
  simp only [cotangentSpaceBasis_apply, map_tmul, map_one, Hom.toAlgHom_X, Hom.id_val,
    LinearMap.id_coe, id_eq]

lemma map_comp (f : Hom P P') (g : Hom P' P'') :
    CotangentSpace.map (g.comp f) =
      (CotangentSpace.map g).restrictScalars S ∘ₗ CotangentSpace.map f := by
  apply P.cotangentSpaceBasis.ext
  intro i
  simp only [cotangentSpaceBasis_apply, map_tmul, map_one, Hom.toAlgHom_X, Hom.comp_val,
    LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply]
  rfl

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
        coe_eval₂Hom, ← aeval_def, ker, RingHom.mem_ker, map_sub, algebraMap_toAlgHom, aeval_val_σ,
        sub_self]
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
    Submodule.restrictScalars_mem, RingHom.mem_ker, map_sub, RingHom.coe_coe, algebraMap_toAlgHom,
    map_aeval, coe_eval₂Hom, sub_self]

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
    IsScalarTower.of_algebraMap_eq fun x ↦ (f.algebraMap_toAlgHom x).symm
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
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      Cotangent.val_mk, Cotangent.val_zero, Ideal.toCotangent_eq_zero]
    erw [LinearMap.codRestrict_apply]
    simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, map_one, sub_self, Submodule.zero_mem]
  · intro x y
    ext
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      Cotangent.val_mk, Cotangent.val_add, Cotangent.val_smul''', ← map_smul, ← map_add,
      Ideal.toCotangent_eq, AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid,
      SetLike.val_smul, smul_eq_mul]
    exact Hom.sub_aux f g x y

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
  apply P.cotangentSpaceBasis.ext
  intro i
  simp only [cotangentSpaceBasis_apply, LinearMap.sub_apply, map_tmul, map_one,
    Hom.toAlgHom_X, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    Hom.sub_one_tmul, cotangentComplex_mk, Hom.subToKer_apply_coe, map_sub, tmul_sub]

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
    Hom.subToKer_apply_coe]

variable (P) in
/-- The projection map from the relative cotangent space to the module of differentials. -/
noncomputable
abbrev toKaehler : P.CotangentSpace →ₗ[S] Ω[S⁄R] := mapBaseChange _ _ _

@[simp]
lemma toKaehler_cotangentSpaceBasis (i) :
    P.toKaehler (P.cotangentSpaceBasis i) = D R S (P.val i) := by
  simp [cotangentSpaceBasis_apply]

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

variable {P : Generators R S}

noncomputable
instance : AddCommGroup P.H1Cotangent := by delta Generators.H1Cotangent; infer_instance

noncomputable
instance {R₀} [CommRing R₀] [Algebra R₀ S] [Module R₀ P.Cotangent]
    [IsScalarTower R₀ S P.Cotangent] : Module R₀ P.H1Cotangent := by
  delta Generators.H1Cotangent; infer_instance

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
  delta Generators.H1Cotangent; infer_instance

lemma subsingleton_h1Cotangent (P : Generators R S) :
    Subsingleton P.H1Cotangent ↔ Function.Injective P.cotangentComplex := by
  delta Generators.H1Cotangent
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff, subsingleton_iff_forall_eq 0, Subtype.forall']
  simp only [Subtype.ext_iff, Submodule.coe_zero]

/-- The inclusion of `H¹(L_{S/R})` into the conormal space of a presentation. -/
@[simps!] def h1Cotangentι : P.H1Cotangent →ₗ[S] P.Cotangent := Submodule.subtype _

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

lemma H1Cotangent.map_comp [IsScalarTower R R' R''] (f : Hom P P') (g : Hom P' P'') :
    map (g.comp f) = (map g).restrictScalars S ∘ₗ map f := by ext; simp [Cotangent.map_comp]

/-- `H¹(L_{S/R})` is independent of the presentation chosen. -/
@[simps! apply]
noncomputable
def H1Cotangent.equiv (P : Generators.{w} R S) (P' : Generators.{w'} R S) :
    P.H1Cotangent ≃ₗ[S] P'.H1Cotangent where
  __ := map default
  invFun := map default
  left_inv x :=
    show ((map (defaultHom P' P)) ∘ₗ (map (defaultHom P P'))) x = LinearMap.id x by
    rw [← map_id, eq_comm, map_eq _ ((defaultHom P' P).comp (defaultHom P P')), map_comp]; rfl
  right_inv x :=
    show ((map (defaultHom P P')) ∘ₗ (map (defaultHom P' P))) x = LinearMap.id x by
    rw [← map_id, eq_comm, map_eq _ ((defaultHom P P').comp (defaultHom P' P)), map_comp]; rfl

end Generators

variable {S' : Type*} [CommRing S'] [Algebra R S']
variable {T : Type w} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable [Algebra S' T] [IsScalarTower R S' T]

variable (R S S' T)

/-- `H¹(L_{S/R})`, the first homology of the (naive) cotangent complex of `S` over `R`. -/
abbrev H1Cotangent : Type _ := (Generators.self R S).H1Cotangent

/-- The induced map on the first homology of the (naive) cotangent complex of `S` over `R`. -/
noncomputable
def H1Cotangent.map : H1Cotangent R S' →ₗ[S'] H1Cotangent S T :=
  Generators.H1Cotangent.map (Generators.defaultHom _ _)

variable {R S S' T}

/-- `H¹(L_{S/R})` is independent of the presentation chosen. -/
noncomputable
abbrev Generators.equivH1Cotangent (P : Generators.{w} R S) :
    P.H1Cotangent ≃ₗ[S] H1Cotangent R S :=
  Generators.H1Cotangent.equiv _ _

end Algebra
