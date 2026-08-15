/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.NumberTheory.CFT.ClassFormation.Basic
public import Mathlib.NumberTheory.CFT.ClassFormation.Sheaves
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.RingHom.Etale

/-!
# Statement of the existence of the class formation for a local field

-/

universe u

@[expose] public section

open CategoryTheory Opposite PreGaloisCategory GaloisCategory

variable (R K : Type u) [CommRing R] [Field K]

/-- The category of finite étale algebras over a commutative ring `R`. -/
abbrev EtaleAlgCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun (X : Under (CommRingCat.of R)) ↦
      RingHom.Etale X.hom.hom ∧ RingHom.Finite X.hom.hom)

/-- Constructor for objects of `EtaleAlgCat`. -/
abbrev EtaleAlgCat.of (S : Type u) [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.Etale R S] :
    EtaleAlgCat R where
  obj := Under.mk (Y := .of S) (CommRingCat.ofHom (algebraMap R S))
  property :=
    ⟨by simpa [RingHom.etale_algebraMap], by simpa [RingHom.finite_algebraMap]⟩

/-- Constructor for morphisms in `EtaleAlgCat`. -/
abbrev EtaleAlgCat.ofHom (S₁ S₂ : Type u)
    [CommRing S₁] [Algebra R S₁] [Module.Finite R S₁] [Algebra.Etale R S₁]
    [CommRing S₂] [Algebra R S₂] [Module.Finite R S₂] [Algebra.Etale R S₂]
    [Algebra S₁ S₂] [IsScalarTower R S₁ S₂] :
    of R S₁ ⟶ of R S₂ :=
  ObjectProperty.homMk (Under.homMk (CommRingCat.ofHom (algebraMap S₁ S₂)) (by
    ext x
    exact (IsScalarTower.algebraMap_apply R S₁ S₂ x).symm))

namespace EtaleAlgCat

variable {R} in
/-- Induction principle for objects of `EtaleAlgCat`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def rec {motive : EtaleAlgCat R → Sort*}
    (of : ∀ (S : Type u) [CommRing S] [Algebra R S]
        [Module.Finite R S] [Algebra.Etale R S],
        motive (EtaleAlgCat.of R S))
    (Z : EtaleAlgCat R) : motive Z :=
  let : Algebra R Z.obj.right := Z.obj.hom.hom.toAlgebra
  let : Algebra.Etale R Z.obj.right := by
    simpa [RingHom.etale_algebraMap] using! Z.property.1
  let : Module.Finite R Z.obj.right := by
    simpa [RingHom.finite_algebraMap] using! Z.property.2
  of Z.obj.right

variable {R} in
/-- Induction principle for morphisms in `EtaleAlgCat`. -/
def homRec {S₁ S₂ : Type u} [CommRing S₁] [CommRing S₂]
    [Algebra R S₁] [Algebra R S₂]
    [Module.Finite R S₁] [Algebra.Etale R S₁]
    [Module.Finite R S₂] [Algebra.Etale R S₂]
    (motive : (of R S₁ ⟶ of R S₂) → Sort*)
    (ofHom : ∀ [Algebra S₁ S₂] [IsScalarTower R S₁ S₂], motive (ofHom R S₁ S₂))
    (f : of R S₁ ⟶ of R S₂) : motive f := by
  let : Algebra S₁ S₂ := f.hom.right.hom.toAlgebra
  have : IsScalarTower R S₁ S₂ := ⟨fun x y z ↦ by
    simp only [Algebra.smul_def, map_mul, ← mul_assoc]
    congr 2
    exact ConcreteCategory.congr_hom f.hom.w x⟩
  exact ofHom

instance : GaloisCategory (EtaleAlgCat K)ᵒᵖ := by
  -- this has probably been proven by Christian Merten
  -- with a greater generality
  sorry

lemma isConnected_iff (S : Type u) [CommRing S] [Algebra K S]
    [Module.Finite K S] [Algebra.Etale K S] :
    PreGaloisCategory.IsConnected (op (of K S)) ↔ IsField S := sorry

instance (S : Type u) [Field S] [Algebra K S]
    [Module.Finite K S] [Algebra.Etale K S] :
    PreGaloisCategory.IsConnected (op (of K S)) := by
  rw [isConnected_iff]
  exact Field.toIsField S

lemma isGaloisCover_iff (S₁ S₂ : Type u) [Field S₁] [Field S₂]
    [Algebra K S₁] [Algebra K S₂] [Algebra S₁ S₂] [IsScalarTower K S₁ S₂]
    [Module.Finite K S₁] [Algebra.Etale K S₁]
    [Module.Finite K S₂] [Algebra.Etale K S₂] :
    IsGaloisCover (ofHom K S₁ S₂).op ↔ IsGalois S₁ S₂ := sorry

/-- In the over categories of the category of connected objects in `(EtaleAlgCat K)ᵒᵖ`,
groups of automorphisms identify to Galois groups of field extensions. -/
def galMulEquiv (S₁ S₂ : Type u) [Field S₁] [Field S₂]
    [Algebra K S₁] [Algebra K S₂] [Algebra S₁ S₂] [IsScalarTower K S₁ S₂]
    [Module.Finite K S₁] [Algebra.Etale K S₁]
    [Module.Finite K S₂] [Algebra.Etale K S₂] :
    Aut (Over.mk (ofHom K S₁ S₂).op) ≃* Gal(S₂/S₁) where
  toFun g :=
    { toRingEquiv :=
        ((ObjectProperty.ι _ ⋙ Under.forget _).mapIso
          ((Over.forget _).mapIso g.symm).unop).commRingCatIsoToRingEquiv
      commutes' x₁ :=
        ConcreteCategory.congr_hom ((ObjectProperty.ι _ ⋙ Under.forget _).congr_map
          (Quiver.Hom.op_inj g.inv.w)) x₁ }
  invFun g :=
    Over.isoMk (ObjectProperty.isoMk _ (Under.isoMk
      g.symm.toRingEquiv.toCommRingCatIso (by
        ext x
        simp [IsScalarTower.algebraMap_apply K S₁ S₂ x]))).op
          (Quiver.Hom.unop_inj (by cat_disch))
  map_mul' _ _ := rfl

/-- When a connected object of `(EtaleAlgCat K)ᵒᵖ` is represented as `op (of K S)`,
this promotes the commutative ring structure on `S` to a field structure. -/
noncomputable abbrev fieldOfIsConnected (S : Type u) [CommRing S] [Algebra K S]
    [Module.Finite K S] [Algebra.Etale K S]
    [PreGaloisCategory.IsConnected (op (of K S))] : Field S :=
  IsField.toField (by simpa [← isConnected_iff K S])

/-- For any field `K`, this is the field formation which sends a connected object
of `(EtaleAlgCat K)ᵒᵖ`, i.e. a finite separable extension `L/K` to `Lˣ`. -/
@[implicit_reducible]
def fieldFormationUnits : FieldFormation (EtaleAlgCat K)ᵒᵖ where
  sheaf.obj.obj X := .of (Additive (Units X.unop.obj.unop.obj.right))
  sheaf.obj.map f :=
    AddCommGrpCat.ofHom (Units.map (f.unop.hom.unop.hom.right.hom.toMonoidHom)).toAdditive
  sheaf.property := isSheaf_of_reflectsFiniteLimits (forget _) (by
    rw [isSheaf_iff_isSheaf_of_type, isSheaf_type_iff]
    intro B A
    induction B with | _ B
    induction B with | of B
    induction A with | _ A
    induction A with | of A
    intro _ _ f
    induction f with | _ f
    dsimp at f ⊢
    let := fieldOfIsConnected K A
    let := fieldOfIsConnected K B
    induction f using homRec
    intro hf
    rw [isSheafFor_singleton_iff_of_isGaloisCover]
    refine ⟨fun _ _ hb ↦ Units.ext (FaithfulSMul.algebraMap_injective A B
      (Units.ext_iff.1 hb)), ?_⟩
    have : IsGalois A B := (isGaloisCover_iff K A B).1 hf
    have := Module.Finite.right K A B
    intro (b : Units B) hb
    obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (x := b.val)).2
      (fun g ↦ Units.ext_iff.1 (hb ((galMulEquiv K A B).symm g.symm)))
    obtain ⟨a, rfl⟩ : IsUnit a := by
      rw [isUnit_iff_ne_zero]
      rintro rfl
      exact b.ne_zero (by simp [← ha])
    exact ⟨a, Units.ext ha⟩)
  isZero_H_one := sorry

end EtaleAlgCat

/-- The class formation that is responsible for local class field theory. -/
@[implicit_reducible]
def IsNonarchimedeanLocalField.classFormation
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    ClassFormation (EtaleAlgCat K)ᵒᵖ where
  toFieldFormation := EtaleAlgCat.fieldFormationUnits K
  u := sorry
  addOrderOf_u := sorry
  zmultiples_u := sorry
  inflation_u := sorry
  restriction_u := sorry
