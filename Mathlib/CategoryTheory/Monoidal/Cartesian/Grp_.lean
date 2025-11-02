/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Monoidal.Grp_

/-!
# Yoneda embedding of `Grp C`

We show that group objects are exactly those whose yoneda presheaf is a presheaf of groups,
by constructing the yoneda embedding `Grp C ⥤ Cᵒᵖ ⥤ GrpCat.{v}` and
showing that it is fully faithful and its (essential) image is the representable functors.
-/

assert_not_exists Field

open CategoryTheory MonoidalCategory Limits Opposite CartesianMonoidalCategory MonObj

namespace CategoryTheory
universe w v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {M G H X Y : C} [MonObj M] [GrpObj G] [GrpObj H]

/-- Construct a morphism `G ⟶ H` of `Grp C` C from a map `f : G ⟶ H` and a `IsMonHom f`
instance. -/
@[simps]
def Grp.homMk (f : G ⟶ H) [IsMonHom f] : .mk G ⟶ Grp.mk H := ⟨f⟩

@[deprecated (since := "2025-10-13")] alias Grp_.homMk := Grp.homMk

@[simp]
lemma Grp.homMk_hom' {G H : Grp C} (f : G ⟶ H) : homMk (G := G.X) (H := H.X) f.hom = f := rfl

@[deprecated (since := "2025-10-13")] alias Grp_.homMk_hom' := Grp.homMk_hom'

variable (X) in
/-- If `X` represents a presheaf of monoids, then `X` is a monoid object. -/
def GrpObj.ofRepresentableBy (F : Cᵒᵖ ⥤ GrpCat.{w}) (α : (F ⋙ forget _).RepresentableBy X) :
    GrpObj X where
  __ := MonObj.ofRepresentableBy X (F ⋙ forget₂ GrpCat MonCat) α
  inv := α.homEquiv.symm (α.homEquiv (𝟙 _))⁻¹
  left_inv := by
    change lift (α.homEquiv.symm (α.homEquiv (𝟙 X))⁻¹) (𝟙 X) ≫
      α.homEquiv.symm (α.homEquiv (fst X X) * α.homEquiv (snd X X)) =
        toUnit X ≫ α.homEquiv.symm 1
    apply α.homEquiv.injective
    simp only [α.homEquiv_comp, Equiv.apply_symm_apply]
    simp only [Functor.comp_map, ConcreteCategory.forget_map_eq_coe, map_one, map_mul]
    simp only [← ConcreteCategory.forget_map_eq_coe, ← Functor.comp_map, ← α.homEquiv_comp]
    simp [- Functor.comp_obj]
  right_inv := by
    change lift (𝟙 X) (α.homEquiv.symm (α.homEquiv (𝟙 X))⁻¹) ≫
      α.homEquiv.symm (α.homEquiv (fst X X) * α.homEquiv (snd X X)) =
        toUnit X ≫ α.homEquiv.symm 1
    apply α.homEquiv.injective
    simp only [α.homEquiv_comp, Equiv.apply_symm_apply]
    simp only [Functor.comp_map, ConcreteCategory.forget_map_eq_coe, map_one, map_mul]
    simp only [← ConcreteCategory.forget_map_eq_coe, ← Functor.comp_map, ← α.homEquiv_comp]
    simp [- Functor.comp_obj]

@[deprecated (since := "2025-09-13")] alias Grp_Class.ofRepresentableBy := GrpObj.ofRepresentableBy

/-- If `G` is a group object, then `Hom(X, G)` has a group structure. -/
abbrev Hom.group : Group (X ⟶ G) where
  inv f := f ≫ ι
  inv_mul_cancel f := calc
    lift (f ≫ ι) f ≫ μ
    _ = (f ≫ lift ι (𝟙 G)) ≫ μ := by simp
    _ = toUnit X ≫ η := by rw [Category.assoc]; simp

scoped[CategoryTheory.MonObj] attribute [instance] Hom.group

lemma Hom.inv_def (f : X ⟶ G) : f⁻¹ = f ≫ ι := rfl

variable (G) in
/-- If `G` is a group object, then `Hom(-, G)` is a presheaf of groups. -/
@[simps]
def yonedaGrpObj : Cᵒᵖ ⥤ GrpCat.{v} where
  obj X := GrpCat.of (unop X ⟶ G)
  map φ := GrpCat.ofHom ((yonedaMonObj G).map φ).hom

variable (G) in
/-- If `G` is a monoid object, then `Hom(-, G)` as a presheaf of monoids is represented by `G`. -/
def yonedaGrpObjRepresentableBy : (yonedaGrpObj G ⋙ forget _).RepresentableBy G :=
  Functor.representableByEquiv.symm (.refl _)

variable (G) in
lemma GrpObj.ofRepresentableBy_yonedaGrpObjRepresentableBy :
    ofRepresentableBy G _ (yonedaGrpObjRepresentableBy G) = ‹GrpObj G› := by
  ext; change lift (fst G G) (snd G G) ≫ μ = μ; rw [lift_fst_snd, Category.id_comp]

@[deprecated (since := "2025-09-13")]
alias Grp_Class.ofRepresentableBy_yonedaGrpObjRepresentableBy :=
  GrpObj.ofRepresentableBy_yonedaGrpObjRepresentableBy

variable (X) in
/-- If `X` represents a presheaf of groups `F`, then `Hom(-, X)` is isomorphic to `F` as
a presheaf of groups. -/
@[simps! hom inv]
def yonedaGrpObjIsoOfRepresentableBy (F : Cᵒᵖ ⥤ GrpCat.{v}) (α : (F ⋙ forget _).RepresentableBy X) :
    letI := GrpObj.ofRepresentableBy X F α
    yonedaGrpObj X ≅ F :=
  letI := GrpObj.ofRepresentableBy X F α
  NatIso.ofComponents (fun Y ↦ MulEquiv.toGrpIso
    { toEquiv := α.homEquiv
      map_mul' :=
  ((yonedaMonObjIsoOfRepresentableBy X (F ⋙ forget₂ GrpCat MonCat) α).hom.app Y).hom.map_mul})
      fun φ ↦ GrpCat.hom_ext <| MonoidHom.ext <| α.homEquiv_comp φ.unop

/-- The yoneda embedding of `Grp_C` into presheaves of groups. -/
@[simps]
def yonedaGrp : Grp C ⥤ Cᵒᵖ ⥤ GrpCat.{v} where
  obj G := yonedaGrpObj G.X
  map {G H} ψ := { app Y := GrpCat.ofHom ((yonedaMon.map ψ).app Y).hom }

@[reassoc]
lemma yonedaGrp_naturality (α : yonedaGrpObj G ⟶ yonedaGrpObj H) (f : X ⟶ Y) (g : Y ⟶ G) :
    α.app _ (f ≫ g) = f ≫ α.app _ g := congr($(α.naturality f.op) g)

/-- The yoneda embedding for `Grp_C` is fully faithful. -/
def yonedaGrpFullyFaithful : yonedaGrp (C := C).FullyFaithful where
  preimage {G H} α :=
    yonedaMonFullyFaithful.preimage (Functor.whiskerRight α (forget₂ GrpCat MonCat))
  map_preimage {G H} α := by
    ext X : 3
    exact congr(($(yonedaMonFullyFaithful.map_preimage (X := G.toMon) (Y := H.toMon)
      (Functor.whiskerRight α (forget₂ GrpCat MonCat))).app X).hom)
  preimage_map := yonedaMonFullyFaithful.preimage_map

instance : yonedaGrp (C := C).Full := yonedaGrpFullyFaithful.full
instance : yonedaGrp (C := C).Faithful := yonedaGrpFullyFaithful.faithful

lemma essImage_yonedaGrp :
    yonedaGrp (C := C).essImage = (· ⋙ forget _) ⁻¹' setOf Functor.IsRepresentable := by
  ext F
  constructor
  · rintro ⟨G, ⟨α⟩⟩
    exact ⟨G.X, ⟨Functor.representableByEquiv.symm (Functor.isoWhiskerRight α (forget _))⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    letI := GrpObj.ofRepresentableBy X F e
    exact ⟨⟨X⟩, ⟨yonedaGrpObjIsoOfRepresentableBy X F e⟩⟩

@[reassoc]
lemma GrpObj.inv_comp (f : X ⟶ G) (g : G ⟶ H) [IsMonHom g] : f⁻¹ ≫ g = (f ≫ g)⁻¹ := by
  simp [Hom.inv_def]

@[deprecated (since := "2025-09-13")] alias Grp_Class.inv_comp := GrpObj.inv_comp

@[reassoc]
lemma GrpObj.div_comp (f g : X ⟶ G) (h : G ⟶ H) [IsMonHom h] :
    (f / g) ≫ h = (f ≫ h) / (g ≫ h) :=
  ((yonedaGrp.map <| Grp.homMk h).app <| op X).hom.map_div f g

@[deprecated (since := "2025-09-13")] alias Grp_Class.div_comp := GrpObj.div_comp

@[reassoc]
lemma GrpObj.zpow_comp (f : X ⟶ G) (n : ℤ) (g : G ⟶ H) [IsMonHom g] :
    (f ^ n) ≫ g = (f ≫ g) ^ n :=
  ((yonedaGrp.map <| Grp.homMk g).app <| op X).hom.map_zpow f n

@[deprecated (since := "2025-09-13")] alias Grp_Class.zpow_comp := GrpObj.zpow_comp

@[reassoc]
lemma GrpObj.comp_inv (f : X ⟶ Y) (g : Y ⟶ G) : f ≫ g⁻¹ = (f ≫ g)⁻¹ :=
  ((yonedaGrp.obj ⟨G⟩).map f.op).hom.map_inv g

@[deprecated (since := "2025-09-13")] alias Grp_Class.comp_inv := GrpObj.comp_inv

@[reassoc]
lemma GrpObj.comp_div (f : X ⟶ Y) (g h : Y ⟶ G) : f ≫ (g / h) = f ≫ g / f ≫ h :=
  ((yonedaGrp.obj ⟨G⟩).map f.op).hom.map_div g h

@[deprecated (since := "2025-09-13")] alias Grp_Class.comp_div := GrpObj.comp_div

@[reassoc]
lemma GrpObj.comp_zpow (f : X ⟶ Y) (g : Y ⟶ G) : ∀ n : ℤ, f ≫ g ^ n = (f ≫ g) ^ n
  | (n : ℕ) => by simp [comp_pow]
  | .negSucc n => by simp [comp_pow, comp_inv]

@[deprecated (since := "2025-09-13")] alias Grp_Class.comp_zpow := GrpObj.comp_zpow

lemma GrpObj.inv_eq_inv : ι = (𝟙 G)⁻¹ := by simp [Hom.inv_def]

@[reassoc (attr := simp)]
lemma GrpObj.one_inv : η[G] ≫ ι = η := by simp [GrpObj.inv_eq_inv, GrpObj.comp_inv, one_eq_one]

@[deprecated (since := "2025-09-13")] alias Grp_Class.inv_eq_inv := GrpObj.inv_eq_inv

instance [BraidedCategory C] [IsCommMonObj G] : IsMonHom ι[G] where
  one_hom := by simp [one_eq_one, ← Hom.inv_def]
  mul_hom := by simp [GrpObj.mul_inv_rev]

attribute [local simp] Hom.inv_def in
instance [BraidedCategory C] [IsCommMonObj G] {f : M ⟶ G} [IsMonHom f] : IsMonHom f⁻¹ where

/-- If `G` is a commutative group object, then `Hom(X, G)` has a commutative group structure. -/
abbrev Hom.commGroup [BraidedCategory C] [IsCommMonObj G] : CommGroup (X ⟶ G) where

scoped[CategoryTheory.MonObj] attribute [instance] Hom.commGroup

end CategoryTheory
