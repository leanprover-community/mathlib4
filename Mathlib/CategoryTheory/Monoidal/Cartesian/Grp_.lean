/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon_
public import Mathlib.CategoryTheory.Monoidal.Grp_

/-!
# Yoneda embedding of `Grp C`

We show that group objects are exactly those whose yoneda presheaf is a presheaf of groups,
by constructing the yoneda embedding `Grp C ⥤ Cᵒᵖ ⥤ GrpCat.{v}` and
showing that it is fully faithful and its (essential) image is the representable functors.
-/

@[expose] public section

assert_not_exists Field

open CategoryTheory MonoidalCategory Limits Opposite CartesianMonoidalCategory MonObj

namespace CategoryTheory
universe w v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {M G H X Y : C} [MonObj M] [GrpObj G] [GrpObj H]

set_option backward.isDefEq.respectTransparency false in
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
    simp [-Functor.comp_obj]
  right_inv := by
    change lift (𝟙 X) (α.homEquiv.symm (α.homEquiv (𝟙 X))⁻¹) ≫
      α.homEquiv.symm (α.homEquiv (fst X X) * α.homEquiv (snd X X)) =
        toUnit X ≫ α.homEquiv.symm 1
    apply α.homEquiv.injective
    simp only [α.homEquiv_comp, Equiv.apply_symm_apply]
    simp only [Functor.comp_map, ConcreteCategory.forget_map_eq_coe, map_one, map_mul]
    simp only [← ConcreteCategory.forget_map_eq_coe, ← Functor.comp_map, ← α.homEquiv_comp]
    simp [-Functor.comp_obj]

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
  ((yonedaMonObjIsoOfRepresentableBy X (F ⋙ forget₂ GrpCat MonCat) α).hom.app Y).hom.map_mul })
      fun φ ↦ GrpCat.hom_ext <| MonoidHom.ext <| α.homEquiv_comp φ.unop

set_option backward.isDefEq.respectTransparency false in
/-- The yoneda embedding of `Grp_C` into presheaves of groups. -/
@[simps]
def yonedaGrp : Grp C ⥤ Cᵒᵖ ⥤ GrpCat.{v} where
  obj G := yonedaGrpObj G.X
  map {G H} ψ := { app Y := GrpCat.ofHom ((yonedaMon.map ψ.hom).app Y).hom }

@[reassoc]
lemma yonedaGrp_naturality (α : yonedaGrpObj G ⟶ yonedaGrpObj H) (f : X ⟶ Y) (g : Y ⟶ G) :
    α.app _ (f ≫ g) = f ≫ α.app _ g := congr($(α.naturality f.op) g)

/-- The yoneda embedding for `Grp_C` is fully faithful. -/
def yonedaGrpFullyFaithful : yonedaGrp (C := C).FullyFaithful where
  preimage {G H} α :=
    Grp.homMk' (yonedaMonFullyFaithful.preimage ((Functor.whiskerRight α (forget₂ GrpCat MonCat))))
  map_preimage {G H} α := by
    ext X : 3
    exact congr(($(yonedaMonFullyFaithful.map_preimage (X := G.toMon) (Y := H.toMon)
      (Functor.whiskerRight α (forget₂ GrpCat MonCat))).app X).hom)
  preimage_map f := by
    ext
    congr
    apply yonedaMonFullyFaithful.preimage_map

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
  ((yonedaGrp.map (Grp.homMk (A := .mk G) (B := .mk H) h)).app (op X)).hom.map_div f g

@[deprecated (since := "2025-09-13")] alias Grp_Class.div_comp := GrpObj.div_comp

@[reassoc]
lemma GrpObj.zpow_comp (f : X ⟶ G) (n : ℤ) (g : G ⟶ H) [IsMonHom g] :
    (f ^ n) ≫ g = (f ≫ g) ^ n :=
  ((yonedaGrp.map (Grp.homMk (A := .mk G) (B := .mk H) g)).app (op X)).hom.map_zpow f n

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

open scoped _root_.CategoryTheory.Obj in
/-- If `G` is a group object and `F` is monoidal,
then `Hom(X, G) → Hom(F X, F G)` preserves inverses. -/
@[simp] lemma Functor.map_inv' {D : Type*} [Category* D] [CartesianMonoidalCategory D] (F : C ⥤ D)
    [F.Monoidal] {X G : C} (f : X ⟶ G) [GrpObj G] :
    F.map (f⁻¹) = (F.map f)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← Functor.map_mul, inv_mul_cancel, Functor.map_one]

@[deprecated (since := "2025-09-13")] alias Grp_Class.inv_eq_inv := GrpObj.inv_eq_inv

/-- The commutator of `G` as a morphism. This is the map `(x, y) ↦ x * y * x⁻¹ * y⁻¹`,
see `CategoryTheory.GrpObj.lift_commutator_eq_mul_mul_inv_inv`.
This morphism is constant with value `1` if and only if `G` is commutative
(see `CategoryTheory.isCommMonObj_iff_commutator_eq_toUnit_η`). -/
def GrpObj.commutator (G : C) [GrpObj G] : G ⊗ G ⟶ G :=
  fst _ _ * snd _ _ * (fst _ _) ⁻¹ * (snd _ _) ⁻¹

@[reassoc (attr := simp)]
lemma GrpObj.lift_commutator_eq_mul_mul_inv_inv {X G : C} [GrpObj G] (f₁ f₂ : X ⟶ G) :
    lift f₁ f₂ ≫ commutator G = f₁ * f₂ * f₁⁻¹ * f₂⁻¹ := by
  simp [commutator, comp_mul, comp_inv]

@[reassoc (attr := simp)]
lemma GrpObj.η_whiskerRight_commutator : η ▷ G ≫ commutator G = toUnit _ ≫ η := by
  simp [commutator, comp_mul, comp_inv, one_eq_one]

@[reassoc (attr := simp)]
lemma GrpObj.whiskerLeft_η_commutator : G ◁ η ≫ commutator G = toUnit _ ≫ η := by
  simp [commutator, comp_mul, comp_inv, one_eq_one]

variable [BraidedCategory C]

instance [IsCommMonObj G] : IsMonHom ι[G] where
  one_hom := by simp [one_eq_one, ← Hom.inv_def]
  mul_hom := by simp [GrpObj.mul_inv_rev]

attribute [local simp] Hom.inv_def in
instance [IsCommMonObj G] {f : M ⟶ G} [IsMonHom f] : IsMonHom f⁻¹ where

namespace Grp
variable {G H : Grp C} [IsCommMonObj H.X]

instance : MonObj H where
  one := Grp.homMk η[H.toMon].hom
  mul := Grp.homMk μ[H.toMon].hom

@[simp] lemma hom_one (H : Grp C) [IsCommMonObj H.X] : η[H].hom.hom = η[H.X] := rfl
@[simp] lemma hom_mul (H : Grp C) [IsCommMonObj H.X] : μ[H].hom.hom = μ[H.X] := rfl

namespace Hom

@[simp] lemma hom_one : (1 : G ⟶ H).hom = 1 := rfl
@[simp] lemma hom_mul (f g : G ⟶ H) : (f * g).hom = f.hom * g.hom := rfl
@[simp] lemma hom_pow (f : G ⟶ H) (n : ℕ) : (f ^ n).hom = f.hom ^ n := by
  induction n with
  | zero => simp
  | succ n hn => simp [pow_succ, hn]

end Hom

/-- A commutative group object is a group object in the category of group objects. -/
instance : GrpObj H where inv := Grp.homMk' { hom := ι[H.X] }

namespace Hom

@[simp] lemma hom_hom_inv (f : G ⟶ H) : f⁻¹.hom.hom = f.hom.hom⁻¹ := rfl
@[simp] lemma hom_hom_div (f g : G ⟶ H) : (f / g).hom.hom = f.hom.hom / g.hom.hom := rfl
@[simp] lemma hom_hom_zpow (f : G ⟶ H) (n : ℤ) : (f ^ n).hom.hom = f.hom.hom ^ n := by
  cases n <;> simp

@[deprecated (since := "2025-12-18")] alias hom_inv := hom_hom_inv
@[deprecated (since := "2025-12-18")] alias hom_div := hom_hom_div
@[deprecated (since := "2025-12-18")] alias hom_zpow := hom_hom_zpow

end Hom

attribute [local simp] mul_eq_mul comp_mul mul_comm mul_div_mul_comm in
/-- A commutative group object is a commutative group object in the category of group objects. -/
instance : IsCommMonObj H where

instance [IsCommMonObj G.X] (f : G ⟶ H) : IsMonHom f where

end Grp

/-- If `G` is a commutative group object, then `Hom(X, G)` has a commutative group structure. -/
abbrev Hom.commGroup [IsCommMonObj G] : CommGroup (X ⟶ G) where

scoped[CategoryTheory.MonObj] attribute [instance] Hom.commGroup

section

/-- `G` is a commutative group object if and only if the commutator map `(x, y) ↦ x * y * x⁻¹ * y⁻¹`
is constant. -/
lemma isCommMonObj_iff_commutator_eq_toUnit_η :
    IsCommMonObj G ↔ GrpObj.commutator G = toUnit _ ≫ η := by
  rw [isCommMonObj_iff_isMulCommutative]
  refine ⟨fun h ↦ ?_, fun heq X ↦ ⟨⟨fun f g ↦ ?_⟩⟩⟩
  · simp [GrpObj.commutator, one_eq_one]
  · simpa [one_eq_one, mul_inv_eq_iff_eq_mul] using congr(lift f g ≫ $heq)

end

end CategoryTheory
