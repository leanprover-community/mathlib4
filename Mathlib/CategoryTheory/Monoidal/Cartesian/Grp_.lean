/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Monoidal.Grp_

/-!
# Yoneda embedding of `Grp_ C`

We show that group objects are exactly those whose yoneda presheaf is a presheaf of groups,
by constructing the yoneda embedding `Grp_ C ⥤ Cᵒᵖ ⥤ Grp.{v}` and
showing that it is fully faithful and its (essential) image is the representable functors.
-/

open CategoryTheory MonoidalCategory Limits Opposite CartesianMonoidalCategory Mon_Class

universe w v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {M G H X Y : C} [Mon_Class M] [Grp_Class G] [Grp_Class H]

/-- Construct a morphism `G ⟶ H` of `Grp_ C` C from a map `f : G ⟶ H` and a `IsMon_Hom f`
instance. -/
@[simps]
def Grp_.homMk (f : G ⟶ H) [IsMon_Hom f] : .mk' G ⟶ Grp_.mk' H := Mon_.Hom.mk' f

variable (X) in
/-- If `X` represents a presheaf of monoids, then `X` is a monoid object. -/
def Grp_Class.ofRepresentableBy (F : Cᵒᵖ ⥤ Grp.{w}) (α : (F ⋙ forget _).RepresentableBy X) :
    Grp_Class X where
  __ := Mon_Class.ofRepresentableBy X (F ⋙ forget₂ Grp MonCat) α
  inv := α.homEquiv.symm (α.homEquiv (𝟙 _))⁻¹
  left_inv' := by
    change lift (α.homEquiv.symm (α.homEquiv (𝟙 X))⁻¹) (𝟙 X) ≫
      α.homEquiv.symm (α.homEquiv (fst X X) * α.homEquiv (snd X X)) =
        toUnit X ≫ α.homEquiv.symm 1
    apply α.homEquiv.injective
    simp only [α.homEquiv_comp, Equiv.apply_symm_apply]
    simp only [Functor.comp_map, ConcreteCategory.forget_map_eq_coe, map_one, map_mul]
    simp only [← ConcreteCategory.forget_map_eq_coe, ← Functor.comp_map, ← α.homEquiv_comp]
    simp [← Functor.comp_obj]
  right_inv' := by
    change lift (𝟙 X) (α.homEquiv.symm (α.homEquiv (𝟙 X))⁻¹) ≫
      α.homEquiv.symm (α.homEquiv (fst X X) * α.homEquiv (snd X X)) =
        toUnit X ≫ α.homEquiv.symm 1
    apply α.homEquiv.injective
    simp only [α.homEquiv_comp, Equiv.apply_symm_apply]
    simp only [Functor.comp_map, ConcreteCategory.forget_map_eq_coe, map_one, map_mul]
    simp only [← ConcreteCategory.forget_map_eq_coe, ← Functor.comp_map, ← α.homEquiv_comp]
    simp [← Functor.comp_obj]

/-- If `G` is a group object, then `Hom(X, G)` has a group structure. -/
abbrev Hom.group : Group (X ⟶ G) where
  inv f := f ≫ ι
  inv_mul_cancel f := calc
    lift (f ≫ ι) f ≫ μ
    _ = (f ≫ lift ι (𝟙 G)) ≫ μ := by simp
    _ = toUnit X ≫ η := by rw [Category.assoc]; simp

scoped[Hom] attribute [instance] Hom.group

open scoped Hom

lemma Hom.inv_def (f : X ⟶ G) : f⁻¹ = f ≫ ι := rfl

variable (G) in
/-- If `G` is a group object, then `Hom(-, G)` is a presheaf of groups. -/
@[simps]
def yonedaGrpObj : Cᵒᵖ ⥤ Grp.{v} where
  obj X := Grp.of (unop X ⟶ G)
  map φ := Grp.ofHom ((yonedaMonObj G).map φ).hom

variable (G) in
/-- If `G` is a monoid object, then `Hom(-, G)` as a presheaf of monoids is represented by `G`. -/
def yonedaGrpObjRepresentableBy : (yonedaGrpObj G ⋙ forget _).RepresentableBy G :=
  Functor.representableByEquiv.symm (.refl _)

variable (G) in
lemma Grp_Class.ofRepresentableBy_yonedaGrpObjRepresentableBy :
    ofRepresentableBy G _ (yonedaGrpObjRepresentableBy G) = ‹Grp_Class G› := by
  ext; show lift (fst G G) (snd G G) ≫ μ = μ; rw [lift_fst_snd, Category.id_comp]

variable (X) in
/-- If `X` represents a presheaf of groups `F`, then `Hom(-, X)` is isomorphic to `F` as
a presheaf of groups. -/
@[simps! hom inv]
def yonedaGrpObjIsoOfRepresentableBy (F : Cᵒᵖ ⥤ Grp.{v}) (α : (F ⋙ forget _).RepresentableBy X) :
    letI := Grp_Class.ofRepresentableBy X F α
    yonedaGrpObj X ≅ F :=
  letI := Grp_Class.ofRepresentableBy X F α
  NatIso.ofComponents (fun Y ↦ MulEquiv.toGrpIso
    { toEquiv := α.homEquiv
      map_mul' :=
  ((yonedaMonObjIsoOfRepresentableBy X (F ⋙ forget₂ Grp MonCat) α).hom.app Y).hom.map_mul})
      fun φ ↦ Grp.hom_ext <| MonoidHom.ext <| α.homEquiv_comp φ.unop

/-- The yoneda embedding of `Grp_C` into presheaves of groups. -/
@[simps]
def yonedaGrp : Grp_ C ⥤ Cᵒᵖ ⥤ Grp.{v} where
  obj G := yonedaGrpObj G.X
  map {G H} ψ := { app Y := Grp.ofHom ((yonedaMon.map ψ).app Y).hom }

@[reassoc]
lemma yonedaGrp_naturality (α : yonedaGrpObj G ⟶ yonedaGrpObj H) (f : X ⟶ Y) (g : Y ⟶ G) :
    α.app _ (f ≫ g) = f ≫ α.app _ g := congr($(α.naturality f.op) g)

/-- The yoneda embedding for `Grp_C` is fully faithful. -/
def yonedaGrpFullyFaithful : yonedaGrp (C := C).FullyFaithful where
  preimage {G H} α := yonedaMonFullyFaithful.preimage (whiskerRight α (forget₂ Grp MonCat))
  map_preimage {G H} α := by
    ext X : 3
    exact congr(($(yonedaMonFullyFaithful.map_preimage
      (whiskerRight α (forget₂ Grp MonCat))).app X).hom)
  preimage_map := yonedaMonFullyFaithful.preimage_map

instance : yonedaGrp (C := C).Full := yonedaGrpFullyFaithful.full
instance : yonedaGrp (C := C).Faithful := yonedaGrpFullyFaithful.faithful

lemma essImage_yonedaGrp :
    yonedaGrp (C := C).essImage = (· ⋙ forget _) ⁻¹' setOf Functor.IsRepresentable := by
  ext F
  constructor
  · rintro ⟨G, ⟨α⟩⟩
    exact ⟨G.X, ⟨Functor.representableByEquiv.symm (isoWhiskerRight α (forget _))⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    letI := Grp_Class.ofRepresentableBy X F e
    exact ⟨.mk' X, ⟨yonedaGrpObjIsoOfRepresentableBy X F e⟩⟩

@[reassoc]
lemma Grp_Class.inv_comp (f : X ⟶ G) (g : G ⟶ H) [IsMon_Hom g] : f⁻¹ ≫ g = (f ≫ g)⁻¹ := by
  simp [Hom.inv_def, IsMon_Hom.inv_hom]

@[reassoc]
lemma Grp_Class.div_comp (f g : X ⟶ G) (h : G ⟶ H) [IsMon_Hom h] :
    (f / g) ≫ h = (f ≫ h) / (g ≫ h) :=
  ((yonedaGrp.map (Grp_.homMk h)).app (.op X)).hom.map_div f g

@[reassoc]
lemma Grp_Class.zpow_comp (f : X ⟶ G) (n : ℤ) (g : G ⟶ H) [IsMon_Hom g] :
    (f ^ n) ≫ g = (f ≫ g) ^ n :=
  ((yonedaGrp.map (Grp_.homMk g)).app (.op X)).hom.map_zpow f n

@[reassoc]
lemma Grp_Class.comp_inv (f : X ⟶ Y) (g : Y ⟶ G) : f ≫ g⁻¹ = (f ≫ g)⁻¹ :=
  ((yonedaGrp.obj <| .mk' G).map f.op).hom.map_inv g

@[reassoc]
lemma Grp_Class.comp_div (f : X ⟶ Y) (g h : Y ⟶ G) : f ≫ (g / h) = f ≫ g / f ≫ h :=
  ((yonedaGrp.obj (.mk' G)).map f.op).hom.map_div g h

@[reassoc]
lemma Grp_Class.comp_zpow (f : X ⟶ Y) (g : Y ⟶ G) : ∀ n : ℤ, f ≫ g ^ n = (f ≫ g) ^ n
  | (n : ℕ) => by simp [comp_pow]
  | .negSucc n => by simp [comp_pow, comp_inv]

lemma Grp_Class.inv_eq_inv : ι = (𝟙 G)⁻¹ := by simp [Hom.inv_def]

lemma Grp_Class.mul_inv_rev [BraidedCategory C] : μ ≫ ι = (ι[G] ⊗ ι) ≫ (β_ _ _).hom ≫ μ := by
  simp [mul_eq_mul, inv_eq_inv, mul_comp, comp_inv, comp_mul]

instance [BraidedCategory C] [IsCommMon G] : IsMon_Hom ι[G] where
  one_hom := by simp [one_eq_one, ← Hom.inv_def]
  mul_hom := by simp [Grp_Class.mul_inv_rev]

instance [BraidedCategory C] [IsCommMon G] {f : M ⟶ G} [IsMon_Hom f] : IsMon_Hom f⁻¹ where
  one_hom := by simp [Hom.inv_def]
  mul_hom := by simp [Hom.inv_def]

/-- If `G` is a commutative group object, then `Hom(X, G)` has a commutative group structure. -/
abbrev Hom.commGroup [BraidedCategory C] [IsCommMon G] : CommGroup (X ⟶ G) where
  inv_mul_cancel f := by simp

scoped[Hom] attribute [instance] Hom.commGroup

namespace Grp_
variable {G H : Grp_ C}

lemma inv_eq_inv (G : Grp_ C) : G.inv = (𝟙 G.X)⁻¹ := Grp_Class.inv_eq_inv (G := G.X)

namespace Hom

instance instOne : One (G ⟶ H) := inferInstanceAs <| One (G.toMon_ ⟶ H.toMon_)

@[simp] lemma hom_one : (1 : (G ⟶ H)).hom = 1 := rfl

variable [BraidedCategory C] [IsCommMon H.X]

instance instMul : Mul (G ⟶ H) := inferInstanceAs <| Mul (G.toMon_ ⟶ H.toMon_)

instance instPow : Pow (G ⟶ H) ℕ := inferInstanceAs <| Pow (G.toMon_ ⟶ H.toMon_) ℕ

instance instInv : Inv (G ⟶ H) where
  inv f := {
    hom := f.hom⁻¹
    one_hom := by simp [Mon_.one_eq_one]
    mul_hom := by simp [Mon_.mul_eq_mul, Mon_Class.comp_mul, Mon_Class.mul_comp]
  }

instance instDiv : Div (G ⟶ H) where
  div f g := {
    hom := f.hom / g.hom
    one_hom := by simp [Mon_.one_eq_one, Grp_Class.comp_div, Mon_Class.one_comp]
    mul_hom := by
      simp [Mon_.mul_eq_mul, Grp_Class.comp_div, Mon_Class.comp_mul, Mon_Class.mul_comp,
        mul_div_mul_comm]
  }

instance instPowInt : Pow (G ⟶ H) ℤ where
  pow f i := {
    hom := f.hom ^ i
    one_hom := by simp [Mon_.one_eq_one, Mon_Class.one_comp, Grp_Class.comp_zpow]
    mul_hom := by
      simp [Mon_.mul_eq_mul, Mon_Class.comp_mul, Mon_Class.mul_comp, Grp_Class.comp_zpow, mul_zpow]
  }

@[simp] lemma hom_mul (f g : G ⟶ H) : (f * g).hom = f.hom * g.hom := rfl
@[simp] lemma hom_pow (f : G ⟶ H) (n : ℕ) : (f ^ n).hom = f.hom ^ n := rfl
@[simp] lemma hom_inv (f : G ⟶ H) : (f⁻¹).hom = f.hom⁻¹ := rfl
@[simp] lemma hom_div (f g : G ⟶ H) : (f / g).hom = f.hom / g.hom := rfl
@[simp] lemma hom_zpow (f : G ⟶ H) (n : ℤ) : (f ^ n).hom = f.hom ^ n := rfl

instance instCommGroup : CommGroup (G ⟶ H) :=
  Mon_.hom_injective.commGroup Mon_.Hom.hom hom_one hom_mul hom_inv hom_div hom_pow hom_zpow

end Grp_.Hom
