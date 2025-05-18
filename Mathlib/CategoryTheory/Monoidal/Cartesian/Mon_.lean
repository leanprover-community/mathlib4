/-
Copyright (c) 2025 Markus Himmel, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Andrew Yang
-/
import Mathlib.Algebra.Category.MonCat.Limits
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_

/-!
# Yoneda embedding of `Mon_ C`

We show that monoid objects in cartesian monoidal categories are exactly those whose yoneda presheaf
is a presheaf of monoids, by constructing the yoneda embedding `Mon_ C ⥤ Cᵒᵖ ⥤ MonCat.{v}` and
showing that it is fully faithful and its (essential) image is the representable functors.
-/

open CategoryTheory MonoidalCategory Limits Opposite CartesianMonoidalCategory Mon_Class

universe w v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {M N X Y : C} [Mon_Class M] [Mon_Class N]

namespace Mon_

theorem lift_lift_assoc {A : C} {B : Mon_ C} (f g h : A ⟶ B.X) :
    lift (lift f g ≫ B.mul) h ≫ B.mul = lift f (lift g h ≫ B.mul) ≫ B.mul := by
  have := lift (lift f g) h ≫= B.mul_assoc
  rwa [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc] at this

@[reassoc (attr := simp)]
theorem lift_comp_one_left {A : C} {B : Mon_ C} (f : A ⟶ 𝟙_ C) (g : A ⟶ B.X) :
    lift (f ≫ B.one) g ≫ B.mul = g := by
  have := lift f g ≫= B.one_mul
  rwa [lift_whiskerRight_assoc, lift_leftUnitor_hom] at this

@[reassoc (attr := simp)]
theorem lift_comp_one_right {A : C} {B : Mon_ C} (f : A ⟶ B.X) (g : A ⟶ 𝟙_ C) :
    lift f (g ≫ B.one) ≫ B.mul = f := by
  have := lift f g ≫= B.mul_one
  rwa [lift_whiskerLeft_assoc, lift_rightUnitor_hom] at this

end Mon_

variable (X) in
/-- If `X` represents a presheaf of monoids, then `X` is a monoid object. -/
@[simps]
def Mon_Class.ofRepresentableBy (F : Cᵒᵖ ⥤ MonCat.{w}) (α : (F ⋙ forget _).RepresentableBy X) :
    Mon_Class X where
  one := α.homEquiv.symm 1
  mul := α.homEquiv.symm (α.homEquiv (fst X X) * α.homEquiv (snd X X))
  one_mul' := by
    apply α.homEquiv.injective
    simp only [α.homEquiv_comp, Equiv.apply_symm_apply]
    simp only [Functor.comp_map, ConcreteCategory.forget_map_eq_coe, map_mul]
    simp only [← ConcreteCategory.forget_map_eq_coe, ← Functor.comp_map, ← α.homEquiv_comp]
    simp only [whiskerRight_fst, whiskerRight_snd]
    simp only [α.homEquiv_comp, Equiv.apply_symm_apply]
    simp [leftUnitor_hom]
  mul_one' := by
    apply α.homEquiv.injective
    simp only [α.homEquiv_comp, Equiv.apply_symm_apply]
    simp only [Functor.comp_map, ConcreteCategory.forget_map_eq_coe, map_mul]
    simp only [← ConcreteCategory.forget_map_eq_coe, ← Functor.comp_map, ← α.homEquiv_comp]
    simp only [whiskerLeft_fst, whiskerLeft_snd]
    simp only [α.homEquiv_comp, Equiv.apply_symm_apply]
    simp [rightUnitor_hom]
  mul_assoc' := by
    apply α.homEquiv.injective
    simp only [α.homEquiv_comp, Equiv.apply_symm_apply]
    simp only [Functor.comp_map, ConcreteCategory.forget_map_eq_coe, map_mul]
    simp only [← ConcreteCategory.forget_map_eq_coe, ← Functor.comp_map, ← α.homEquiv_comp]
    simp only [whiskerRight_fst, whiskerRight_snd, whiskerLeft_fst,
      associator_hom_fst, whiskerLeft_snd]
    simp only [α.homEquiv_comp, Equiv.apply_symm_apply]
    simp only [Functor.comp_map, ConcreteCategory.forget_map_eq_coe, map_mul, _root_.mul_assoc]
    simp only [← ConcreteCategory.forget_map_eq_coe, ← Functor.comp_map, ← α.homEquiv_comp]
    simp

@[deprecated (since := "2025-03-07")]
alias Mon_ClassOfRepresentableBy := Mon_Class.ofRepresentableBy

/-- If `M` is a monoid object, then `Hom(X, M)` has a monoid structure. -/
abbrev Hom.monoid : Monoid (X ⟶ M) where
  mul f₁ f₂ := lift f₁ f₂ ≫ μ
  mul_assoc f₁ f₂ f₃ := by
    show lift (lift f₁ f₂ ≫ μ) f₃ ≫ μ = lift f₁ (lift f₂ f₃ ≫ μ) ≫ μ
    trans lift (lift f₁ f₂) f₃ ≫ μ ▷ M ≫ μ
    · rw [← tensorHom_id, lift_map_assoc, Category.comp_id]
    trans lift f₁ (lift f₂ f₃) ≫ M ◁ μ ≫ μ
    · rw [Mon_Class.mul_assoc]
      simp_rw [← Category.assoc]
      congr 2
      ext <;> simp
    · rw [← id_tensorHom, lift_map_assoc, Category.comp_id]
  one := toUnit X ≫ η
  one_mul f := by
    show lift (toUnit _ ≫ η) f ≫ μ = f
    rw [← Category.comp_id f, ← lift_map_assoc, tensorHom_id, Mon_Class.one_mul,
      Category.comp_id, leftUnitor_hom]
    exact lift_snd _ _
  mul_one f := by
    show lift f (toUnit _ ≫ η) ≫ μ = f
    rw [← Category.comp_id f, ← lift_map_assoc, id_tensorHom, Mon_Class.mul_one,
      Category.comp_id, rightUnitor_hom]
    exact lift_fst _ _

attribute [local instance] Hom.monoid

lemma Hom.one_def : (1 : X ⟶ M) = toUnit X ≫ η := rfl
lemma Hom.mul_def (f₁ f₂ : X ⟶ M) : f₁ * f₂ = lift f₁ f₂ ≫ μ := rfl

variable (M) in
/-- If `M` is a monoid object, then `Hom(-, M)` is a presheaf of monoids. -/
@[simps]
def yonedaMonObj : Cᵒᵖ ⥤ MonCat.{v} where
  obj X := MonCat.of (unop X ⟶ M)
  map {X Y₂} φ := MonCat.ofHom
    { toFun := (φ.unop ≫ ·)
      map_one' := by
        show φ.unop ≫ toUnit _ ≫ η = toUnit _ ≫ η
        rw [← Category.assoc, toUnit_unique (φ.unop ≫ toUnit _)]
      map_mul' f₁ f₂ := by
        show φ.unop ≫ lift f₁ f₂ ≫ μ = lift (φ.unop ≫ f₁) (φ.unop ≫ f₂) ≫ μ
        rw [← Category.assoc]
        aesop_cat }
  map_id _ := MonCat.hom_ext (MonoidHom.ext Category.id_comp)
  map_comp _ _ := MonCat.hom_ext (MonoidHom.ext (Category.assoc _ _))

variable (X) in
/-- If `X` represents a presheaf of monoids `F`, then `Hom(-, X)` is isomorphic to `F` as
a presheaf of monoids. -/
@[simps!]
def yonedaMonObjIsoOfRepresentableBy
    (F : Cᵒᵖ ⥤ MonCat.{v}) (α : (F ⋙ forget _).RepresentableBy X) :
    letI := Mon_Class.ofRepresentableBy X F α
    yonedaMonObj X ≅ F :=
  letI := Mon_Class.ofRepresentableBy X F α
  NatIso.ofComponents (fun Y ↦ MulEquiv.toMonCatIso
    { toEquiv := α.homEquiv
      map_mul' f₁ f₂ := by
        show α.homEquiv (lift f₁ f₂ ≫ α.homEquiv.symm (α.homEquiv (fst X X) *
          α.homEquiv (snd X X))) = α.homEquiv f₁ * α.homEquiv f₂
        simp only [α.homEquiv_comp, Equiv.apply_symm_apply,
          Functor.comp_map, ConcreteCategory.forget_map_eq_coe, map_mul]
        simp only [← Functor.comp_map, ← ConcreteCategory.forget_map_eq_coe, ← α.homEquiv_comp]
        simp }) (fun φ ↦ MonCat.hom_ext (MonoidHom.ext (α.homEquiv_comp φ.unop)))

/-- The yoneda embedding of `Mon_C` into presheaves of monoids. -/
@[simps]
def yonedaMon : Mon_ C ⥤ Cᵒᵖ ⥤ MonCat.{v} where
  obj M := yonedaMonObj M.X
  map {M N} ψ :=
  { app Y := MonCat.ofHom
      { toFun := (· ≫ ψ.hom)
        map_one' := by simp [Hom.one_def, Hom.one_def]
        map_mul' φ₁ φ₂ := by simp [Hom.mul_def] }
    naturality {M N} φ := MonCat.hom_ext <| MonoidHom.ext fun f ↦ Category.assoc φ.unop f ψ.hom }
  map_id M := NatTrans.ext <| funext fun _ ↦ MonCat.hom_ext <| MonoidHom.ext Category.comp_id
  map_comp _ _ :=
    NatTrans.ext <| funext fun _ ↦ MonCat.hom_ext <| MonoidHom.ext (.symm <| Category.assoc · _ _)

@[reassoc]
lemma yonedaMon_naturality (α : yonedaMonObj M ⟶ yonedaMonObj N) (f : X ⟶ Y) (g : Y ⟶ M) :
      α.app _ (f ≫ g) = f ≫ α.app _ g := congr($(α.naturality f.op) g)

variable (M) in
/-- If `M` is a monoid object, then `Hom(-, M)` as a presheaf of monoids is represented by `M`. -/
def yonedaMonObjRepresentableBy : (yonedaMonObj M ⋙ forget _).RepresentableBy M :=
  Functor.representableByEquiv.symm (.refl _)

variable (M) in
lemma Mon_Class.ofRepresentableBy_yonedaMonObjRepresentableBy :
    ofRepresentableBy M _ (yonedaMonObjRepresentableBy M) = ‹_› := by
  ext; show lift (fst M M) (snd M M) ≫ μ = μ; rw [lift_fst_snd, Category.id_comp]

@[deprecated (since := "2025-03-07")]
alias Mon_ClassOfRepresentableBy_yonedaMonObjRepresentableBy :=
  Mon_Class.ofRepresentableBy_yonedaMonObjRepresentableBy

/-- The yoneda embedding for `Mon_C` is fully faithful. -/
def yonedaMonFullyFaithful : yonedaMon (C := C).FullyFaithful where
  preimage {M N} α :=
  { hom := α.app (op M.X) (𝟙 M.X)
    one_hom := by
      dsimp only [yonedaMon_obj] at α ⊢
      rw [← yonedaMon_naturality, Category.comp_id,
        ← Category.id_comp M.one, toUnit_unique (𝟙 _) (toUnit _),
        ← Category.id_comp N.one, toUnit_unique (𝟙 _) (toUnit _)]
      exact (α.app _).hom.map_one
    mul_hom := by
      dsimp only [yonedaMon_obj] at α ⊢
      rw [← yonedaMon_naturality, Category.comp_id, ← Category.id_comp M.mul, ← lift_fst_snd]
      refine ((α.app _).hom.map_mul _ _).trans ?_
      show lift _ _ ≫ N.mul = _
      congr 1
      ext <;> simp only [lift_fst, tensorHom_fst, lift_snd, tensorHom_snd,
        ← yonedaMon_naturality, Category.comp_id] }
  map_preimage {M N} α := by
    ext Y f
    dsimp only [yonedaMon_obj, yonedaMon_map_app, MonCat.hom_ofHom]
    simp_rw [← yonedaMon_naturality]
    simp
  preimage_map φ := Mon_.ext (Category.id_comp φ.hom)

instance : yonedaMon (C := C).Full := yonedaMonFullyFaithful.full
instance : yonedaMon (C := C).Faithful := yonedaMonFullyFaithful.faithful

lemma essImage_yonedaMon :
    yonedaMon (C := C).essImage = (· ⋙ forget _) ⁻¹' setOf Functor.IsRepresentable := by
  ext F
  constructor
  · rintro ⟨M, ⟨α⟩⟩
    exact ⟨M.X, ⟨Functor.representableByEquiv.symm (isoWhiskerRight α (forget _))⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    letI := Mon_Class.ofRepresentableBy X F e
    exact ⟨.mk' X, ⟨yonedaMonObjIsoOfRepresentableBy X F e⟩⟩

@[reassoc]
lemma Mon_Class.one_comp (f : M ⟶ N) [IsMon_Hom f] : (1 : X ⟶ M) ≫ f = 1 := by simp [Hom.one_def]

@[reassoc]
lemma Mon_Class.mul_comp (f₁ f₂ : X ⟶ M) (g : M ⟶ N) [IsMon_Hom g] :
    (f₁ * f₂) ≫ g = f₁ ≫ g * f₂ ≫ g := by simp [Hom.mul_def]

@[reassoc]
lemma Mon_Class.comp_one (f : X ⟶ Y) : f ≫ (1 : Y ⟶ M) = 1 :=
  ((yonedaMon.obj <| .mk' M).map f.op).hom.map_one

@[reassoc]
lemma Mon_Class.comp_mul (f : X ⟶ Y) (g₁ g₂ : Y ⟶ M) : f ≫ (g₁ * g₂) = f ≫ g₁ * f ≫ g₂ :=
  ((yonedaMon.obj <| .mk' M).map f.op).hom.map_mul _ _

variable (M) in
lemma Mon_Class.one_eq_one : η = (1 : _ ⟶ M) :=
  show _ = _ ≫ _ by rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

variable (M) in
lemma Mon_Class.mul_eq_mul : μ = fst M M * snd _ _ :=
  show _ = _ ≫ _ by rw [lift_fst_snd, Category.id_comp]
