/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Category.MonCat.Limits
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_

/-!
# Yoneda embedding of `Mon_ C`

We show that monoid objects are exactly those whose yoneda presheaf is a presheaf of monoids,
by constructing the yoneda embedding `Mon_ C ⥤ Cᵒᵖ ⥤ MonCat.{v}` and
showing that it is fully faithful and its (essential) image is the representable functors.

-/

open CategoryTheory MonoidalCategory Limits Opposite CartesianMonoidalCategory Mon_Class

universe w v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable (X : C)

section Mon_

/-- If `X` represents a presheaf of monoids, then `X` is a monoid object. -/
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

/-- If `X` is a monoid object, then `Hom(Y, X)` has a monoid structure. -/
@[reducible] def monoidOfMon_Class [Mon_Class X] (Y : C) : Monoid (Y ⟶ X) where
  mul f₁ f₂ := lift f₁ f₂ ≫ μ
  mul_assoc f₁ f₂ f₃ := by
    show lift (lift f₁ f₂ ≫ μ) f₃ ≫ μ = lift f₁ (lift f₂ f₃ ≫ μ) ≫ μ
    trans lift (lift f₁ f₂) f₃ ≫ (μ ▷ X) ≫ μ
    · rw [← tensorHom_id, lift_map_assoc, Category.comp_id]
    trans lift f₁ (lift f₂ f₃) ≫ (X ◁ μ) ≫ μ
    · rw [Mon_Class.mul_assoc]
      simp_rw [← Category.assoc]
      congr 2
      ext <;> simp
    · rw [← id_tensorHom, lift_map_assoc, Category.comp_id]
  one := toUnit Y ≫ η
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

attribute [local instance] monoidOfMon_Class

/-- If `X` is a monoid object, then `Hom(-, X)` is a presheaf of monoids. -/
@[simps]
def yonedaMonObj [Mon_Class X] : Cᵒᵖ ⥤ MonCat.{v} where
  obj Y := MonCat.of (unop Y ⟶ X)
  map {Y₁ Y₂} φ := MonCat.ofHom
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

/-- If `X` is a monoid object, then `Hom(-, X)` as a presheaf of monoids is represented by `X`. -/
def yonedaMonObjRepresentableBy [Mon_Class X] : (yonedaMonObj X ⋙ forget _).RepresentableBy X :=
  Functor.representableByEquiv.symm (Iso.refl _)

lemma Mon_Class.ofRepresentableBy_yonedaMonObjRepresentableBy [Mon_Class X] :
    Mon_Class.ofRepresentableBy X _ (yonedaMonObjRepresentableBy X) = ‹_› := by
  ext
  show lift (fst X X) (snd X X) ≫ μ = μ
  rw [lift_fst_snd, Category.id_comp]

@[deprecated (since := "2025-03-07")]
alias Mon_ClassOfRepresentableBy_yonedaMonObjRepresentableBy :=
  Mon_Class.ofRepresentableBy_yonedaMonObjRepresentableBy

/-- If `X` represents a presheaf of monoids `F`, then `Hom(-, X)` is isomorphic to `F` as
a presheaf of monoids. -/
@[simps!]
def yonedaMonObjMon_Class.ofRepresentableBy
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
  obj X := yonedaMonObj X.X
  map {X₁ X₂} ψ :=
  { app Y := MonCat.ofHom
      { toFun := (· ≫ ψ.hom)
        map_one' := by
          show (toUnit _ ≫ X₁.one) ≫ ψ.hom = toUnit _ ≫ X₂.one
          rw [Category.assoc, ψ.one_hom]
        map_mul' φ₁ φ₂ := by
          show (lift _ _ ≫ X₁.mul) ≫ _ = lift (_ ≫ _) (_ ≫ _) ≫ X₂.mul
          rw [Category.assoc, ψ.mul_hom, lift_map_assoc] }
    naturality {Y₁ Y₂} φ := MonCat.hom_ext (MonoidHom.ext fun f ↦ Category.assoc φ.unop f ψ.hom) }
  map_id X := NatTrans.ext (funext fun _ ↦ MonCat.hom_ext (MonoidHom.ext Category.comp_id))
  map_comp _ _ := NatTrans.ext (funext fun _ ↦
    MonCat.hom_ext (MonoidHom.ext (.symm <| Category.assoc · _ _)))

@[reassoc]
lemma yonedaMon_naturality {X₁ X₂ : C} [Mon_Class X₁] [Mon_Class X₂]
    (α : yonedaMonObj X₁ ⟶ yonedaMonObj X₂) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ X₁) :
      α.app _ (f ≫ g) = f ≫ α.app _ g := congr($(α.naturality f.op) g)

/-- The yoneda embedding for `Mon_C` is fully faithful. -/
def yonedaMonFullyFaithful : yonedaMon (C := C).FullyFaithful where
  preimage {X₁ X₂} α :=
  { hom := α.app (op X₁.X) (𝟙 X₁.X)
    one_hom := by
      dsimp only [yonedaMon_obj] at α ⊢
      rw [← yonedaMon_naturality, Category.comp_id,
        ← Category.id_comp X₁.one, toUnit_unique (𝟙 _) (toUnit _),
        ← Category.id_comp X₂.one, toUnit_unique (𝟙 _) (toUnit _)]
      exact (α.app _).hom.map_one
    mul_hom := by
      dsimp only [yonedaMon_obj] at α ⊢
      rw [← yonedaMon_naturality, Category.comp_id, ← Category.id_comp X₁.mul, ← lift_fst_snd]
      refine ((α.app _).hom.map_mul _ _).trans ?_
      show lift _ _ ≫ X₂.mul = _
      congr 1
      ext <;> simp only [lift_fst, tensorHom_fst, lift_snd, tensorHom_snd,
        ← yonedaMon_naturality, Category.comp_id] }
  map_preimage {X₁ X₂} α := by
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
  · rintro ⟨X, ⟨α⟩⟩
    exact ⟨X.X, ⟨Functor.representableByEquiv.symm (isoWhiskerRight α (forget _))⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    letI := Mon_Class.ofRepresentableBy X F e
    exact ⟨Mon_.mk' X, ⟨yonedaMonObjMon_Class.ofRepresentableBy X F e⟩⟩

end Mon_

section CommMon_

/-- If `X` represents a presheaf of commutative groups, then `X` is a commutative group object. -/
lemma IsCommMon.ofRepresentableBy [BraidedCategory C] (F : Cᵒᵖ ⥤ CommMonCat)
    (α : (F ⋙ forget _).RepresentableBy X) :
    letI := Mon_Class.ofRepresentableBy X (F ⋙ forget₂ CommMonCat MonCat) α
    IsCommMon X := by
  letI : Mon_Class X := Mon_Class.ofRepresentableBy X (F ⋙ forget₂ CommMonCat MonCat) α
  have : μ = α.homEquiv.symm (α.homEquiv (fst X X) * α.homEquiv (snd X X)) := rfl
  constructor
  simp_rw [this, ← α.homEquiv.apply_eq_iff_eq, α.homEquiv_comp, Functor.comp_map,
    ConcreteCategory.forget_map_eq_coe, Equiv.apply_symm_apply, map_mul,
    ← ConcreteCategory.forget_map_eq_coe, ← Functor.comp_map, ← α.homEquiv_comp, op_tensorObj,
    Functor.comp_obj, braiding_hom_fst, braiding_hom_snd, _root_.mul_comm]

end CommMon_
