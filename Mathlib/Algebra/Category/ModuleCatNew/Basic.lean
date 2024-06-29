import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic

open CategoryTheory

universe v u

attribute [local instance] ConcreteCategory.instFunLike

variable (R : Type u) [Ring R]

structure ModuleCatNew where
  carrier : Type v
  addCommGroup : AddCommGroup carrier := by infer_instance
  module : Module R carrier := by infer_instance

namespace ModuleCatNew

variable {R}
variable (M M₁ M₂ M₃ : ModuleCatNew.{v} R)

instance : CoeSort (ModuleCatNew.{v} R) (Type v) := ⟨carrier⟩
attribute [coe] carrier

instance : AddCommGroup M := M.addCommGroup
instance : Module R M := M.module

structure Hom where
  linearMap : M₁ →ₗ[R] M₂

variable {M₁ M₂ M₃}

namespace Hom

@[simps]
def id : Hom M M where
  linearMap := LinearMap.id

@[simps]
def comp (f : Hom M₁ M₂) (g : Hom M₂ M₃) : Hom M₁ M₃ where
  linearMap := g.linearMap.comp f.linearMap

end Hom

instance : Category (ModuleCatNew.{v} R) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[simp]
lemma id_linearMap : Hom.linearMap (𝟙 M) = LinearMap.id := rfl

@[simp]
lemma comp_linearMap (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) :
    (f ≫ g).linearMap = g.linearMap.comp f.linearMap := rfl

variable (R) in
@[simps obj]
def forget : ModuleCatNew.{v} R ⥤ Type v where
  obj M := M
  map {M₁ M₂} f x := f.linearMap x

instance : (forget.{v} R).Faithful where
  map_injective {M₁ M₂ f g} h:= by
    obtain ⟨f⟩ := f
    obtain ⟨g⟩ := g
    suffices f = g by rw [this]
    ext x
    exact congr_fun h x

instance : ConcreteCategory (ModuleCatNew.{v} R) where
  forget := forget R

variable (R) in
@[simps]
def of (X : Type v) [AddCommGroup X] [Module R X] : ModuleCatNew.{v} R where
  carrier := X

lemma unbundle (M : ModuleCatNew.{v} R) :
    ∃ (X : Type v) (_ : AddCommGroup X) (_ : Module R X), M = of R X :=
  ⟨M, _, _, rfl⟩

section

variable {X Y : Type v} [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y]

@[simps]
def homMk (f : X →ₗ[R] Y) : of R X ⟶ of R Y where
  linearMap := f

@[simp]
lemma homMk_apply (f : X →ₗ[R] Y) (x : X) : homMk f x = f x := rfl

lemma unbundle_hom (f : of R X ⟶ of R Y) : ∃ (φ : X →ₗ[R] Y), f = homMk φ := ⟨_, rfl⟩

end

@[ext 1100]
lemma hom_ext {M₁ M₂ : ModuleCatNew.{v} R} {f g : M₁ ⟶ M₂} (h : ∀ (x : M₁), f x = g x) :
    f = g := by
  ext x
  exact h x

lemma hom_ext'
    {M₁ M₂ : ModuleCatNew.{v} R} {f g : M₁ ⟶ M₂} (h : f.linearMap = g.linearMap) :
    f = g :=
  by cases f; cases g; subst h; rfl

@[simp]
lemma hom_mk_apply {M₁ M₂ : ModuleCatNew.{u} R} (f : M₁ →ₗ[R] M₂) (x : M₁) :
    letI g : M₁ ⟶ M₂ := { linearMap := f }; g x = f x := rfl

example {M₁ M₂ M₃ : ModuleCatNew.{v} R} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (x : M₁) :
    (f ≫ g) x = g (f x) := by
  obtain ⟨M₁, _, _, rfl⟩ := unbundle M₁
  obtain ⟨M₂, _, _, rfl⟩ := unbundle M₂
  obtain ⟨M₃, _, _, rfl⟩ := unbundle M₃
  obtain ⟨f, rfl⟩ := unbundle_hom f
  obtain ⟨g, rfl⟩ := unbundle_hom g
  simp

@[simp]
lemma id_apply {M : ModuleCatNew.{v} R} (x : M) :
    (𝟙 M) x = x := rfl

example {M₁ M₂ M₃ : ModuleCatNew.{v} R} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (x : M₁) :
    (f ≫ g) x = g (f x) := by
  simp

end ModuleCatNew
