import Mathlib.CategoryTheory.Localization.LocalizerMorphism

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Localization

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂)

structure RightResolution (X₂ : C₂) where
  {X₁ : C₁}
  w : X₂ ⟶ Φ.functor.obj X₁
  hw : W₂ w

class HasRightResolutions : Prop where
  nonempty_rightResolution (X₂ : C₂) : Nonempty (Φ.RightResolution X₂)

namespace RightResolution

variable {Φ} {X₂ : C₂}

@[ext]
structure Hom (R R' : Φ.RightResolution X₂) where
  f : R.X₁ ⟶ R'.X₁
  hf : W₁ f
  comm : R.w ≫ Φ.functor.map f = R'.w := by aesop_cat

attribute [reassoc (attr := simp)] Hom.comm

@[simps]
def Hom.id [W₁.ContainsIdentities] (R : Φ.RightResolution X₂) : Hom R R where
  f := 𝟙 _
  hf := W₁.id_mem _

@[simps]
def Hom.comp [W₁.IsMultiplicative] {R R' R'' : Φ.RightResolution X₂}
    (φ : Hom R R') (ψ : Hom R' R'') : Hom R R'' where
  f := φ.f ≫ ψ.f
  hf := W₁.comp_mem _ _ φ.hf ψ.hf

instance [W₁.IsMultiplicative] : Category (Φ.RightResolution X₂) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

end RightResolution

end LocalizerMorphism
