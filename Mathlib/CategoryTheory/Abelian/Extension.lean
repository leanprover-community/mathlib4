import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

universe v u

open CategoryTheory
open ZeroObject

namespace CategoryTheory.Abelian
variable {C : Type u} [Category.{v} C] [Abelian C]

structure Extension (X Y : C) where
  Z : C
  ι : X ⟶ Z
  π : Z ⟶ Y
  hι : Mono ι
  hιπ : Exact ι π
  hπ : Epi π

instance {X Y : C} (E : Extension X Y) : Mono E.ι :=
E.hι

instance {X Y : C} (E : Extension X Y) : Epi E.π :=
E.hπ

@[ext]
structure ExtensionMorphism {X Y : C} (E E' : Extension X Y) where
  f : E.Z ⟶ E'.Z
  hf₁ : E.ι ≫ f = E'.ι := by aesop_cat
  hf₂ : f ≫ E'.π = E.π := by aesop_cat

namespace ExtensionMorphism

@[reassoc (attr := simp)]
lemma ιComp {X Y : C} {E E' : Extension X Y} (f : ExtensionMorphism E E') : E.ι ≫ f.f = E'.ι :=
f.hf₁

@[reassoc (attr := simp)]
lemma compπ {X Y : C} {E E' : Extension X Y} (f : ExtensionMorphism E E') : f.f ≫ E'.π = E.π :=
f.hf₂

@[simps]
def id {X Y : C} (E : Extension X Y) : ExtensionMorphism E E where
  f := 𝟙 _

@[simps]
def comp {X Y : C} {E E' E'' : Extension X Y} (f : ExtensionMorphism E E')
    (g : ExtensionMorphism E' E'') : ExtensionMorphism E E'' where
  f := f.f ≫ g.f

end ExtensionMorphism

instance {X Y : C} : Category (Extension X Y) where
  Hom := fun E E' => ExtensionMorphism E E'
  id := fun E => ExtensionMorphism.id E
  comp := fun f g => ExtensionMorphism.comp f g

@[reassoc (attr := simp)]
lemma Extension.comp_f {X Y : C} {E E' E'' : Extension X Y} (f : E ⟶ E') (g : E' ⟶ E'') :
  (f ≫ g).f = f.f ≫ g.f :=
rfl

@[simp]
lemma Extension.id_f {X Y : C} (E : Extension X Y) : (𝟙 E : ExtensionMorphism E E).f = 𝟙 E.Z :=
rfl

@[ext]
lemma Extension.ext {X Y : C} {E E' : Extension X Y} (f g : E ⟶ E') : f.f = g.f → f = g :=
ExtensionMorphism.ext _ _

instance Extension.isIso {X Y : C} (E E' : Extension X Y) (f : E ⟶ E') : IsIso f.f := by
  apply isIso_of_isIso_of_isIso_of_isIso_of_isIso
    (f := (0 : 0 ⟶ X))
    (g := E.ι)
    (h := E.π)
    (i := (0 : Y ⟶ 0))
    (f' := (0 : 0 ⟶ X))
    (g' := E'.ι)
    (h' := E'.π)
    (i' := (0 : Y ⟶ 0))
    (α := 0)
    (β := 𝟙 X)
    (γ := f.f)
    (δ := 𝟙 Y)
    (ε := 0)
  · simp
  · simp
  · simp
  · simp
  · apply exact_zero_left_of_mono
  · exact E.hιπ
  · exact ((tfae_epi 0 E.π).out 0 2).1 E.hπ
  · apply exact_zero_left_of_mono
  · exact E'.hιπ
  · exact ((tfae_epi 0 E'.π).out 0 2).1 E'.hπ

@[simps]
noncomputable def Extension.inv {X Y : C} {E E' : Extension X Y} (f : E ⟶ E') : E' ⟶ E where
  f := CategoryTheory.inv f.f

noncomputable instance {X Y : C} : Groupoid (Extension X Y) where
  inv := Extension.inv

end CategoryTheory.Abelian
