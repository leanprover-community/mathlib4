/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Descent data as coalgebras...

-/

namespace CategoryTheory

@[simps]
def Bicategory.Adjunction.toCategory {C D : Cat} {F : C ⟶ D} {G : D ⟶ C}
    (adj : Bicategory.Adjunction F G) :
    CategoryTheory.Adjunction F G where
  unit := adj.unit
  counit := adj.counit
  left_triangle_components X := by
    have := congr_app adj.left_triangle X
    dsimp [leftZigzag, bicategoricalComp] at this
    simpa [Cat.associator_hom_app, Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app] using this
  right_triangle_components X := by
    have := congr_app adj.right_triangle X
    dsimp [rightZigzag, bicategoricalComp] at this
    simpa [Cat.associator_inv_app, Cat.leftUnitor_inv_app] using this

open Opposite Limits Bicategory

namespace Pseudofunctor

variable {C : Type*} [Category C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) (Adj Cat))

namespace LocallyDiscreteToAdjCat

set_option quotPrecheck false in
scoped notation g:80 " _* " M:81 => ((_ : Pseudofunctor _ (Adj Cat)).map
  (Quiver.Hom.op g).toLoc).g.obj M

set_option quotPrecheck false in
scoped notation g:80 " ^* " M:81 => ((_ : Pseudofunctor _ (Adj Cat)).map
  (Quiver.Hom.op g).toLoc).f.obj M

end LocallyDiscreteToAdjCat

open LocallyDiscreteToAdjCat

structure DescentDataAsCoalgebra {ι : Type*} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) where
  obj (i : ι) : (F.obj (.mk (op (X i)))).obj
  hom (i₁ i₂ : ι) : obj i₁ ⟶ (f i₁) ^* (f i₂) _* (obj i₂)
  counit (i : ι) : hom i i ≫ (F.map (f i).op.toLoc).adj.counit.app _ = 𝟙 _ := by aesop_cat
  coassoc (i₁ i₂ i₃ : ι) :
    hom i₁ i₂ ≫ (F.map (f i₁).op.toLoc).f.map ((F.map (f i₂).op.toLoc).g.map (hom i₂ i₃)) =
      hom i₁ i₃ ≫
        (F.map (f i₁).op.toLoc).f.map ((F.map (f i₂).op.toLoc).adj.unit.app _) := by aesop_cat

namespace DescentDataAsCoalgebra

attribute [reassoc (attr := simp)] counit coassoc
variable {F}

section

variable {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

@[ext]
structure Hom (D₁ D₂ : F.DescentDataAsCoalgebra f) where
  hom (i : ι) : D₁.obj i ⟶ D₂.obj i
  comm (i₁ i₂ : ι) :
    D₁.hom i₁ i₂ ≫
      (F.map (f i₁).op.toLoc).f.map ((F.map (f i₂).op.toLoc).g.map (hom i₂)) =
    hom i₁ ≫ D₂.hom i₁ i₂ := by aesop_cat

attribute [reassoc (attr := simp)] Hom.comm

@[simps]
def Hom.id (D : F.DescentDataAsCoalgebra f) : Hom D D where
  hom _ := 𝟙 _

@[simps]
def Hom.comp {D₁ D₂ D₃ : F.DescentDataAsCoalgebra f} (φ : Hom D₁ D₂) (φ' : Hom D₂ D₃) :
    Hom D₁ D₃ where
  hom i := φ.hom i ≫ φ'.hom i

instance : Category (F.DescentDataAsCoalgebra f) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[ext]
lemma hom_ext {D₁ D₂ : F.DescentDataAsCoalgebra f} {φ φ' : D₁ ⟶ D₂}
    (h : ∀ i, φ.hom i = φ'.hom i): φ = φ' :=
  Hom.ext (funext h)

@[simp]
lemma id_hom (D : F.DescentDataAsCoalgebra f) (i : ι) :
    Hom.hom (𝟙 D) i = 𝟙 _ := rfl

@[reassoc, simp]
lemma comp_hom {D₁ D₂ D₃ : F.DescentDataAsCoalgebra f} (φ : D₁ ⟶ D₂) (φ' : D₂ ⟶ D₃) (i : ι) :
    (φ ≫ φ').hom i = φ.hom i ≫ φ'.hom i := rfl

end

section Unit

variable {X S : C} {f : X ⟶ S}

@[simps]
def toCoalgebra (D : F.DescentDataAsCoalgebra (fun (_ : Unit) ↦ f)) :
    (F.map f.op.toLoc).adj.toCategory.toComonad.Coalgebra where
  A := D.obj .unit
  a := D.hom .unit .unit

@[simps]
def ofCoalgebra (A : (F.map f.op.toLoc).adj.toCategory.toComonad.Coalgebra) :
    F.DescentDataAsCoalgebra (fun (_ : Unit) ↦ f) where
  obj _ := A.A
  hom _ _ := A.a
  counit _ := A.counit
  coassoc _ _ _ := A.coassoc.symm

variable (F f)

@[simps]
def toCoalgebraFunctor :
    F.DescentDataAsCoalgebra (fun (_ : Unit) ↦ f) ⥤
    (F.map f.op.toLoc).adj.toCategory.toComonad.Coalgebra where
  obj D := D.toCoalgebra
  map φ := { f := φ.hom .unit }

@[simps]
def fromCoalgebraFunctor :
    (F.map f.op.toLoc).adj.toCategory.toComonad.Coalgebra ⥤
      F.DescentDataAsCoalgebra (fun (_ : Unit) ↦ f) where
  obj A := ofCoalgebra A
  map φ :=
    { hom _ := φ.f
      comm _ _ := φ.h }

@[simps]
def coalgebraEquivalence :
    F.DescentDataAsCoalgebra (fun (_ : Unit) ↦ f) ≌
    (F.map f.op.toLoc).adj.toCategory.toComonad.Coalgebra where
  functor := toCoalgebraFunctor F f
  inverse := fromCoalgebraFunctor F f
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end Unit

variable (F) {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))

-- needs "base change" assumptions
def descentData'Equivalence :
    F.DescentDataAsCoalgebra f ≌ (F.comp Adj.forget₁).DescentData' sq sq₃ := by
  sorry

end DescentDataAsCoalgebra

namespace DescentData'

variable {X S : C} {f : X ⟶ S} (sq : ChosenPullback f f) (sq₃ : ChosenPullback₃ sq sq sq)

-- needs "base change" assumptions
noncomputable def equivalenceOfComonadicLeftAdjoint
    [(Comonad.comparison (F.map f.op.toLoc).adj.toCategory).IsEquivalence] :
    (F.obj (.mk (op S))).obj ≌
      (F.comp Adj.forget₁).DescentData' (fun (_ : Unit) _ ↦ sq) (fun _ _ _ ↦ sq₃) :=
  (Comonad.comparison (F.map f.op.toLoc).adj.toCategory).asEquivalence.trans
    ((DescentDataAsCoalgebra.coalgebraEquivalence _ _).symm.trans
      (DescentDataAsCoalgebra.descentData'Equivalence _ _ _))

end DescentData'

namespace DescentData

variable {X S : C} (f : X ⟶ S) (sq : ChosenPullback f f) (sq₃ : ChosenPullback₃ sq sq sq)

-- needs "base change" assumptions
noncomputable def equivalenceOfComonadicLeftAdjoint
    [(Comonad.comparison (F.map f.op.toLoc).adj.toCategory).IsEquivalence] :
    (F.obj (.mk (op S))).obj ≌
      (F.comp Adj.forget₁).DescentData (fun (_ : Unit) ↦ f) :=
  (DescentData'.equivalenceOfComonadicLeftAdjoint F sq sq₃).trans
    (DescentData'.descentDataEquivalence (F.comp Adj.forget₁) _ _)

end DescentData

end Pseudofunctor

end CategoryTheory
