/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.Descent.DescentDataDoublePrime
import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Bicategory.Adjunction.BaseChange

/-!
# Descent data as coalgebras...

-/

namespace CategoryTheory

open Opposite Limits Bicategory

namespace Pseudofunctor

variable {C : Type*} [Category C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) (Adj Cat))

namespace LocallyDiscreteToAdjCat

set_option quotPrecheck false in
scoped notation g:80 " _* " M:81 => ((_ : Pseudofunctor _ (Adj Cat)).map
  (Quiver.Hom.op g).toLoc).r.obj M

set_option quotPrecheck false in
scoped notation g:80 " ^* " M:81 => ((_ : Pseudofunctor _ (Adj Cat)).map
  (Quiver.Hom.op g).toLoc).l.obj M

end LocallyDiscreteToAdjCat

open LocallyDiscreteToAdjCat

@[ext]
structure DescentDataAsCoalgebra {ι : Type*} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) where
  obj (i : ι) : (F.obj (.mk (op (X i)))).obj
  hom (i₁ i₂ : ι) : obj i₁ ⟶ (f i₁) ^* (f i₂) _* (obj i₂)
  counit (i : ι) : hom i i ≫ (F.map (f i).op.toLoc).adj.counit.app _ = 𝟙 _ := by aesop_cat
  coassoc (i₁ i₂ i₃ : ι) :
    hom i₁ i₂ ≫ (F.map (f i₁).op.toLoc).l.map ((F.map (f i₂).op.toLoc).r.map (hom i₂ i₃)) =
      hom i₁ i₃ ≫
        (F.map (f i₁).op.toLoc).l.map ((F.map (f i₂).op.toLoc).adj.unit.app _) := by aesop_cat

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
      (F.map (f i₁).op.toLoc).l.map ((F.map (f i₂).op.toLoc).r.map (hom i₂)) =
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

@[simps]
def isoMk {D₁ D₂ : F.DescentDataAsCoalgebra f} (e : ∀ (i : ι), D₁.obj i ≅ D₂.obj i)
    (comm : ∀ (i₁ i₂ : ι), D₁.hom i₁ i₂ ≫
      (F.map (f i₁).op.toLoc).l.map ((F.map (f i₂).op.toLoc).r.map (e i₂).hom) =
      (e i₁).hom ≫ D₂.hom i₁ i₂ := by aesop_cat) :
    D₁ ≅ D₂ where
  hom.hom i := (e i).hom
  hom.comm := comm
  inv.hom i := (e i).inv
  inv.comm i₁ i₂ := by
    rw [← cancel_epi (e i₁).hom, ← reassoc_of% (comm i₁ i₂), ← Functor.map_comp, ← Functor.map_comp]
    simp

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

section

variable {F}

variable (A : F.DescentDataAsCoalgebra f)

open DescentData''

variable [∀ i₁ i₂, IsIso (F.baseChange (sq i₁ i₂).isPullback.toCommSq.flip.op.toLoc)]
  [∀ i₁ i₂ i₃, IsIso (F.baseChange (sq₃ i₁ i₂ i₃).isPullback₂.toCommSq.flip.op.toLoc)]

@[simps]
noncomputable
def toDescentDataAsCoalgebra : F.DescentData'' sq sq₃ ⥤ F.DescentDataAsCoalgebra f where
  obj D :=
    { obj := D.obj
      hom := dataEquivCoalgebra D.hom
      counit i := by
        obtain ⟨δ⟩ := inferInstanceAs (Nonempty (sq i i).Diagonal)
        rw [← hom_self_iff_dataEquivCoalgebra _ δ]
        exact D.hom_self i δ
      coassoc i₁ i₂ i₃ := by
        rw [← hom_comp_iff_dataEquivCoalgebra sq₃]
        exact D.hom_comp i₁ i₂ i₃ }
  map {D₁ D₂} g :=
    { hom := g.hom
      comm i₁ i₂ := by
        rw [← hom_comm_iff_dataEquivCoalgebra]
        exact g.comm i₁ i₂ }

set_option maxHeartbeats 400000 in
-- TODO: automation is slow here
@[simps]
noncomputable
def fromDescentDataAsCoalgebra : F.DescentDataAsCoalgebra f ⥤ F.DescentData'' sq sq₃ where
  obj D :=
    { obj := D.obj
      hom := dataEquivCoalgebra.symm D.hom
      hom_self i δ := by
        rw [hom_self_iff_dataEquivCoalgebra _ δ]
        simp
      hom_comp i₁ i₂ i₃ := by
        rw [hom_comp_iff_dataEquivCoalgebra sq₃]
        simp }
  map {D₁ D₂} g :=
    { hom := g.hom
      comm i₁ i₂ := by
        rw [hom_comm_iff_dataEquivCoalgebra]
        simp }

noncomputable
def equivDescentData'' : F.DescentDataAsCoalgebra f ≌ F.DescentData'' sq sq₃ where
  functor := fromDescentDataAsCoalgebra sq sq₃
  inverse := toDescentDataAsCoalgebra sq sq₃
  unitIso := NatIso.ofComponents
    (fun D ↦ isoMk (fun i ↦ Iso.refl _)
    (fun i₁ i₂ ↦ by simp [fromDescentDataAsCoalgebra]))
  counitIso := NatIso.ofComponents
    (fun D ↦ DescentData''.isoMk (fun i ↦ Iso.refl _)
    (fun i₁ i₂ ↦ by simp [toDescentDataAsCoalgebra]))

end

noncomputable
def descentData'Equivalence [∀ i₁ i₂, IsIso (F.baseChange (sq i₁ i₂).commSq.flip.op.toLoc)]
    [∀ i₁ i₂ i₃, IsIso (F.baseChange (sq₃ i₁ i₂ i₃).isPullback₂.toCommSq.flip.op.toLoc)] :
    F.DescentDataAsCoalgebra f ≌ (F.comp Adj.forget₁).DescentData' sq sq₃ :=
  (equivDescentData'' sq sq₃).trans (DescentData''.equivDescentData' sq₃)

end DescentDataAsCoalgebra

namespace DescentData'

variable {X S : C} {f : X ⟶ S} (sq : ChosenPullback f f) (sq₃ : ChosenPullback₃ sq sq sq)

noncomputable def equivalenceOfComonadicLeftAdjoint [IsIso (F.baseChange sq.commSq.flip.op.toLoc)]
    [IsIso (F.baseChange sq₃.isPullback₂.toCommSq.flip.op.toLoc)]
    [(Comonad.comparison (F.map f.op.toLoc).adj.toCategory).IsEquivalence] :
    (F.obj (.mk (op S))).obj ≌
      (F.comp Adj.forget₁).DescentData' (fun (_ : Unit) _ ↦ sq) (fun _ _ _ ↦ sq₃) :=
  (Comonad.comparison (F.map f.op.toLoc).adj.toCategory).asEquivalence.trans
    ((DescentDataAsCoalgebra.coalgebraEquivalence _ _).symm.trans
      (DescentDataAsCoalgebra.descentData'Equivalence _ _ _))

end DescentData'

namespace DescentData

variable {X S : C} (f : X ⟶ S) (sq : ChosenPullback f f) (sq₃ : ChosenPullback₃ sq sq sq)

noncomputable def equivalenceOfComonadicLeftAdjoint [IsIso (F.baseChange sq.commSq.flip.op.toLoc)]
    [IsIso (F.baseChange sq₃.isPullback₂.toCommSq.flip.op.toLoc)]
    [(Comonad.comparison (F.map f.op.toLoc).adj.toCategory).IsEquivalence] :
    (F.obj (.mk (op S))).obj ≌
      (F.comp Adj.forget₁).DescentData (fun (_ : Unit) ↦ f) :=
  (DescentData'.equivalenceOfComonadicLeftAdjoint F sq sq₃).trans
    (DescentData'.descentDataEquivalence (F.comp Adj.forget₁) _ _)

end DescentData

end Pseudofunctor

end CategoryTheory
