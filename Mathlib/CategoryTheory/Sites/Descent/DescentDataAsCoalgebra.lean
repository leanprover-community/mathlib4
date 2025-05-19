/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Bicategory.Adjunction.BaseChange

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

/-- A slightly reformulated characterisation of the composition condition in `DescentData'`. -/
lemma DescentData'.pullHom'_comp_pullHom'_eq_iff
    {C : Type*} [Category C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    {ι : Type*} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) (sq : ∀ i j, ChosenPullback (f i) (f j))
    (sq₃ : (i₁ i₂ i₃ : ι) → ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))
    (obj : ∀ i, F.obj (.mk (op (X i))))
    (hom : ∀ i j, (F.map (sq i j).p₁.op.toLoc).obj (obj i) ⟶
      (F.map (sq i j).p₂.op.toLoc).obj (obj j))
    {i₁ i₂ i₃ : ι} :
    DescentData'.pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂
        (by simp) (by simp) ≫
      DescentData'.pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃
        (by simp) (by simp) =
      DescentData'.pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃
        (by simp) (by simp) ↔
        (F.isoMapOfCommSq ⟨by simp [← Quiver.Hom.comp_toLoc, ← op_comp]⟩).hom.app _ ≫
        (F.map ((sq i₁ i₂).isPullback.lift
          (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ (by simp)).op.toLoc).map (hom i₁ i₂) ≫
        (F.isoMapOfCommSq ⟨by simp [← Quiver.Hom.comp_toLoc, ← op_comp]⟩).hom.app _ ≫
        (F.map ((sq i₂ i₃).isPullback.lift
          (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ (by simp)).op.toLoc).map (hom i₂ i₃) ≫
        (F.isoMapOfCommSq ⟨by simp [← Quiver.Hom.comp_toLoc, ← op_comp]⟩).hom.app _ =
        (F.map ((sq i₁ i₃).isPullback.lift
            (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ (by simp)).op.toLoc).map (hom i₁ i₃) := by
  dsimp [DescentData'.pullHom', LocallyDiscreteOpToCat.pullHom]
  simp only [Category.assoc]
  rw [← cancel_epi ((F.mapComp' (sq i₁ i₃).p₁.op.toLoc _ _ _).inv.app (obj i₁))]
  rw [Iso.inv_hom_id_app_assoc]
  rw [← cancel_mono ((F.mapComp' (sq i₁ i₃).p₂.op.toLoc _ _ _).hom.app _)]
  · simp_rw [Category.assoc]
    rw [Iso.inv_hom_id_app]
    simp only [Cat.comp_obj, Category.comp_id]
    rw [isoMapOfCommSq_eq, isoMapOfCommSq_eq, isoMapOfCommSq_eq]
    · simp only [Iso.trans_hom, Iso.symm_hom, Cat.comp_app, Cat.comp_obj, Category.assoc]
      rfl
    · simp [← Quiver.Hom.comp_toLoc, ← op_comp]
    · simp [← Quiver.Hom.comp_toLoc, ← op_comp]
    · simp [← Quiver.Hom.comp_toLoc, ← op_comp]

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

@[simps]
def descentData' : (F.comp Adj.forget₁).DescentData' sq sq₃ where
  obj := A.obj
  hom i j := F.coalgHom (sq i j).commSq.flip.op.toLoc (A.hom i j)
  pullHom'_hom_self i := by
    dsimp [DescentData'.pullHom', LocallyDiscreteOpToCat.pullHom]
    rw [map_coalgHom_of_comp_eq_id]
    · simp [A.counit]
    · simp [← Quiver.Hom.comp_toLoc, ← op_comp]
    · simp [← Quiver.Hom.comp_toLoc, ← op_comp]
  pullHom'_hom_comp i₁ i₂ i₃ := by
    rw [DescentData'.pullHom'_comp_pullHom'_eq_iff]
    simp only [comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
      PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj, Adj.forget₁_obj,
      Prefunctor.comp_map, Adj.forget₁_map, Cat.comp_obj]
    rw [coalgHom_eq_coalgHom_coalgHom (f₂ := (f i₂).op.toLoc) (A₂ := A.obj i₂)
      (u₁₂ := (sq i₁ i₂).p₁.op.toLoc) (u₂₁ := (sq i₁ i₂).p₂.op.toLoc)
      (u₂₃ := (sq i₂ i₃).p₁.op.toLoc) (u₃₂ := (sq i₂ i₃).p₂.op.toLoc)
      (p₁₂ := ((sq i₁ i₂).isPullback.lift (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ (by simp)).op.toLoc)
      (p₂₃ := ((sq i₂ i₃).isPullback.lift (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ (by simp)).op.toLoc)
      (sq₁₂ := (sq i₁ i₂).commSq.flip.op.toLoc) (sq₂₃ := (sq i₂ i₃).commSq.flip.op.toLoc)
      (sq₁₃ := (sq i₁ i₃).commSq.flip.op.toLoc)
      (a₁₂ := (A.hom i₁ i₂)) (a₂₃ := (A.hom i₂ i₃))]
    simp

@[simps]
def Hom.descentData' {D E : F.DescentDataAsCoalgebra f} (b : D ⟶ E) :
    D.descentData' sq sq₃ ⟶ E.descentData' sq sq₃ where
  hom := b.hom
  comm i₁ i₂ := by
    apply map_comp_coalgHom_eq_coalgHom_map
    exact b.comm i₁ i₂

@[simps]
def toDescentData' : F.DescentDataAsCoalgebra f ⥤ (F.comp Adj.forget₁).DescentData' sq sq₃ where
  obj := descentData' sq sq₃
  map {D E} b := b.descentData' sq sq₃

@[simps]
noncomputable
def ofDescentData' [∀ i₁ i₂, IsIso (F.baseChange (sq i₁ i₂).commSq.flip.op.toLoc)]
    (D : (F.comp Adj.forget₁).DescentData' sq sq₃) : F.DescentDataAsCoalgebra f where
  obj := D.obj
  hom i₁ i₂ := (F.coalgEquiv (sq i₁ i₂).commSq.flip.op.toLoc _ _).symm (D.hom i₁ i₂)
  counit i := by
    have := D.pullHom'_hom_self i
    dsimp [DescentData'.pullHom', LocallyDiscreteOpToCat.pullHom] at this
    rw [F.comp_counit_eq_id_iff _ _ _ (sq i i).commSq.flip.op.toLoc
      (((sq i i).isPullback.lift (𝟙 (X i)) (𝟙 (X i)) (by simp)).op.toLoc)]
    · simp only [comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
        PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj, Adj.forget₁_obj,
        Prefunctor.comp_map, Adj.forget₁_map, Cat.comp_obj]
      rw [← cancel_epi (((F.comp Adj.forget₁).mapComp' (sq i i).p₁.op.toLoc _ (𝟙 _) _).hom.app _)]
      · rw [← cancel_mono (((F.comp Adj.forget₁).mapComp' _ _ (𝟙 _) _).inv.app _)]
        · simp only [comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
            PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj, Adj.forget₁_obj,
            Prefunctor.comp_map, Adj.forget₁_map, Cat.comp_obj, Category.assoc,
            Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
          convert this
          apply (F.coalgEquiv _ (D.obj i) (D.obj i)).apply_symm_apply
        · simp [← Quiver.Hom.comp_toLoc, ← op_comp]
        · simp [← Quiver.Hom.comp_toLoc, ← op_comp]
  coassoc i₁ i₂ i₃ := by
    rw [F.coalgHom_eq_coalgHom_coalgHom_iff (sq i₁ i₂).commSq.flip.op.toLoc
      (sq i₂ i₃).commSq.flip.op.toLoc (sq i₁ i₃).commSq.flip.op.toLoc
      (p₁₂ := ((sq i₁ i₂).isPullback.lift (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ (by simp)).op.toLoc)
      (p₂₃ := ((sq i₂ i₃).isPullback.lift (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ (by simp)).op.toLoc)
      (p₁₃ := ((sq i₁ i₃).isPullback.lift (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ (by simp)).op.toLoc)]
    · have := D.pullHom'_hom_comp i₁ i₂ i₃
      rw [DescentData'.pullHom'_comp_pullHom'_eq_iff] at this
      simp only [comp_toPrelaxFunctor, PrelaxFunctor.comp_toPrelaxFunctorStruct,
        PrelaxFunctorStruct.comp_toPrefunctor, Prefunctor.comp_obj, Adj.forget₁_obj,
        Prefunctor.comp_map, Adj.forget₁_map, Cat.comp_obj] at this
      simp only [coalgHom_coalgEquiv_symm, comp_toPrelaxFunctor,
        PrelaxFunctor.comp_toPrelaxFunctorStruct, PrelaxFunctorStruct.comp_toPrefunctor,
        Prefunctor.comp_obj, Adj.forget₁_obj, Prefunctor.comp_map, Adj.forget₁_map, Cat.comp_obj]
      exact this.symm

lemma ofDescentData'_descentData' [∀ i₁ i₂, IsIso (F.baseChange (sq i₁ i₂).commSq.flip.op.toLoc)]
    (A : F.DescentDataAsCoalgebra f) :
    ofDescentData' sq sq₃ (descentData' sq sq₃ A) = A := by
  ext
  · simp
  · simp only [ofDescentData'_obj, descentData'_obj, heq_eq_eq]
    ext
    simp

@[simps]
noncomputable
def Hom.ofDescentData' [∀ i₁ i₂, IsIso (F.baseChange (sq i₁ i₂).commSq.flip.op.toLoc)]
    {D E : (F.comp Adj.forget₁).DescentData' sq sq₃} (f : D ⟶ E) :
    ofDescentData' sq sq₃ D ⟶ ofDescentData' sq sq₃ E where
  hom := f.hom
  comm i₁ i₂ := by
    rw [F.iff_map_comp_coalgHom_eq_coalgHom_map (sq i₁ i₂).commSq.flip.op.toLoc]
    simpa using f.comm i₁ i₂

end

-- needs "base change" assumptions
noncomputable
def descentData'Equivalence [∀ i₁ i₂, IsIso (F.baseChange (sq i₁ i₂).commSq.flip.op.toLoc)] :
    F.DescentDataAsCoalgebra f ≌ (F.comp Adj.forget₁).DescentData' sq sq₃ where
  functor := toDescentData' sq sq₃
  inverse.obj D := .ofDescentData' sq sq₃ D
  inverse.map f := .ofDescentData' sq sq₃ f
  unitIso := NatIso.ofComponents (fun A ↦ isoMk (fun i ↦ Iso.refl _)) <| fun _ ↦ by ext; simp
  counitIso := NatIso.ofComponents (fun A ↦ DescentData'.isoMk (fun i ↦ Iso.refl _))

end DescentDataAsCoalgebra

namespace DescentData'

variable {X S : C} {f : X ⟶ S} (sq : ChosenPullback f f) (sq₃ : ChosenPullback₃ sq sq sq)

-- needs "base change" assumptions
noncomputable def equivalenceOfComonadicLeftAdjoint [IsIso (F.baseChange sq.commSq.flip.op.toLoc)]
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
noncomputable def equivalenceOfComonadicLeftAdjoint [IsIso (F.baseChange sq.commSq.flip.op.toLoc)]
    [(Comonad.comparison (F.map f.op.toLoc).adj.toCategory).IsEquivalence] :
    (F.obj (.mk (op S))).obj ≌
      (F.comp Adj.forget₁).DescentData (fun (_ : Unit) ↦ f) :=
  (DescentData'.equivalenceOfComonadicLeftAdjoint F sq sq₃).trans
    (DescentData'.descentDataEquivalence (F.comp Adj.forget₁) _ _)

end DescentData

end Pseudofunctor

end CategoryTheory
