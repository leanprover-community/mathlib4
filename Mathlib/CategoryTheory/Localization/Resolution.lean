/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# Resolutions for a morphism of localizers

Given a morphism of localizers `Φ : LocalizerMorphism W₁ W₂` (i.e. `W₁` and `W₂` are
morphism properties on categories `C₁` and `C₂`, and we have a functor
`Φ.functor : C₁ ⥤ C₂` which sends morphisms in `W₁` to morphisms in `W₂`), we introduce
the notion of right resolutions of objects in `C₂`: if `X₂ : C₂`.
A right resolution consists of an object `X₁ : C₁` and a morphism
`w : X₂ ⟶ Φ.functor.obj X₁` that is in `W₂`. Then, the typeclass
`Φ.HasRightResolutions` holds when any `X₂ : C₂` has a right resolution.

The type of right resolutions `Φ.RightResolution X₂` is endowed with a category
structure when the morphism property `W₁` is multiplicative.

Similar definitions are done from left resolutions.

## Future works

* formalize right derivability structures as localizer morphisms admitting right resolutions
and forming a Guitart exact square, as it is defined in
[the paper by Kahn and Maltsiniotis][KahnMaltsiniotis2008] (TODO @joelriou)
* show that if `C` is an abelian category with enough injectives, there is a derivability
structure associated to the inclusion of the full subcategory of complexes of injective
objects into the bounded below homotopy category of `C` (TODO @joelriou)
* formalize dual results

## References
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

universe v₁ v₂ v₂' u₁ u₂ u₂'

namespace CategoryTheory

open Category Localization

variable {C₁ C₂ D₂ H : Type*} [Category C₁] [Category C₂] [Category D₂] [Category H]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂)

/-- The category of right resolutions of an object in the target category
of a localizer morphism. -/
structure RightResolution (X₂ : C₂) where
  /-- an object in the source category -/
  {X₁ : C₁}
  /-- a morphism to an object of the form `Φ.functor.obj X₁` -/
  w : X₂ ⟶ Φ.functor.obj X₁
  hw : W₂ w

/-- The category of left resolutions of an object in the target category
of a localizer morphism. -/
structure LeftResolution (X₂ : C₂) where
  /-- an object in the source category -/
  {X₁ : C₁}
  /-- a morphism from an object of the form `Φ.functor.obj X₁` -/
  w : Φ.functor.obj X₁ ⟶ X₂
  hw : W₂ w

variable {Φ X₂} in
lemma RightResolution.mk_surjective (R : Φ.RightResolution X₂) :
    ∃ (X₁ : C₁) (w : X₂ ⟶ Φ.functor.obj X₁) (hw : W₂ w), R = RightResolution.mk w hw :=
  ⟨_, R.w, R.hw, rfl⟩

variable {Φ X₂} in
lemma LeftResolution.mk_surjective (L : Φ.LeftResolution X₂) :
    ∃ (X₁ : C₁) (w : Φ.functor.obj X₁ ⟶ X₂) (hw : W₂ w), L = LeftResolution.mk w hw :=
  ⟨_, L.w, L.hw, rfl⟩

/-- A localizer morphism has right resolutions when any object has a right resolution. -/
abbrev HasRightResolutions := ∀ (X₂ : C₂), Nonempty (Φ.RightResolution X₂)

/-- A localizer morphism has right resolutions when any object has a right resolution. -/
abbrev HasLeftResolutions := ∀ (X₂ : C₂), Nonempty (Φ.LeftResolution X₂)

namespace RightResolution

variable {Φ} {X₂ : C₂}

/-- The type of morphisms in the category `Φ.RightResolution X₂` (when `W₁` is multiplicative). -/
@[ext]
structure Hom (R R' : Φ.RightResolution X₂) where
  /-- a morphism in the source category -/
  f : R.X₁ ⟶ R'.X₁
  hf : W₁ f
  comm : R.w ≫ Φ.functor.map f = R'.w := by aesop_cat

attribute [reassoc (attr := simp)] Hom.comm

/-- The identity of a object in `Φ.RightResolution X₂`. -/
@[simps]
def Hom.id [W₁.ContainsIdentities] (R : Φ.RightResolution X₂) : Hom R R where
  f := 𝟙 _
  hf := W₁.id_mem _

variable [W₁.IsMultiplicative]

/-- The composition of morphisms in `Φ.RightResolution X₂`. -/
@[simps]
def Hom.comp {R R' R'' : Φ.RightResolution X₂}
    (φ : Hom R R') (ψ : Hom R' R'') :
    Hom R R'' where
  f := φ.f ≫ ψ.f
  hf := W₁.comp_mem _ _ φ.hf ψ.hf

instance : Category (Φ.RightResolution X₂) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[simp]
lemma id_f (R : Φ.RightResolution X₂) : Hom.f (𝟙 R) = 𝟙 R.X₁ := rfl

@[simp, reassoc]
lemma comp_f {R R' R'' : Φ.RightResolution X₂} (φ : R ⟶ R') (ψ : R' ⟶ R'') :
    (φ ≫ ψ).f = φ.f ≫ ψ.f := rfl

@[ext]
lemma hom_ext {R R' : Φ.RightResolution X₂} {φ₁ φ₂ : R ⟶ R'} (h : φ₁.f = φ₂.f) :
    φ₁ = φ₂ :=
  Hom.ext h

@[simps]
def isoMk {R R' : Φ.RightResolution X₂} [W₁.RespectsIso] (e : R.X₁ ≅ R'.X₁)
    (comm : R.w ≫ Φ.functor.map e.hom = R'.w := by aesop_cat) : R ≅ R' where
  hom :=
    { f := e.hom
      hf := W₁.of_isIso _
      comm := comm }
  inv :=
    { f := e.inv
      hf := W₁.of_isIso _
      comm := by
        rw [← comm, Category.assoc, Iso.map_hom_inv_id, comp_id] }

end RightResolution

namespace LeftResolution

variable {Φ} {X₂ : C₂}

/-- The type of morphisms in the category `Φ.LeftResolution X₂` (when `W₁` is multiplicative). -/
@[ext]
structure Hom (L L' : Φ.LeftResolution X₂) where
  /-- a morphism in the source category -/
  f : L.X₁ ⟶ L'.X₁
  hf : W₁ f
  comm : Φ.functor.map f ≫ L'.w = L.w := by aesop_cat

attribute [reassoc (attr := simp)] Hom.comm

/-- The identity of a object in `Φ.LeftResolution X₂`. -/
@[simps]
def Hom.id [W₁.ContainsIdentities] (L : Φ.LeftResolution X₂) : Hom L L where
  f := 𝟙 _
  hf := W₁.id_mem _

variable [W₁.IsMultiplicative]

/-- The composition of morphisms in `Φ.LeftResolution X₂`. -/
@[simps]
def Hom.comp {L L' L'' : Φ.LeftResolution X₂}
    (φ : Hom L L') (ψ : Hom L' L'') :
    Hom L L'' where
  f := φ.f ≫ ψ.f
  hf := W₁.comp_mem _ _ φ.hf ψ.hf

instance : Category (Φ.LeftResolution X₂) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[simp]
lemma id_f (L : Φ.LeftResolution X₂) : Hom.f (𝟙 L) = 𝟙 L.X₁ := rfl

@[simp, reassoc]
lemma comp_f {L L' L'' : Φ.LeftResolution X₂} (φ : L ⟶ L') (ψ : L' ⟶ L'') :
    (φ ≫ ψ).f = φ.f ≫ ψ.f := rfl

@[ext]
lemma hom_ext {L L' : Φ.LeftResolution X₂} {φ₁ φ₂ : L ⟶ L'} (h : φ₁.f = φ₂.f) :
    φ₁ = φ₂ :=
  Hom.ext h

@[simps]
def isoMk {L L' : Φ.LeftResolution X₂} [W₁.RespectsIso] (e : L.X₁ ≅ L'.X₁)
    (comm : Φ.functor.map e.hom ≫ L'.w = L.w := by aesop_cat) : L ≅ L' where
  hom :=
    { f := e.hom
      hf := W₁.of_isIso _
      comm := comm }
  inv :=
    { f := e.inv
      hf := W₁.of_isIso _
      comm := by
        rw [← comm, Iso.map_inv_hom_id_assoc] }

end LeftResolution

variable {Φ}

/-- The canonical map `Φ.LeftResolution X₂ → Φ.op.RightResolution (Opposite.op X₂)`. -/
@[simps]
def LeftResolution.op {X₂ : C₂} (L : Φ.LeftResolution X₂) :
    Φ.op.RightResolution (Opposite.op X₂) where
  X₁ := Opposite.op L.X₁
  w := L.w.op
  hw := L.hw

/-- The canonical map `Φ.op.LeftResolution X₂ → Φ.RightResolution X₂`. -/
@[simps]
def LeftResolution.unop {X₂ : C₂ᵒᵖ} (L : Φ.op.LeftResolution X₂) :
    Φ.RightResolution X₂.unop where
  X₁ := Opposite.unop L.X₁
  w := L.w.unop
  hw := L.hw

/-- The canonical map `Φ.RightResolution X₂ → Φ.op.LeftResolution (Opposite.op X₂)`. -/
@[simps]
def RightResolution.op {X₂ : C₂} (L : Φ.RightResolution X₂) :
    Φ.op.LeftResolution (Opposite.op X₂) where
  X₁ := Opposite.op L.X₁
  w := L.w.op
  hw := L.hw

/-- The canonical map `Φ.op.RightResolution X₂ → Φ.LeftResolution X₂`. -/
@[simps]
def RightResolution.unop {X₂ : C₂ᵒᵖ} (L : Φ.op.RightResolution X₂) :
    Φ.LeftResolution X₂.unop where
  X₁ := Opposite.unop L.X₁
  w := L.w.unop
  hw := L.hw

variable (Φ)

lemma nonempty_leftResolution_iff_op (X₂ : C₂) :
    Nonempty (Φ.LeftResolution X₂) ↔ Nonempty (Φ.op.RightResolution (Opposite.op X₂)) :=
  Equiv.nonempty_congr
    { toFun := fun L => L.op
      invFun := fun R => R.unop
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

lemma nonempty_rightResolution_iff_op (X₂ : C₂) :
    Nonempty (Φ.RightResolution X₂) ↔ Nonempty (Φ.op.LeftResolution (Opposite.op X₂)) :=
  Equiv.nonempty_congr
    { toFun := fun R => R.op
      invFun := fun L => L.unop
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

lemma hasLeftResolutions_iff_op : Φ.HasLeftResolutions ↔ Φ.op.HasRightResolutions :=
  ⟨fun _ X₂ => ⟨(Classical.arbitrary (Φ.LeftResolution X₂.unop)).op⟩,
    fun _ X₂ => ⟨(Classical.arbitrary (Φ.op.RightResolution (Opposite.op X₂))).unop⟩⟩

lemma hasRightResolutions_iff_op : Φ.HasRightResolutions ↔ Φ.op.HasLeftResolutions :=
  ⟨fun _ X₂ => ⟨(Classical.arbitrary (Φ.RightResolution X₂.unop)).op⟩,
    fun _ X₂ => ⟨(Classical.arbitrary (Φ.op.LeftResolution (Opposite.op X₂))).unop⟩⟩

instance [Φ.HasRightResolutions] : Φ.op.HasLeftResolutions := by
  rwa [← hasRightResolutions_iff_op]

instance [Φ.HasLeftResolutions] : Φ.op.HasRightResolutions := by
  rwa [← hasLeftResolutions_iff_op]

/-- The functor `(Φ.LeftResolution X₂)ᵒᵖ ⥤ Φ.op.RightResolution (Opposite.op X₂)`. -/
@[simps]
def LeftResolution.opFunctor (X₂ : C₂) [W₁.IsMultiplicative] :
    (Φ.LeftResolution X₂)ᵒᵖ ⥤ Φ.op.RightResolution (Opposite.op X₂) where
  obj L := L.unop.op
  map φ :=
    { f := φ.unop.f.op
      hf := φ.unop.hf
      comm := Quiver.Hom.unop_inj φ.unop.comm }

/-- The functor `(Φ.op.RightResolution X₂)ᵒᵖ ⥤ Φ.LeftResolution X₂.unop`. -/
@[simps]
def RightResolution.unopFunctor (X₂ : C₂ᵒᵖ) [W₁.IsMultiplicative] :
    (Φ.op.RightResolution X₂)ᵒᵖ ⥤ Φ.LeftResolution X₂.unop where
  obj R := R.unop.unop
  map φ :=
    { f := φ.unop.f.unop
      hf := φ.unop.hf
      comm := Quiver.Hom.op_inj φ.unop.comm }

/-- The equivalence of categories
`(Φ.LeftResolution X₂)ᵒᵖ ≌ Φ.op.RightResolution (Opposite.op X₂)`. -/
@[simps]
def LeftResolution.opEquivalence (X₂ : C₂) [W₁.IsMultiplicative] :
    (Φ.LeftResolution X₂)ᵒᵖ ≌ Φ.op.RightResolution (Opposite.op X₂) where
  functor := LeftResolution.opFunctor Φ X₂
  inverse := (RightResolution.unopFunctor Φ (Opposite.op X₂)).rightOp
  unitIso := Iso.refl _
  counitIso := Iso.refl _

section

variable (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]

lemma essSurj_of_hasRightResolutions [Φ.HasRightResolutions] : (Φ.functor ⋙ L₂).EssSurj where
  mem_essImage X₂ := by
    have := Localization.essSurj L₂ W₂
    have R : Φ.RightResolution (L₂.objPreimage X₂) := Classical.arbitrary _
    exact ⟨R.X₁, ⟨(Localization.isoOfHom L₂ W₂ _ R.hw).symm ≪≫ L₂.objObjPreimageIso X₂⟩⟩

lemma isIso_iff_of_hasRightResolutions [Φ.HasRightResolutions] {F G : D₂ ⥤ H} (α : F ⟶ G) :
    IsIso α ↔ ∀ (X₁ : C₁), IsIso (α.app (L₂.obj (Φ.functor.obj X₁))) := by
  constructor
  · intros
    infer_instance
  · intro hα
    have : ∀ (X₂ : D₂), IsIso (α.app X₂) := fun X₂ => by
      have := Φ.essSurj_of_hasRightResolutions L₂
      rw [← NatTrans.isIso_app_iff_of_iso α ((Φ.functor ⋙ L₂).objObjPreimageIso X₂)]
      apply hα
    exact NatIso.isIso_of_isIso_app α

lemma essSurj_of_hasLeftResolutions [Φ.HasLeftResolutions] : (Φ.functor ⋙ L₂).EssSurj where
  mem_essImage X₂ := by
    have := Localization.essSurj L₂ W₂
    have L : Φ.LeftResolution (L₂.objPreimage X₂) := Classical.arbitrary _
    exact ⟨L.X₁, ⟨Localization.isoOfHom L₂ W₂ _ L.hw ≪≫ L₂.objObjPreimageIso X₂⟩⟩

lemma isIso_iff_of_hasLeftResolutions [Φ.HasLeftResolutions] {F G : D₂ ⥤ H} (α : F ⟶ G) :
    IsIso α ↔ ∀ (X₁ : C₁), IsIso (α.app (L₂.obj (Φ.functor.obj X₁))) := by
  constructor
  · intros
    infer_instance
  · intro hα
    have : ∀ (X₂ : D₂), IsIso (α.app X₂) := fun X₂ => by
      have := Φ.essSurj_of_hasLeftResolutions L₂
      rw [← NatTrans.isIso_app_iff_of_iso α ((Φ.functor ⋙ L₂).objObjPreimageIso X₂)]
      apply hα
    exact NatIso.isIso_of_isIso_app α

end

lemma hasRightResolutions_of_arrow [Φ.arrow.HasRightResolutions] :
    Φ.HasRightResolutions := fun X₂ => by
  let R : Φ.arrow.RightResolution (Arrow.mk (𝟙 X₂)) := Classical.arbitrary _
  exact
   ⟨{ w := R.w.left
      hw := R.hw.1 } ⟩

end LocalizerMorphism

end CategoryTheory
