/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.CatCommSq

/-! # Morphisms of categorical cospans.

Given `F : A ⥤ B`, `G : C ⥤ B`, `F' : A' ⥤ B'` and `G' : C' ⥤ B'`,
this files defines `CatCospanTransform F G F' G'`, the category of
"categorical transformations" from the (categorical) cospan `F G` to
the (categorical) cospan `F' G'`. Such a transformation consists of a
diagram

```
    F   G
  A ⥤ B ⥢ C
H₁|   |H₂ |H₃
  v   v   v
  A'⥤ B'⥢ C'
    F'  G'
```

with specified `CatCommSq`s expressing 2-commutativity of the squares.
-/

namespace CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

/-- A `CatCospanTransform F G F' G'` is a diagram
```
    F   G
  A ⥤ B ⥢ C
H₁|   |H₂ |H₃
  v   v   v
  A'⥤ B'⥢ C'
    F'  G'
```
with specified `CatCommSq`s expressing 2-commutativity of the squares. This
is mainly a bookkeeping structure to avoid an explosion of parameter numbers. -/
structure CatCospanTransform
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    (F : A ⥤ B) (G : C ⥤ B)
    {A' : Type u₄} {B' : Type u₅} {C' : Type u₆}
    [Category.{v₄} A'] [Category.{v₅} B'] [Category.{v₆} C']
    (F' : A' ⥤ B') (G' : C' ⥤ B') where
  /-- The functor on the left component -/
  left : A ⥤ A'
  /-- The functor on the base component -/
  base : B ⥤ B'
  /-- The functor on the right component -/
  right : C ⥤ C'
  /-- A `CatCommSq` bundling the natural isomorphism `F ⋙ base ≅ left ⋙ F'`. -/
  squareLeft : CatCommSq F left base F' := by infer_instance
  /-- A `CatCommSq` bundling the natural isomorphism `G ⋙ base ≅ right ⋙ G'`. -/
  squareRight : CatCommSq G right base G' := by infer_instance

namespace CatCospanTransform

section

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  (F : A ⥤ B) (G : C ⥤ B)

attribute [local instance] CatCommSq.vId in
/-- The identitiy `CatCospanTransform` -/
@[simps]
def id : CatCospanTransform F G F G where
  left := 𝟭 A
  base := 𝟭 B
  right := 𝟭 C

variable {F G}
/-- Vertical composition of `CatCospanTransforms`. -/
@[simps!]
def vComp
  {A' : Type u₄} {B' : Type u₅} {C' : Type u₆}
  [Category.{v₄} A'] [Category.{v₅} B'] [Category.{v₆} C']
  {F' : A' ⥤ B'} {G' : C' ⥤ B'}
  {A'' : Type u₇} {B'' : Type u₈} {C'' : Type u₉}
  [Category.{v₇} A''] [Category.{v₈} B''] [Category.{v₉} C'']
  {F'' : A'' ⥤ B''} {G'' : C'' ⥤ B''}
  (ψ : CatCospanTransform F G F' G') (ψ' : CatCospanTransform F' G' F'' G'') :
    CatCospanTransform F G F'' G'' where
  left := ψ.left ⋙ ψ'.left
  base := ψ.base ⋙ ψ'.base
  right := ψ.right ⋙ ψ'.right
  squareLeft := ψ.squareLeft.vComp' (ψ'.squareLeft)
  squareRight := ψ.squareRight.vComp' (ψ'.squareRight)

end

end CatCospanTransform

/-- A `CatCospanEquiv F G F' G'` is a diagram
```
    F   G
  A ⥤ B ⥢ C
H₁|   |H₂ |H₃
  v   v   v
  A'⥤ B'⥢ C'
    F'  G'
```
where H₁, H₂ and H₃ are equivalences, along with commutative 2-squares structure on the
squares in the forward direction. -/
structure CatCospanEquivalence
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : C ⥤ B)
    {A' B' C' : Type*} [Category A'] [Category B'] [Category C']
    (F' : A' ⥤ B') (G' : C' ⥤ B') where
  /-- The functor on the left component -/
  left : A ≌ A'
  /-- The functor on the base component -/
  base : B ≌ B'
  /-- The functor on the right component -/
  right : C ≌ C'
  /-- A `CatCommSq` bundling the natural isomorphism `F ⋙ base ≅ left ⋙ F'`. -/
  squareLeft : CatCommSq F left.functor base.functor F' := by infer_instance
  /-- A `CatCommSq` bundling the natural isomorphism `G ⋙ base ≅ right ⋙ G'`. -/
  squareRight : CatCommSq G right.functor base.functor G' := by infer_instance

namespace CatCospanEquivalence

variable {A B C : Type*} [Category A] [Category B] [Category C]
  (F : A ⥤ B) (G : C ⥤ B)

/-- The identitiy `CatCospanTransform` -/
@[simps!]
def refl : CatCospanEquivalence F G F G where
  left := Equivalence.refl
  base := Equivalence.refl
  right := Equivalence.refl
  squareLeft := CatCommSq.vId _
  squareRight := CatCommSq.vId _

variable {F G}

variable {A' B' C' : Type*} [Category A'] [Category B'] [Category C']
  {F' : A' ⥤ B'} {G' : C' ⥤ B'}

/-- The `CatCospanTransform` formed by the functors of the components
of a `CatCospanEquivalence`. -/
@[simps!]
def functor (ψ : CatCospanEquivalence F G F' G') : CatCospanTransform F G F' G' where
  left := ψ.left.functor
  base := ψ.base.functor
  right := ψ.right.functor
  squareLeft := ψ.squareLeft
  squareRight := ψ.squareRight

/-- The `CatCospanTransform` formed by the inverses of the components
of a `CatCospanEquivalence`. -/
@[simps!]
def inverse (ψ : CatCospanEquivalence F G F' G') : CatCospanTransform F' G' F G where
  left := ψ.left.inverse
  base := ψ.base.inverse
  right := ψ.right.inverse
  squareLeft := CatCommSq.vInv _ _ _ _ ψ.squareLeft
  squareRight := CatCommSq.vInv _ _ _ _ ψ.squareRight

end CatCospanEquivalence

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
    {A' : Type u₄} {B' : Type u₅} {C' : Type u₆}
    {A'' : Type u₇} {B'' : Type u₈} {C'' : Type u₉}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] {F : A ⥤ B} {G : C ⥤ B}
    [Category.{v₄} A'] [Category.{v₅} B'] [Category.{v₆} C'] {F' : A' ⥤ B'} {G' : C' ⥤ B'}
    [Category.{v₇} A''] [Category.{v₈} B''] [Category.{v₅} C''] {F'' : A'' ⥤ B''} {G'' : C'' ⥤ B''}

/-- A morphism of `CatCospanTransform F G F' G'` is a triple of natural
transformations between the component functors, subjects to
coherence conditions respective to the squares. -/
structure CatCospanTransformMorphism
    (ψ ψ' : CatCospanTransform F G F' G') where
  /- the natural transformations between the left components -/
  left : ψ.left ⟶ ψ'.left
  /- the natural transformations between the right components -/
  right : ψ.right ⟶ ψ'.right
  /- the natural transformations between the base components -/
  base : ψ.base ⟶ ψ'.base
  /- the coherence condition for the left square -/
  left_coherence :
    ψ.squareLeft.iso.hom ≫ whiskerRight left F' =
    whiskerLeft F base ≫ ψ'.squareLeft.iso.hom := by aesop_cat
  right_coherence :
    ψ.squareRight.iso.hom ≫ whiskerRight right G' =
    whiskerLeft G base ≫ ψ'.squareRight.iso.hom := by aesop_cat

attribute [reassoc (attr := simp)]
  CatCospanTransformMorphism.left_coherence
  CatCospanTransformMorphism.right_coherence

-- attribute [local simp] CatCospanTransformMorphism.base_eq

@[simps!]
instance : Category (CatCospanTransform F G F' G') where
  Hom ψ ψ' := CatCospanTransformMorphism ψ ψ'
  id ψ :=
    { left := 𝟙 _
      right := 𝟙 _
      base := 𝟙 _ }
  comp α β :=
    { left := α.left ≫ β.left
      right := α.right ≫ β.right
      base := α.base ≫ β.base}

attribute [local ext] CatCospanTransformMorphism in
@[ext]
lemma hom_ext {ψ ψ' : CatCospanTransform F G F' G'} {θ θ': ψ ⟶ ψ'}
    (hl : θ.left = θ'.left) (hr : θ.right = θ'.right) (hb : θ.base = θ'.base) :
    θ = θ' := by
  apply CatCospanTransformMorphism.ext <;> assumption

namespace CatCospanTransformMorphism

@[reassoc (attr := simp)]
lemma left_coherence_app {ψ ψ' : CatCospanTransform F G F' G'} (α : ψ ⟶ ψ') (x : A) :
    ψ.squareLeft.iso.hom.app x ≫ F'.map (α.left.app x) =
    α.base.app (F.obj x) ≫ ψ'.squareLeft.iso.hom.app x :=
  congr_app α.left_coherence x

@[reassoc (attr := simp)]
lemma right_coherence_app {ψ ψ' : CatCospanTransform F G F' G'} (α : ψ ⟶ ψ') (x : C) :
    ψ.squareRight.iso.hom.app x ≫ G'.map (α.right.app x) =
    α.base.app (G.obj x) ≫ ψ'.squareRight.iso.hom.app x :=
  congr_app α.right_coherence x

/-- Whiskering left a `CatCospanTransformMorphism` by a `CatCospanTransform`. -/
@[simps]
def whiskerLeft (φ : CatCospanTransform F G F' G') {ψ ψ' : CatCospanTransform F' G' F'' G''}
    (α : ψ ⟶ ψ') :
    (φ.vComp ψ) ⟶ (φ.vComp ψ') where
  left := CategoryTheory.whiskerLeft φ.left α.left
  right := CategoryTheory.whiskerLeft φ.right α.right
  base := CategoryTheory.whiskerLeft φ.base α.base

/-- Whiskering right a `CatCospanTransformMorphism` by a `CatCospanTransform`. -/
@[simps]
def whiskerRight {ψ ψ': CatCospanTransform F G F' G'} (α : CatCospanTransformMorphism ψ ψ')
    (φ : CatCospanTransform F' G' F'' G'') :
    (ψ.vComp φ) ⟶ (ψ'.vComp φ) where
  left := CategoryTheory.whiskerRight α.left φ.left
  right := CategoryTheory.whiskerRight α.right φ.right
  base := CategoryTheory.whiskerRight α.base φ.base
  left_coherence := by
    ext x
    dsimp
    simp only [CatCommSq.vComp_iso'_hom_app, Category.assoc]
    rw [← Functor.map_comp_assoc, ← left_coherence_app, Functor.map_comp_assoc]
    simp [CatCommSq.iso_hom_naturality]
  right_coherence := by
    ext x
    dsimp
    simp only [CatCommSq.vComp_iso'_hom_app, Category.assoc]
    rw [← Functor.map_comp_assoc, ← right_coherence_app, Functor.map_comp_assoc]
    simp [CatCommSq.iso_hom_naturality]

  -- left := α.left.vPaste (CatCommSqIso.id φ.squareLeft)
  -- right := α.right.vPaste (CatCommSqIso.id φ.squareRight)

end CatCospanTransformMorphism

namespace CatCospanTransform

@[simps]
def leftUnitor (φ : CatCospanTransform F G F' G') :
    (CatCospanTransform.id F G).vComp φ ≅ φ where
  hom :=
    { left := φ.squareLeft.vLeftUnitor
      right := φ.squareRight.vLeftUnitor }
  inv :=
    { left := φ.squareLeft.vLeftUnitor.symm
      right := φ.squareRight.vLeftUnitor.symm }

@[simps]
def rightUnitor (φ : CatCospanTransform F G F' G') :
    φ.vComp (.id F' G') ≅ φ where
  hom :=
    { left := φ.squareLeft.vRightUnitor
      right := φ.squareRight.vRightUnitor }
  inv :=
    { left := φ.squareLeft.vRightUnitor.symm
      right := φ.squareRight.vRightUnitor.symm }

@[simps!]
def associator {A''' B''' C''' : Type*} [Category A'''] [Category B'''] [Category C''']
    {F''' : A''' ⥤ B'''} {G''' : C''' ⥤ B'''}
    (φ : CatCospanTransform F G F' G') (φ' : CatCospanTransform F' G' F'' G'')
    (φ'' : CatCospanTransform F'' G'' F''' G''') :
    (φ.vComp φ').vComp φ'' ≅ φ.vComp (φ'.vComp φ'') where
  hom :=
    { left := CatCommSq.vAssociator _ _ _
      right := CatCommSq.vAssociator _ _ _ }
  inv :=
    { left := CatCommSq.vAssociator _ _ _|>.symm
      right := CatCommSq.vAssociator _ _ _|>.symm }

end CatCospanTransform

namespace CatCospanEquivalence

variable (ψ : CatCospanEquivalence F G F' G')

/-- Bundle the units of the components of a `CatCospanEquivalence` into a
morphism of `CatCospanTransforms`. -/
@[simps!]
def unitIso :
    CatCospanTransform.id F G ≅ ψ.functor.vComp ψ.inverse where
  hom :=
    { left := ψ.squareLeft.vUnit
      right := ψ.squareRight.vUnit }
  inv :=
    { left := ψ.squareLeft.vUnit.symm
      right := ψ.squareRight.vUnit.symm }

/-- Bundle the counits of the components of a `CatCospanEquivalence` into a
morphism of `CatCospanTransforms`. -/
@[simps!]
def counitIso :
    ψ.inverse.vComp ψ.functor ≅ CatCospanTransform.id F' G' where
  hom :=
    { left := ψ.squareLeft.vCounit
      right := ψ.squareRight.vCounit }
  inv :=
    { left := ψ.squareLeft.vCounit.symm
      right := ψ.squareRight.vCounit.symm }

end CatCospanEquivalence

end CategoryTheory.Limits
