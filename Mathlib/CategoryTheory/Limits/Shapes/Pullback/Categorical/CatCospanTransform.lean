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

with specified `CatCommSq`s expressing 2-commutativity of the squares. These
transformations are used to encode 2-functoriality of categorical pullback squares.
-/

namespace CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂

/-- A `CatCospanTransform F G F' G'` is a diagram
```
    F   G
  A ⥤ B ⥢ C
H₁|   |H₂ |H₃
  v   v   v
  A'⥤ B'⥢ C'
    F'  G'
```
with specified `CatCommSq`s expressing 2-commutativity of the squares. -/
structure CatCospanTransform
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    (F : A ⥤ B) (G : C ⥤ B)
    {A' : Type u₄} {B' : Type u₅} {C' : Type u₆}
    [Category.{v₄} A'] [Category.{v₅} B'] [Category.{v₆} C']
    (F' : A' ⥤ B') (G' : C' ⥤ B') where
  /-- the functor on the left component -/
  left : A ⥤ A'
  /-- the functor on the base component -/
  base : B ⥤ B'
  /-- the functor on the right component -/
  right : C ⥤ C'
  /-- a `CatCommSq` bundling the natural isomorphism `F ⋙ base ≅ left ⋙ F'`. -/
  squareLeft : CatCommSq F left base F' := by infer_instance
  /-- a `CatCommSq` bundling the natural isomorphism `G ⋙ base ≅ right ⋙ G'`. -/
  squareRight : CatCommSq G right base G' := by infer_instance

namespace CatCospanTransform

section

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  (F : A ⥤ B) (G : C ⥤ B)

attribute [local instance] CatCommSq.vId in
/-- The identity `CatCospanTransform` -/
@[simps]
def id : CatCospanTransform F G F G where
  left := 𝟭 A
  base := 𝟭 B
  right := 𝟭 C

variable {F G}
/-- Composition of `CatCospanTransforms` is defined "componentwise". -/
@[simps]
def comp
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
  squareLeft := ψ.squareLeft.vComp' ψ'.squareLeft
  squareRight := ψ.squareRight.vComp' ψ'.squareRight

end

end CatCospanTransform

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
    {A' : Type u₄} {B' : Type u₅} {C' : Type u₆}
    {A'' : Type u₇} {B'' : Type u₈} {C'' : Type u₉}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    {F : A ⥤ B} {G : C ⥤ B}
    [Category.{v₄} A'] [Category.{v₅} B'] [Category.{v₆} C']
    {F' : A' ⥤ B'} {G' : C' ⥤ B'}
    [Category.{v₇} A''] [Category.{v₈} B''] [Category.{v₅} C'']
    {F'' : A'' ⥤ B''} {G'' : C'' ⥤ B''}

/-- A morphism of `CatCospanTransform F G F' G'` is a triple of natural
transformations between the component functors, subjects to
coherence conditions respective to the squares. -/
structure CatCospanTransformMorphism
    (ψ ψ' : CatCospanTransform F G F' G') where
  /-- the natural transformations between the left components -/
  left : ψ.left ⟶ ψ'.left
  /-- the natural transformations between the right components -/
  right : ψ.right ⟶ ψ'.right
  /-- the natural transformations between the base components -/
  base : ψ.base ⟶ ψ'.base
  /-- the coherence condition for the left square -/
  left_coherence :
      ψ.squareLeft.iso.hom ≫ Functor.whiskerRight left F' =
      Functor.whiskerLeft F base ≫ ψ'.squareLeft.iso.hom := by
    aesop_cat
  /-- the coherence condition for the right square -/
  right_coherence :
      ψ.squareRight.iso.hom ≫ Functor.whiskerRight right G' =
      Functor.whiskerLeft G base ≫ ψ'.squareRight.iso.hom := by
    aesop_cat

namespace CatCospanTransform

attribute [reassoc (attr := simp)]
  CatCospanTransformMorphism.left_coherence
  CatCospanTransformMorphism.right_coherence

@[simps]
instance category : Category (CatCospanTransform F G F' G') where
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
lemma hom_ext {ψ ψ' : CatCospanTransform F G F' G'} {θ θ' : ψ ⟶ ψ'}
    (hl : θ.left = θ'.left) (hr : θ.right = θ'.right) (hb : θ.base = θ'.base) :
    θ = θ' := by
  apply CatCospanTransformMorphism.ext <;> assumption

end CatCospanTransform

namespace CatCospanTransformMorphism

@[reassoc (attr := simp)]
lemma left_coherence_app {ψ ψ' : CatCospanTransform F G F' G'}
    (α : ψ ⟶ ψ') (x : A) :
    ψ.squareLeft.iso.hom.app x ≫ F'.map (α.left.app x) =
    α.base.app (F.obj x) ≫ ψ'.squareLeft.iso.hom.app x :=
  congr_app α.left_coherence x

@[reassoc (attr := simp)]
lemma right_coherence_app {ψ ψ' : CatCospanTransform F G F' G'}
    (α : ψ ⟶ ψ') (x : C) :
    ψ.squareRight.iso.hom.app x ≫ G'.map (α.right.app x) =
    α.base.app (G.obj x) ≫ ψ'.squareRight.iso.hom.app x :=
  congr_app α.right_coherence x

/-- Whiskering left of a `CatCospanTransformMorphism` by a `CatCospanTransform`. -/
@[simps]
def whiskerLeft (φ : CatCospanTransform F G F' G')
    {ψ ψ' : CatCospanTransform F' G' F'' G''} (α : ψ ⟶ ψ') :
    (φ.comp ψ) ⟶ (φ.comp ψ') where
  left := Functor.whiskerLeft φ.left α.left
  right := Functor.whiskerLeft φ.right α.right
  base := Functor.whiskerLeft φ.base α.base

/-- Whiskering right of a `CatCospanTransformMorphism` by a `CatCospanTransform`. -/
@[simps]
def whiskerRight {ψ ψ' : CatCospanTransform F G F' G'} (α : ψ ⟶ ψ')
    (φ : CatCospanTransform F' G' F'' G'') :
    (ψ.comp φ) ⟶ (ψ'.comp φ) where
  left := Functor.whiskerRight α.left φ.left
  right := Functor.whiskerRight α.right φ.right
  base := Functor.whiskerRight α.base φ.base
  left_coherence := by
    ext x
    dsimp
    simp only [CatCommSq.vComp_iso_hom_app, Category.assoc]
    rw [← Functor.map_comp_assoc, ← left_coherence_app, Functor.map_comp_assoc]
    simp
  right_coherence := by
    ext x
    dsimp
    simp only [CatCommSq.vComp_iso_hom_app, Category.assoc]
    rw [← Functor.map_comp_assoc, ← right_coherence_app, Functor.map_comp_assoc]
    simp

end CatCospanTransformMorphism

namespace CatCospanTransform

/-- A constructor for isomorphisms of `CatCospanTransform`'s. -/
@[simps]
def mkIso {ψ ψ' : CatCospanTransform F G F' G'}
    (left : ψ.left ≅ ψ'.left) (right : ψ.right ≅ ψ'.right)
    (base : ψ.base ≅ ψ'.base)
    (left_coherence :
        ψ.squareLeft.iso.hom ≫ Functor.whiskerRight left.hom F' =
        Functor.whiskerLeft F base.hom ≫ ψ'.squareLeft.iso.hom := by
      aesop_cat)
    (right_coherence :
        ψ.squareRight.iso.hom ≫ Functor.whiskerRight right.hom G' =
        Functor.whiskerLeft G base.hom ≫ ψ'.squareRight.iso.hom := by
      aesop_cat) :
    ψ ≅ ψ' where
  hom :=
    { left := left.hom
      right := right.hom
      base := base.hom }
  inv :=
    { left := left.inv
      right := right.inv
      base := base.inv
      left_coherence := by
        simpa using ψ'.squareLeft.iso.hom ≫=
          IsIso.inv_eq_inv.mpr left_coherence =≫
          ψ.squareLeft.iso.hom
      right_coherence := by
        simpa using ψ'.squareRight.iso.hom ≫=
          IsIso.inv_eq_inv.mpr right_coherence =≫
          ψ.squareRight.iso.hom }

section Iso

variable {ψ ψ' : CatCospanTransform F G F' G'}
  (f : ψ' ⟶ ψ') [IsIso f] (e : ψ ≅ ψ')

instance isIso_left : IsIso f.left :=
  ⟨(inv f).left, by simp [← CatCospanTransform.category_comp_left]⟩

instance isIso_right : IsIso f.right :=
  ⟨(inv f).right, by simp [← CatCospanTransform.category_comp_right]⟩

instance isIso_base : IsIso f.base :=
  ⟨(inv f).base, by simp [← CatCospanTransform.category_comp_base]⟩

@[simp]
lemma inv_left : inv f.left = (inv f).left := by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← CatCospanTransform.category_comp_left]

@[simp]
lemma inv_right : inv f.right = (inv f).right := by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← CatCospanTransform.category_comp_right]

@[simp]
lemma inv_base : inv f.base = (inv f).base := by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← CatCospanTransform.category_comp_base]

/-- Extract an isomorphism between left components from an isomorphism in
`CatCospanTransform F G F' G'`. -/
@[simps]
def leftIso : ψ.left ≅ ψ'.left where
  hom := e.hom.left
  inv := e.inv.left
  hom_inv_id := by simp [← category_comp_left]
  inv_hom_id := by simp [← category_comp_left]

/-- Extract an isomorphism between right components from an isomorphism in
`CatCospanTransform F G F' G'`. -/
@[simps]
def rightIso : ψ.right ≅ ψ'.right where
  hom := e.hom.right
  inv := e.inv.right
  hom_inv_id := by simp [← category_comp_right]
  inv_hom_id := by simp [← category_comp_right]

/-- Extract an isomorphism between base components from an isomorphism in
`CatCospanTransform F G F' G'`. -/
@[simps]
def baseIso : ψ.base ≅ ψ'.base where
  hom := e.hom.base
  inv := e.inv.base
  hom_inv_id := by simp [← category_comp_base]
  inv_hom_id := by simp [← category_comp_base]

omit [IsIso f] in
lemma isIso_iff : IsIso f ↔ IsIso f.left ∧ IsIso f.base ∧ IsIso f.right where
  mp h := ⟨inferInstance, inferInstance, inferInstance⟩
  mpr h := by
    obtain ⟨_, _, _⟩ := h
    use mkIso (asIso f.left) (asIso f.right) (asIso f.base)
      f.left_coherence f.right_coherence|>.inv
    aesop_cat

end Iso

/-- The left unitor isomorphism for categorical cospan transformations. -/
@[simps!]
def leftUnitor (φ : CatCospanTransform F G F' G') :
    (CatCospanTransform.id F G).comp φ ≅ φ :=
  mkIso φ.left.leftUnitor φ.right.leftUnitor φ.base.leftUnitor

/-- The right unitor isomorphism for categorical cospan transformations. -/
@[simps!]
def rightUnitor (φ : CatCospanTransform F G F' G') :
    φ.comp (.id F' G') ≅ φ :=
  mkIso φ.left.rightUnitor φ.right.rightUnitor φ.base.rightUnitor

/-- The associator isomorphism for categorical cospan transformations. -/
@[simps!]
def associator {A''' : Type u₁₀} {B''' : Type u₁₁} {C''' : Type u₁₂}
    [Category.{v₁₀} A'''] [Category.{v₁₁} B'''] [Category.{v₁₂} C''']
    {F''' : A''' ⥤ B'''} {G''' : C''' ⥤ B'''}
    (φ : CatCospanTransform F G F' G') (φ' : CatCospanTransform F' G' F'' G'')
    (φ'' : CatCospanTransform F'' G'' F''' G''') :
    (φ.comp φ').comp φ'' ≅ φ.comp (φ'.comp φ'') :=
  mkIso
    (φ.left.associator φ'.left φ''.left)
    (φ.right.associator φ'.right φ''.right)
    (φ.base.associator φ'.base φ''.base)

end CatCospanTransform

end CategoryTheory.Limits
