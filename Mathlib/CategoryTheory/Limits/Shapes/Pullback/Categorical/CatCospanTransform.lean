/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.CatCommSq
import Mathlib.CategoryTheory.Adjunction.Mates

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

attribute [local simp]
  CatCommSq.iso_hom_naturality CatCommSq.iso_hom_naturality_assoc
  CatCommSq.iso_hom_naturality CatCommSq.iso_inv_naturality_assoc

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃ v₁₄ v₁₅
universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ u₁₄ u₁₅

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
/-- The identitiy `CatCospanTransform` -/
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
  squareLeft := ψ.squareLeft.vComp' (ψ'.squareLeft)
  squareRight := ψ.squareRight.vComp' (ψ'.squareRight)

end

end CatCospanTransform

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
    {A' : Type u₄} {B' : Type u₅} {C' : Type u₆}
    {A'' : Type u₇} {B'' : Type u₈} {C'' : Type u₉}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    {F : A ⥤ B} {G : C ⥤ B}
    [Category.{v₄} A'] [Category.{v₅} B'] [Category.{v₆} C']
    {F' : A' ⥤ B'} {G' : C' ⥤ B'}
    [Category.{v₇} A''] [Category.{v₈} B''] [Category.{v₉} C'']
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
      ψ.squareLeft.iso.hom ≫ whiskerRight left F' =
      whiskerLeft F base ≫ ψ'.squareLeft.iso.hom := by
    aesop_cat
  /-- the coherence condition for the right square -/
  right_coherence :
      ψ.squareRight.iso.hom ≫ whiskerRight right G' =
      whiskerLeft G base ≫ ψ'.squareRight.iso.hom := by
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
lemma hom_ext {ψ ψ' : CatCospanTransform F G F' G'} {θ θ': ψ ⟶ ψ'}
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
    {ψ ψ' : CatCospanTransform F' G' F'' G''}
    (α : ψ ⟶ ψ') :
    (φ.comp ψ) ⟶ (φ.comp ψ') where
  left := CategoryTheory.whiskerLeft φ.left α.left
  right := CategoryTheory.whiskerLeft φ.right α.right
  base := CategoryTheory.whiskerLeft φ.base α.base

/-- Whiskering right of a `CatCospanTransformMorphism` by a `CatCospanTransform`. -/
@[simps]
def whiskerRight {ψ ψ' : CatCospanTransform F G F' G'}
    (α : CatCospanTransformMorphism ψ ψ')
    (φ : CatCospanTransform F' G' F'' G'') :
    (ψ.comp φ) ⟶ (ψ'.comp φ) where
  left := CategoryTheory.whiskerRight α.left φ.left
  right := CategoryTheory.whiskerRight α.right φ.right
  base := CategoryTheory.whiskerRight α.base φ.base
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
        ψ.squareLeft.iso.hom ≫ CategoryTheory.whiskerRight left.hom F' =
        CategoryTheory.whiskerLeft F base.hom ≫ ψ'.squareLeft.iso.hom := by
      aesop_cat)
    (right_coherence :
        ψ.squareRight.iso.hom ≫ CategoryTheory.whiskerRight right.hom G' =
        CategoryTheory.whiskerLeft G base.hom ≫ ψ'.squareRight.iso.hom := by
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

section lemmas

-- We scope the notations with notations from bicategories to make life easier.
-- Due to performance issues, these notations should not be in scope at the same time
-- as the ones in bicategories.

@[inherit_doc] scoped infixr:81 " ◁ " => CatCospanTransformMorphism.whiskerLeft
@[inherit_doc] scoped infixl:81 " ▷ " => CatCospanTransformMorphism.whiskerRight
@[inherit_doc] scoped notation "α_" => CatCospanTransform.associator
@[inherit_doc] scoped notation "λ_" => CatCospanTransform.leftUnitor
@[inherit_doc] scoped notation "ρ_" => CatCospanTransform.rightUnitor

variable
    {A''' : Type u₁₀} {B''' : Type u₁₁} {C''' : Type u₁₂}
    [Category.{v₁₀} A'''] [Category.{v₁₁} B'''] [Category.{v₁₂} C''']
    {F''' : A''' ⥤ B'''} {G''' : C''' ⥤ B'''}
    {ψ ψ' ψ'' : CatCospanTransform F G F' G'}
    (η : ψ ⟶ ψ') (η' : ψ' ⟶ ψ'')
    {φ φ' φ'' : CatCospanTransform F' G' F'' G''}
    (θ : φ ⟶ φ') (θ' : φ' ⟶ φ'')
    {τ τ' : CatCospanTransform F'' G'' F''' G'''}
    (γ : τ ⟶ τ')

lemma whisker_exchange : ψ ◁ θ ≫ η ▷ φ' = η ▷ φ ≫ ψ' ◁ θ := by aesop_cat

lemma whiskerRight_id : η ▷ (.id _ _) = (ρ_ _).hom ≫ η ≫ (ρ_ _).inv := by aesop_cat
lemma comp_whiskerRight : (η ≫ η') ▷ φ = η ▷ φ ≫ η' ▷ φ := by aesop_cat
lemma whiskerRight_comp :
    η ▷ (φ.comp τ) = (α_ _ _ _).inv ≫ (η ▷ φ) ▷ τ ≫ (α_ _ _ _ ).hom := by
  aesop_cat

lemma whiskerLeft_id : (.id _ _) ◁ η = (λ_ _).hom ≫ η ≫ (λ_ _).inv := by aesop_cat
lemma whiskerLeft_comp : ψ ◁ (θ ≫ θ') = (ψ ◁ θ) ≫ (ψ ◁ θ') := by aesop_cat
lemma comp_whiskerLeft :
    (ψ.comp φ) ◁ γ = (α_ _ _ _).hom ≫ (ψ ◁ (φ ◁ γ)) ≫ (α_ _ _ _).inv := by
  aesop_cat

lemma pentagon
    {A'''' : Type u₁₃} {B'''' : Type u₁₄} {C'''' : Type u₁₅}
    [Category.{v₁₃} A''''] [Category.{v₁₄} B''''] [Category.{v₁₅} C'''']
    {F'''' : A'''' ⥤ B''''} {G'''' : C'''' ⥤ B''''}
    {σ : CatCospanTransform F''' G''' F'''' G''''} :
    (α_ ψ φ τ).hom ▷ σ ≫ (α_ ψ (φ.comp τ) σ).hom ≫ ψ ◁ (α_ φ τ σ).hom =
      (α_ (ψ.comp φ) τ σ).hom ≫ (α_ ψ φ (τ.comp σ)).hom := by
  aesop_cat

lemma triangle : (α_ ψ (.id _ _) φ).hom ≫ ψ ◁ (λ_ φ).hom = (ρ_ ψ).hom ▷ φ := by aesop_cat

end lemmas

end CatCospanTransform

open scoped CatCospanTransform

/--
A `CatCospanAdjunction F G F' G'` is the data of a
`ψ : CatCospanTransform F G F' G'`, a `φ CatCospanTransform F' G' F G`, along
with unit and counit morphisms satisfying the triangle identities
It can be thought of as a diagram
```
    F     G
 A = ⥤ B ⥢ = C
| ^   | ^   | ^
|⊣|   |⊣|   |⊣|
v |   v |   v |
 A'= ⥤ B'⥢ = C'
    F'    G'

```
with suitable CatCommSq between the lefts and right adjoints, where the square between
the left and right adjoints are related through `mateEquiv`.
-/
structure CatCospanAdjunction
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : C ⥤ B)
    {A' B' C' : Type*} [Category A'] [Category B'] [Category C']
    (F' : A' ⥤ B') (G' : C' ⥤ B') where
  /-- the left adjoint transformation -/
  leftAdjoint : CatCospanTransform F G F' G'
  /-- the right adjoint transformation -/
  rightAdjoint : CatCospanTransform F' G' F G
  /-- the unit morphism of `CatCospanTransform` -/
  unit : CatCospanTransform.id F G ⟶ leftAdjoint.comp rightAdjoint
  /-- the counit morphism of `CatCospanTransform` -/
  counit : rightAdjoint.comp leftAdjoint ⟶ CatCospanTransform.id F' G'
  /-- the left triangle identitiy -/
  left_triangle :
      unit ▷ leftAdjoint ≫ (α_ _ _ _).hom ≫ leftAdjoint ◁ counit =
      (λ_ _).hom ≫ (ρ_ _).inv := by
    aesop_cat
  /-- the right triangle identitiy -/
  right_triangle :
      rightAdjoint ◁ unit ≫ (α_ _ _ _).inv ≫ counit ▷ rightAdjoint =
      (ρ_ _).hom ≫ (λ_ _).inv := by
    aesop_cat

namespace CatCospanAdjunction

variable {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : C ⥤ B}
    {A' B' C' : Type*} [Category A'] [Category B'] [Category C']
    {F' : A' ⥤ B'} {G' : C' ⥤ B'}
    (𝔄 : CatCospanAdjunction F G F' G')

/-- The adjunction on the left components of a `CatCospanAdjunction`. -/
@[simps]
def leftAdjunction : 𝔄.leftAdjoint.left ⊣ 𝔄.rightAdjoint.left where
  unit := 𝔄.unit.left
  counit := 𝔄.counit.left
  left_triangle_components x := by
    simpa using congr_arg (fun t ↦ t.left.app x) 𝔄.left_triangle
  right_triangle_components x := by
    simpa using congr_arg (fun t ↦ t.left.app x) 𝔄.right_triangle

/-- The adjunction on the right components of a `CatCospanAdjunction`. -/
@[simps]
def rightAdjunction : 𝔄.leftAdjoint.right ⊣ 𝔄.rightAdjoint.right where
  unit := 𝔄.unit.right
  counit := 𝔄.counit.right
  left_triangle_components x := by
    simpa using congr_arg (fun t ↦ t.right.app x) 𝔄.left_triangle
  right_triangle_components x := by
    simpa using congr_arg (fun t ↦ t.right.app x) 𝔄.right_triangle

/-- The adjunction on the base components of a `CatCospanAdjunction`. -/
@[simps]
def baseAdjunction : 𝔄.leftAdjoint.base ⊣ 𝔄.rightAdjoint.base where
  unit := 𝔄.unit.base
  counit := 𝔄.counit.base
  left_triangle_components x := by
    simpa using congr_arg (fun t ↦ t.base.app x) 𝔄.left_triangle
  right_triangle_components x := by
    simpa using congr_arg (fun t ↦ t.base.app x) 𝔄.right_triangle

/-- In a `CatCospanAdjunction`, the left square on the right adjoints is
related to the left square on the left adjoints via the calculus of mates. -/
lemma mateEquivLeftAdjointSquares :
    mateEquiv 𝔄.leftAdjunction 𝔄.baseAdjunction
      (TwoSquare.mk _ _ _ _ 𝔄.leftAdjoint.squareLeft.iso.hom) =
    TwoSquare.mk _ _ _ _ (𝔄.rightAdjoint.squareLeft.iso.inv) := by
  ext x
  dsimp [TwoSquare.mk, TwoSquare.natTrans]
  -- Collecting some facts
  have h₁ := 𝔄.unit.left_coherence_app (𝔄.rightAdjoint.left.obj x) =≫
    (𝔄.rightAdjoint.squareLeft.iso).inv.app
        (𝔄.leftAdjoint.left.obj (𝔄.rightAdjoint.left.obj x))
  have h₂ := 𝔄.rightAdjoint.squareLeft.iso_inv_naturality
    (f := 𝔄.counit.left.app x)
  have := 𝔄.leftAdjunction.right_triangle_components x
  dsimp at h₁ this
  simp only [CatCommSq.vId_iso_hom_app, Category.id_comp,
    CatCommSq.vComp_iso_hom_app, Category.assoc, Iso.hom_inv_id_app,
    Functor.comp_obj, Category.comp_id] at h₁
  simp only [CatCospanTransform.comp_left, Functor.comp_obj,
    CatCospanTransform.id_left, Functor.id_obj] at h₂
  rw [← reassoc_of% h₁, ← h₂, ← Functor.map_comp_assoc, this]
  simp

/-- In a `CatCospanAdjunction`, the right square on the right adjoints is
related to the right square on the left adjoints via the calculus of mates. -/
lemma mateEquivRightAdjointSquares :
    mateEquiv 𝔄.rightAdjunction 𝔄.baseAdjunction
      (TwoSquare.mk _ _ _ _ 𝔄.leftAdjoint.squareRight.iso.hom) =
    TwoSquare.mk _ _ _ _ (𝔄.rightAdjoint.squareRight.iso.inv) := by
  ext x
  dsimp [TwoSquare.mk, TwoSquare.natTrans]
  -- Collecting some facts
  have h₁ := 𝔄.unit.right_coherence_app (𝔄.rightAdjoint.right.obj x) =≫
    (𝔄.rightAdjoint.squareRight.iso).inv.app
        (𝔄.leftAdjoint.right.obj (𝔄.rightAdjoint.right.obj x))
  have h₂ := 𝔄.rightAdjoint.squareRight.iso_inv_naturality
    (f := 𝔄.counit.right.app x)
  have := 𝔄.rightAdjunction.right_triangle_components x
  dsimp at h₁ this
  simp only [CatCommSq.vId_iso_hom_app, Category.id_comp,
    CatCommSq.vComp_iso_hom_app, Category.assoc, Iso.hom_inv_id_app,
    Functor.comp_obj, Category.comp_id] at h₁
  simp only [CatCospanTransform.comp_right, Functor.comp_obj,
    CatCospanTransform.id_right, Functor.id_obj] at h₂
  rw [← reassoc_of% h₁, ← h₂, ← Functor.map_comp_assoc, this]
  simp

end CatCospanAdjunction

/-- A `CatCospanEquivalence F G F' G'` is a diagram
```
    F   G
  A ⥤ B ⥢ C
H₁|   |H₂ |H₃
  v   v   v
  A'⥤ B'⥢ C'
    F'  G'
```
where H₁, H₂ and H₃ are equivalences, along with commutative 2-squares structure
on the squares in the forward direction.
It is defined as a `CatCospanAdjunction F G F' G'` with given inverses to the unit and counit
morphisms. See `CatCospanEquivalence.mk'` for a constructor that asks for 3 equivalences and
squares only on their functors (the square on inverses being uniquely determined). -/
structure CatCospanEquivalence
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : C ⥤ B)
    {A' B' C' : Type*} [Category A'] [Category B'] [Category C']
    (F' : A' ⥤ B') (G' : C' ⥤ B') extends CatCospanAdjunction F G F' G' where
  /-- the unit morphism of `CatCospanTransform` -/
  unitInv : leftAdjoint.comp rightAdjoint ⟶ CatCospanTransform.id F G
  /-- the counit morphism of `CatCospanTransform` -/
  counitInv : CatCospanTransform.id F' G' ⟶ rightAdjoint.comp leftAdjoint
  unit_hom_inv_id : unit ≫ unitInv = 𝟙 _ := by aesop_cat
  unit_inv_hom_id : unitInv ≫ unit = 𝟙 _ := by aesop_cat
  counit_hom_inv_id : counit ≫ counitInv = 𝟙 _ := by aesop_cat
  counit_inv_hom_id : counitInv ≫ counit = 𝟙 _ := by aesop_cat

namespace CatCospanEquivalence

attribute [reassoc (attr := simp)] unit_hom_inv_id unit_inv_hom_id
  counit_inv_hom_id counit_hom_inv_id

variable {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : C ⥤ B}
    {A' B' C' : Type*} [Category A'] [Category B'] [Category C']
    {F' : A' ⥤ B'} {G' : C' ⥤ B'}
    (𝔈 : CatCospanEquivalence F G F' G')

/-- A shorthand for the "forward" direction of a `CatCospanEquivalence`. -/
abbrev transform : CatCospanTransform F G F' G' := 𝔈.leftAdjoint

/-- A shorthand for the "inverse" direction of a `CatCospanEquivalence`. -/
abbrev inverse : CatCospanTransform F' G' F G := 𝔈.rightAdjoint

/-- The unit of the `CatCospanEquivalence` as an isomorphism. -/
@[simps]
def unitIso : CatCospanTransform.id F G ≅ 𝔈.transform.comp 𝔈.inverse where
  hom := 𝔈.unit
  inv := 𝔈.unitInv

/-- The counit of the `CatCospanEquivalence` as an isomorphism. -/
@[simps]
def counitIso : 𝔈.inverse.comp 𝔈.transform ≅ CatCospanTransform.id F' G' where
  hom := 𝔈.counit
  inv := 𝔈.counitInv

def leftEquiv : A ≌ A' where
  functor := 𝔈.transform.left
  inverse := 𝔈.inverse.left
  unitIso := ⟨𝔈.unitIso.hom.left, 𝔈.unitIso.hom.left, sorry, sorry⟩

-- def mk' (leftEquiv : A ≌ A') (rightEquiv : C ≌ C') (baseEquiv : B ≌ B') 
--   (squareLeft : ) (squareRight : )

end CatCospanEquivalence

end CategoryTheory.Limits
