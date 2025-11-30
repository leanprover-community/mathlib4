/-
Copyright (c) 2025 Judah Towery. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judah Towery
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor

/-!

# The lax slice bicategory F ↓ X of a lax functor F : B ⥤ᴸ C over an object X : C

* objects are pairs (A : B, f_A : FA ⟶ X)
* 1-cells are pairs (p : A₀ ⟶ A₁, θ_p : f₀ ⟶ f₁(Fp) in C
* 2-cells are 2-cells α : p₀ ⟶ p₁ in B with Fα subject to the ice cream cone condition.

Provides a change-of-slice strict pseudofunctor for a 1-cell u : X ⟶ Y,
F ↓ u : (F ↓ X) ⥤ᵖ (F ↓ Y)

## References
* [Niles Johnson, Donald Yau, *2-Dimensional Categories*](https://arxiv.org/abs/2002.06055),
section 7.1
-/

namespace CategoryTheory

open Category Bicategory

universe w₁ w₂ v₁ v₂

namespace LaxSlice

variable {B C : Type*} [Bicategory.{w₁, v₁} B] [Bicategory.{w₂, v₂} C] (F : B ⥤ᴸ C) (X : C)

/-- Objects of the lax slice bicategory `F ↓ X`.
A pair `(A, f_A)` where `A ∈ B` and `f_A : FA ⟶ X` in `C`. -/
@[ext]
structure Obj where
  ob : B
  map : F.obj ob ⟶ X

/-- Notation for objects of lax slice bicategory. -/
scoped notation F " ↓ " X => Obj F X

/-- 1-cells in `F ↓ X`
A 1-cell `(A₀, f₀) ⟶ (A₁, f₁)` is a pair `(p, θ_p)` with
`p : A₀ ⟶ A₁` in `B`, and `θ_p : f₀ ⟶ f₁(Fp)` in `C`.
This is depicted as a triangle
```
FA₀-----Fp----->FA₁
|               |
|    ⇒⇒θ_p⇒⇒    |
|               |
|--f₀-->X<--f₁--|
``` -/
@[ext]
structure Hom₁ (A B : F ↓ X) where
  dom_map : A.ob ⟶ B.ob
  cod_map : A.map ⟶ F.map dom_map ≫ B.map

/-- Identity 1-cell
For an object `(A, f)`, the identity 1-cell is `(1_A, r')`, with `r'` from this pasting diagram:
```
|-------F1_A------|
|        ⇑        |
|      F^0_A      |
|        ⇑        ↓
FA------1_FA----->FA
|                 |
|     ⇒⇒r^-1⇒⇒    |
|                 |
|--f_A-->X<--f_A--|
``` -/
@[simps]
def id₁ (A : F ↓ X) : Hom₁ F X A A where
  dom_map := 𝟙 A.ob
  cod_map := (λ_ A.map).inv ≫ (F.mapId A.ob ▷ A.map)

/-- Composition of 1-cells.
For 1-cells `(p₀, θ₀) : (A₀, f₀) ⟶ (A₁, f₁), (p₁, θ₁) : (A₁, f₁) ⟶ (A₂, f₂)`, their composite is
`(p₁p₀, θ')`, where `θ'` is formed from the composite of the pasting diagram:
```
|-------F(p₁p₀)-------|
|          ⇑          |
|       F^2_{p₁,p₀}   |
|          ⇑          ↓
FA₀--Fp₀-->FA₁--Fp₁-->FA₂
|          |          |
|  ⇒⇒θ₀⇒⇒  f₁ ⇒⇒θ₁⇒⇒  |
|          ↓          |
|----f₀--->X<---f₂----|
``` -/
@[simps]
def comp₁ {A B C : F ↓ X} (p₀ : Hom₁ F X A B) (p₁ : Hom₁ F X B C) : Hom₁ F X A C where
  dom_map := p₀.dom_map ≫ p₁.dom_map
  cod_map := p₀.cod_map ≫ (F.map p₀.dom_map ◁ p₁.cod_map)
    ≫ (α_ (F.map p₀.dom_map) (F.map p₁.dom_map) C.map).inv
    ≫ (F.mapComp p₀.dom_map p₁.dom_map ▷ C.map)

/-- Underlying CategoryStruct on objects. -/
@[simps]
instance : CategoryStruct (F ↓ X) where
  Hom A B := Hom₁ F X A B
  id A := id₁ F X A
  comp f g := comp₁ F X f g

/-- 2-cells in `F ↓ X`
A 2-cell `(p₀, θ₀) ⟶ (p₁, θ₁)` is a 2-cell `α : p₀ ⟶ p₁` in `B` such that
`Fα` satisfies the ice cream cone condition:
```
|-------Fp₁-----|     FA₀-----Fp₁---->FA₁
|        ⇑      |     |               |
|       Fα      |     |               |
|        ⇑      ↓     |               |
FA₀-----Fp₀---->FA₁ = |     ⇒⇒θ₁⇒⇒    |
|               |     |               |
|     ⇒⇒θ₀⇒⇒    |     |               |
|               |     |               |
|--f₀-->X<--f₁--|     |--f₀-->X<--f₁--|
``` -/
@[ext]
structure Hom₂ {A B : F ↓ X} (f : A ⟶ B) (g : A ⟶ B) where
  map : f.dom_map ⟶ g.dom_map
  icc : f.cod_map ≫ (F.map₂ map ▷ B.map) = g.cod_map

/-- Identity 2-cell.
For a 1-cell `(p, θ)`, the identity 2-cell is `1_p` -/
@[simps]
def id₂ {A B : F ↓ X} (f : A ⟶ B) : Hom₂ F X f f where
  map := 𝟙 f.dom_map
  icc := by simp

/-- Vertical composition of 2-cells.
For 1-cells `(p, θ), (p', θ'), (p'', θ'') : (A₀, F₀) ⟶ (A₁, F₁)`
and 2-cells `α : (p, θ) ⟶ (p', θ'), α' : (p', θ') ⟶ (p'', θ'')`,
their vertical composite is the composite `α'α : (p, θ) ⟶ (p'', θ'')`. -/
@[simps]
def comp₂ {A B : F ↓ X} {f g h : A ⟶ B} (α : Hom₂ F X f g) (β : Hom₂ F X g h) :
    Hom₂ F X f h where
  map := α.map ≫ β.map
  icc := by simp [←α.icc, ←β.icc]

/-- Category structure on 1-cells with vertical composition. -/
instance (A B : F ↓ X) : Category (A ⟶ B) where
  Hom f g := Hom₂ F X f g
  id f := id₂ F X f
  comp η θ := comp₂ F X η θ

/-- Whisker a 2-cell on the left by a 1-cell.
Comes precisely from the whiskering on `B`. -/
@[simps]
def whiskerLeft {A B C : F ↓ X} (f : A ⟶ B) {g h : B ⟶ C} (η : g ⟶ h) :
    (f ≫ g) ⟶ (f ≫ h) where
  map := f.dom_map ◁ η.map
  icc := by simp only [comp_def, comp₁_dom_map, comp₁_cod_map, assoc,
                       ← comp_whiskerRight, LaxFunctor.mapComp_naturality_right,
                       ← η.icc, whiskerLeft_comp]
            simp

@[simp]
theorem whiskerLeft_id {A B C : F ↓ X} (f : A ⟶ B) (g : B ⟶ C) :
    whiskerLeft F X f (𝟙 g) = 𝟙 (f ≫ g) := by
  refine Hom₂.ext ?_
  change f.dom_map ◁ 𝟙 g.dom_map = 𝟙 _
  simp

@[simp]
theorem whiskerLeft_comp {A B C : F ↓ X} (f : A ⟶ B) {g h i : B ⟶ C} (η : g ⟶ h) (θ : h ⟶ i) :
    whiskerLeft F X f (η ≫ θ) = whiskerLeft F X f η ≫ whiskerLeft F X f θ := by
  refine Hom₂.ext ?_
  change f.dom_map ◁ (η.map ≫ θ.map) = _ ≫ _
  simp

/-- Whisker a 2-cell on the right by a 1-cell.
Comes precisely from the whiskering on `B`. -/
@[simps]
def whiskerRight {A B C : F ↓ X} {f g : A ⟶ B} (η : f ⟶ g) (h : B ⟶ C) : (f ≫ h) ⟶ (g ≫ h) where
  map := η.map ▷ h.dom_map
  icc := by simp [←η.icc, ←assoc (F.map₂ η.map ▷ B.map), ←whisker_exchange, ←comp_whiskerRight]

@[simp]
theorem id_whiskerRight {A B C : F ↓ X} (f : A ⟶ B) (g : B ⟶ C) : whiskerRight F X (𝟙 f) g =
    𝟙 (f ≫ g) := by
  refine Hom₂.ext ?_
  change (𝟙 f.dom_map) ▷ g.dom_map = 𝟙 _
  simp

@[simp]
theorem comp_whiskerRight {A B C : F ↓ X} {f g h : A ⟶ B} (η : f ⟶ g) (θ : g ⟶ h) (i : B ⟶ C) :
    whiskerRight F X (η ≫ θ) i = whiskerRight F X η i ≫ whiskerRight F X θ i := by
  refine Hom₂.ext ?_
  change (η.map ≫ θ.map) ▷ i.dom_map = _ ≫ _
  simp

/- Associator forward direction. -/
@[simps]
def associatorHom {A B C D : F ↓ X} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    (f ≫ g) ≫ h ⟶ f ≫ g ≫ h where
  map := by simpa using (α_ f.dom_map g.dom_map h.dom_map).hom
  icc := by simp only [comp_def, comp₁_dom_map, comp₁_cod_map, id_eq,
                       Bicategory.whiskerLeft_comp, ←assoc (F.mapComp f.dom_map g.dom_map ▷ C.map),
                       ← whisker_exchange, comp_whiskerLeft, whiskerRight_comp,
                       assoc, ← Bicategory.comp_whiskerRight, Iso.hom_inv_id_assoc,
                       LaxFunctor.map₂_associator, Iso.inv_hom_id_assoc, whisker_assoc_symm]
            simp

/- Associator reverse direction -/
@[simps]
def associatorInv {A B C D : F ↓ X} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    f ≫ g ≫ h ⟶ (f ≫ g) ≫ h where
  map := by simpa using (α_ f.dom_map g.dom_map h.dom_map).inv
  icc := by simp only [comp_def, comp₁_dom_map, comp₁_cod_map,
                       Bicategory.whiskerLeft_comp, assoc, id_eq,
                       ←assoc (F.mapComp f.dom_map g.dom_map ▷ C.map),
                       ← whisker_exchange, comp_whiskerLeft, whiskerRight_comp,
                       Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
                       ←assoc ((α_ (F.map f.dom_map) (F.map g.dom_map)
                       (F.map h.dom_map ≫ D.map)).inv),
                       ←pentagon_inv, whisker_assoc_symm,
                       ←assoc ((α_ (F.map f.dom_map) (F.map (g.dom_map ≫ h.dom_map)) D.map).hom),
                       Iso.hom_inv_id, id_comp, ←Bicategory.comp_whiskerRight,
                       ←Bicategory.comp_whiskerRight]
            simp [LaxFunctor.mapComp_assoc_left]

/- Associator isomorphism part 1 -/
@[simp]
theorem associator_hom_inv_id {A B C D : F ↓ X} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    associatorHom F X f g h ≫ associatorInv F X f g h = 𝟙 ((f ≫ g) ≫ h) := by
  refine Hom₂.ext ?_
  change _ ≫ _ = 𝟙 _
  simp

/- Associator isomorphism part 2 -/
@[simp]
theorem associator_inv_hom_id {A B C D : F ↓ X} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    associatorInv F X f g h ≫ associatorHom F X f g h = 𝟙 (f ≫ g ≫ h) := by
  refine Hom₂.ext ?_
  change _ ≫ _ = 𝟙 _
  simp

/-- Associator 2-cell.
For a composable triple of 1-cells `(p₀, θ₀) : (A₀, f₀) ⟶ (A₁, f₁), (p₁, θ₁) : (A₁, f₁) ⟶ (A₂, f₂)`,
`(p₂, θ₂) : (A₂, f₂) ⟶ (A₃, f₃)`, the associator `α_B` in `B` is the associator in `F ↓ X`:
`α_B : ((p₂, θ₂)(p₁, θ₁))(p₀, θ₀) ⟶ (p₂, θ₂)((p₁, θ₁)(p₀, θ₀))` -/
@[simps]
def associator {A B C D : F ↓ X} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) : (f ≫ g) ≫ h ≅ f ≫ g ≫ h where
  hom := associatorHom F X f g h
  inv := associatorInv F X f g h
  hom_inv_id := associator_hom_inv_id F X f g h
  inv_hom_id := associator_inv_hom_id F X f g h

@[simp]
theorem comp_whiskerLeft {A B C D : F ↓ X} (f : A ⟶ B) (g : B ⟶ C) {h i : C ⟶ D} (η : h ⟶ i) :
    whiskerLeft F X (comp₁ F X f g) η =
    (associator F X f g h).hom ≫ whiskerLeft F X f (whiskerLeft F X g η) ≫
    (associator F X f g i).inv := by
  refine Hom₂.ext ?_
  change _ = _ ≫ _ ≫ _
  simp

@[simp]
theorem whiskerRight_comp {A B C D : F ↓ X} {f g : A ⟶ B} (η : f ⟶ g) (h : B ⟶ C) (i : C ⟶ D) :
    whiskerRight F X η (comp₁ F X h i) =
    (associator F X f h i).inv ≫ whiskerRight F X (whiskerRight F X η h) i ≫
    (associator F X g h i).hom := by
  refine Hom₂.ext ?_
  change _ = _ ≫ _ ≫ _
  simp

@[simp]
theorem whisker_assoc {A B C D : F ↓ X} (f : A ⟶ B) {g h : B ⟶ C} (η : g ⟶ h) (i : C ⟶ D)
    : whiskerRight F X (whiskerLeft F X f η) i =
    (associator F X f g i).hom ≫ whiskerLeft F X f (whiskerRight F X η i) ≫
    (associator F X f h i).inv := by
  refine Hom₂.ext ?_
  change _ = _ ≫ _ ≫ _
  simp

@[simp]
theorem whisker_exchange {A B C : F ↓ X} {f g : A ⟶ B} {h i : B ⟶ C} (η : f ⟶ g) (θ : h ⟶ i) :
    whiskerLeft F X f θ ≫ whiskerRight F X η i =
    whiskerRight F X η h ≫ whiskerLeft F X g θ := by
  refine Hom₂.ext ?_
  change _ ≫ _ = _ ≫ _
  simp [Bicategory.whisker_exchange]

@[simp]
theorem pentagon {A B C D E : F ↓ X} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (i : D ⟶ E) :
    whiskerRight F X (associatorHom F X f g h) i ≫ (associatorHom F X f (g ≫ h) i) ≫
    whiskerLeft F X f (associatorHom F X g h i) =
    (associatorHom F X (f ≫ g) h i) ≫ (associatorHom F X f g (h ≫ i)) := by
  refine Hom₂.ext ?_
  change _ ≫ _ ≫ _ = _ ≫ _
  simp

/- Left unitor forward direction -/
@[simps]
def leftUnitorHom {A B : F ↓ X} (f : A ⟶ B) : (𝟙 A) ≫ f ⟶ f where
  map := by simpa using (λ_ f.dom_map).hom
  icc := by simp [←assoc (F.mapId A.ob ▷ A.map), ←Bicategory.whisker_exchange,
                  ←Bicategory.comp_whiskerRight, ←LaxFunctor.map₂_leftUnitor_hom]

/- Left unitor reverse direction -/
@[simps]
def leftUnitorInv {A B : F ↓ X} (f : A ⟶ B) : f ⟶ (𝟙 A) ≫ f where
  map := by simpa using (λ_ f.dom_map).inv
  icc := by simp [←assoc (F.mapId A.ob ▷ A.map), ←Bicategory.whisker_exchange]

/- Left unitor isomorphism part 1 -/
@[simp]
theorem leftUnitor_hom_inv_id {A B : F ↓ X} (f : A ⟶ B) :
    leftUnitorHom F X f ≫ leftUnitorInv F X f = 𝟙 (𝟙 A ≫ f) := by
  refine Hom₂.ext ?_
  change _ ≫ _ = 𝟙 _
  simp

/- Left unitor isomorphism part 2 -/
@[simp]
theorem leftUnitor_inv_hom_id {A B : F ↓ X} (f : A ⟶ B) :
    leftUnitorInv F X f ≫ leftUnitorHom F X f = 𝟙 f := by
  refine Hom₂.ext ?_
  change _ ≫ _ = 𝟙 _
  simp

/-- Left unitor 2-cell.
Given a 1-cell `(p, θ) : (A₀, f₀) ⟶ (A₁, f₁)`, the left unitor `ℓ_B` in `B` is the left unitor in
`F ↓ X`: `ℓ_B : (1_{A₁}, r')(p, θ) ⟶ (p, θ)`. -/
@[simps]
def leftUnitor {A B : F ↓ X} (f : A ⟶ B) : (𝟙 A) ≫ f ≅ f where
  hom := leftUnitorHom F X f
  inv := leftUnitorInv F X f
  hom_inv_id := leftUnitor_hom_inv_id F X f
  inv_hom_id := leftUnitor_inv_hom_id F X f

@[simp]
theorem id_whiskerLeft {A B : F ↓ X} {f g : A ⟶ B} (η : f ⟶ g) :
    whiskerLeft F X (id₁ F X A) η = (leftUnitor F X f).hom ≫ η ≫ (leftUnitor F X g).inv := by
  refine Hom₂.ext ?_
  change _ = _ ≫ _ ≫ _
  simp

/- Right unitor forward direction -/
@[simps]
def rightUnitorHom {A B : F ↓ X} (f : A ⟶ B) : f ≫ (𝟙 B) ⟶ f where
  map := by simpa using (ρ_ f.dom_map).hom
  icc := by simp only [id_def, comp_def, comp₁_dom_map, id₁_dom_map,
                       comp₁_cod_map, id₁_cod_map, Bicategory.whiskerLeft_comp,
                       assoc, id_eq, ← Bicategory.comp_whiskerRight, whisker_assoc_symm,
                       ←assoc (α_ (F.map f.dom_map) (F.map (𝟙 B.ob)) B.map).hom, Iso.hom_inv_id,
                       id_comp, ←Bicategory.comp_whiskerRight, ←LaxFunctor.map₂_rightUnitor_hom]
            simp

/- Right unitor reverse direction -/
@[simps]
def rightUnitorInv {A B : F ↓ X} (f : A ⟶ B) : f ⟶ f ≫ (𝟙 B) where
  map := by simpa using (ρ_ f.dom_map).inv
  icc := by simp

/- Right unitor isomorphism part 1 -/
@[simp]
theorem rightUnitor_hom_inv_id {A B : F ↓ X} (f : A ⟶ B) :
    rightUnitorHom F X f ≫ rightUnitorInv F X f = 𝟙 (f ≫ 𝟙 B) := by
  refine Hom₂.ext ?_
  change _ ≫ _ = 𝟙 _
  simp

/- Right unitor isomorphism part 2 -/
@[simp]
theorem rightUnitor_inv_hom_id {A B : F ↓ X} (f : A ⟶ B) :
    rightUnitorInv F X f ≫ rightUnitorHom F X f = 𝟙 f := by
  refine Hom₂.ext ?_
  change _ ≫ _ = 𝟙 _
  simp

/-- Right unitor 2-cetell.
Given a 1-cell `(p, θ) : (A₀, f₀) ⟶ (A₁, f₁)`, the right unitor `r_B` in `B` is the right unitor in
`F ↓ X`: `r_B : (p, θ)(1_{A_0}, r') ⟶ (p, θ)`. -/
@[simps]
def rightUnitor {A B : F ↓ X} (f : A ⟶ B) : f ≫ (𝟙 B) ≅ f where
  hom := rightUnitorHom F X f
  inv := rightUnitorInv F X f
  hom_inv_id := rightUnitor_hom_inv_id F X f
  inv_hom_id := rightUnitor_inv_hom_id F X f

@[simp]
theorem whiskerRight_id {A B : F ↓ X} {f g : A ⟶ B} (η : f ⟶ g) :
    whiskerRight F X η (id₁ F X B) = (rightUnitor F X f).hom ≫ η ≫ (rightUnitor F X g).inv := by
  refine Hom₂.ext ?_
  change _ = _ ≫ _ ≫ _
  simp

@[simp]
theorem triangle {A B C : F ↓ X} (f : A ⟶ B) (g : B ⟶ C) :
    (associatorHom F X f (id₁ F X B) g) ≫ whiskerLeft F X f (leftUnitorHom F X g) =
    whiskerRight F X (rightUnitor F X f).hom g := by
  refine Hom₂.ext ?_
  change _ ≫ _ = _
  simp

@[simp]
instance : Bicategory (F ↓ X) where
  whiskerLeft f _ _ η := whiskerLeft F X f η
  whiskerRight f η := whiskerRight F X f η
  associator f g h := associator F X f g h
  leftUnitor f := leftUnitor F X f
  rightUnitor f := rightUnitor F X f
  whiskerLeft_id f g := whiskerLeft_id F X f g
  whiskerLeft_comp f _ _ _ η θ := whiskerLeft_comp F X f η θ
  id_whiskerLeft η := id_whiskerLeft F X η
  comp_whiskerLeft f g _ _ η := comp_whiskerLeft F X f g η
  id_whiskerRight f g := id_whiskerRight F X f g
  comp_whiskerRight η θ f := comp_whiskerRight F X η θ f
  whiskerRight_id η := whiskerRight_id F X η
  whiskerRight_comp η f g := whiskerRight_comp F X η f g
  whisker_assoc f _ _ η g := whisker_assoc F X f η g
  whisker_exchange η θ := whisker_exchange F X η θ
  pentagon f g h i := pentagon F X f g h i
  triangle f g := triangle F X f g

namespace ChangeOfSlice

variable {X Y : C} (f : X ⟶ Y)

/-- Assignment of the change of slice functor F ↓ u on objects: `(A, f_A) ↦ (A, uf_A))`. -/
@[simps]
def obj : (F ↓ X) → F ↓ Y := fun A => Obj.mk A.ob (A.map ≫ f)

/-- Assignment on 1-cells: `(p, θ) ↦ (p, a_C^{-1} ∘ (1_u ∗ θ))`. -/
@[simps]
def map {A B : F ↓ X} : (A ⟶ B) → (obj F f A ⟶ obj F f B) :=
    fun g => Hom₁.mk g.dom_map (g.cod_map ▷ f ≫ (α_ _ _ _).hom)

@[simp]
theorem map_id (A : F ↓ X) : map F f (id₁ F X A) = 𝟙 (obj F f A) := by
  refine Hom₁.ext ?_ ?_
  · simp
  simp

@[simp]
theorem map_comp {A B C : F ↓ X} (g : A ⟶ B) (h : B ⟶ C) :
    map F f (comp₁ F X g h) = map F f g ≫ map F f h := by
  refine Hom₁.ext ?_ ?_
  · simp
  simp

/-- Assignment on 2-cells: `α ↦ α`. -/
@[simps]
def map₂ {A B : F ↓ X} {g h : A ⟶ B} : (g ⟶ h) → (map F f g ⟶ map F f h) :=
    fun η => Hom₂.mk η.map (by simp [←η.icc])

@[simp]
theorem eqToHom_map {A B : F ↓ X} {g h : A ⟶ B} (e : g = h)
    : (eqToHom e).map = eqToHom (congrArg Hom₁.dom_map e) := by
  cases e
  simp
  rfl

@[simp]
theorem map₂_whisker_left {A B C : F ↓ X} (g : A ⟶ B) {h i : B ⟶ C} (η : h ⟶ i) :
    map₂ F f (whiskerLeft F X g η) = eqToHom (map_comp F f g h) ≫ map F f g ◁ map₂ F f η
    ≫ eqToHom (map_comp F f g i).symm := by
  refine Hom₂.ext ?_
  change _ = _ ≫ _ ≫ _
  rw [eqToHom_map, eqToHom_map]
  simp

@[simp]
theorem map₂_whisker_right {A B C : F ↓ X} {g h : A ⟶ B} (η : g ⟶ h) (i : B ⟶ C) :
    map₂ F f (whiskerRight F X η i) = eqToHom (map_comp F f g i) ≫ map₂ F f η ▷ map F f i
    ≫ eqToHom (map_comp F f h i).symm := by
  refine Hom₂.ext ?_
  change _ = _ ≫ _ ≫ _
  rw [eqToHom_map, eqToHom_map]
  simp

@[simp]
theorem map₂_left_unitor {A B : F ↓ X} (g : A ⟶ B) :
    map₂ F f (leftUnitorHom F X g) =
    eqToHom (by simp) ≫ (λ_ (map F f g)).hom := by
  refine Hom₂.ext ?_
  change _ = _ ≫ _
  rw [eqToHom_map]
  simp

@[simp]
theorem map₂_right_unitor {A B : F ↓ X} (g : A ⟶ B) :
    map₂ F f (rightUnitorHom F X g) =
    eqToHom (by simp) ≫ (ρ_ (map F f g)).hom := by
  refine Hom₂.ext ?_
  change _ = _ ≫ _
  rw [eqToHom_map]
  simp

@[simp]
theorem map₂_associator {A B C D : F ↓ X} (g : A ⟶ B) (h : B ⟶ C) (i : C ⟶ D) :
    map₂ F f (associatorHom F X g h i) =
    eqToHom (by simp) ≫ (α_ (map F f g) (map F f h) (map F f i)).hom
    ≫ eqToHom (by simp) := by
  refine Hom₂.ext ?_
  change _ = _ ≫ _ ≫ _
  rw [eqToHom_map, eqToHom_map]
  simp

@[simp]
def changeOfSliceCore {X Y : C} (f : X ⟶ Y) : StrictPseudofunctorCore (F ↓ X) (F ↓ Y) where
  obj := obj F f
  map := map F f
  map₂ := map₂ F f
  map_id := map_id F f
  map_comp := map_comp F f
  map₂_whisker_left := map₂_whisker_left F f
  map₂_whisker_right := map₂_whisker_right F f
  map₂_left_unitor := map₂_left_unitor F f
  map₂_right_unitor := map₂_right_unitor F f
  map₂_associator := map₂_associator F f

/-- The change of slice strict pseudofunctor for a 1-cell u : X ⟶ Y, F ↓ u : (F ↓ X) ⥤ᵖ (F ↓ Y). -/
def changeOfSlice {X Y : C} (f : X ⟶ Y) :
    StrictPseudofunctor (F ↓ X) (F ↓ Y) := StrictPseudofunctor.mk' (changeOfSliceCore F f)

end ChangeOfSlice

end LaxSlice

end CategoryTheory
