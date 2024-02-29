/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison, Bhavik Mehta, Brendan Murphy
-/
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.Mates

#align_import category_theory.monoidal.functor from "leanprover-community/mathlib"@"3d7987cda72abc473c7cdbbb075170e9ac620042"

/-!
# (Co)Lax and strong monoidal functors

A lax monoidal functor `F` between monoidal categories `C` and `D`
is a functor between the underlying categories equipped with morphisms
* `η : 𝟙_ D ⟶ F.obj (𝟙_ C)` (called the unit morphism)
* `μ X Y : (F.obj X) ⊗ (F.obj Y) ⟶ F.obj (X ⊗ Y)` (called the tensorator, or strength).
satisfying various axioms.
It is more common in the literature to use `ε` in place of `η`, but this
is inconsistent with the convention that `η` is a unit and `ε` is a counit for
(co)monoid objects (this is how the symbols are used for monads, comonads and bialgebras).

A colax monoidal functor `F` between monoidal categories `C` and `D`
is a functor between the underlying categories equipped with morphisms
* `ε : F.obj (𝟙_ C) ⟶ 𝟙_ D` (called the counit morphism)
* `δ X Y : F.obj (X ⊗ Y) ⟶ (F.obj X) ⊗ (F.obj Y)` (called the cotensorator).
satisfying various axioms.
These are equivalent to lax monoidal functors between `Cᵒᵖ` and `Dᵒᵖ`.
An alternate name for these is oplax monoidal.

A (strong) monoidal functor is equivalently
* A lax monoidal functor for which `η` and `μ` are isomorphisms.
* A colax monoidal functor for which `ε` and `δ` are isomorphisms.
* A pair of lax and colax structures on a functor where `η, ε` and `μ, δ` are inverse pairs.

We show that the composition of ((co)lax) monoidal functors gives a ((co)lax) monoidal functor.

See also `CategoryTheory.Monoidal.Functorial` for a typeclass decorating an object-level
function with the additional data of a monoidal functor.
This is useful when stating that a pre-existing functor is monoidal.

See `CategoryTheory.Monoidal.NaturalTransformation` for monoidal natural transformations.

We show in `CategoryTheory.Monoidal.Mon_` that lax monoidal functors take monoid objects
to monoid objects.

## References

See <https://stacks.math.columbia.edu/tag/0FFL>.
-/


open CategoryTheory
open Quiver.Hom (op_inj unop_inj)

universe v₀ u₀ v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory.Category

open CategoryTheory.Functor

namespace CategoryTheory

variable {B : Type u₀} [Category.{v₀} B] [MonoidalCategory.{v₀} B]
  (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C]
  (D : Type u₂) [Category.{v₂} D] [MonoidalCategory.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory.{v₃} E]

open MonoidalCategory

-- The direction of `left_unitality` and `right_unitality` as simp lemmas may look strange:
-- remember the rule of thumb that component indices of natural transformations
-- "weigh more" than structural maps.
-- (However by this argument `associativity` is currently stated backwards!)
/-- A lax monoidal functor is a functor `F : C ⥤ D` between monoidal categories,
equipped with morphisms `η : 𝟙 _D ⟶ F.obj (𝟙_ C)` and
`μ X Y : F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y)`, satisfying the appropriate coherences. -/
structure LaxMonoidalFunctor extends C ⥤ D where
  /-- unit morphism -/
  η : 𝟙_ D ⟶ obj (𝟙_ C)
  /-- tensorator -/
  μ : ∀ X Y : C, obj X ⊗ obj Y ⟶ obj (X ⊗ Y)
  μ_natural_left :
    ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
      (map f ⊗ 𝟙 (obj X')) ≫ μ Y X' = μ X X' ≫ map (f ⊗ 𝟙 X') := by
    aesop_cat
  μ_natural_right :
    ∀ {X Y : C} (X' : C) (f : X ⟶ Y) ,
      (𝟙 (obj X') ⊗ map f) ≫ μ X' Y = μ X' X ≫ map (𝟙 X' ⊗ f) := by
    aesop_cat
  /-- associativity of the tensorator -/
  associativity :
    ∀ X Y Z : C,
      (μ X Y ⊗ 𝟙 (obj Z)) ≫ μ (X ⊗ Y) Z ≫ map (α_ X Y Z).hom =
        (α_ (obj X) (obj Y) (obj Z)).hom ≫ (𝟙 (obj X) ⊗ μ Y Z) ≫ μ X (Y ⊗ Z) := by
    aesop_cat
  -- unitality
  left_unitality : ∀ X : C, (λ_ (obj X)).hom = (η ⊗ 𝟙 (obj X)) ≫ μ (𝟙_ C) X ≫ map (λ_ X).hom :=
    by aesop_cat
  right_unitality : ∀ X : C, (ρ_ (obj X)).hom = (𝟙 (obj X) ⊗ η) ≫ μ X (𝟙_ C) ≫ map (ρ_ X).hom :=
    by aesop_cat
#align category_theory.lax_monoidal_functor CategoryTheory.LaxMonoidalFunctor

/-- Notation for a lax monoidal functor between monoidal categories. -/
scoped [CategoryTheory] infixr:26 " ⥤⊗ℓ " => LaxMonoidalFunctor

/-- A colax monoidal functor is a functor `F : C ⥤ D` between monoidal categories,
equipped with morphisms `ε : F.obj (𝟙_ C) ⟶ 𝟙 _D` and
`δ X Y : F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y`, satisfying the appropriate coherences. -/
structure ColaxMonoidalFunctor extends C ⥤ D where
  /-- counit morphism -/
  ε : obj (𝟙_ C) ⟶ 𝟙_ D
  /-- cotensorator -/
  δ : ∀ X Y : C, obj (X ⊗ Y) ⟶ obj X ⊗ obj Y
  δ_natural_left :
    ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
      map (f ⊗ 𝟙 X') ≫ δ Y X' = δ X X' ≫ (map f ⊗ 𝟙 (obj X')) := by
    aesop_cat
  δ_natural_right :
    ∀ {X Y : C} (X' : C) (f : X ⟶ Y) ,
      map (𝟙 X' ⊗ f) ≫ δ X' Y = δ X' X ≫ (𝟙 (obj X') ⊗ map f) := by
    aesop_cat
  /-- coassociativity of the cotensorator -/
  coassociativity :
    ∀ X Y Z : C,
      map (α_ X Y Z).hom ≫ δ X (Y ⊗ Z) ≫ (𝟙 (obj X) ⊗ δ Y Z) =
        δ (X ⊗ Y) Z ≫ (δ X Y ⊗ 𝟙 (obj Z)) ≫ (α_ (obj X) (obj Y) (obj Z)).hom := by
    aesop_cat
  -- unitality
  left_counitality : ∀ X : C, δ (𝟙_ C) X ≫ (ε ⊗ 𝟙 (obj X)) ≫ (λ_ (obj X)).hom = map (λ_ X).hom :=
    by aesop_cat
  right_counitality : ∀ X : C, δ X (𝟙_ C) ≫ (𝟙 (obj X) ⊗ ε) ≫ (ρ_ (obj X)).hom = map (ρ_ X).hom :=
    by aesop_cat

/-- Notation for a colax monoidal functor between monoidal categories. -/
scoped [CategoryTheory] infixr:26 " ⥤⊗c " => ColaxMonoidalFunctor
-- very irritating that unicode doesn't have a subscript c

/--
A monoidal functor is a lax monoidal functor for which the tensorator and unitor are isomorphisms,
equivalently a colax monoidal functor for which the cotensorator and the counitor are isomorphisms,
equivalently a pair of a lax and colax monoidal functors which have the same underlying functor
and where the structure maps are inverses.

See <https://stacks.math.columbia.edu/tag/0FFL>.
-/
structure MonoidalFunctor
    extends LaxMonoidalFunctor.{v₁, v₂} C D, ColaxMonoidalFunctor.{v₁, v₂} C D where
  η_ε_id : η ≫ ε = 𝟙 (𝟙_ D) := by aesop_cat
  ε_η_id : ε ≫ η = 𝟙 (obj (𝟙_ C)) := by aesop_cat
  μ_δ_id : (X Y : C) → μ X Y ≫ δ X Y = 𝟙 (obj X ⊗ obj Y) := by aesop_cat
  δ_μ_id : (X Y : C) → δ X Y ≫ μ X Y = 𝟙 (obj (X ⊗ Y)) := by aesop_cat
#align category_theory.monoidal_functor CategoryTheory.MonoidalFunctor

/-- Notation for a (strong) monoidal functor between monoidal categories. -/
scoped [CategoryTheory] infixr:26 " ⥤⊗s " => MonoidalFunctor

--Porting note: was `[simp, reassoc.1]`
attribute [reassoc (attr := simp)] LaxMonoidalFunctor.μ_natural_left
attribute [reassoc (attr := simp)] LaxMonoidalFunctor.μ_natural_right

attribute [simp] LaxMonoidalFunctor.left_unitality

attribute [simp] LaxMonoidalFunctor.right_unitality

--Porting note: was `[simp, reassoc.1]`
attribute [reassoc (attr := simp)] LaxMonoidalFunctor.associativity

attribute [reassoc (attr := simp)] ColaxMonoidalFunctor.δ_natural_left
attribute [reassoc (attr := simp)] ColaxMonoidalFunctor.δ_natural_right

attribute [simp] ColaxMonoidalFunctor.left_counitality
attribute [simp] ColaxMonoidalFunctor.right_counitality

attribute [reassoc (attr := simp)] ColaxMonoidalFunctor.coassociativity

attribute [reassoc (attr := simp)] MonoidalFunctor.η_ε_id
attribute [reassoc (attr := simp)] MonoidalFunctor.ε_η_id
attribute [reassoc (attr := simp)] MonoidalFunctor.μ_δ_id
attribute [reassoc (attr := simp)] MonoidalFunctor.δ_μ_id

initialize_simps_projections ColaxMonoidalFunctor (+toFunctor, -obj, -map)
initialize_simps_projections LaxMonoidalFunctor (+toFunctor, -obj, -map)
initialize_simps_projections MonoidalFunctor (+toFunctor, -obj, -map)

variable {C D}

section bootstrap

namespace LaxMonoidalFunctor

variable (F : C ⥤⊗ℓ D)

--Porting note: was `[simp, reassoc.1]`
@[reassoc (attr := simp)]
theorem left_unitality_inv (X : C) :
    (λ_ (F.obj X)).inv ≫ (F.η ⊗ 𝟙 (F.obj X)) ≫ F.μ (𝟙_ C) X = F.map (λ_ X).inv := by
  rw [Iso.inv_comp_eq, F.left_unitality, Category.assoc, Category.assoc, ← F.map_comp,
    Iso.hom_inv_id, F.map_id, comp_id]
#align category_theory.lax_monoidal_functor.left_unitality_inv CategoryTheory.LaxMonoidalFunctor.left_unitality_inv

--Porting note: was `[simp, reassoc.1]`
@[reassoc (attr := simp)]
theorem right_unitality_inv (X : C) :
    (ρ_ (F.obj X)).inv ≫ (𝟙 (F.obj X) ⊗ F.η) ≫ F.μ X (𝟙_ C) = F.map (ρ_ X).inv := by
  rw [Iso.inv_comp_eq, F.right_unitality, Category.assoc, Category.assoc, ← F.map_comp,
    Iso.hom_inv_id, F.map_id, comp_id]
#align category_theory.lax_monoidal_functor.right_unitality_inv CategoryTheory.LaxMonoidalFunctor.right_unitality_inv

--Porting note: was `[simp, reassoc.1]`
@[reassoc (attr := simp)]
theorem associativity_inv (X Y Z : C) :
    (𝟙 (F.obj X) ⊗ F.μ Y Z) ≫ F.μ X (Y ⊗ Z) ≫ F.map (α_ X Y Z).inv =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫ (F.μ X Y ⊗ 𝟙 (F.obj Z)) ≫ F.μ (X ⊗ Y) Z := by
  rw [Iso.eq_inv_comp, ← F.associativity_assoc, ← F.map_comp, Iso.hom_inv_id,
    F.map_id, comp_id]
#align category_theory.lax_monoidal_functor.associativity_inv CategoryTheory.LaxMonoidalFunctor.associativity_inv

end LaxMonoidalFunctor

namespace ColaxMonoidalFunctor

variable (F : C ⥤⊗c D)

@[reassoc (attr := simp)]
theorem left_counitality_inv (X : C) :
    F.map (λ_ X).inv ≫ F.δ (𝟙_ C) X ≫ (F.ε ⊗ 𝟙 (F.obj X)) = (λ_ (F.obj X)).inv := by
  rw [← mapIso_inv, Iso.inv_comp_eq, mapIso_hom, ← F.left_counitality,
      Category.assoc, Category.assoc, Iso.hom_inv_id, comp_id]

@[reassoc (attr := simp)]
theorem right_counitality_inv (X : C) :
    F.map (ρ_ X).inv ≫ F.δ X (𝟙_ C) ≫ (𝟙 (F.obj X) ⊗ F.ε) = (ρ_ (F.obj X)).inv := by
  rw [← mapIso_inv, Iso.inv_comp_eq, mapIso_hom, ← F.right_counitality,
      Category.assoc, Category.assoc, Iso.hom_inv_id, comp_id]

@[reassoc (attr := simp)]
theorem coassociativity_inv (X Y Z : C) :
    F.map (α_ X Y Z).inv ≫ F.δ (X ⊗ Y) Z ≫ (F.δ X Y ⊗ 𝟙 (F.obj Z)) =
      F.δ X (Y ⊗ Z) ≫ (𝟙 (F.obj X) ⊗ F.δ Y Z) ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv := by
  rw [← mapIso_inv, Iso.inv_comp_eq, mapIso_hom, F.coassociativity_assoc,
      Iso.hom_inv_id, comp_id]

end ColaxMonoidalFunctor

end bootstrap

section opposites

attribute [local ext] unop_inj in
@[simps, pp_dot]
def LaxMonoidalFunctor.op (F : C ⥤⊗ℓ D) : Cᵒᵖ ⥤⊗c Dᵒᵖ where
  ε := F.η.op
  δ X Y := (F.μ X.unop Y.unop).op
  __ := F.toFunctor.op

@[simps, pp_dot]
def LaxMonoidalFunctor.unop (F : Cᵒᵖ ⥤⊗ℓ Dᵒᵖ) : C ⥤⊗c D where
  ε := F.η.unop
  δ X Y := (F.μ (.op X) (.op Y)).unop
  δ_natural_left f X' := op_inj <| by simp
  δ_natural_right X' f := op_inj <| by simp
  coassociativity X Y Z := op_inj <| by simp
  left_counitality X := op_inj <| by simp
  right_counitality X := op_inj <| by simp
  __ := F.toFunctor.unop

attribute [local ext] unop_inj in
@[simps, pp_dot]
def ColaxMonoidalFunctor.op (F : C ⥤⊗c D) : Cᵒᵖ ⥤⊗ℓ Dᵒᵖ where
  η := F.ε.op
  μ X Y := (F.δ X.unop Y.unop).op
  __ := F.toFunctor.op

@[simps, pp_dot]
def ColaxMonoidalFunctor.unop (F : Cᵒᵖ ⥤⊗c Dᵒᵖ) : C ⥤⊗ℓ D where
  η := F.ε.unop
  μ X Y := (F.δ (.op X) (.op Y)).unop
  μ_natural_left f X' := op_inj <| by simp
  μ_natural_right X' f := op_inj <| by simp
  associativity X Y Z := op_inj <| by simp
  left_unitality X := op_inj <| by simp
  right_unitality X := op_inj <| by simp
  __ := F.toFunctor.unop

attribute [local ext] unop_inj in
@[simps! ε η δ μ toFunctor, pp_dot]
def MonoidalFunctor.op (F : C ⥤⊗s D) : Cᵒᵖ ⥤⊗s Dᵒᵖ where
  __ := F.toLaxMonoidalFunctor.op
  __ := F.toColaxMonoidalFunctor.op

@[simps! ε η δ μ toFunctor, pp_dot]
def MonoidalFunctor.unop (F : Cᵒᵖ ⥤⊗s Dᵒᵖ) : C ⥤⊗s D where
  η_ε_id := op_inj <| by simp
  ε_η_id := op_inj <| by simp
  μ_δ_id X Y := op_inj <| by simp
  δ_μ_id X Y := op_inj <| by simp
  __ := F.toLaxMonoidalFunctor.unop
  __ := F.toColaxMonoidalFunctor.unop

end opposites

-- When `rewrite_search` lands, add @[search] attributes to
-- LaxMonoidalFunctor.μ_natural LaxMonoidalFunctor.left_unitality
-- LaxMonoidalFunctor.right_unitality LaxMonoidalFunctor.associativity
namespace LaxMonoidalFunctor

section

variable (F : C ⥤⊗ℓ D)

@[reassoc (attr := simp)]
theorem μ_natural {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
      (F.map f ⊗ F.map g) ≫ F.μ Y Y' = F.μ X X' ≫ F.map (f ⊗ g) := by
  rw [← id_tensor_comp_tensor_id_assoc, μ_natural_left, μ_natural_right_assoc,
      ← F.map_comp, id_tensor_comp_tensor_id]

/-- The tensorator of a lax monoidal functor as a natural transformation. -/
@[simps, pp_dot]
def μNatTrans : .prod F.toFunctor F.toFunctor ⋙ tensor D ⟶ tensor C ⋙ F.toFunctor where
  app XY := F.μ XY.1 XY.2

@[reassoc (attr := simp)]
theorem associativity' (X Y Z : C) :
    (F.μ X Y ▷ F.obj Z) ≫ F.μ (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom =
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ ((F.obj X) ◁ F.μ Y Z) ≫ F.μ X (Y ⊗ Z) := by
  simp [← id_tensorHom, ← tensorHom_id]

@[reassoc]
theorem left_unitality' (X : C) :
    (λ_ (F.obj X)).hom = (F.η ▷ F.obj X) ≫ F.μ (𝟙_ C) X ≫ F.map (λ_ X).hom := by
  simp [← id_tensorHom, ← tensorHom_id]

@[reassoc]
theorem right_unitality' (X : C) :
    (ρ_ (F.obj X)).hom = (F.obj X ◁ F.η) ≫ F.μ X (𝟙_ C) ≫ F.map (ρ_ X).hom := by
  simp [← id_tensorHom, ← tensorHom_id]

@[reassoc (attr := simp)]
theorem μ_natural_left' {X Y : C} (f : X ⟶ Y) (X' : C) :
      F.map f ▷ F.obj X' ≫ F.μ Y X' = F.μ X X' ≫ F.map (f ▷ X') := by
  simp [← id_tensorHom, ← tensorHom_id]

@[reassoc (attr := simp)]
theorem μ_natural_right' {X Y : C} (X' : C) (f : X ⟶ Y) :
      F.obj X' ◁ F.map f ≫ F.μ X' Y = F.μ X' X ≫ F.map (X' ◁ f) := by
  simp [← id_tensorHom, ← tensorHom_id]

@[reassoc (attr := simp)]
theorem left_unitality_inv' (X : C) :
    (λ_ (F.obj X)).inv ≫ (F.η ▷ F.obj X) ≫ F.μ (𝟙_ C) X = F.map (λ_ X).inv := by
  simp [← id_tensorHom, ← tensorHom_id]

@[reassoc (attr := simp)]
theorem right_unitality_inv' (X : C) :
    (ρ_ (F.obj X)).inv ≫ (F.obj X ◁ F.η) ≫ F.μ X (𝟙_ C) = F.map (ρ_ X).inv := by
  simp [← id_tensorHom, ← tensorHom_id]

@[reassoc (attr := simp)]
theorem associativity_inv' (X Y Z : C) :
    (F.obj X ◁ F.μ Y Z) ≫ F.μ X (Y ⊗ Z) ≫ F.map (α_ X Y Z).inv =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫ (F.μ X Y ▷ F.obj Z) ≫ F.μ (X ⊗ Y) Z := by
  simp [← id_tensorHom, ← tensorHom_id]

#check F.associativity

/-
(F.obj X ⊗ F.obj Y) ⊗ F.obj Z ⟶ F.obj (X ⊗ Y ⊗ Z)

F.toFunctor.prod (F.toFunctor.prod F.toFunctor) ⋙ leftAssocTensor D ⟶
rightAssocTensor C ⋙ F.toFunctor
-/

/-
(μ X Y ⊗ 𝟙 (F.obj Z)) ≫
  μ (X ⊗ Y) Z ≫
    map (α_ X Y Z).hom =
(α_ (obj X) (obj Y) (obj Z)).hom ≫
  (𝟙 (obj X) ⊗ μ Y Z) ≫
    μ X (Y ⊗ Z)
-/

namespace associativity_nat_trans
-- TODO: make these coherences isos
def coherence1 :=
  (Functor.associator _ _ _).inv ≫
    whiskerRight ((transferNatTrans (prod.associativity C C C).symm.toAdjunction
                                    (prod.associativity D D D).symm.toAdjunction).symm
                    (prod.associator_naturality _ _ _).hom)
                  ((tensor D).prod (𝟭 D) ⋙ tensor D) ≫
      (Functor.associator _ _ _).hom ≫
        whiskerLeft (prod.inverseAssociator C C C) ((Functor.associator _ _ _).inv ≫
          whiskerRight ((prodCompIso _ _ _ _).inv ≫
            .prod (𝟙 (F.toFunctor.prod F.toFunctor ⋙ tensor D))
                  F.toFunctor.rightUnitor.hom) (tensor D))

@[simp]
lemma coherence1_app (X : C × C × C) :
    (coherence1 F).app X = 𝟙 ((F.obj X.1 ⊗ F.obj X.2.1) ⊗ F.obj X.2.2) := by
  dsimp [coherence1, Equivalence.symm]
  simp only [map_id, comp_id, tensor_id]

def coherence2 :=
  whiskerLeft (prod.inverseAssociator C C C)
    (whiskerRight (.prod (𝟙 _) F.toFunctor.leftUnitor.inv) (tensor D) ≫
      whiskerRight (prodCompIso _ _ _ _).hom (tensor D) ≫
        (((tensor C).prod (𝟭 C)).associator (.prod F.toFunctor F.toFunctor) _).hom)

@[simp]
lemma coherence2_app (X : C × C × C) :
    (coherence2 F).app X = 𝟙 (F.obj (X.1 ⊗ X.2.1) ⊗ F.obj X.2.2) := by
  dsimp [coherence2]
  simp only [tensor_id, comp_id]

def coherence3 :=
  whiskerLeft (prod.inverseAssociator C C C)
    (Functor.associator ((tensor C).prod (𝟭 C)) (tensor C) F.toFunctor).inv ≫
    (Functor.associator _ _ _).inv

@[simp]
lemma coherence3_app (X : C × C × C) :
    (coherence3 F).app X = 𝟙 (F.obj ((X.1 ⊗ X.2.1) ⊗ X.2.2)) := by
  dsimp [coherence3]
  simp only [comp_id]

-- lemma thm :
--     coherence1 F ≫ whiskerLeft _ (whiskerRight (.prod F.μNatTrans (𝟙 _)) _) ≫
--       coherence2 F ≫ whiskerLeft _ (whiskerLeft _ F.μNatTrans) ≫
--         coherence3 F ≫ whiskerRight (associatorNatIso C).hom _ =
--   --   (α_ (obj X) (obj Y) (obj Z)).hom ≫
--   -- (𝟙 (obj X) ⊗ μ Y Z) ≫
--   --   μ X (Y ⊗ Z)

--     (by
--       let a := (associatorNatIso C).hom
--       unfold leftAssocTensor at
--       admit) := sorry

end associativity_nat_trans

end

/--
A constructor for lax monoidal functors whose axioms are described by `tensorHom` instead of
`whiskerLeft` and `whiskerRight`.
-/
@[simps]
def ofTensorHom (F : C ⥤ D)
    /- unit morphism -/
    (η : 𝟙_ D ⟶ F.obj (𝟙_ C))
    /- tensorator -/
    (μ : ∀ X Y : C, F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y))
    (μ_natural :
      ∀ {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'),
        (F.map f ⊗ F.map g) ≫ μ Y Y' = μ X X' ≫ F.map (f ⊗ g) := by
      aesop_cat)
    /- associativity of the tensorator -/
    (associativity :
      ∀ X Y Z : C,
        (μ X Y ⊗ 𝟙 (F.obj Z)) ≫ μ (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom =
          (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ (𝟙 (F.obj X) ⊗ μ Y Z) ≫ μ X (Y ⊗ Z) :=
        by aesop_cat)
    /- unitality -/
    (left_unitality :
      ∀ X : C, (λ_ (F.obj X)).hom = (η ⊗ 𝟙 (F.obj X)) ≫ μ (𝟙_ C) X ≫ F.map (λ_ X).hom :=
        by aesop_cat)
    (right_unitality :
      ∀ X : C, (ρ_ (F.obj X)).hom = (𝟙 (F.obj X) ⊗ η) ≫ μ X (𝟙_ C) ≫ F.map (ρ_ X).hom :=
        by aesop_cat) : C ⥤⊗ℓ D where
  η := η
  μ := μ
  μ_natural_left := fun f X' => by
    simp_rw [← F.map_id, μ_natural]
  μ_natural_right := fun X' f => by
    simp_rw [← F.map_id, μ_natural]
  associativity := associativity
  left_unitality := left_unitality
  right_unitality := right_unitality
  __ := F

end LaxMonoidalFunctor

namespace ColaxMonoidalFunctor

section

variable (F : C ⥤⊗c D)

@[reassoc (attr := simp)]
theorem δ_natural {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    F.map (f ⊗ g) ≫ F.δ Y Y' = F.δ X X' ≫ (F.map f ⊗ F.map g) :=
  op_inj <| Eq.symm <| F.op.μ_natural f.op g.op

/-- The cotensorator of a colax monoidal functor as a natural transformation. -/
@[simps, pp_dot]
def δNatTrans : tensor C ⋙ F.toFunctor ⟶ .prod F.toFunctor F.toFunctor ⋙ tensor D where
  app XY := F.δ XY.1 XY.2

@[reassoc (attr := simp)]
theorem coassociativity' (X Y Z : C) :
    F.map (α_ X Y Z).hom ≫ F.δ X (Y ⊗ Z) ≫ (F.obj X ◁ F.δ Y Z) =
      F.δ (X ⊗ Y) Z ≫ (F.δ X Y ▷ F.obj Z) ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom := by
  convert op_inj (F.op.associativity_inv' (.op X) (.op Y) (.op Z)) using 1 <;> simp

@[reassoc]
theorem left_counitality' (X : C) :
    F.δ (𝟙_ C) X ≫ (F.ε ▷ F.obj X) ≫ (λ_ (F.obj X)).hom = F.map (λ_ X).hom := by
  convert op_inj (F.op.left_unitality_inv' (.op X)) using 1; simp

@[reassoc]
theorem right_counitality' (X : C) :
    F.δ X (𝟙_ C) ≫ (F.obj X ◁ F.ε) ≫ (ρ_ (F.obj X)).hom = F.map (ρ_ X).hom := by
  convert op_inj (F.op.right_unitality_inv' (.op X)) using 1; simp

@[reassoc (attr := simp)]
theorem δ_natural_left' {X Y : C} (f : X ⟶ Y) (X' : C) :
    F.map (f ▷ X') ≫ F.δ Y X' = F.δ X X' ≫ (F.map f ▷ F.obj X') :=
  op_inj (F.op.μ_natural_left' f.op (.op X')).symm

@[reassoc (attr := simp)]
theorem μ_natural_right' {X Y : C} (X' : C) (f : X ⟶ Y) :
    F.map (X' ◁ f) ≫ F.δ X' Y = F.δ X' X ≫ (F.obj X' ◁ F.map f) :=
  op_inj (F.op.μ_natural_right' (.op X') f.op).symm

@[reassoc (attr := simp)]
theorem left_counitality_inv' (X : C) :
    F.map (λ_ X).inv ≫ F.δ (𝟙_ C) X ≫ (F.ε ▷ F.obj X) = (λ_ (F.obj X)).inv := by
  convert op_inj (F.op.left_unitality' (.op X)).symm using 1; simp

@[reassoc (attr := simp)]
theorem right_unitality_inv' (X : C) :
    F.map (ρ_ X).inv ≫ F.δ X (𝟙_ C) ≫ (F.obj X ◁ F.ε) = (ρ_ (F.obj X)).inv := by
  convert op_inj (F.op.right_unitality' (.op X)).symm using 1; simp

@[reassoc (attr := simp)]
theorem coassociativity_inv' (X Y Z : C) :
    F.map (α_ X Y Z).inv ≫ F.δ (X ⊗ Y) Z ≫ (F.δ X Y ▷ F.obj Z) =
      F.δ X (Y ⊗ Z) ≫ (F.obj X ◁ F.δ Y Z) ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv := by
  convert op_inj (F.op.associativity' (.op X) (.op Y) (.op Z)) using 1 <;> simp

end

/--
A constructor for colax monoidal functors whose axioms are described by `tensorHom` instead of
`whiskerLeft` and `whiskerRight`.
-/
@[simps]
def ofTensorHom (F : C ⥤ D)
    /- counit morphism -/
    (ε : F.obj (𝟙_ C) ⟶ 𝟙_ D)
    /- cotensorator -/
    (δ : ∀ X Y : C, F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y)
    (δ_natural :
      ∀ {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'),
        F.map (f ⊗ g) ≫ δ Y Y' = δ X X' ≫ (F.map f ⊗ F.map g) := by
      aesop_cat)
    /- coassociativity of the cotensorator -/
    (coassociativity :
      ∀ X Y Z : C,
        F.map (α_ X Y Z).hom ≫ δ X (Y ⊗ Z) ≫ (𝟙 (F.obj X) ⊗ δ Y Z) =
          δ (X ⊗ Y) Z ≫ (δ X Y ⊗ 𝟙 (F.obj Z)) ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom := by
      aesop_cat)
    (left_counitality :
      ∀ X : C, δ (𝟙_ C) X ≫ (ε ⊗ 𝟙 (F.obj X)) ≫ (λ_ (F.obj X)).hom = F.map (λ_ X).hom :=
        by aesop_cat)
    (right_counitality :
      ∀ X : C, δ X (𝟙_ C) ≫ (𝟙 (F.obj X) ⊗ ε) ≫ (ρ_ (F.obj X)).hom = F.map (ρ_ X).hom :=
        by aesop_cat) : C ⥤⊗c D where
  ε := ε
  δ := δ
  δ_natural_left := fun f X' => by
    simp_rw [← F.map_id, δ_natural]
  δ_natural_right := fun X' f => by
    simp_rw [← F.map_id, δ_natural]
  coassociativity := coassociativity
  left_counitality := left_counitality
  right_counitality := right_counitality
  __ := F

end ColaxMonoidalFunctor

namespace MonoidalFunctor

variable (F : C ⥤⊗s D)

/-- The unit morphism of a (strong) monoidal functor as an isomorphism. -/
@[pp_dot, simps]
def ηIso : 𝟙_ D ≅ F.obj (𝟙_ C) :=
  ⟨F.η, F.ε, F.η_ε_id, F.ε_η_id⟩
#align category_theory.monoidal_functor.ε_iso CategoryTheory.MonoidalFunctor.ηIso

/-- The counit morphism of a (strong) monoidal functor as an isomorphism. -/
@[pp_dot, simps]
def εIso : F.obj (𝟙_ C) ≅ 𝟙_ D :=
  ⟨F.ε, F.η, F.ε_η_id, F.η_ε_id⟩

@[simp]
lemma ηIso_trans_εIso : F.ηIso ≪≫ F.εIso = Iso.refl _ :=
  F.ηIso.self_symm_id

@[simp]
lemma εIso_trans_ηIso : F.εIso ≪≫ F.ηIso = Iso.refl _ :=
  F.εIso.self_symm_id

/-- The tensorator of a (strong) monoidal functor as a natural isomorphism. -/
@[pp_dot, simps! hom inv]
def μNatIso : .prod F.toFunctor F.toFunctor ⋙ tensor D ≅ tensor C ⋙ F.toFunctor :=
  .mk F.μNatTrans F.toColaxMonoidalFunctor.δNatTrans
  -- unfortunately we need to spell out ColaxMonoidalFunctor.δNatTrans, see lean4#3467
#align category_theory.monoidal_functor.μ_nat_iso CategoryTheory.MonoidalFunctor.μNatIso

/-- The cotensorator of a (strong) monoidal functor as a natural isomorphism. -/
@[pp_dot, simps! hom inv]
def δNatIso : tensor C ⋙ F.toFunctor ≅ .prod F.toFunctor F.toFunctor ⋙ tensor D :=
  .mk F.toColaxMonoidalFunctor.δNatTrans F.μNatTrans

/-- The tensorator of a (strong) monoidal functor as a pointwise isomorphism. -/
@[pp_dot, simps!]
def μIso (X Y : C) : F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y) :=
  F.μNatIso.app (X, Y)
#align category_theory.monoidal_functor.μ_iso CategoryTheory.MonoidalFunctor.μIso

/-- The cotensorator of a (strong) monoidal functor as a pointwise isomorphism. -/
@[pp_dot, simps!]
def δIso (X Y : C) : F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y :=
  F.δNatIso.app (X, Y)

@[simp] lemma μNatIso_symm : F.μNatIso.symm = F.δNatIso := rfl
@[simp] lemma δNatIso_symm : F.δNatIso.symm = F.μNatIso := rfl
@[simp] lemma μNatIso_trans_δNatIso : F.μNatIso ≪≫ F.δNatIso = Iso.refl _ :=
  F.μNatIso.self_symm_id
@[simp] lemma δNatIso_trans_μNatIso : F.δNatIso ≪≫ F.μNatIso = Iso.refl _ :=
  F.δNatIso.self_symm_id
@[simp] lemma μIso_symm (X Y : C) : (F.μIso X Y).symm = F.δIso X Y := rfl
@[simp] lemma δIso_symm (X Y : C) : (F.δIso X Y).symm = F.μIso X Y := rfl
@[simp] lemma μIso_trans_δIso (X Y : C) : F.μIso X Y ≪≫ F.δIso X Y = Iso.refl _ :=
  (F.μIso X Y).self_symm_id
@[simp] lemma δIso_trans_μIso (X Y : C) : F.δIso X Y ≪≫ F.μIso X Y = Iso.refl _ :=
  (F.δIso X Y).self_symm_id
@[simp] lemma μNatIso_app_eq_μIso (XY : C × C) :
    F.μNatIso.app XY = F.μIso XY.1 XY.2 := rfl
@[simp] lemma δNatIso_app_eq_δIso (XY : C × C) :
    F.δNatIso.app XY = F.δIso XY.1 XY.2 := rfl

instance : IsIso F.η := inferInstanceAs (IsIso F.ηIso.hom)
instance : IsIso F.ε := inferInstanceAs (IsIso F.εIso.hom)
instance (X Y : C) : IsIso (F.μ X Y) := inferInstanceAs (IsIso (F.μIso X Y).hom)
instance (X Y : C) : IsIso (F.δ X Y) := inferInstanceAs (IsIso (F.δIso X Y).hom)

@[simp] lemma inv_η : inv F.η = F.ε := by aesop_cat
@[simp] lemma inv_ε : inv F.ε = F.η := by aesop_cat
@[simp] lemma inv_μ (X Y : C) : inv (F.μ X Y) = F.δ X Y := by aesop_cat
@[simp] lemma inv_δ (X Y : C) : inv (F.δ X Y) = F.μ X Y := by aesop_cat

@[simp]
theorem associativity_iso (X Y Z : C) :
    (tensorRight (F.obj Z)).mapIso (F.μIso X Y) ≪≫
        F.μIso (X ⊗ Y) Z ≪≫ F.mapIso (α_ X Y Z) =
      α_ (F.obj X) (F.obj Y) (F.obj Z) ≪≫
        (tensorLeft (F.obj X)).mapIso (F.μIso Y Z) ≪≫ F.μIso X (Y ⊗ Z) :=
  Iso.ext (F.associativity X Y Z)

@[simp]
theorem associativity'_iso (X Y Z : C) :
    whiskerRightIso (F.μIso X Y) (F.obj Z) ≪≫
        F.μIso (X ⊗ Y) Z ≪≫ F.mapIso (α_ X Y Z) =
      α_ (F.obj X) (F.obj Y) (F.obj Z) ≪≫
        whiskerLeftIso (F.obj X) (F.μIso Y Z) ≪≫ F.μIso X (Y ⊗ Z) :=
  Iso.ext (F.associativity' X Y Z)

@[simp]
theorem associativity_symm_iso (X Y Z : C) :
    (tensorLeft (F.obj X)).mapIso (F.μIso Y Z) ≪≫ F.μIso X (Y ⊗ Z) ≪≫
      (F.mapIso (α_ X Y Z)).symm =
    (α_ (F.obj X) (F.obj Y) (F.obj Z)).symm ≪≫
      (tensorRight (F.obj Z)).mapIso (F.μIso X Y) ≪≫ F.μIso (X ⊗ Y) Z := by
  exact Iso.ext (F.associativity_inv X Y Z)

@[simp]
theorem associativity_symm'_iso (X Y Z : C) :
    whiskerLeftIso (F.obj X) (F.μIso Y Z) ≪≫ F.μIso X (Y ⊗ Z) ≪≫
      (F.mapIso (α_ X Y Z)).symm =
    (α_ (F.obj X) (F.obj Y) (F.obj Z)).symm ≪≫
      whiskerRightIso (F.μIso X Y) (F.obj Z) ≪≫ F.μIso (X ⊗ Y) Z := by
  exact Iso.ext (F.associativity_inv' X Y Z)

@[simp]
theorem coassociativity_iso (X Y Z : C) :
    F.mapIso (α_ X Y Z) ≪≫ F.δIso X (Y ⊗ Z) ≪≫
      (tensorLeft (F.obj X)).mapIso (F.δIso Y Z) =
    F.δIso (X ⊗ Y) Z ≪≫ (tensorRight (F.obj Z)).mapIso (F.δIso X Y) ≪≫
      (α_ (F.obj X) (F.obj Y) (F.obj Z)) :=
  Iso.ext (F.coassociativity X Y Z)

@[simp]
theorem coassociativity'_iso (X Y Z : C) :
    F.mapIso (α_ X Y Z) ≪≫ F.δIso X (Y ⊗ Z) ≪≫
      whiskerLeftIso (F.obj X) (F.δIso Y Z) =
    F.δIso (X ⊗ Y) Z ≪≫ whiskerRightIso (F.δIso X Y) (F.obj Z) ≪≫
      (α_ (F.obj X) (F.obj Y) (F.obj Z)) :=
  Iso.ext (F.toColaxMonoidalFunctor.coassociativity' X Y Z)

@[simp]
theorem coassociativity_symm_iso (X Y Z : C) :
    F.mapIso (α_ X Y Z).symm ≪≫ F.δIso (X ⊗ Y) Z ≪≫
      (tensorRight (F.obj Z)).mapIso (F.δIso X Y) =
    F.δIso X (Y ⊗ Z) ≪≫ (tensorLeft (F.obj X)).mapIso (F.δIso Y Z) ≪≫
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).symm :=
  Iso.ext (F.toColaxMonoidalFunctor.coassociativity_inv X Y Z)

@[simp]
theorem coassociativity_symm'_iso (X Y Z : C) :
    F.mapIso (α_ X Y Z).symm ≪≫ F.δIso (X ⊗ Y) Z ≪≫
      whiskerRightIso (F.δIso X Y) (F.obj Z) =
    F.δIso X (Y ⊗ Z) ≪≫ whiskerLeftIso (F.obj X) (F.δIso Y Z) ≪≫
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).symm :=
  Iso.ext (F.toColaxMonoidalFunctor.coassociativity_inv' X Y Z)

@[simp]
theorem left_counitality_iso (X : C) :
    F.δIso (𝟙_ C) X ≪≫ (tensorRight (F.obj X)).mapIso F.εIso ≪≫ λ_ (F.obj X) =
      F.mapIso (λ_ X) := Iso.ext (F.left_counitality X)

@[simp]
theorem right_counitality_iso (X : C) :
    F.δIso X (𝟙_ C) ≪≫ (tensorLeft (F.obj X)).mapIso F.εIso ≪≫ ρ_ (F.obj X) =
      F.mapIso (ρ_ X) := Iso.ext (F.right_counitality X)

@[simp]
theorem left_unitality'_iso (X : C) :
    F.δIso (𝟙_ C) X ≪≫ whiskerRightIso F.εIso (F.obj X) ≪≫ λ_ (F.obj X) =
      F.mapIso (λ_ X) := Iso.ext (F.toColaxMonoidalFunctor.left_counitality' X)

@[simp]
theorem right_unitality'_iso (X : C) :
    F.δIso X (𝟙_ C) ≪≫ whiskerLeftIso (F.obj X) F.εIso ≪≫ ρ_ (F.obj X) =
      F.mapIso (ρ_ X) := Iso.ext (F.toColaxMonoidalFunctor.right_counitality' X)

/-- Make a strong monoidal functor from a lax monoidal functor and inverses to
its unit and tensorator maps. -/
@[simps! ε δ]
def mkOfLaxMonoidalFunctor (F : C ⥤⊗ℓ D)
    (ε : F.obj (𝟙_ C) ⟶ 𝟙_ D) (δ : (X Y : C) → F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y)
    (η_ε_id : F.η ≫ ε = 𝟙 (𝟙_ D) := by aesop_cat)
    (ε_η_id : ε ≫ F.η = 𝟙 (F.obj (𝟙_ C)) := by aesop_cat)
    (μ_δ_id : (X Y : C) → F.μ X Y ≫ δ X Y = 𝟙 _ := by aesop_cat)
    (δ_μ_id : (X Y : C) → δ X Y ≫ F.μ X Y = 𝟙 _ := by aesop_cat) : C ⥤⊗s D :=
  let ηIso := Iso.mk F.η ε η_ε_id ε_η_id
  let μIso X Y := Iso.mk (F.μ X Y) (δ X Y) (μ_δ_id X Y) (δ_μ_id X Y)
  { F with
    ε := ε
    δ := δ
    δ_natural_left := fun {X Y} f X' => by
      rw [(μIso Y X').comp_inv_eq, assoc, F.μ_natural_left,
          (μIso X X').inv_hom_id_assoc]
    δ_natural_right := fun {X Y} X' f => by
      rw [(μIso X' Y).comp_inv_eq, assoc, F.μ_natural_right,
          (μIso X' X).inv_hom_id_assoc]
    coassociativity := fun X Y Z => by
      erw [(μIso (X ⊗ Y) Z).eq_inv_comp,
           ((tensorRight (F.obj Z)).mapIso (μIso X Y)).eq_inv_comp,
           F.associativity_assoc X Y Z, (μIso X (Y ⊗ Z)).hom_inv_id_assoc,
           ((tensorLeft (F.obj X)).mapIso (μIso Y Z)).hom_inv_id, comp_id]
    left_counitality := fun X => by
      erw [F.left_unitality,
           ((tensorRight (F.obj X)).mapIso ηIso).inv_hom_id_assoc,
           (μIso (𝟙_ C) X).inv_hom_id_assoc]
    right_counitality := fun X => by
      erw [F.right_unitality,
          ((tensorLeft (F.obj X)).mapIso ηIso).inv_hom_id_assoc,
          (μIso X (𝟙_ C)).inv_hom_id_assoc] }

@[simp] lemma mkOfLaxMonoidalFunctor_toFunctor (F : C ⥤⊗ℓ D) ε δ h1 h2 h3 h4 :
    (mkOfLaxMonoidalFunctor F ε δ h1 h2 h3 h4).toFunctor = F.toFunctor := rfl

@[simp] lemma mkOfLaxMonoidalFunctor_η (F : C ⥤⊗ℓ D) ε δ h1 h2 h3 h4 :
    (mkOfLaxMonoidalFunctor F ε δ h1 h2 h3 h4).η = F.η := rfl

@[simp] lemma mkOfLaxMonoidalFunctor_μ (F : C ⥤⊗ℓ D) ε δ h1 h2 h3 h4 :
    (mkOfLaxMonoidalFunctor F ε δ h1 h2 h3 h4).μ = F.μ := rfl

/-- Make a strong monoidal functor from a lax monoidal functor whose unit and
tensorator maps are isomorphisms. -/
@[simps! ε δ]
noncomputable def mkOfLaxMonoidalFunctor' (F : C ⥤⊗ℓ D)
    [IsIso F.η] [∀ X Y, IsIso (F.μ X Y)] : MonoidalFunctor C D :=
  mkOfLaxMonoidalFunctor F (inv F.η) (fun X Y => inv (F.μ X Y))

@[simp] lemma mkOfLaxMonoidalFunctor'_toFunctor (F : C ⥤⊗ℓ D)
    [IsIso F.η] [∀ X Y, IsIso (F.μ X Y)] :
    (mkOfLaxMonoidalFunctor' F).toFunctor = F.toFunctor := rfl

@[simp] lemma mkOfLaxMonoidalFunctor'_η (F : C ⥤⊗ℓ D)
    [IsIso F.η] [∀ X Y, IsIso (F.μ X Y)] :
    (mkOfLaxMonoidalFunctor' F).η = F.η := rfl

@[simp] lemma mkOfLaxMonoidalFunctor'_μ (F : C ⥤⊗ℓ D)
    [IsIso F.η] [∀ X Y, IsIso (F.μ X Y)] (X Y : C) :
    (mkOfLaxMonoidalFunctor' F).μ X Y = F.μ X Y := rfl

-- should there be a version which takes μIso as a natural isomorphism?
/-- Make a strong monoidal functor from coherent unitor, tensorator isomorphisms. -/
@[simps! η ε μ δ toFunctor]
def mkOfUnitTensoratorIsos (F : C ⥤ D) (ηIso : 𝟙_ D ≅ F.obj (𝟙_ C))
    (μIso : (X Y : C) → F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y))
    (μ_natural_left : ∀ {X Y} (f : X ⟶ Y) (X' : C),
      (F.map f ⊗ 𝟙 (F.obj X')) ≫ (μIso Y X').hom =
        (μIso X X').hom ≫ F.map (f ⊗ 𝟙 X') := by aesop_cat)
    (μ_natural_right : ∀ {X Y} (X' : C) (f : X ⟶ Y),
      (𝟙 (F.obj X') ⊗ F.map f) ≫ (μIso X' Y).hom =
        (μIso X' X).hom ≫ F.map (𝟙 X' ⊗ f) := by aesop_cat)
    (associativity : ∀ X Y Z,
      ((μIso X Y).hom ⊗ 𝟙 (F.obj Z)) ≫ (μIso (X ⊗ Y) Z).hom ≫ F.map (α_ X Y Z).hom =
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ (𝟙 (F.obj X) ⊗ (μIso Y Z).hom) ≫
          (μIso X (Y ⊗ Z)).hom := by aesop_cat)
    (left_unitality : ∀ X, (λ_ (F.obj X)).hom =
      (ηIso.hom ⊗ 𝟙 (F.obj X)) ≫ (μIso (𝟙_ C) X).hom ≫ F.map (λ_ X).hom := by aesop_cat)
    (right_unitality : ∀ X, (ρ_ (F.obj X)).hom =
      (𝟙 (F.obj X) ⊗ ηIso.hom) ≫ (μIso X (𝟙_ C)).hom ≫ F.map (ρ_ X).hom := by aesop_cat) :
    MonoidalFunctor C D :=
  mkOfLaxMonoidalFunctor ⟨F, ηIso.hom, fun X Y => (μIso X Y).hom, ‹_›, ‹_›,
    ‹_›, ‹_›, ‹_›⟩ ηIso.inv (fun X Y => (μIso X Y).inv)

attribute [local ext] unop_inj in
/-- Make a strong monoidal functor from a colax monoidal functor and inverses to
its counit and cotensorator maps. -/
@[simps! η μ]
def mkOfColaxMonoidalFunctor (F : C ⥤⊗cD)
    (η : 𝟙_ D ⟶ F.obj (𝟙_ C)) (μ : (X Y : C) → F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y))
    (η_ε_id : η ≫ F.ε = 𝟙 (𝟙_ D) := by aesop_cat)
    (ε_η_id : F.ε ≫ η = 𝟙 (F.obj (𝟙_ C)) := by aesop_cat)
    (μ_δ_id : (X Y : C) → μ X Y ≫ F.δ X Y = 𝟙 _ := by aesop_cat)
    (δ_μ_id : (X Y : C) → F.δ X Y ≫ μ X Y = 𝟙 _ := by aesop_cat) :
    MonoidalFunctor C D :=
  .unop <| mkOfLaxMonoidalFunctor F.op η.op (fun X Y => (μ X.unop Y.unop).op)

@[simp] lemma mkOfColaxMonoidalFunctor_toFunctor (F : C ⥤⊗c D) η μ h1 h2 h3 h4 :
    (mkOfColaxMonoidalFunctor F η μ h1 h2 h3 h4).toFunctor = F.toFunctor := rfl

@[simp] lemma mkOfColaxMonoidalFunctor_ε (F : C ⥤⊗c D) η μ h1 h2 h3 h4 :
    (mkOfColaxMonoidalFunctor F η μ h1 h2 h3 h4).ε = F.ε := rfl

@[simp] lemma mkOfColaxMonoidalFunctor_δ (F : C ⥤⊗c D) η μ h1 h2 h3 h4 (X Y : C) :
    (mkOfColaxMonoidalFunctor F η μ h1 h2 h3 h4).δ X Y = F.δ X Y := rfl

/-- Make a strong monoidal functor from a colax monoidal functor whose counit and
cotensorator maps are isomorphisms. -/
@[simps! η μ]
noncomputable def mkOfColaxMonoidalFunctor' (F : C ⥤⊗c D)
    [IsIso F.ε] [∀ X Y, IsIso (F.δ X Y)] : MonoidalFunctor C D :=
  mkOfColaxMonoidalFunctor F (inv F.ε) (fun X Y => inv (F.δ X Y))

@[simp] lemma mkOfColaxMonoidalFunctor'_toFunctor (F : C ⥤⊗c D)
    [IsIso F.ε] [∀ X Y, IsIso (F.δ X Y)] :
    (mkOfColaxMonoidalFunctor' F).toFunctor = F.toFunctor := rfl

@[simp] lemma mkOfColMonoidalFunctor'_ε (F : C ⥤⊗c D)
    [IsIso F.ε] [∀ X Y, IsIso (F.δ X Y)] :
    (mkOfColaxMonoidalFunctor' F).ε = F.ε := rfl

@[simp] lemma mkOfColMonoidalFunctor'_δ (F : C ⥤⊗c D)
    [IsIso F.ε] [∀ X Y, IsIso (F.δ X Y)] (X Y : C) :
    (mkOfColaxMonoidalFunctor' F).δ X Y = F.δ X Y := rfl

/-- Make a strong monoidal functor from coherent counitor, cotensorator isomorphisms. -/
@[simps! η ε μ δ toFunctor]
def mkOfCounitCotensoratorIsos (F : C ⥤ D) (εIso : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (δIso : (X Y : C) → F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
    (δ_natural_left : ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
        F.map (f ⊗ 𝟙 X') ≫ (δIso Y X').hom =
          (δIso X X').hom ≫ (F.map f ⊗ 𝟙 (F.obj X')) := by aesop_cat)
    (δ_natural_right : ∀ {X Y : C} (X' : C) (f : X ⟶ Y),
        F.map (𝟙 X' ⊗ f) ≫ (δIso X' Y).hom =
          (δIso X' X).hom ≫ (𝟙 (F.obj X') ⊗ F.map f) := by aesop_cat)
    (coassociativity : ∀ X Y Z : C,
        F.map (α_ X Y Z).hom ≫ (δIso X (Y ⊗ Z)).hom ≫ (𝟙 (F.obj X) ⊗ (δIso Y Z).hom) =
          (δIso (X ⊗ Y) Z).hom ≫ ((δIso X Y).hom ⊗ 𝟙 (F.obj Z)) ≫
            (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom := by aesop_cat)
    (left_counitality : ∀ X : C,
      (δIso (𝟙_ C) X).hom ≫ (εIso.hom ⊗ 𝟙 (F.obj X)) ≫ (λ_ (F.obj X)).hom =
        F.map (λ_ X).hom := by aesop_cat)
    (right_counitality : ∀ X : C,
      (δIso X (𝟙_ C)).hom ≫ (𝟙 (F.obj X) ⊗ εIso.hom) ≫ (ρ_ (F.obj X)).hom =
        F.map (ρ_ X).hom := by aesop_cat) :
    MonoidalFunctor C D :=
  mkOfColaxMonoidalFunctor ⟨F, εIso.hom, fun X Y => (δIso X Y).hom, ‹_›, ‹_›,
    ‹_›, ‹_›, ‹_›⟩ εIso.inv (fun X Y => (δIso X Y).inv)

variable (F : C ⥤⊗s D)

@[reassoc]
theorem map_tensor {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    F.map (f ⊗ g) = F.δ X X' ≫ (F.map f ⊗ F.map g) ≫ F.μ Y Y' := by simp
#align category_theory.monoidal_functor.map_tensor CategoryTheory.MonoidalFunctor.map_tensor

-- Note: `𝟙 X ⊗ f` will be replaced by `X ◁ f` in #6307.
@[reassoc]
theorem map_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) :
    F.map (𝟙 X ⊗ f) = F.δ X Y ≫ (𝟙 (F.obj X) ⊗ F.map f) ≫ F.μ X Z := by simp

-- Note: `f ⊗ 𝟙 Z` will be replaced by `f ▷ Z` in #6307.
@[reassoc]
theorem map_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) :
    F.map (f ⊗ 𝟙 Z) = F.δ X Z ≫ (F.map f ⊗ 𝟙 (F.obj Z)) ≫ F.μ Y Z := by simp

theorem mapIso_leftUnitor (X : C) :
    F.mapIso (λ_ X) = (F.μIso (𝟙_ C) X).symm ≪≫
      (tensorRight (F.obj X)).mapIso F.εIso ≪≫ λ_ (F.obj X) := by simp

@[reassoc]
theorem map_leftUnitor_hom (X : C) :
    F.map (λ_ X).hom =
      F.δ (𝟙_ C) X ≫ (F.ε ⊗ 𝟙 (F.obj X)) ≫ (λ_ (F.obj X)).hom :=
  (F.toColaxMonoidalFunctor.left_counitality X).symm
#align category_theory.monoidal_functor.map_left_unitor CategoryTheory.MonoidalFunctor.map_leftUnitor_hom

@[reassoc]
theorem map_leftUnitor_inv (X : C) :
    F.map (λ_ X).inv =
      (λ_ (F.obj X)).inv ≫ (F.η ⊗ 𝟙 (F.obj X)) ≫ (F.μIso (𝟙_ C) X).hom := by
  simp

theorem mapIso_rightUnitor (X : C) :
    F.mapIso (ρ_ X) = (F.μIso X (𝟙_ C)).symm ≪≫
      (tensorLeft (F.obj X)).mapIso F.εIso ≪≫ ρ_ (F.obj X) := by simp

@[reassoc]
theorem map_rightUnitor_hom (X : C) :
    F.map (ρ_ X).hom =
      (F.μIso X (𝟙_ C)).inv ≫ (𝟙 (F.obj X) ⊗ F.ε) ≫ (ρ_ (F.obj X)).hom :=
  (F.toColaxMonoidalFunctor.right_counitality X).symm
#align category_theory.monoidal_functor.map_right_unitor CategoryTheory.MonoidalFunctor.map_rightUnitor_hom

@[reassoc]
theorem map_rightUnitor_inv (X : C) :
    F.map (ρ_ X).inv =
      (ρ_ (F.obj X)).inv ≫ (𝟙 (F.obj X) ⊗ F.η) ≫ F.μ X (𝟙_ C) := by
  simp

/-- Monoidal functors commute with left tensoring up to isomorphism -/
@[simps!]
def commTensorLeft (X : C) :
    F.toFunctor ⋙ tensorLeft (F.obj X) ≅ tensorLeft X ⋙ F.toFunctor :=
  NatIso.ofComponents (fun Y => F.μIso X Y) fun f => F.μ_natural_right X f
#align category_theory.monoidal_functor.comm_tensor_left CategoryTheory.MonoidalFunctor.commTensorLeft

/-- Monoidal functors commute with right tensoring up to isomorphism -/
@[simps!]
def commTensorRight (X : C) :
    F.toFunctor ⋙ tensorRight (F.obj X) ≅ tensorRight X ⋙ F.toFunctor :=
  NatIso.ofComponents (fun Y => F.μIso Y X) fun f => F.μ_natural_left f X
#align category_theory.monoidal_functor.comm_tensor_right CategoryTheory.MonoidalFunctor.commTensorRight

variable (C)

/-- The identity monoidal functor. -/
@[simps! ε δ η μ toFunctor]
def id : C ⥤⊗s C :=
  .mkOfUnitTensoratorIsos (𝟭 C) (Iso.refl _) (fun _ _ => Iso.refl _)
#align category_theory.monoidal_functor.id CategoryTheory.MonoidalFunctor.id

instance : Inhabited (C ⥤⊗s C) := ⟨id C⟩

/-- The diagonal functor as a monoidal functor. -/
@[simps! ε δ η μ toFunctor]
def diag : C ⥤⊗s (C × C) :=
  .mkOfUnitTensoratorIsos (.diag C) (Iso.refl _) (fun _ _ => Iso.refl _)
#align category_theory.monoidal_functor.diag CategoryTheory.MonoidalFunctor.diag

end MonoidalFunctor

namespace LaxMonoidalFunctor

variable (F : C ⥤⊗ℓ D) (G : D ⥤⊗ℓ E)

/-- The composition of two lax monoidal functors is again lax monoidal. -/
@[simps! η μ toFunctor]
def comp : C ⥤⊗ℓ E where
  η := G.η ≫ G.map F.η
  μ X Y := G.μ (F.obj X) (F.obj Y) ≫ G.map (F.μ X Y)
  μ_natural_left {X Y} f X' := by
    simp [← G.map_comp, -map_comp]
  μ_natural_right {X Y} f X' := by
    simp [← G.map_comp, -map_comp]
  associativity X Y Z := by
    simp [id_tensorHom, tensorHom_id, ← G.associativity'_assoc,
          ← G.map_comp, F.associativity', -associativity', -map_comp]
  __ := F.toFunctor ⋙ G.toFunctor
#align category_theory.lax_monoidal_functor.comp CategoryTheory.LaxMonoidalFunctor.comp

@[inherit_doc]
infixr:80 " ⊗⋙ " => comp

protected lemma comp_toFunctor_eq_toFunctor_comp :
    (F ⊗⋙ G).toFunctor = (F.toFunctor ⋙ G.toFunctor) := rfl

/-- The isomorphism witnessing that the functor underlying a composition of
lax monoidal functors is the composition of the underlying functors. -/
@[simps!]
def comp_toFunctor_iso_toFunctor_comp :
    (F ⊗⋙ G).toFunctor ≅ (F.toFunctor ⋙ G.toFunctor) := Iso.refl _

variable (F : B ⥤⊗ℓ C) (G : D ⥤⊗ℓ E)

attribute [local simp] μ_natural associativity left_unitality right_unitality

/-- The cartesian product of two lax monoidal functors is lax monoidal. -/
@[simps! η μ toFunctor]
def prod : B × D ⥤⊗ℓ C × E where
  η := (F.η, G.η)
  μ := fun X Y => (F.μ X.1 Y.1, G.μ X.2 Y.2)
  __ := Functor.prod F.toFunctor G.toFunctor
#align category_theory.lax_monoidal_functor.prod CategoryTheory.LaxMonoidalFunctor.prod

variable (F : C ⥤⊗ℓ D) (G : C ⥤⊗ℓ E)

/-- The cartesian product of two lax monoidal functors starting from the same monoidal category `C`
    is lax monoidal. -/
@[simps! η μ toFunctor]
def prod' : C ⥤⊗ℓ D × E :=
  (MonoidalFunctor.diag C).toLaxMonoidalFunctor ⊗⋙ F.prod G
#align category_theory.lax_monoidal_functor.prod' CategoryTheory.LaxMonoidalFunctor.prod'
#align category_theory.lax_monoidal_functor.prod'_to_functor CategoryTheory.LaxMonoidalFunctor.prod'_toFunctor

variable (C)

/-- The identity lax monoidal functor. -/
@[simps! η μ toFunctor] -- is this necessary for an `abbrev`?
abbrev id : C ⥤⊗ℓ C :=
  (MonoidalFunctor.id C).toLaxMonoidalFunctor
#align category_theory.lax_monoidal_functor.id CategoryTheory.LaxMonoidalFunctor.id

instance : Inhabited (C ⥤⊗ℓ C) := ⟨id C⟩

@[simp]
lemma id_μNatTrans :
    (id C).μNatTrans =
      whiskerRight (prodIdIso C C).inv (tensor C) ≫
        (tensor C).leftUnitor.hom ≫ (tensor C).rightUnitor.inv := by
  aesop_cat

end LaxMonoidalFunctor

namespace ColaxMonoidalFunctor

variable (F : C ⥤⊗c D) (G : D ⥤⊗c E)

/-- The composition of two colax monoidal functors is again colax monoidal. -/
@[simps! ε δ toFunctor]
def comp : C ⥤⊗c E := (F.op.comp G.op).unop

@[inherit_doc]
infixr:80 " ⊗⋙ " => comp

protected lemma comp_toFunctor_eq_toFunctor_comp :
    (F ⊗⋙ G).toFunctor = (F.toFunctor ⋙ G.toFunctor) := rfl

/-- The isomorphism witnessing that the functor underlying a composition of
colax monoidal functors is the composition of the underlying functors. -/
@[simps!]
def comp_toFunctor_iso_toFunctor_comp :
    (F ⊗⋙ G).toFunctor ≅ (F.toFunctor ⋙ G.toFunctor) := Iso.refl _

variable (F : B ⥤⊗c C) (G : D ⥤⊗c E)

attribute [local simp] δ_natural coassociativity left_counitality right_counitality

/-- The cartesian product of two colax monoidal functors is colax monoidal. -/
@[simps! ε δ toFunctor]
def prod : B × D ⥤⊗c C × E where
  ε := (F.ε, G.ε)
  δ := fun X Y => (F.δ X.1 Y.1, G.δ X.2 Y.2)
  __ := Functor.prod F.toFunctor G.toFunctor

variable (F : C ⥤⊗c D) (G : C ⥤⊗c E)

/-- The cartesian product of two colax monoidal functors starting from the same
monoidal category `C` is colax monoidal. -/
@[simps! ε δ toFunctor]
def prod' : C ⥤⊗c D × E :=
  (MonoidalFunctor.diag C).toColaxMonoidalFunctor ⊗⋙ F.prod G

variable (C)

/-- The identity colax monoidal functor. -/
@[simps! ε δ toFunctor] -- is this necessary for an `abbrev`?
abbrev id : C ⥤⊗c C :=
  (MonoidalFunctor.id C).toColaxMonoidalFunctor

instance : Inhabited (C ⥤⊗c C) := ⟨id C⟩

@[simp]
lemma id_δNatTrans :
    (id C).δNatTrans =
      (tensor C).rightUnitor.hom ≫ (tensor C).leftUnitor.inv ≫
        whiskerRight (prodIdIso C C).hom (tensor C) := by
  aesop_cat

end ColaxMonoidalFunctor

namespace MonoidalFunctor

variable (F : C ⥤⊗s D) (G : D ⥤⊗s E)

/-- The composition of two monoidal functors is again monoidal. -/
@[simps! ε δ η μ toFunctor]
def comp : C ⥤⊗s E where
  η_ε_id := by simp [← G.map_comp_assoc]
  ε_η_id := by simp [← G.map_comp, -map_comp]
  μ_δ_id := by simp [← G.map_comp_assoc]
  δ_μ_id := by simp [← G.map_comp, -map_comp]
  __ := F.toLaxMonoidalFunctor ⊗⋙ G.toLaxMonoidalFunctor
  __ := F.toColaxMonoidalFunctor ⊗⋙ G.toColaxMonoidalFunctor
#align category_theory.monoidal_functor.comp CategoryTheory.MonoidalFunctor.comp

@[inherit_doc]
infixr:80
  " ⊗⋙ " =>-- We overload notation; potentially dangerous, but it seems to work.
  comp

protected lemma comp_toFunctor_eq_toFunctor_comp :
    (F ⊗⋙ G).toLaxMonoidalFunctor =
      (F.toLaxMonoidalFunctor ⊗⋙ G.toLaxMonoidalFunctor) := rfl

variable (F : B ⥤⊗s C) (G : D ⥤⊗s E)

/-- The cartesian product of two monoidal functors is monoidal. -/
@[simps! ε δ η μ toFunctor]
def prod : B × D ⥤⊗s C × E where
  __ := ColaxMonoidalFunctor.prod F.toColaxMonoidalFunctor G.toColaxMonoidalFunctor
  __ := LaxMonoidalFunctor.prod F.toLaxMonoidalFunctor G.toLaxMonoidalFunctor
#align category_theory.monoidal_functor.prod CategoryTheory.MonoidalFunctor.prod

variable (F : C ⥤⊗s D) (G : C ⥤⊗s E)

/-- The cartesian product of two monoidal functors starting from the same
monoidal category `C` is monoidal. -/
@[simps! ε δ η μ toFunctor]
def prod' : C ⥤⊗s D × E := diag C ⊗⋙ F.prod G
#align category_theory.monoidal_functor.prod' CategoryTheory.MonoidalFunctor.prod'

end MonoidalFunctor

end CategoryTheory
