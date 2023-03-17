/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta, Adam Topaz

! This file was ported from Lean 3 source module category_theory.monad.basic
! leanprover-community/mathlib commit 1995c7bbdbb0adb1b6d5acdc654f6cf46ed96cfa
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Functor.Category
import Mathbin.CategoryTheory.Functor.FullyFaithful
import Mathbin.CategoryTheory.Functor.ReflectsIsomorphisms

/-!
# Monads

We construct the categories of monads and comonads, and their forgetful functors to endofunctors.

(Note that these are the category theorist's monads, not the programmers monads.
For the translation, see the file `category_theory.monad.types`.)

For the fact that monads are "just" monoids in the category of endofunctors, see the file
`category_theory.monad.equiv_mon`.
-/


namespace CategoryTheory

open Category

universe v₁ u₁

-- morphism levels before object levels. See note [category_theory universes].
variable (C : Type u₁) [Category.{v₁} C]

/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`η'] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`μ'] [] -/
/-- The data of a monad on C consists of an endofunctor T together with natural transformations
η : 𝟭 C ⟶ T and μ : T ⋙ T ⟶ T satisfying three equations:
- T μ_X ≫ μ_X = μ_(TX) ≫ μ_X (associativity)
- η_(TX) ≫ μ_X = 1_X (left unit)
- Tη_X ≫ μ_X = 1_X (right unit)
-/
structure Monad extends C ⥤ C where
  η' : 𝟭 _ ⟶ to_functor
  μ' : to_functor ⋙ to_functor ⟶ to_functor
  assoc' : ∀ X, to_functor.map (NatTrans.app μ' X) ≫ μ'.app _ = μ'.app _ ≫ μ'.app _ := by obviously
  left_unit' : ∀ X : C, η'.app (to_functor.obj X) ≫ μ'.app _ = 𝟙 _ := by obviously
  right_unit' : ∀ X : C, to_functor.map (η'.app X) ≫ μ'.app _ = 𝟙 _ := by obviously
#align category_theory.monad CategoryTheory.Monad

/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`ε'] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`δ'] [] -/
/-- The data of a comonad on C consists of an endofunctor G together with natural transformations
ε : G ⟶ 𝟭 C and δ : G ⟶ G ⋙ G satisfying three equations:
- δ_X ≫ G δ_X = δ_X ≫ δ_(GX) (coassociativity)
- δ_X ≫ ε_(GX) = 1_X (left counit)
- δ_X ≫ G ε_X = 1_X (right counit)
-/
structure Comonad extends C ⥤ C where
  ε' : to_functor ⟶ 𝟭 _
  δ' : to_functor ⟶ to_functor ⋙ to_functor
  coassoc' : ∀ X, NatTrans.app δ' _ ≫ to_functor.map (δ'.app X) = δ'.app _ ≫ δ'.app _ := by
    obviously
  left_counit' : ∀ X : C, δ'.app X ≫ ε'.app (to_functor.obj X) = 𝟙 _ := by obviously
  right_counit' : ∀ X : C, δ'.app X ≫ to_functor.map (ε'.app X) = 𝟙 _ := by obviously
#align category_theory.comonad CategoryTheory.Comonad

variable {C} (T : Monad C) (G : Comonad C)

instance coeMonad : Coe (Monad C) (C ⥤ C) :=
  ⟨fun T => T.toFunctor⟩
#align category_theory.coe_monad CategoryTheory.coeMonad

instance coeComonad : Coe (Comonad C) (C ⥤ C) :=
  ⟨fun G => G.toFunctor⟩
#align category_theory.coe_comonad CategoryTheory.coeComonad

@[simp]
theorem monad_toFunctor_eq_coe : T.toFunctor = T :=
  rfl
#align category_theory.monad_to_functor_eq_coe CategoryTheory.monad_toFunctor_eq_coe

@[simp]
theorem comonad_toFunctor_eq_coe : G.toFunctor = G :=
  rfl
#align category_theory.comonad_to_functor_eq_coe CategoryTheory.comonad_toFunctor_eq_coe

/-- The unit for the monad `T`. -/
def Monad.η : 𝟭 _ ⟶ (T : C ⥤ C) :=
  T.η'
#align category_theory.monad.η CategoryTheory.Monad.η

/-- The multiplication for the monad `T`. -/
def Monad.μ : (T : C ⥤ C) ⋙ (T : C ⥤ C) ⟶ T :=
  T.μ'
#align category_theory.monad.μ CategoryTheory.Monad.μ

/-- The counit for the comonad `G`. -/
def Comonad.ε : (G : C ⥤ C) ⟶ 𝟭 _ :=
  G.ε'
#align category_theory.comonad.ε CategoryTheory.Comonad.ε

/-- The comultiplication for the comonad `G`. -/
def Comonad.δ : (G : C ⥤ C) ⟶ (G : C ⥤ C) ⋙ G :=
  G.δ'
#align category_theory.comonad.δ CategoryTheory.Comonad.δ

/-- A custom simps projection for the functor part of a monad, as a coercion. -/
def Monad.Simps.coe :=
  (T : C ⥤ C)
#align category_theory.monad.simps.coe CategoryTheory.Monad.Simps.coe

/-- A custom simps projection for the unit of a monad, in simp normal form. -/
def Monad.Simps.η : 𝟭 _ ⟶ (T : C ⥤ C) :=
  T.η
#align category_theory.monad.simps.η CategoryTheory.Monad.Simps.η

/-- A custom simps projection for the multiplication of a monad, in simp normal form. -/
def Monad.Simps.μ : (T : C ⥤ C) ⋙ (T : C ⥤ C) ⟶ (T : C ⥤ C) :=
  T.μ
#align category_theory.monad.simps.μ CategoryTheory.Monad.Simps.μ

/-- A custom simps projection for the functor part of a comonad, as a coercion. -/
def Comonad.Simps.coe :=
  (G : C ⥤ C)
#align category_theory.comonad.simps.coe CategoryTheory.Comonad.Simps.coe

/-- A custom simps projection for the counit of a comonad, in simp normal form. -/
def Comonad.Simps.ε : (G : C ⥤ C) ⟶ 𝟭 _ :=
  G.ε
#align category_theory.comonad.simps.ε CategoryTheory.Comonad.Simps.ε

/-- A custom simps projection for the comultiplication of a comonad, in simp normal form. -/
def Comonad.Simps.δ : (G : C ⥤ C) ⟶ (G : C ⥤ C) ⋙ (G : C ⥤ C) :=
  G.δ
#align category_theory.comonad.simps.δ CategoryTheory.Comonad.Simps.δ

initialize_simps_projections category_theory.monad (toFunctor → coe, η' → η, μ' → μ)

initialize_simps_projections category_theory.comonad (toFunctor → coe, ε' → ε, δ' → δ)

@[reassoc.1]
theorem Monad.assoc (T : Monad C) (X : C) :
    (T : C ⥤ C).map (T.μ.app X) ≫ T.μ.app _ = T.μ.app _ ≫ T.μ.app _ :=
  T.assoc' X
#align category_theory.monad.assoc CategoryTheory.Monad.assoc

@[simp, reassoc.1]
theorem Monad.left_unit (T : Monad C) (X : C) :
    T.η.app ((T : C ⥤ C).obj X) ≫ T.μ.app X = 𝟙 ((T : C ⥤ C).obj X) :=
  T.left_unit' X
#align category_theory.monad.left_unit CategoryTheory.Monad.left_unit

@[simp, reassoc.1]
theorem Monad.right_unit (T : Monad C) (X : C) :
    (T : C ⥤ C).map (T.η.app X) ≫ T.μ.app X = 𝟙 ((T : C ⥤ C).obj X) :=
  T.right_unit' X
#align category_theory.monad.right_unit CategoryTheory.Monad.right_unit

@[reassoc.1]
theorem Comonad.coassoc (G : Comonad C) (X : C) :
    G.δ.app _ ≫ (G : C ⥤ C).map (G.δ.app X) = G.δ.app _ ≫ G.δ.app _ :=
  G.coassoc' X
#align category_theory.comonad.coassoc CategoryTheory.Comonad.coassoc

@[simp, reassoc.1]
theorem Comonad.left_counit (G : Comonad C) (X : C) :
    G.δ.app X ≫ G.ε.app ((G : C ⥤ C).obj X) = 𝟙 ((G : C ⥤ C).obj X) :=
  G.left_counit' X
#align category_theory.comonad.left_counit CategoryTheory.Comonad.left_counit

@[simp, reassoc.1]
theorem Comonad.right_counit (G : Comonad C) (X : C) :
    G.δ.app X ≫ (G : C ⥤ C).map (G.ε.app X) = 𝟙 ((G : C ⥤ C).obj X) :=
  G.right_counit' X
#align category_theory.comonad.right_counit CategoryTheory.Comonad.right_counit

/-- A morphism of monads is a natural transformation compatible with η and μ. -/
@[ext]
structure MonadHom (T₁ T₂ : Monad C) extends NatTrans (T₁ : C ⥤ C) T₂ where
  app_η' : ∀ X, T₁.η.app X ≫ app X = T₂.η.app X := by obviously
  app_μ' : ∀ X, T₁.μ.app X ≫ app X = ((T₁ : C ⥤ C).map (app X) ≫ app _) ≫ T₂.μ.app X := by obviously
#align category_theory.monad_hom CategoryTheory.MonadHom

/-- A morphism of comonads is a natural transformation compatible with ε and δ. -/
@[ext]
structure ComonadHom (M N : Comonad C) extends NatTrans (M : C ⥤ C) N where
  app_ε' : ∀ X, app X ≫ N.ε.app X = M.ε.app X := by obviously
  app_δ' : ∀ X, app X ≫ N.δ.app X = M.δ.app X ≫ app _ ≫ (N : C ⥤ C).map (app X) := by obviously
#align category_theory.comonad_hom CategoryTheory.ComonadHom

restate_axiom monad_hom.app_η'

restate_axiom monad_hom.app_μ'

attribute [simp, reassoc.1] monad_hom.app_η monad_hom.app_μ

restate_axiom comonad_hom.app_ε'

restate_axiom comonad_hom.app_δ'

attribute [simp, reassoc.1] comonad_hom.app_ε comonad_hom.app_δ

instance : Category (Monad C) where
  Hom := MonadHom
  id M := { toNatTrans := 𝟙 (M : C ⥤ C) }
  comp _ _ _ f g :=
    {
      toNatTrans :=
        { app := fun X => f.app X ≫ g.app X
          naturality' := fun X Y h => by rw [assoc, f.1.naturality_assoc, g.1.naturality] } }
  id_comp' _ _ _ := by
    ext
    apply id_comp
  comp_id' _ _ _ := by
    ext
    apply comp_id
  assoc' _ _ _ _ _ _ _ := by
    ext
    apply assoc

instance : Category (Comonad C) where
  Hom := ComonadHom
  id M := { toNatTrans := 𝟙 (M : C ⥤ C) }
  comp _ _ _ f g :=
    {
      toNatTrans :=
        { app := fun X => f.app X ≫ g.app X
          naturality' := fun X Y h => by rw [assoc, f.1.naturality_assoc, g.1.naturality] } }
  id_comp' _ _ _ := by
    ext
    apply id_comp
  comp_id' _ _ _ := by
    ext
    apply comp_id
  assoc' _ _ _ _ _ _ _ := by
    ext
    apply assoc

instance {T : Monad C} : Inhabited (MonadHom T T) :=
  ⟨𝟙 T⟩

@[simp]
theorem MonadHom.id_toNatTrans (T : Monad C) : (𝟙 T : T ⟶ T).toNatTrans = 𝟙 (T : C ⥤ C) :=
  rfl
#align category_theory.monad_hom.id_to_nat_trans CategoryTheory.MonadHom.id_toNatTrans

@[simp]
theorem MonadHom.comp_toNatTrans {T₁ T₂ T₃ : Monad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    (f ≫ g).toNatTrans = ((f.toNatTrans : _ ⟶ (T₂ : C ⥤ C)) ≫ g.toNatTrans : (T₁ : C ⥤ C) ⟶ T₃) :=
  rfl
#align category_theory.monad_hom.comp_to_nat_trans CategoryTheory.MonadHom.comp_toNatTrans

instance {G : Comonad C} : Inhabited (ComonadHom G G) :=
  ⟨𝟙 G⟩

@[simp]
theorem ComonadHom.id_toNatTrans (T : Comonad C) : (𝟙 T : T ⟶ T).toNatTrans = 𝟙 (T : C ⥤ C) :=
  rfl
#align category_theory.comonad_hom.id_to_nat_trans CategoryTheory.ComonadHom.id_toNatTrans

@[simp]
theorem comp_toNatTrans {T₁ T₂ T₃ : Comonad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    (f ≫ g).toNatTrans = ((f.toNatTrans : _ ⟶ (T₂ : C ⥤ C)) ≫ g.toNatTrans : (T₁ : C ⥤ C) ⟶ T₃) :=
  rfl
#align category_theory.comp_to_nat_trans CategoryTheory.comp_toNatTrans

/-- Construct a monad isomorphism from a natural isomorphism of functors where the forward
direction is a monad morphism. -/
@[simps]
def MonadIso.mk {M N : Monad C} (f : (M : C ⥤ C) ≅ N) (f_η f_μ) : M ≅ N
    where
  Hom :=
    { toNatTrans := f.Hom
      app_η' := f_η
      app_μ' := f_μ }
  inv :=
    { toNatTrans := f.inv
      app_η' := fun X => by simp [← f_η]
      app_μ' := fun X => by
        rw [← nat_iso.cancel_nat_iso_hom_right f]
        simp only [nat_trans.naturality, iso.inv_hom_id_app, assoc, comp_id, f_μ,
          nat_trans.naturality_assoc, iso.inv_hom_id_app_assoc, ← functor.map_comp_assoc]
        simp }
#align category_theory.monad_iso.mk CategoryTheory.MonadIso.mk

/-- Construct a comonad isomorphism from a natural isomorphism of functors where the forward
direction is a comonad morphism. -/
@[simps]
def ComonadIso.mk {M N : Comonad C} (f : (M : C ⥤ C) ≅ N) (f_ε f_δ) : M ≅ N
    where
  Hom :=
    { toNatTrans := f.Hom
      app_ε' := f_ε
      app_δ' := f_δ }
  inv :=
    { toNatTrans := f.inv
      app_ε' := fun X => by simp [← f_ε]
      app_δ' := fun X => by
        rw [← nat_iso.cancel_nat_iso_hom_left f]
        simp only [reassoc_of (f_δ X), iso.hom_inv_id_app_assoc, nat_trans.naturality_assoc]
        rw [← functor.map_comp, iso.hom_inv_id_app, Functor.map_id]
        apply (comp_id _).symm }
#align category_theory.comonad_iso.mk CategoryTheory.ComonadIso.mk

variable (C)

/-- The forgetful functor from the category of monads to the category of endofunctors.
-/
@[simps]
def monadToFunctor : Monad C ⥤ C ⥤ C where
  obj T := T
  map M N f := f.toNatTrans
#align category_theory.monad_to_functor CategoryTheory.monadToFunctor

instance : Faithful (monadToFunctor C) where

@[simp]
theorem monadToFunctor_mapIso_monad_iso_mk {M N : Monad C} (f : (M : C ⥤ C) ≅ N) (f_η f_μ) :
    (monadToFunctor _).mapIso (MonadIso.mk f f_η f_μ) = f :=
  by
  ext
  rfl
#align category_theory.monad_to_functor_map_iso_monad_iso_mk CategoryTheory.monadToFunctor_mapIso_monad_iso_mk

instance : ReflectsIsomorphisms (monadToFunctor C)
    where reflects M N f i := by
    skip
    convert is_iso.of_iso (monad_iso.mk (as_iso ((monad_to_functor C).map f)) f.app_η f.app_μ)
    ext <;> rfl

/-- The forgetful functor from the category of comonads to the category of endofunctors.
-/
@[simps]
def comonadToFunctor : Comonad C ⥤ C ⥤ C where
  obj G := G
  map M N f := f.toNatTrans
#align category_theory.comonad_to_functor CategoryTheory.comonadToFunctor

instance : Faithful (comonadToFunctor C) where

@[simp]
theorem comonadToFunctor_mapIso_comonad_iso_mk {M N : Comonad C} (f : (M : C ⥤ C) ≅ N) (f_ε f_δ) :
    (comonadToFunctor _).mapIso (ComonadIso.mk f f_ε f_δ) = f :=
  by
  ext
  rfl
#align category_theory.comonad_to_functor_map_iso_comonad_iso_mk CategoryTheory.comonadToFunctor_mapIso_comonad_iso_mk

instance : ReflectsIsomorphisms (comonadToFunctor C)
    where reflects M N f i := by
    skip
    convert is_iso.of_iso (comonad_iso.mk (as_iso ((comonad_to_functor C).map f)) f.app_ε f.app_δ)
    ext <;> rfl

variable {C}

/-- An isomorphism of monads gives a natural isomorphism of the underlying functors.
-/
@[simps (config := { rhsMd := semireducible })]
def MonadIso.toNatIso {M N : Monad C} (h : M ≅ N) : (M : C ⥤ C) ≅ N :=
  (monadToFunctor C).mapIso h
#align category_theory.monad_iso.to_nat_iso CategoryTheory.MonadIso.toNatIso

/-- An isomorphism of comonads gives a natural isomorphism of the underlying functors.
-/
@[simps (config := { rhsMd := semireducible })]
def ComonadIso.toNatIso {M N : Comonad C} (h : M ≅ N) : (M : C ⥤ C) ≅ N :=
  (comonadToFunctor C).mapIso h
#align category_theory.comonad_iso.to_nat_iso CategoryTheory.ComonadIso.toNatIso

variable (C)

namespace Monad

/-- The identity monad. -/
@[simps]
def id : Monad C where
  toFunctor := 𝟭 C
  η' := 𝟙 (𝟭 C)
  μ' := 𝟙 (𝟭 C)
#align category_theory.monad.id CategoryTheory.Monad.id

instance : Inhabited (Monad C) :=
  ⟨Monad.id C⟩

end Monad

namespace Comonad

/-- The identity comonad. -/
@[simps]
def id : Comonad C where
  toFunctor := 𝟭 _
  ε' := 𝟙 (𝟭 C)
  δ' := 𝟙 (𝟭 C)
#align category_theory.comonad.id CategoryTheory.Comonad.id

instance : Inhabited (Comonad C) :=
  ⟨Comonad.id C⟩

end Comonad

end CategoryTheory

