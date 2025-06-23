/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Monad.Basic

/-! # Kleisli category on a (co)monad

This file defines the Kleisli category on a monad `(T, η_ T, μ_ T)` as well as the co-Kleisli
category on a comonad `(U, ε_ U, δ_ U)`. It also defines the Kleisli adjunction which gives rise to
the monad `(T, η_ T, μ_ T)` as well as the co-Kleisli adjunction which gives rise to the comonad
`(U, ε_ U, δ_ U)`.

## References
* [Riehl, *Category theory in context*, Definition 5.2.9][riehl2017]
-/


namespace CategoryTheory

universe v u

-- morphism levels before object levels. See note [CategoryTheory universes].
variable {C : Type u} [Category.{v} C]

/-- The objects for the Kleisli category of the monad `T : Monad C`, which are the same
thing as objects of the base category `C`.
-/
@[nolint unusedArguments]
def Kleisli (_T : Monad C) :=
  C

namespace Kleisli

variable (T : Monad C)

instance [Inhabited C] (T : Monad C) : Inhabited (Kleisli T) :=
  ⟨(default : C)⟩

/-- The Kleisli category on a monad `T`.
    cf Definition 5.2.9 in [Riehl][riehl2017]. -/
instance category : Category (Kleisli T) where
  Hom := fun X Y : C => X ⟶ (T : C ⥤ C).obj Y
  id X := T.η.app X
  comp {_} {_} {Z} f g := f ≫ (T : C ⥤ C).map g ≫ T.μ.app Z
  id_comp {X} {Y} f := by
    rw [← T.η.naturality_assoc f, T.left_unit]
    apply Category.comp_id
  assoc f g h := by
    simp [Monad.assoc, T.mu_naturality_assoc]

namespace Adjunction

/-- The left adjoint of the adjunction which induces the monad `(T, η_ T, μ_ T)`. -/
@[simps]
def toKleisli : C ⥤ Kleisli T where
  obj X := (X : Kleisli T)
  map {X} {Y} f := (f ≫ T.η.app Y : X ⟶ T.obj Y)
  map_comp {X} {Y} {Z} f g := by
    -- Porting note: hack for missing unfold_projs tactic
    change _ = (f ≫ (Monad.η T).app Y) ≫ T.map (g ≫ (Monad.η T).app Z) ≫ T.μ.app Z
    simp [← T.η.naturality g]

/-- The right adjoint of the adjunction which induces the monad `(T, η_ T, μ_ T)`. -/
@[simps]
def fromKleisli : Kleisli T ⥤ C where
  obj X := T.obj X
  map {_} {Y} f := T.map f ≫ T.μ.app Y
  map_id _ := T.right_unit _
  map_comp {X} {Y} {Z} f g := by
    -- Porting note: hack for missing unfold_projs tactic
    change T.map (f ≫ T.map g ≫ T.μ.app Z) ≫ T.μ.app Z = _
    simp only [Functor.map_comp, Category.assoc]
    rw [← T.μ.naturality_assoc g, T.assoc]
    rfl

/-- The Kleisli adjunction which gives rise to the monad `(T, η_ T, μ_ T)`.
    cf Lemma 5.2.11 of [Riehl][riehl2017]. -/
def adj : toKleisli T ⊣ fromKleisli T :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => Equiv.refl (X ⟶ T.obj Y)
      homEquiv_naturality_left_symm := fun {X} {Y} {Z} f g => by
        -- Porting note: used to be unfold_projs; dsimp
        change f ≫ g = (f ≫ T.η.app Y) ≫ T.map g ≫ T.μ.app Z
        rw [Category.assoc, ← T.η.naturality_assoc g, Functor.id_map]
        simp [Monad.left_unit] }

/-- The composition of the adjunction gives the original functor. -/
def toKleisliCompFromKleisliIsoSelf : toKleisli T ⋙ fromKleisli T ≅ T :=
  NatIso.ofComponents fun _ => Iso.refl _

end Adjunction

end Kleisli

/-- The objects for the co-Kleisli category of the comonad `U : Comonad C`, which are the same
thing as objects of the base category `C`.
-/
@[nolint unusedArguments]
def Cokleisli (_U : Comonad C) :=
  C

namespace Cokleisli

variable (U : Comonad C)

instance [Inhabited C] (U : Comonad C) : Inhabited (Cokleisli U) :=
  ⟨(default : C)⟩

/-- The co-Kleisli category on a comonad `U`. -/
instance category : Category (Cokleisli U) where
  Hom := fun X Y : C => (U : C ⥤ C).obj X ⟶ Y
  id X := U.ε.app X
  comp f g := U.δ.app _ ≫ (U : C ⥤ C).map f ≫ g

namespace Adjunction

/-- The right adjoint of the adjunction which induces the comonad `(U, ε_ U, δ_ U)`. -/
@[simps]
def toCokleisli : C ⥤ Cokleisli U where
  obj X := (X : Cokleisli U)
  map {X} {_} f := (U.ε.app X ≫ f :)
  map_comp {X} {Y} {_} f g := by
    -- Porting note: working around lack of unfold_projs
    change U.ε.app X ≫ f ≫ g = U.δ.app X ≫ U.map (U.ε.app X ≫ f) ≫ U.ε.app Y ≫ g
    simp [← U.ε.naturality g]

/-- The left adjoint of the adjunction which induces the comonad `(U, ε_ U, δ_ U)`. -/
@[simps]
def fromCokleisli : Cokleisli U ⥤ C where
  obj X := U.obj X
  map {X} {_} f := U.δ.app X ≫ U.map f
  map_id _ := U.right_counit _
  map_comp {X} {Y} {_} f g := by
    -- Porting note: working around lack of unfold_projs
    change U.δ.app X ≫ U.map (U.δ.app X ≫ U.map f ≫ g) =
      (U.δ.app X ≫ U.map f) ≫ (U.δ.app Y ≫ U.map g)
    simp only [Functor.map_comp, ← Category.assoc]
    rw [Comonad.coassoc]
    simp only [Category.assoc, NatTrans.naturality, Functor.comp_map]

/-- The co-Kleisli adjunction which gives rise to the monad `(U, ε_ U, δ_ U)`. -/
def adj : fromCokleisli U ⊣ toCokleisli U :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => Equiv.refl (U.obj X ⟶ Y)
      homEquiv_naturality_right := fun {X} {Y} {_} f g => by
        -- Porting note: working around lack of unfold_projs
        change f ≫ g = U.δ.app X ≫ U.map f ≫ U.ε.app Y ≫ g
        rw [← Category.assoc (U.map f), U.ε.naturality]; dsimp
        simp only [← Category.assoc, Comonad.left_counit, Category.id_comp] }

/-- The composition of the adjunction gives the original functor. -/
def toCokleisliCompFromCokleisliIsoSelf : toCokleisli U ⋙ fromCokleisli U ≅ U :=
  NatIso.ofComponents fun _ => Iso.refl _

end Adjunction

end Cokleisli

end CategoryTheory
