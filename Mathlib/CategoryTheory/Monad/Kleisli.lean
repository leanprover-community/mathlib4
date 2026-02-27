/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monad.Basic

/-! # Kleisli category on a (co)monad

This file defines the Kleisli category on a monad `(T, η_ T, μ_ T)` as well as the co-Kleisli
category on a comonad `(U, ε_ U, δ_ U)`. It also defines the Kleisli adjunction which gives rise to
the monad `(T, η_ T, μ_ T)` as well as the co-Kleisli adjunction which gives rise to the comonad
`(U, ε_ U, δ_ U)`.

## References
* [Riehl, *Category theory in context*, Definition 5.2.9][riehl2017]
-/

@[expose] public section


namespace CategoryTheory

universe v u

-- morphism levels before object levels. See note [category theory universes].
variable {C : Type u} [Category.{v} C]

/-- The objects for the Kleisli category of the monad `T : Monad C`, which are the same
thing as objects of the base category `C`.
-/
structure Kleisli (T : Monad C) where mk (T) ::
  /-- The underlying object of the base category. -/
  of : C

namespace Kleisli

variable {T : Monad C}

@[simp] lemma mk_of (c : Kleisli T) : Kleisli.mk T c.of = c := rfl
lemma of_mk (c : C) : (Kleisli.mk T c).of = c := rfl

/-- For (T : Monad C), morphisms `c ⟶ c'` in the Kleisli category of `T` are
morphisms ` c ⟶ T.obj c'` in `C`. -/
structure Hom (c c' : Kleisli T) where
  /-- The morphism in C underlying the morphism in the Kleisli category. -/
  of : c.of ⟶ T.obj c'.of

instance [Inhabited C] (T : Monad C) : Inhabited (Kleisli T) := ⟨.mk T default⟩

variable (T)

attribute [local ext] Hom in
/-- The Kleisli category on a monad `T`.
cf Definition 5.2.9 in [Riehl][riehl2017]. -/
@[simps!]
instance category : Category (Kleisli T) where
  Hom X Y := Hom X Y
  id X := .mk <| T.η.app X.of
  comp {_} {_} {Z} f g := .mk <| f.of ≫ T.map g.of ≫ T.μ.app Z.of
  id_comp {X} {Y} f := by
    ext
    dsimp
    rw [← T.η.naturality_assoc f.of, T.left_unit]
    apply Category.comp_id
  assoc f g h := by
    simp [Monad.assoc, T.mu_naturality_assoc]

variable {T} in
attribute [local ext] Hom in
@[ext]
lemma hom_ext {x y : Kleisli T} {f g : x ⟶ y} (h : f.of = g.of) : f = g :=
  Hom.ext h

namespace Adjunction

/-- The left adjoint of the adjunction which induces the monad `(T, η_ T, μ_ T)`. -/
@[simps]
def toKleisli : C ⥤ Kleisli T where
  obj X := .mk T X
  map {X} {Y} f := .mk <| f ≫ T.η.app Y
  map_comp {X} {Y} {Z} f g := by
    unfold_projs
    simp [← T.η.naturality g]

/-- The right adjoint of the adjunction which induces the monad `(T, η_ T, μ_ T)`. -/
@[simps]
def fromKleisli : Kleisli T ⥤ C where
  obj X := T.obj X.of
  map {_} {Y} f := T.map f.of ≫ T.μ.app Y.of
  map_id _ := T.right_unit _
  map_comp {X} {Y} {Z} f g := by
    simp [← T.μ.naturality_assoc g.of, T.assoc]

/-- The Kleisli adjunction which gives rise to the monad `(T, η_ T, μ_ T)`.
cf Lemma 5.2.11 of [Riehl][riehl2017]. -/
def adj : toKleisli T ⊣ fromKleisli T :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y := { toFun f := f.of, invFun f := .mk f }
      homEquiv_naturality_left_symm := fun {X} {Y} {Z} f g => by
        ext
        simp [← T.η.naturality_assoc g] }

/-- The composition of the adjunction gives the original functor. -/
def toKleisliCompFromKleisliIsoSelf : toKleisli T ⋙ fromKleisli T ≅ T :=
  NatIso.ofComponents fun _ => Iso.refl _

end Adjunction

end Kleisli

/-- The objects for the co-Kleisli category of the comonad `U : Comonad C`, which are the same
thing as objects of the base category `C`.
-/
structure Cokleisli (U : Comonad C) where mk (U) ::
  /-- The underlying object of the base category. -/
  of : C

namespace Cokleisli

variable (U : Comonad C)

@[simp] lemma mk_of (c : Cokleisli U) : Cokleisli.mk U c.of = c := rfl
lemma of_mk (c : C) : (Cokleisli.mk U c).of = c := rfl

variable {U} in
/-- For (U : Comonad C), morphisms `c ⟶ c'` in the Cokleisli category of `U` are
morphisms ` U.obj c ⟶ c'` in `C`. -/
structure Hom (c c' : Cokleisli U) where
  /-- The morphism in C underlying the morphism in the Kleisli category. -/
  of : U.obj c.of ⟶ c'.of

instance [Inhabited C] (U : Comonad C) : Inhabited (Cokleisli U) := ⟨.mk U default⟩

/-- The co-Kleisli category on a comonad `U`. -/
@[simps!]
instance category : Category (Cokleisli U) where
  Hom X Y := Hom X Y
  id X := .mk <| U.ε.app X.of
  comp f g := .mk <| U.δ.app _ ≫ (U : C ⥤ C).map f.of ≫ g.of

variable {T} in
attribute [local ext] Hom in
@[ext]
lemma hom_ext {x y : Cokleisli U} {f g : x ⟶ y} (h : f.of = g.of) : f = g :=
  Hom.ext h

namespace Adjunction

/-- The right adjoint of the adjunction which induces the comonad `(U, ε_ U, δ_ U)`. -/
@[simps]
def toCokleisli : C ⥤ Cokleisli U where
  obj X := .mk U X
  map {X} {_} f := .mk (U.ε.app X ≫ f)

/-- The left adjoint of the adjunction which induces the comonad `(U, ε_ U, δ_ U)`. -/
@[simps]
def fromCokleisli : Cokleisli U ⥤ C where
  obj X := U.obj X.of
  map {X} {_} f := U.δ.app X.of ≫ U.map f.of
  map_id _ := U.right_counit _

/-- The co-Kleisli adjunction which gives rise to the comonad `(U, ε_ U, δ_ U)`. -/
def adj : fromCokleisli U ⊣ toCokleisli U :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y := { toFun f := .mk f, invFun f := f.of }
      homEquiv_naturality_right := fun {X} {Y} {_} f g => by cat_disch }

/-- The composition of the adjunction gives the original functor. -/
def toCokleisliCompFromCokleisliIsoSelf : toCokleisli U ⋙ fromCokleisli U ≅ U :=
  NatIso.ofComponents fun _ => Iso.refl _

end Adjunction

end Cokleisli

end CategoryTheory
