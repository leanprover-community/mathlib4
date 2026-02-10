import Mathlib.Algebra.Category.Semigrp.Basic

universe v u

open CategoryTheory Semigrp

set_option maxHeartbeats 10000
set_option synthInstance.maxHeartbeats 2000

/- We test if all the coercions and `map_mul` lemmas trigger correctly. -/

example (X : Type u) [Semigroup X] : ⇑(𝟙 (of X)) = id := by simp

example {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) :
    ⇑(ofHom f) = ⇑f := by simp

example {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y)
    (x : X) : (ofHom f) x = f x := by simp

example {X Y Z : Semigrp} (f : X ⟶ Y) (g : Y ⟶ Z) : ⇑(f ≫ g) = ⇑g ∘ ⇑f := by simp

example {X Y Z : Type u} [Semigroup X] [Semigroup Y] [Semigroup Z]
    (f : X →ₙ* Y) (g : Y →ₙ* Z) :
    ⇑(ofHom f ≫ ofHom g) = g ∘ f := by simp

example {X Y : Type u} [Semigroup X] [Semigroup Y] {Z : Semigrp}
    (f : X →ₙ* Y) (g : of Y ⟶ Z) :
    ⇑(ofHom f ≫ g) = g ∘ f := by simp

example {X Y : Semigrp} {Z : Type u} [Semigroup Z] (f : X ⟶ Y) (g : Y ⟶ of Z) :
    ⇑(f ≫ g) = g ∘ f := by simp

example {Y Z : Semigrp} {X : Type u} [Semigroup X] (f : of X ⟶ Y) (g : Y ⟶ Z) :
    ⇑(f ≫ g) = g ∘ f := by simp

example {X Y Z : Semigrp} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) := by simp

example {X Y : Semigrp} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by simp

example {X Y : Semigrp} (e : X ≅ Y) (y : Y) : e.hom (e.inv y) = y := by simp

example (X : Semigrp) : ⇑(𝟙 X) = id := by simp

example {X : Type*} [Semigroup X] : ⇑(MulHom.id X) = id := by simp

example {M N : Semigrp} (f : M ⟶ N) (x y : M) : f (x * y) = f x * f y := by
  simp
