import Mathlib

universe v u

open CategoryTheory AlgebraCat

set_option maxHeartbeats 10000

variable (R : Type u) [CommRing R]

/- We test if all the coercions and `map_add` lemmas trigger correctly. -/

example (X : Type u) [CommRing X] [Algebra R X] : ⇑(𝟙 (of R X)) = id := by simp

example {X Y : Type v} [CommRing X] [Algebra R X] [CommRing Y] [Algebra R Y] (f : X →ₐ[R] Y) :
    ⇑(ofHom f) = ⇑f := by simp

example {X Y : Type v} [CommRing X] [Algebra R X] [CommRing Y] [Algebra R Y] (f : X →ₐ[R] Y)
    (x : X) : (ofHom f) x = f x := by simp

example {X Y Z : AlgebraCat R} (f : X ⟶ Y) (g : Y ⟶ Z) : ⇑(f ≫ g) = ⇑g ∘ ⇑f := by simp

example {X Y Z : Type v} [CommRing X] [Algebra R X] [CommRing Y] [Algebra R Y] [CommRing Z]
    [Algebra R Z] (f : X →ₐ[R] Y) (g : Y →ₐ[R] Z) :
    ⇑(ofHom f ≫ ofHom g) = g ∘ f := by simp

example {X Y : Type v} [CommRing X] [Algebra R X] [CommRing Y] [Algebra R Y] {Z : AlgebraCat R}
    (f : X →ₐ[R] Y) (g : of R Y ⟶ Z) :
    ⇑(ofHom f ≫ g) = g ∘ f := by simp

example {X Y : AlgebraCat R} {Z : Type v} [CommRing Z] [Algebra R Z] (f : X ⟶ Y) (g : Y ⟶ of R Z) :
    ⇑(f ≫ g) = g ∘ f := by simp

example {Y Z : AlgebraCat R} {X : Type v} [CommRing X] [Algebra R X] (f : of R X ⟶ Y) (g : Y ⟶ Z) :
    ⇑(f ≫ g) = g ∘ f := by simp

example {X Y Z : AlgebraCat R} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) := by simp

example (X : AlgebraCat R) : ⇑(𝟙 X) = id := by simp

example {M N : AlgebraCat.{v} R} (f : M ⟶ N) (x y : M) : f (x + y) = f x + f y := by
  simp

example {M N : AlgebraCat.{v} R} (f : M ⟶ N) : f 0 = 0 := by
  simp

example {M N : AlgebraCat.{v} R} (f : M ⟶ N) (r : R) (m : M) : f (r • m) = r • f m := by
  simp
