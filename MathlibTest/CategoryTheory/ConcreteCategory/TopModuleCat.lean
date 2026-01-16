import Mathlib.Algebra.Category.ModuleCat.Topology.Basic

universe v u

open CategoryTheory TopModuleCat

set_option maxHeartbeats 10000
set_option synthInstance.maxHeartbeats 2000

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/- We test if all the coercions and `map_add` lemmas trigger correctly. -/

example (X : Type v) [AddCommGroup X] [TopologicalSpace X]
    [ContinuousAdd X] [Module R X] [ContinuousSMul R X] : ⇑(𝟙 (of R X)) = id := by simp

example {X Y : Type v}
    [AddCommGroup X] [Module R X] [TopologicalSpace X] [ContinuousAdd X] [ContinuousSMul R X]
    [AddCommGroup Y] [Module R Y] [TopologicalSpace Y] [ContinuousAdd Y] [ContinuousSMul R Y]
    (f : X →L[R] Y) :
    ⇑(TopModuleCat.ofHom f) = ⇑f := by simp

example {X Y : Type v}
    [AddCommGroup X] [Module R X] [TopologicalSpace X] [ContinuousAdd X] [ContinuousSMul R X]
    [AddCommGroup Y] [Module R Y] [TopologicalSpace Y] [ContinuousAdd Y] [ContinuousSMul R Y]
    (f : X →L[R] Y) (x : X) : (TopModuleCat.ofHom f) x = f x := by simp

example {X Y Z : TopModuleCat R} (f : X ⟶ Y) (g : Y ⟶ Z) : ⇑(f ≫ g) = ⇑g ∘ ⇑f := by simp

example {X Y Z : Type v}
    [AddCommGroup X] [Module R X] [TopologicalSpace X] [ContinuousAdd X] [ContinuousSMul R X]
    [AddCommGroup Y] [Module R Y] [TopologicalSpace Y] [ContinuousAdd Y] [ContinuousSMul R Y]
    [AddCommGroup Z] [Module R Z] [TopologicalSpace Z] [ContinuousAdd Z] [ContinuousSMul R Z]
    (f : X →L[R] Y) (g : Y →L[R] Z) :
    ⇑(TopModuleCat.ofHom f ≫ TopModuleCat.ofHom g) = g ∘ f := by simp

example {X Y : Type v}
    [AddCommGroup X] [Module R X] [TopologicalSpace X] [ContinuousAdd X] [ContinuousSMul R X]
    [AddCommGroup Y] [Module R Y] [TopologicalSpace Y] [ContinuousAdd Y] [ContinuousSMul R Y]
    {Z : TopModuleCat R}
    (f : X →L[R] Y) (g : of R Y ⟶ Z) :
    ⇑(TopModuleCat.ofHom f ≫ g) = g ∘ f := by simp

example {Y Z : TopModuleCat R} {X : Type v}
    [AddCommGroup X] [Module R X] [TopologicalSpace X] [ContinuousAdd X] [ContinuousSMul R X]
    (f : of R X ⟶ Y) (g : Y ⟶ Z) :
    ⇑(f ≫ g) = g ∘ f := by simp

example {X : Type v}
    [AddCommGroup X] [Module R X] [TopologicalSpace X] [ContinuousAdd X] [ContinuousSMul R X]
    {Y Z : TopModuleCat R}
    (f : X →L[R] Y) (g : of R Y ⟶ Z) :
    ⇑(TopModuleCat.ofHom f ≫ g) = g ∘ f := by simp

example {X Y Z : TopModuleCat R} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) := by simp

example {X Y : TopModuleCat R} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by simp

example {X Y : TopModuleCat R} (e : X ≅ Y) (y : Y) : e.hom (e.inv y) = y := by simp

example (X : TopModuleCat R) : ⇑(𝟙 X) = id := by simp

example {M N : TopModuleCat.{v} R} (f : M ⟶ N) (x y : M) : f (x + y) = f x + f y := by
  simp

example {M N : TopModuleCat.{v} R} (f : M ⟶ N) : f 0 = 0 := by
  simp

example {M N : TopModuleCat.{v} R} (f : M ⟶ N) (r : R) (m : M) : f (r • m) = r • f m := by
  simp

example {M N : TopModuleCat.{v} R} (f : M ⟶ N) : Continuous f := by continuity

example {M N : TopModuleCat.{v} R} (f : M ⟶ N) : Continuous f := by fun_prop
