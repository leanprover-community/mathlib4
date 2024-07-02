import Mathlib.Algebra.Category.ModuleCatNew.Basic
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.CategoryTheory.Functor.Category

universe u

open CategoryTheory Category

namespace ModuleCatNew

attribute [local instance] ConcreteCategory.instFunLike

variable (R : Type u) [Ring R]

-- purposely no @[simps]
noncomputable def free : Type u ⥤ ModuleCatNew.{u} R where
  obj X := of R (X →₀ R)
  map {X₁ X₂} f := homMk (Finsupp.lmapDomain _ _ f)
  map_id X := by
    apply hom_ext'
    simpa only [of_carrier, homMk_linearMap, id_linearMap] using Finsupp.lmapDomain_id R R
  map_comp f g := by
    apply hom_ext'
    simpa only [of_carrier, homMk_linearMap, comp_linearMap] using Finsupp.lmapDomain_comp R R f g

variable {R}

noncomputable def freeMk {X : Type u} (x : X) : (free R).obj X := Finsupp.single x 1

@[ext 1200]
lemma free_hom_ext {X : Type u} {M : ModuleCatNew.{u} R} {f g : (free R).obj X ⟶ M}
    (h : ∀ (x : X), f (freeMk x) = g (freeMk x)) :
    f = g :=
  hom_ext' (Finsupp.lhom_ext' (fun x ↦ LinearMap.ext_ring (h x)))

@[simps]
noncomputable def freeDesc {X : Type u} {M : ModuleCatNew.{u} R} (f : X ⟶ M) :
    (free R).obj X ⟶ M where
  linearMap := (Finsupp.lift M R X f)

@[simp]
lemma freeDesc_apply {X : Type u} {M : ModuleCatNew.{u} R} (f : X ⟶ M) (x : X) :
    freeDesc f (freeMk x) = f x := by
  dsimp [freeDesc]
  erw [Finsupp.lift_apply, Finsupp.sum_single_index]
  all_goals simp

@[simp]
lemma free_map_apply {X Y : Type u} (f : X → Y) (x : X) :
    (free R).map f (freeMk x) = freeMk (f x) := by
  apply Finsupp.mapDomain_single

--attribute [irreducible] free

end ModuleCatNew
