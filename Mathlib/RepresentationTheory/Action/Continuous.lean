import Mathlib.RepresentationTheory.Action.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.MulAction

universe u v

open CategoryTheory

variable (V : Type (u+1)) [LargeCategory V] (G : MonCat.{u}) [ConcreteCategory V]

instance (X : Action V G) : MulAction G ((forget V).obj X.V) where
  smul g x := (forget V).map (X.ρ g) x
  one_smul x := by
    show (forget V).map (X.ρ 1) x = x
    simp only [Action.ρ_one, FunctorToTypes.map_id_apply]
  mul_smul g h x := by
    show (forget V).map (X.ρ (g * h)) x = ((forget V).map (X.ρ h) ≫ (forget V).map (X.ρ g)) x
    rw [←Functor.map_comp, map_mul]
    rfl

variable [∀ (X : Action V G), TopologicalSpace ((forget V).obj X.V)]
    [TopologicalSpace (G : Type u)] 

def cont (X : Action V G) : Prop := ContinuousSMul G ((forget V).obj X.V)

def ContAction : Type (u+1) := FullSubcategory (cont V G)

instance : Category (ContAction V G) := FullSubcategory.category (cont V G)
