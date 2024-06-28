import Mathlib.CategoryTheory.Monad.Comonadicity
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Flat.Algebra
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorPower

noncomputable section

open CategoryTheory Comonad ModuleCat Limits MonoidalCategory

open scoped TensorProduct

variable {A B : Type} [CommRing.{0} A] [CommRing.{0} B] (f : A →+* B) [f.Flat]
  -- [(extendScalars f).ReflectsIsomorphisms] -- `f` is faithfully flat.

example : ModuleCat A ⥤ ModuleCat B := ModuleCat.extendScalars f

instance : Module A B := f.toAlgebra.toModule

example : extendScalars f ⋙ restrictScalars f ≅
    tensorLeft ((restrictScalars f).obj (ModuleCat.of B B)) :=
  Iso.refl _

instance : Module.Flat A ((restrictScalars f).obj (ModuleCat.of B B)) :=
  -- algebraize f
  let _ : Algebra A B := f.toAlgebra
  (inferInstance : f.Flat).1.1

instance : PreservesFiniteLimits <| tensorLeft ((restrictScalars f).obj (ModuleCat.of B B)) :=
  sorry -- This is in a PR

instance : PreservesFiniteLimits (extendScalars f) := by
  have : PreservesFiniteLimits (extendScalars f ⋙ restrictScalars f) :=
    inferInstanceAs
      (PreservesFiniteLimits <| tensorLeft ((restrictScalars f).obj (ModuleCat.of B B)))
  apply preservesFiniteLimitsOfReflectsOfPreserves (extendScalars f) (restrictScalars f)

def extendScalarsComonadic : ComonadicLeftAdjoint (extendScalars f) := by
  apply (config := {allowSynthFailures := true})
    comonadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms (G := restrictScalars f)
  · exact (extendRestrictScalarsAdj f)
  · sorry -- This follows from `f` being faithfully flat.
  · constructor
    intros
    infer_instance
  · suffices ∀ {M N : ModuleCat A} (g : M ⟶ N),
        PreservesLimit (parallelPair g (0 : M ⟶ N)) (extendScalars f) by
      constructor
      intros
      apply CategoryTheory.Functor.preservesEqualizerOfPreservesKernels
    intro M N g
    infer_instance

example : Comonad (ModuleCat B) := (extendRestrictScalarsAdj f).toComonad

example (Q : Coalgebra (extendRestrictScalarsAdj f).toComonad) : ModuleCat A :=
  (comparison (extendScalarsComonadic f).adj).asEquivalence.inverse.obj Q


variable (M : ModuleCat A)
variable (R : Type) [CommRing R] [Algebra A R]


instance : Module A B := f.toAlgebra.toModule
instance : Algebra A B := f.toAlgebra


#check TensorProduct A ((restrictScalars f).obj ⟨B⟩) M

example : CommRing (R ⊗[A] R) := by infer_instance

example : CommRing <| @TensorProduct A _ B B _ _ f.toAlgebra.toModule f.toAlgebra.toModule   := by
  infer_instance

-- example : CommRing <| TensorPower A 2 ((restrictScalars f).obj ⟨B⟩) := by
--   let _

-- instance (n: ℕ) : CommRing <| TensorPower A n ((restrictScalars f).obj ⟨B⟩) := by
--   sorry
example (N : ModuleCat R) : Module A (RestrictScalars A R N) := by infer_instance

example (M N : ModuleCat R) :
    let M' := (RestrictScalars A R M)
    let N' := (RestrictScalars A R N)
    Module (R ⊗[A] R) (M' ⊗[A] R) := by
  have : (M' ⊗[A] R) → TensorProduct R M (R ⊗[A] R) := by exact?



example (M N : ModuleCat R) :
    let M' := (RestrictScalars A R M)
    let N' := (RestrictScalars A R N)
    letI _ := @TensorProduct.Algebra.module A R R (M' ⊗[A] N') _ _ _ _ _
    Module (R ⊗[A] R) (M' ⊗[A] N') := by

  sorry

--example : B ⟶ (TensorPower A n ((restrictScalars f).obj ⟨B⟩)) := by sorry

example : CommRing <| TensorPower A 2 ((restrictScalars f).obj ⟨B⟩) := by
  sorry

universe u v

example : Algebra R (R ⊗[A] R) := by infer_instance

--Weird issues
structure DescentDatum {A : Type } {B : Type } [CommRing.{0} A] [CommRing.{0} B] (f : A →+* B) where
  /-- The underlying object associated to a descent datum. -/
  M : ModuleCat B

  ϕ : letI _ :=f.toAlgebra
      B ⊗ M ⟶ M ⊗ B
  alg : Algebra A B  := f.toAlgebra -- Delete this field later, and infer automatically
  -- /-- The structure morphism defining a descent datum. -/
  -- ϕ :  B ⊗ M ⟶ M ⊗ B
  -- /-- The cocycle condition. -/
