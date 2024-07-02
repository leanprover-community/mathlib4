import Mathlib.CategoryTheory.Monad.Comonadicity
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Flat.Algebra
import Mathlib.RingTheory.Flat.Basic

noncomputable section

open CategoryTheory Comonad ModuleCat Limits MonoidalCategory

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
    monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms (G := restrictScalars f)
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
