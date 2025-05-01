import Mathlib.CategoryTheory.Monad.Comonadicity
import Mathlib.CategoryTheory.Monad.Monadicity
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.RingHom.Flat

universe u

noncomputable section

open CategoryTheory Comonad ModuleCat Limits MonoidalCategory

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (hf : f.Flat)

instance (M : ModuleCat.{u} A) [Module.Flat A M] :
    PreservesFiniteLimits <| tensorLeft M := by
  have h1 := (Functor.preservesFiniteLimits_tfae (tensorLeft M)).out 0 3
  have h2 := ((Functor.preservesFiniteColimits_tfae (tensorLeft M)).out 0 3).mpr
    (inferInstanceAs <| PreservesFiniteColimits (tensorLeft M))
  rw [← h1]
  intro S hS
  refine ⟨(h2 S hS).1, ?_⟩
  have := hS.mono_f
  rw [ModuleCat.mono_iff_injective] at this ⊢
  apply Module.Flat.lTensor_preserves_injective_linearMap
  exact this

include hf in
lemma ModuleCat.preservesFiniteLimits_tensorLeft_of_flat :
    PreservesFiniteLimits <| tensorLeft ((restrictScalars f).obj (ModuleCat.of B B)) := by
  algebraize [f]
  change PreservesFiniteLimits <| tensorLeft (ModuleCat.of A B)
  infer_instance

instance : (restrictScalars f).ReflectsIsomorphisms :=
  have : (restrictScalars f ⋙ CategoryTheory.forget (ModuleCat A)).ReflectsIsomorphisms :=
    inferInstanceAs (CategoryTheory.forget _).ReflectsIsomorphisms
  reflectsIsomorphisms_of_comp _ (CategoryTheory.forget _)

include hf in
lemma ModuleCat.preservesFiniteLimits_extendScalars_of_flat :
    PreservesFiniteLimits (extendScalars.{_, _, u} f) := by
  have : PreservesFiniteLimits (extendScalars.{_, _, u} f ⋙ restrictScalars.{_, _, u} f) := by
    apply ModuleCat.preservesFiniteLimits_tensorLeft_of_flat
    exact hf
  exact preservesFiniteLimits_of_reflects_of_preserves (extendScalars f) (restrictScalars f)

@[simp]
lemma Module.FaithfullyFlat.lTensor_bijective_iff_bijective {R M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] {N N' : Type*}
    [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
    (f : N →ₗ[R] N')
    [Module.FaithfullyFlat R M] :
    Function.Bijective (f.lTensor M) ↔ Function.Bijective f := by
  simp [Function.Bijective]

include hf in
lemma ModuleCat.reflectsIsomorphisms_extendScalars_of_flat
    (hs : Function.Surjective f.specComap) :
    (extendScalars.{_, _, u} f).ReflectsIsomorphisms := by
  constructor
  intro M N g h
  rw [ConcreteCategory.isIso_iff_bijective] at h ⊢
  algebraize [f]
  have : Module.FaithfullyFlat A B :=
    Module.FaithfullyFlat.of_specComap_surjective hs
  replace h : Function.Bijective (LinearMap.lTensor B g.hom) := h
  rwa [Module.FaithfullyFlat.lTensor_bijective_iff_bijective] at h

def extendScalarsComonadic (hs : Function.Surjective f.specComap) :
    ComonadicLeftAdjoint (extendScalars f) := by
  apply (config := {allowSynthFailures := true})
    Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms (G := restrictScalars f)
  · exact (extendRestrictScalarsAdj f)
  · exact reflectsIsomorphisms_extendScalars_of_flat f hf hs
  · constructor
    intros
    infer_instance
  · suffices ∀ {M N : ModuleCat A} (g : M ⟶ N),
        PreservesLimit (parallelPair g (0 : M ⟶ N)) (extendScalars f) by
      constructor
      intros
      apply CategoryTheory.Functor.preservesEqualizer_of_preservesKernels
    have : PreservesFiniteLimits (extendScalars f) :=
      preservesFiniteLimits_extendScalars_of_flat f hf
    intro M N g
    infer_instance
