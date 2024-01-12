import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.RegularExtensive

universe u

namespace CategoryTheory

open GrothendieckTopology

namespace Equivalence

variable {C : Type*} [Category C]
variable {D : Type*} [Category D] (e : C ≌ D)

section Coherent

variable [Precoherent C]

theorem precoherent : Precoherent D where
  pullback f α _ X₁ π₁ _ := by
    have : EffectiveEpiFamily _ fun i ↦ (e.inverse.map (π₁ i)) :=
      ⟨⟨effectiveEpiFamilyStructOfEquivalence e.symm X₁ π₁⟩⟩
    obtain ⟨β, x, X₂', π₂', _, i, ι', h'⟩ :=
      Precoherent.pullback (e.inverse.map f) α (fun i ↦ e.inverse.obj (X₁ i))
      (fun i ↦ (e.inverse.map (π₁ i))) this
    refine ⟨β, x, e.functor.obj ∘ X₂', fun b ↦ e.functor.map (π₂' b) ≫ e.counit.app _, ?_, i,
      fun b ↦ (e.toAdjunction.homEquiv _ _).symm (ι' b), fun b ↦ ?_⟩
    · sorry
    · simpa using congrArg ((fun f ↦ f ≫ e.counit.app _) ∘ e.functor.map) (h' b)
-- (e.toAdjunction.homEquiv _ _).symm (π₂' b)

end Coherent

section Regular

variable [Preregular C]

theorem preregular : Preregular D where
  exists_fac f g _ := by
    have : EffectiveEpi (e.inverse.map g) := sorry
    obtain ⟨W', h', _, i', hh⟩ := Preregular.exists_fac (e.inverse.map f) (e.inverse.map g)
    refine ⟨e.functor.obj W', e.functor.map h' ≫ e.counitIso.hom.app _, ?_,
      e.functor.map i' ≫ e.counitIso.hom.app _, ?_⟩
    · sorry
    · apply_fun e.functor.map at hh
      simp only [Functor.map_comp, fun_inv_map, Functor.comp_obj, Functor.id_obj] at hh
      sorry


theorem bla :
    haveI := preregular e
    (e.locallyCoverDense (regularCoverage C).toGrothendieck).inducedTopology =
    (regularCoverage D).toGrothendieck := by
  ext d S
  simp only [LocallyCoverDense.inducedTopology]
  sorry


end Regular

section Extensive

end Extensive
