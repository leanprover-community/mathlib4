/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.AdjoinRoot

/-!
# Finitely presented algebras and finitely presented modules

In this file we establish relations between finitely presented as an algebra and
finitely presented as a module.

## Main results:

- `Algebra.FinitePresentation.of_finitePresentation`: If `S` is finitely presented as a
  module over `R`, then it is finitely presented as an algebra over `R`.
- `Module.FinitePresentation.of_finite_of_finitePresentation`: If `S` is finite as a module over `R`
  and finitely presented as an algebra over `R`, then it is finitely presented as a module over `R`.

## References

- [Grothendieck, EGA IV₁ 1.4.7][ega-iv-1]
-/

universe u

variable (R : Type u) (S : Type*) [CommRing R] [CommRing S] [Algebra R S]

attribute [instance] AdjoinRoot.finitePresentation

/-- EGA IV₁, 1.4.7.1 -/
lemma Module.Finite.exists_free_surjective [Module.Finite R S] :
    ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra R S') (_ : Module.Finite R S')
      (_ : Module.Free R S') (_ : Algebra.FinitePresentation R S')
      (f : S' →ₐ[R] S), Function.Surjective f := by
  classical
  obtain ⟨s, hs⟩ : (⊤ : Submodule R S).FG := Module.finite_def.mp inferInstance
  suffices h : ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra R S') (_ : Module.Finite R S')
      (_ : Module.Free R S') (_ : Algebra.FinitePresentation R S')
      (f : S' →ₐ[R] S), (s : Set S) ⊆ AlgHom.range f by
    obtain ⟨S', _, _, _, _, _, f, hsf⟩ := h
    have hf : Function.Surjective f := by
      have := (Submodule.span_le (p := LinearMap.range f.toLinearMap)).mpr hsf
      rwa [hs, top_le_iff, LinearMap.range_eq_top] at this
    use S', ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, f
  clear hs
  induction s using Finset.induction with
  | empty =>
    exact ⟨R, _, _, inferInstance, inferInstance, inferInstance, Algebra.ofId R S, by simp⟩
  | insert a s has IH =>
    obtain ⟨S', _, _, _, _, _, f, hsf⟩ := IH
    have ha := Algebra.IsIntegral.isIntegral (R := R) a
    have := ((minpoly.monic ha).map (algebraMap R S')).finite_adjoinRoot
    have := ((minpoly.monic ha).map (algebraMap R S')).free_adjoinRoot
    algebraize [f.toRingHom]
    refine ⟨AdjoinRoot ((minpoly R a).map (algebraMap R S')), inferInstance, inferInstance,
      .trans S' _, .trans (S := S'), .trans _ S' _,
      (AdjoinRoot.liftHom _ a (by simp)).restrictScalars R, ?_⟩
    simp only [Finset.coe_insert, AlgHom.coe_range, AlgHom.coe_restrictScalars',
      Set.insert_subset_iff, Set.mem_range]
    exact ⟨⟨.root _, by simp⟩, hsf.trans fun y ⟨x, hx⟩ ↦ ⟨.of _ x, by simpa⟩⟩

/-- If `S` is finitely presented as a module over `R`, it is finitely
presented as an algebra over `R`. -/
instance Algebra.FinitePresentation.of_finitePresentation
    [Module.FinitePresentation R S] : Algebra.FinitePresentation R S := by
  obtain ⟨S', _, _, _, _, _, f, hf⟩ := Module.Finite.exists_free_surjective R S
  refine .of_surjective hf ?_
  apply Submodule.FG.of_restrictScalars R
  exact Module.FinitePresentation.fg_ker f.toLinearMap hf

/-- If `S` is finite as a module over `R` and finitely presented as an algebra over `R`, then
it is finitely presented as a module over `R`. -/
@[stacks 0564 "The case M = S"]
lemma Module.FinitePresentation.of_finite_of_finitePresentation
    [Module.Finite R S] [Algebra.FinitePresentation R S] :
    Module.FinitePresentation R S := by
  classical
  obtain ⟨R', _, _, _, _, _, f, hf⟩ := Module.Finite.exists_free_surjective R S
  letI := f.toRingHom.toAlgebra
  have : IsScalarTower R R' S := .of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.FinitePresentation R R' :=
    Module.finitePresentation_of_projective R R'
  have : Module.FinitePresentation R' S :=
    Module.finitePresentation_of_surjective (Algebra.linearMap R' S) hf
      (Algebra.FinitePresentation.ker_fG_of_surjective f hf)
  exact .trans R S R'

/-- If `S` is a finite `R`-algebra, finitely presented as a module and as an algebra
is equivalent. -/
lemma Module.FinitePresentation.iff_finitePresentation_of_finite [Module.Finite R S] :
    Module.FinitePresentation R S ↔ Algebra.FinitePresentation R S :=
  ⟨fun _ ↦ .of_finitePresentation R S, fun _ ↦ .of_finite_of_finitePresentation R S⟩
