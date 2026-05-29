/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# Kan complexes

In this file, the abbreviation `KanComplex` is introduced for
fibrant objects in the category `SSet` which is equipped with
Kan fibrations.

In `Mathlib/AlgebraicTopology/Quasicategory/Basic.lean`
we show that every Kan complex is a quasicategory.

## TODO

- Show that the singular simplicial set of a topological space is a Kan complex.

-/

public section

universe u

namespace SSet

open CategoryTheory Simplicial Limits HomotopicalAlgebra

open modelCategoryQuillen in
/-- A simplicial set `S` is a Kan complex if it is fibrant, which means that
the projection `S ⟶ ⊤_ _` has the right lifting property with respect to horn inclusions. -/
abbrev KanComplex (S : SSet.{u}) : Prop := HomotopicalAlgebra.IsFibrant S

/-- A Kan complex `S` satisfies the following horn-filling condition:
for every nonzero `n : ℕ` and `0 ≤ i ≤ n`,
every map of simplicial sets `σ₀ : Λ[n, i] → S` can be extended to a map `σ : Δ[n] → S`. -/
lemma KanComplex.hornFilling {S : SSet.{u}} [KanComplex S]
    {n : ℕ} {i : Fin (n + 2)} (σ₀ : (Λ[n + 1, i] : SSet) ⟶ S) :
    ∃ σ : Δ[n + 1] ⟶ S, σ₀ = Λ[n + 1, i].ι ≫ σ := by
  have sq' : CommSq σ₀ Λ[n + 1, i].ι (terminal.from S) (terminal.from _) := ⟨by simp⟩
  exact ⟨sq'.lift, by simp⟩

namespace horn.IsCompatible

variable {X : SSet.{u}} {n : ℕ}
  {i : Fin (n + 2)} {f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ X}

lemma exists_lift_of_kanComplex [KanComplex X]
    (hf : horn.IsCompatible f) :
    ∃ (φ : Δ[n + 1] ⟶ X),
      ∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ φ = f j hj := by
  obtain ⟨φ, hφ, _⟩ := hf.exists_lift (terminal.from _) (terminal.from _) (by simp)
  exact ⟨φ, hφ⟩

/-- If `X` is a Kan complex and `f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ X`
is a compatible family of morphisms (which defines a morphism `Λ[n + 1, i] ⟶ X`),
then this is a lifting `Δ[n + 1] ⟶ X`. -/
@[no_expose]
noncomputable def liftOfKanComplex [KanComplex X] (hf : horn.IsCompatible f) :
    Δ[n + 1] ⟶ X :=
  hf.exists_lift_of_kanComplex.choose

@[reassoc]
lemma δ_liftOfKanComplex [KanComplex X] (hf : horn.IsCompatible f)
    (j : Fin (n + 2)) (hj : j ≠ i := by grind) :
    stdSimplex.δ j ≫ hf.liftOfKanComplex = f j hj :=
  hf.exists_lift_of_kanComplex.choose_spec j hj

end horn.IsCompatible

open modelCategoryQuillen in
/-- A simplicial set `X` is a Kan complex iff for any `n : ℕ`, `i : Fin (n + 2)`,
and any family of morphisms `Δ[n] ⟶ Z` for all `j ≠ i` that is compatible
(in the sense that it extends to a morphism `Λ[n + 1, i] ⟶ X`), there
exists a morphism `Δ[n + 1] ⟶ Z` which induces the given family of morphisms
on the faces `j ≠ i`. -/
lemma KanComplex.iff {Z : SSet.{u}} :
    KanComplex Z ↔
      ∀ ⦃n : ℕ⦄ ⦃i : Fin (n + 2)⦄ (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ Z)
        (_ : horn.IsCompatible f),
        ∃ (φ : Δ[n + 1] ⟶ Z),
          ∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ φ = f j hj := by
  refine ⟨fun _ n i f hf ↦ hf.exists_lift_of_kanComplex,
    fun h ↦ (isFibrant_iff _).2 ⟨?_⟩⟩
  rw [fibrations_eq]
  intro _ _ _ hf
  simp only [J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  refine ⟨fun {t _} _ ↦ ?_⟩
  obtain ⟨φ, hφ⟩ := h _ (horn.IsCompatible.of_hom t)
  exact ⟨⟨{
    l := φ
    fac_left := horn.hom_ext' (by simpa using hφ)
    fac_right := by subsingleton }⟩⟩

end SSet
