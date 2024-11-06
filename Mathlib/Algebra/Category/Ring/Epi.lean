/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Epimorphisms in `CommRingCat`

## Main results
- `RingHom.surjective_iff_epi_and_finite`: surjective <=> epi + finite
-/

open CategoryTheory TensorProduct

universe u

lemma CommRingCat.epi_iff_tmul_eq_tmul {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    Epi (CommRingCat.ofHom (algebraMap R S)) ↔
      ∀ s : S, s ⊗ₜ[R] 1 = 1 ⊗ₜ s := by
  constructor
  · intro H
    have := H.1 (CommRingCat.ofHom <| Algebra.TensorProduct.includeLeftRingHom (R := R))
      (CommRingCat.ofHom <| Algebra.TensorProduct.includeRight.toRingHom)
      (by ext r; show algebraMap R S r ⊗ₜ 1 = 1 ⊗ₜ algebraMap R S r;
          simp only [Algebra.algebraMap_eq_smul_one, smul_tmul])
    exact RingHom.congr_fun this
  · refine fun H ↦ ⟨fun {T} f g e ↦ ?_⟩
    letI : Algebra R T := (ofHom (algebraMap R S) ≫ g).toAlgebra
    let f' : S →ₐ[R] T := ⟨f, RingHom.congr_fun e⟩
    let g' : S →ₐ[R] T := ⟨g, fun _ ↦ rfl⟩
    ext s
    simpa using congr(Algebra.TensorProduct.lift f' g' (fun _ _ ↦ .all _ _) $(H s))

lemma RingHom.surjective_of_epi_of_finite {R S : CommRingCat} (f : R ⟶ S) [Epi f]
    (h₂ : RingHom.Finite f) : Function.Surjective f := by
  letI := f.toAlgebra
  have : Module.Finite R S := h₂
  apply RingHom.surjective_of_tmul_eq_tmul_of_finite
  rwa [← CommRingCat.epi_iff_tmul_eq_tmul]

lemma RingHom.surjective_iff_epi_and_finite {R S : CommRingCat} {f : R ⟶ S} :
    Function.Surjective f ↔ Epi f ∧ RingHom.Finite f where
  mp h := ⟨ConcreteCategory.epi_of_surjective f h, .of_surjective f h⟩
  mpr := fun ⟨_, h⟩ ↦ surjective_of_epi_of_finite f h
