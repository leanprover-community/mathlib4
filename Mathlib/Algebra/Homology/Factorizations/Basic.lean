<<<<<<< HEAD
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Abelian.Injective

open CategoryTheory Limits Category Preadditive ZeroObject

variable {C : Type*} [Category C] [Abelian C]

namespace CategoryTheory

def epiWithInjectiveKernel : MorphismProperty C :=
  fun _ _ f => Epi f ∧ (Injective (kernel f))

lemma epiWithInjectiveKernel_iff {X Y : C} (f : X ⟶ Y) :
    epiWithInjectiveKernel f ↔
    ∃ (I : C) (_ : Injective I) (i : I ⟶ X) (s : Y ⟶ X) (q : X ⟶ I)
      (_ : i ≫ f = 0) (_ : s ≫ q = 0) (_ : i ≫ q = 𝟙 I)
      (_ : s ≫ f = 𝟙 Y), 𝟙 X = q ≫ i + f ≫ s := by
  constructor
  · rintro ⟨_, _⟩
    let S := ShortComplex.mk (kernel.ι f) f (by simp)
    have hS : S.Exact := S.exact_of_f_is_kernel (kernelIsKernel f)
    let σ : S.Splitting := ShortComplex.Splitting.ofExactOfRetraction S hS
        (Injective.factorThru (𝟙 _) (kernel.ι f)) (by simp) inferInstance
    exact ⟨kernel f, inferInstance, kernel.ι f, σ.s, σ.r, by simp, by simp, σ.f_r, σ.s_g, σ.id.symm⟩
  · rintro ⟨I, _, i, s, q, hif, _, hiq, hsf, H⟩
    have : IsSplitEpi f := ⟨s, hsf⟩
    refine' ⟨inferInstance, _⟩
    have e : I ≅ kernel f :=
      { hom := kernel.lift _ i hif
        inv := kernel.ι f ≫ q
        hom_inv_id := by simp [hiq]
        inv_hom_id := by
          simp only [← cancel_mono (kernel.ι f), assoc,
            kernel.lift_ι, assoc, id_comp]
          conv_rhs => rw [← comp_id (kernel.ι f)]
          rw [H, comp_add]
          simp }
    exact Injective.of_iso e inferInstance

instance : (epiWithInjectiveKernel : MorphismProperty C).ContainsIdentities where
  id_mem' := fun X => by
    rw [epiWithInjectiveKernel_iff]
    exact ⟨0, inferInstance, 0, 𝟙 X, 0, by simp, by simp, by simp, by simp⟩

instance : (epiWithInjectiveKernel : MorphismProperty C).IsMultiplicative where
  stableUnderComposition := fun X Y Z f g hf hg => by
    rw [epiWithInjectiveKernel_iff] at hf hg ⊢
    obtain ⟨I, _, i, s, q, hif, hsq, hiq, hsf, H⟩ := hf
    obtain ⟨J, _, j, t, q', hjg, htq', hjq', htg, H'⟩ := hg
    refine' ⟨I ⊞ J, inferInstance, biprod.fst ≫ i + biprod.snd ≫ j ≫ s, t ≫ s,
      q ≫ biprod.inl + f ≫ q' ≫ biprod.inr, _, _, _, _, _⟩
    · ext
      · simp [reassoc_of% hif]
      · simp [reassoc_of% hsf, hjg]
    · simp [reassoc_of% hsq, reassoc_of% hsf, reassoc_of% htq']
    · ext
      · simp [hiq]
      · simp [reassoc_of% hif]
      · simp [hsq]
      · simp [reassoc_of% hsf, hjq']
    · simp [reassoc_of% hsf, htg]
    · simp only [comp_add, add_comp, assoc, biprod.inl_fst_assoc, BinaryBicone.inr_fst_assoc, zero_comp,
        comp_zero, add_zero, biprod.inl_snd_assoc, BinaryBicone.inr_snd_assoc, zero_add]
      rw [add_assoc, ← comp_add, ← assoc q', ← assoc g, ← add_comp, ← H', id_comp, H]

lemma epiWithInjectiveKernel_of_iso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    epiWithInjectiveKernel f := by
  rw [epiWithInjectiveKernel_iff]
  exact ⟨0, inferInstance, 0, inv f, 0, by simp, by simp, by simp, by simp, by simp⟩

end CategoryTheory

namespace CochainComplex

variable {K L : CochainComplex C ℤ} (φ : K ⟶ L)

def monoUpTo (n : ℤ) : Prop := ∀ (i : ℤ) (_ : i ≤ n), Mono (φ.f i)

def degreewiseEpiWithInjectiveKernel : MorphismProperty (CochainComplex C ℤ) :=
  fun _ _ φ => ∀ (i : ℤ), epiWithInjectiveKernel (φ.f i)

instance : (degreewiseEpiWithInjectiveKernel :
    MorphismProperty (CochainComplex C ℤ)).ContainsIdentities where
  id_mem' _ _ := MorphismProperty.id_mem _ _

instance : (degreewiseEpiWithInjectiveKernel :
    MorphismProperty (CochainComplex C ℤ)).IsMultiplicative where
  stableUnderComposition _ _ _ _ _ hf hg n := MorphismProperty.comp_mem _ _ _ (hf n) (hg n)
=======
/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Abelian.EpiWithInjectiveKernel

/-!
# Basic definitions for factorizations lemmas

We define the class of morphisms
`degreewiseEpiWithInjectiveKernel : MorphismProperty (CochainComplex C ℤ)`
in the category of cochain complexes in an abelian category `C`.

When restricted to the full subcategory of bounded below cochain complexes in an
abelian category `C` that has enough injectives, this is the class of
fibrations for a model category structure on the bounded below
category of cochain complexes in `C`. In this folder, we intend to prove two factorization
lemmas in the category of bounded below cochain complexes (TODO):
* CM5a: any morphism `K ⟶ L` can be factored as `K ⟶ K' ⟶ L` where `i : K ⟶ K'` is a
trivial cofibration (a mono that is also a quasi-isomorphisms) and `p : K' ⟶ L` is a fibration.
* CM5b: any morphism `K ⟶ L` can be factored as `K ⟶ L' ⟶ L` where `i : K ⟶ L'` is a
cofibration (i.e. a mono) and `p : L' ⟶ L` is a trivial fibration (i.e. a quasi-isomorphism
which is also a fibration)

The difficult part is CM5a (whose proof uses CM5b). These lemmas shall be essential
ingredients in the proof that the bounded below derived category of an abelian
category `C` with enough injectives identifies to the bounded below homotopy category
of complexes of injective objects in `C`. This will be used in the construction
of total derived functors (and a refactor of the sequence of derived functors).

-/


open CategoryTheory Abelian

variable {C : Type*} [Category C] [Abelian C]

namespace CochainComplex

/-- A morphism of cochain complexes `φ` in an abelian category satisfies
`degreewiseEpiWithInjectiveKernel φ` if for any `i : ℤ`, the morphism
`φ.f i` is an epimorphism with an injective kernel. -/
def degreewiseEpiWithInjectiveKernel : MorphismProperty (CochainComplex C ℤ) :=
  fun _ _ φ => ∀ (i : ℤ), epiWithInjectiveKernel (φ.f i)

instance : (degreewiseEpiWithInjectiveKernel (C := C)).IsMultiplicative where
  id_mem _ _ := MorphismProperty.id_mem _ _
  comp_mem _ _ hf hg n := MorphismProperty.comp_mem _ _ _ (hf n) (hg n)
>>>>>>> origin/ext-change-of-universes

end CochainComplex
