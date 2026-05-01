/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.CategoryTheory.Abelian.EpiWithInjectiveKernel

/-!
# Basic definitions for factorization lemmas

We define the class of morphisms
`degreewiseEpiWithInjectiveKernel : MorphismProperty (CochainComplex C ℤ)`
in the category of cochain complexes in an abelian category `C`.

When restricted to the full subcategory of bounded below cochain complexes in an
abelian category `C` that has enough injectives, this is the class of
fibrations for a model category structure on the bounded below
category of cochain complexes in `C`. In this folder, we intend to prove two factorization
lemmas in the category of bounded below cochain complexes (TODO):
* CM5a: any morphism `K ⟶ L` can be factored as `K ⟶ K' ⟶ L` where `i : K ⟶ K'` is a
  trivial cofibration (a mono that is also a quasi-isomorphism) and `p : K' ⟶ L` is a fibration.
* CM5b: any morphism `K ⟶ L` can be factored as `K ⟶ L' ⟶ L` where `i : K ⟶ L'` is a
  cofibration (i.e. a mono) and `p : L' ⟶ L` is a trivial fibration (i.e. a quasi-isomorphism
  which is also a fibration)

The difficult part is CM5a (whose proof uses CM5b). These lemmas shall be essential
ingredients in the proof that the bounded below derived category of an abelian
category `C` with enough injectives identifies to the bounded below homotopy category
of complexes of injective objects in `C`. This will be used in the construction
of total derived functors (and a refactor of the sequence of derived functors).

-/

@[expose] public section

open CategoryTheory Abelian Limits

variable {C : Type*} [Category* C] [Abelian C]

namespace CochainComplex

/-- A morphism of cochain complexes `φ` in an abelian category satisfies
`degreewiseEpiWithInjectiveKernel φ` if for any `i : ℤ`, the morphism
`φ.f i` is an epimorphism with an injective kernel. -/
def degreewiseEpiWithInjectiveKernel : MorphismProperty (CochainComplex C ℤ) :=
  fun _ _ φ => ∀ (i : ℤ), epiWithInjectiveKernel (φ.f i)

instance : (degreewiseEpiWithInjectiveKernel (C := C)).IsMultiplicative where
  id_mem _ _ := MorphismProperty.id_mem _ _
  comp_mem _ _ hf hg n := MorphismProperty.comp_mem _ _ _ (hf n) (hg n)

instance : (degreewiseEpiWithInjectiveKernel (C := C)).IsStableUnderRetracts where
  of_retract r h i :=
    MorphismProperty.of_retract (r.map (HomologicalComplex.eval _ _ i)) (h i)

variable {K L : CochainComplex C ℤ} (φ : K ⟶ L)

def monoUpTo (n : ℤ) : Prop := ∀ (i : ℤ) (_ : i ≤ n), Mono (φ.f i)

lemma degreewiseEpiWithInjectiveKernel.epi {K L : CochainComplex C ℤ} {f : K ⟶ L}
    (hf : degreewiseEpiWithInjectiveKernel f) :
    Epi f :=
  HomologicalComplex.epi_of_epi_f f (fun n ↦ (hf n).1)

/-- A morphism of cochain complexes `φ` in an abelian category satisfies
`degreewiseMonoWithProjectiveKernel φ` if for any `i : ℤ`, the morphism
`φ.f i` is a monomorphism with a projective kernel. -/
def degreewiseMonoWithProjectiveCokernel : MorphismProperty (CochainComplex C ℤ) :=
  fun _ _ φ => ∀ (i : ℤ), monoWithProjectiveCokernel (φ.f i)

lemma degreewiseMonoWithProjectiveKernel.mono {K L : CochainComplex C ℤ} {f : K ⟶ L}
    (hf : degreewiseMonoWithProjectiveCokernel f) :
    Mono f :=
  HomologicalComplex.mono_of_mono_f f (fun n ↦ (hf n).1)

lemma degreewiseMonoWithProjectiveCokernel_eq_unop :
    degreewiseMonoWithProjectiveCokernel (C := C) =
      (degreewiseEpiWithInjectiveKernel (C := Cᵒᵖ)).op.inverseImage
        (opEquivalence C).functor.rightOp := by
  ext K L f
  simp only [degreewiseMonoWithProjectiveCokernel, monoWithProjectiveCokernel_eq_unop,
    MorphismProperty.unop, MorphismProperty.inverseImage_iff, MorphismProperty.op,
    degreewiseEpiWithInjectiveKernel, Functor.rightOp_obj, Functor.rightOp_map]
  refine ⟨fun h n ↦ h _, fun h n ↦ ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = - m := ⟨-n, by simp⟩
  apply h

instance : (degreewiseMonoWithProjectiveCokernel (C := C)).IsMultiplicative := by
  rw [degreewiseMonoWithProjectiveCokernel_eq_unop]
  infer_instance

instance : (degreewiseMonoWithProjectiveCokernel (C := C)).IsStableUnderRetracts := by
  rw [degreewiseMonoWithProjectiveCokernel_eq_unop]
  infer_instance

lemma degreewiseMonoWithProjectiveCokernel_iff_of_isZero {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (hK : IsZero K) :
    degreewiseMonoWithProjectiveCokernel f ↔ ∀ (n : ℤ), Projective (L.X n) :=
  forall_congr' (fun n ↦ by
    rw [monoWithProjectiveCokernel_iff_of_isZero]
    exact Functor.map_isZero (HomologicalComplex.eval _ _ n) hK)

lemma degreewiseEpiWithInjectiveKernel_iff_of_isZero {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (hL : IsZero L) :
    degreewiseEpiWithInjectiveKernel f ↔ ∀ (n : ℤ), Injective (K.X n) :=
  forall_congr' (fun n ↦ by
    rw [epiWithInjectiveKernel_iff_of_isZero]
    exact Functor.map_isZero (HomologicalComplex.eval _ _ n) hL)

end CochainComplex
