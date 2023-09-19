import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Abelian.Injective

open CategoryTheory Limits Category Preadditive

variable {C : Type*} [Category C] [Abelian C]

namespace CategoryTheory

def epiWithInjectiveKernel : MorphismProperty C :=
  fun _ _ f => Epi f ∧ (Injective (kernel f))

lemma epiWithInjectiveKernel_iff {X Y : C} (f : X ⟶ Y) :
    epiWithInjectiveKernel f ↔
    ∃ (I : C) (_ : Injective I) (i : I ⟶ X) (s : Y ⟶ X) (q : X ⟶ I)
      (_ : i ≫ f = 0) (_ : i ≫ q = 𝟙 I)
      (_ : s ≫ f = 𝟙 Y), 𝟙 X = q ≫ i + f ≫ s := by
  constructor
  · rintro ⟨_, _⟩
    let S := ShortComplex.mk (kernel.ι f) f (by simp)
    have hS : S.Exact := S.exact_of_f_is_kernel (kernelIsKernel f)
    let σ : S.Splitting := ShortComplex.Splitting.ofExactOfRetraction S hS
        (Injective.factorThru (𝟙 _) (kernel.ι f)) (by simp) inferInstance
    exact ⟨kernel f, inferInstance, kernel.ι f, σ.s, σ.r, by simp, σ.f_r, σ.s_g, σ.id.symm⟩
  · rintro ⟨I, _, i, s, q, hif, hiq, hsf, H⟩
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

end CategoryTheory

namespace CochainComplex

variable {K L : CochainComplex C ℤ} (φ : K ⟶ L)

def monoUpTo (n : ℤ) : Prop := ∀ (i : ℤ) (_ : i ≤ n), Mono (φ.f i)

def fibration : Prop := ∀ (i : ℤ), epiWithInjectiveKernel (φ.f i)

end CochainComplex
