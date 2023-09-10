import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Triangulated.Orthogonal

open CategoryTheory

namespace CochainComplex

variable {C : Type*} [Category C] [Abelian C]
  (K L : CochainComplex C ℤ)

class IsKInjective : Prop where
  nonempty_homotopy_zero (K : CochainComplex C ℤ) (hK : ∀ (n : ℤ), K.ExactAt n) (f : K ⟶ L) :
    Nonempty (Homotopy f 0)

variable {K L}

noncomputable irreducible_def homotopyZero (f : K ⟶ L)
    (hK : ∀ (n : ℤ), K.ExactAt n) [L.IsKInjective] :
    Homotopy f 0 :=
  (IsKInjective.nonempty_homotopy_zero K hK f).some

variable (L)

lemma isKInjective_iff_mem_rightOrthogonal :
    L.IsKInjective ↔
      (HomotopyCategory.quotient _ _).obj L ∈
        (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal.set := by
  constructor
  · intro _ ⟨(K : CochainComplex C ℤ)⟩ f hK
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    erw [HomotopyCategory.mem_subcategoryAcyclic_iff_exactAt] at hK
    rw [HomotopyCategory.eq_of_homotopy f 0 (homotopyZero f hK), Functor.map_zero]
  · intro hL
    refine' ⟨fun K hK f => _⟩
    rw [← HomotopyCategory.mem_subcategoryAcyclic_iff_exactAt] at hK
    refine' ⟨HomotopyCategory.homotopyOfEq _ _ _⟩
    rw [hL ((HomotopyCategory.quotient _ _).map f) hK, Functor.map_zero]

variable {L}

lemma isKInjective_iff_of_iso (e : K ≅ L) :
    K.IsKInjective ↔ L.IsKInjective := by
  simp only [isKInjective_iff_mem_rightOrthogonal]
  exact Set.mem_iff_of_iso _ ((HomotopyCategory.quotient _ _).mapIso e)

lemma isKInjective_of_iso (e : K ≅ L) [K.IsKInjective] : L.IsKInjective := by
  rw [← isKInjective_iff_of_iso e]
  infer_instance

variable (K)

instance sKInjective_shift [hK : K.IsKInjective] (n : ℤ) : K⟦n⟧.IsKInjective := by
  simp only [isKInjective_iff_mem_rightOrthogonal] at hK ⊢
  erw [Set.mem_iff_of_iso _ ((((HomotopyCategory.quotient C
    (ComplexShape.up ℤ))).commShiftIso n).app K)]
  exact Triangulated.Subcategory.shift _ _ n hK

lemma isKInjective_shift_iff (n : ℤ) :
    K⟦n⟧.IsKInjective ↔ K.IsKInjective := by
  constructor
  · intro
    exact isKInjective_of_iso (show K⟦n⟧⟦-n⟧ ≅ K from (shiftEquiv _ n).unitIso.symm.app K)
  · intro
    infer_instance

variable (L)

open HomComplex

lemma homComplex_exactAt_of_KInjective' [L.IsKInjective] (hK : ∀ (n : ℤ), K.ExactAt n) (n : ℤ) :
    (HomComplex K L).ExactAt n := by
  rw [(HomComplex K L).exactAt_iff' (n-1) n (n+1) (by simp) (by simp), ShortComplex.ab_exact_iff]
  intro (x₂ : Cochain K L n) hx₂
  obtain ⟨α, hα⟩ := (Cochain.equivHomotopy _ _) (homotopyZero ((Cocycle.equivHom _ _).symm
    ((Cocycle.mk x₂ (n+1) (by simp) hx₂).rightShift n 0 (zero_add n))) hK)
  simp only [Cocycle.equivHom_symm_apply, Cocycle.cochain_ofHom_homOf_eq_coe,
    Cocycle.rightShift_coe, Cocycle.mk_coe, Cochain.ofHom_zero, add_zero] at hα
  refine' ⟨n.negOnePow • α.rightUnshift (n-1) (by linarith), _⟩
  apply (Cochain.rightShiftEquiv K L n n 0 (zero_add n)).injective
  dsimp [HomComplex]
  simp only [hα, δ_zsmul, Cochain.rightShift_zsmul,
    α.δ_rightUnshift (n-1) (by linarith) n 0 (by linarith),
    Cochain.rightShift_rightUnshift, smul_smul,
    Int.negOnePow_mul_self, one_smul]

end CochainComplex
