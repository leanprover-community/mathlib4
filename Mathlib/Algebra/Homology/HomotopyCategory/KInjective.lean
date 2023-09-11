import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Mathlib.CategoryTheory.Abelian.InjectiveResolution

open CategoryTheory Category Preadditive Limits

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

instance isKInjective_shift [hK : K.IsKInjective] (n : ℤ) : K⟦n⟧.IsKInjective := by
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

lemma homComplex_exactAt_of_KInjective [L.IsKInjective] (hK : ∀ (n : ℤ), K.ExactAt n) (n : ℤ) :
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

namespace HomComplex

variable {K L}

def Cochain.eqUpTo {n : ℤ} (α β : Cochain K L n) (p₀ : ℤ) : Prop :=
  ∀ (p q : ℤ) (hpq : p + n = q), p ≤ p₀ → α.v p q hpq = β.v p q hpq

end HomComplex

namespace IsKInjectiveOfInjective

lemma step (f : K ⟶ L) (α : Cochain K L (-1)) (n : ℤ) (hK : K.ExactAt (n+1)) [Injective (L.X (n+1))]
    (hα : (δ (-1) 0 α).eqUpTo (Cochain.ofHom f) n) :
    ∃ (h : K.X (n + 2) ⟶ L.X (n+1)),
    (δ (-1) 0 (α + Cochain.single h (-1))).eqUpTo (Cochain.ofHom f) (n + 1) := by
  let u := f.f (n + 1) - α.v (n+1) n (by linarith) ≫ L.d n (n+1) -
    K.d (n+1) (n+2) ≫ α.v (n+2) (n+1) (by linarith)
  have hu : K.d n (n+1) ≫ u = 0 := by
    dsimp
    have eq := hα n n (add_zero n) (by rfl)
    simp only [δ_v (-1) 0 (neg_add_self 1) α n n (add_zero _) (n-1) (n+1) (by linarith) (by linarith),
      neg_add_self, Int.negOnePow_zero, one_smul, Cochain.ofHom_v] at eq
    simp only [comp_sub, HomologicalComplex.d_comp_d_assoc, zero_comp, sub_zero,
      ← f.comm, ← eq, add_comp, assoc, L.d_comp_d, comp_zero, zero_add, sub_self]
  rw [K.exactAt_iff' n (n+1) (n+2) (by simp) (by simp; linarith)] at hK
  obtain ⟨h, hh⟩ : ∃ (h : K.X (n+2) ⟶ L.X (n+1)), K.d (n+1) (n+2) ≫ h = u :=
    ⟨hK.descToInjective _ hu, hK.comp_descToInjective _ _⟩
  refine' ⟨h, _⟩
  intro p q hpq hp
  obtain rfl : p = q := by linarith
  obtain hp | rfl := hp.lt_or_eq
  · rw [Int.lt_add_one_iff] at hp
    rw [δ_add, Cochain.add_v, hα p p (by linarith) (by linarith), add_right_eq_self,
      δ_v (-1) 0 (neg_add_self 1) _ p p hpq (p-1) (p+1) rfl rfl]
    simp only [neg_add_self, Int.negOnePow_zero, one_smul]
    rw [Cochain.single_v_eq_zero _ _ _ _ _ (by linarith),
      Cochain.single_v_eq_zero _ _ _ _ _ (by linarith), zero_comp, comp_zero,
      add_zero]
  · rw [δ_v (-1) 0 (neg_add_self 1) _ (n+1) (n+1) (by linarith) n (n+2) (by linarith) (by linarith)]
    simp only [neg_add_self, Int.negOnePow_zero, one_smul, Cochain.add_v, add_comp,
      comp_add, Cochain.ofHom_v, Cochain.single_v]
    rw [Cochain.single_v_eq_zero _ _ _ _ _ (by linarith)]
    simp only [ComplexShape.up_Rel, not_true, zero_comp, add_zero, Cochain.single_v,
      Cochain.ofHom_v, hh]
    abel

end IsKInjectiveOfInjective

end CochainComplex
