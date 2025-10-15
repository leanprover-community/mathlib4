import Mathlib

open NumberField CyclotomicField IsCyclotomicExtension



def Polynomial.isSplittingField_C {K : Type*} [Field K] (a : K) :
    Polynomial.IsSplittingField K K (.C a) where
  splits' := by simp
  adjoin_rootSet' := by simp only [rootSet_C, Algebra.adjoin_empty, Module.finrank_self,
    Subalgebra.bot_eq_top_of_finrank_eq_one]
#find_home Polynomial.isSplittingField_C


instance : IsTotallyReal (CyclotomicField 0 ℚ) :=
  IsTotallyReal.ofRingEquiv
    (Polynomial.IsSplittingField.algEquiv ℚ (Polynomial.cyclotomic 0 ℚ)).toRingEquiv

@[simp]
theorem isTotallyReal_top_iff_top_iff {K : Type*} [Field K] [NumberField K] :
    IsTotallyReal (⊤ : Subfield K) ↔ IsTotallyReal K :=
  ⟨fun _ ↦ .ofRingEquiv Subfield.topEquiv, fun _ ↦ .ofRingEquiv Subfield.topEquiv.symm⟩


theorem isTotallyReal_iff_maximalRealSubfield_eq_top {K : Type*} [Field K] [NumberField K] :
    maximalRealSubfield K = ⊤ ↔ IsTotallyReal K  :=
  ⟨fun h ↦ by rw [←isTotallyReal_top_iff_top_iff, isTotallyReal_iff_le_maximalRealSubfield, h],
    fun _ ↦ le_antisymm le_top <| NumberField.IsTotallyReal.le_maximalRealSubfield _⟩

@[simp]
theorem maximalRealSubfield_cyclotomoticField_zero_rat :
    maximalRealSubfield (CyclotomicField 0 ℚ) = ⊤ := by
  rw [isTotallyReal_iff_maximalRealSubfield_eq_top]
  infer_instance


instance (n : ℕ) : NumberField (maximalRealSubfield (CyclotomicField n ℚ)) := by
  infer_instance
