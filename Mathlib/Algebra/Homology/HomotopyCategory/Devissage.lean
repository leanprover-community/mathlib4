import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.Algebra.Homology.Embedding.ComplementaryTrunc

open CategoryTheory Limits

noncomputable abbrev CategoryTheory.asIso' {C : Type*} [Category C] {X Y : C} {f : X ⟶ Y}
  (_ : IsIso f) : X ≅ Y := asIso f

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C] [HasZeroObject C]

namespace CochainComplex

open HomologicalComplex in
noncomputable def isoSingle (K : CochainComplex C ℤ) (n : ℤ)
    [K.IsStrictlyGE n] [K.IsStrictlyLE n] :
    K ≅ (singleFunctor C n).obj (K.X n) where
  hom := (toSingleEquiv (K.X n) K (n-1) n (by simp)).symm ⟨𝟙 _, by
    apply (isZero_of_isStrictlyGE _ n _ (by omega)).eq_of_src⟩
  inv := (fromSingleEquiv (K.X n) K n (n + 1) (by simp)).symm ⟨𝟙 _, by
    apply (isZero_of_isStrictlyLE _ n _ (by omega)).eq_of_tgt⟩
  hom_inv_id := by
    ext i
    by_cases h₁ : i ≤ n
    · obtain h₂ | rfl := h₁.lt_or_eq
      · apply (isZero_of_isStrictlyGE _ _ _ h₂).eq_of_src
      · simp [toSingleEquiv, fromSingleEquiv]
    · simp only [not_le] at h₁
      apply (isZero_of_isStrictlyLE _ _ _ h₁).eq_of_src
  inv_hom_id := by
    apply from_single_hom_ext
    simp [toSingleEquiv, fromSingleEquiv]
    rfl

variable {ι : Type*} {c : ComplexShape ι} (e : c.Embedding (ComplexShape.up ℤ))
  [e.IsRelIff]

instance (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyGE n] :
    IsStrictlyGE (K.stupidTrunc e) n := by
  rw [isStrictlyGE_iff]
  intro j hj
  by_cases hj' : ∃ i, e.f i = j
  · obtain ⟨i, hi⟩ := hj'
    exact IsZero.of_iso (K.isZero_of_isStrictlyGE n _ hj) (K.stupidTruncXIso e hi)
  · apply K.isZero_stupidTrunc_X e _ (by simpa using hj')

instance (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyLE n] :
    IsStrictlyLE (K.stupidTrunc e) n := by
  rw [isStrictlyLE_iff]
  intro j hj
  by_cases hj' : ∃ i, e.f i = j
  · obtain ⟨i, hi⟩ := hj'
    exact IsZero.of_iso (K.isZero_of_isStrictlyLE n _ hj) (K.stupidTruncXIso e hi)
  · apply K.isZero_stupidTrunc_X e _ (by simpa using hj')

end CochainComplex

namespace HomotopyCategory

variable (S : Triangulated.Subcategory (HomotopyCategory C (ComplexShape.up ℤ)))
  [ClosedUnderIsomorphisms S.P]

lemma mem_subcategory_of_strictly_bounded (K : CochainComplex C ℤ) (a b : ℤ)
    [ha : K.IsStrictlyGE a] [hb : K.IsStrictlyLE b]
    (hK : ∀ (n : ℤ), a ≤ n → n ≤ b → S.P ((singleFunctor C 0).obj (K.X n))) :
    S.P ((quotient C _).obj K) := by
  by_cases h₀ : a ≤ b; swap
  · simp only [not_le] at h₀
    have hK' : 𝟙 K = 0 := by
      ext n
      apply IsZero.eq_of_src
      by_cases hn : a ≤ n
      · apply K.isZero_of_isStrictlyLE b _ (by omega)
      · simp only [not_le] at hn
        exact K.isZero_of_isStrictlyGE a _ hn
    apply S.mem_of_isZero
    rw [IsZero.iff_id_eq_zero, ← CategoryTheory.Functor.map_id, hK', Functor.map_zero]
  · replace h₀ := Int.eq_add_ofNat_of_le h₀
    obtain ⟨n, hn⟩ := h₀
    revert K hn a b
    induction n with
    | zero =>
        intro K a b _ _ hK ha
        obtain rfl : a = b := by simpa using ha.symm
        exact mem_of_iso S.P (((singleFunctors C).shiftIso (-a) a 0 (neg_add_self a)).app _ ≪≫
          (singleFunctorPostCompQuotientIso C a).app _ ≪≫
          ((quotient _ _).mapIso (K.isoSingle a)).symm) (S.shift _ (-a) (hK a (by rfl) (by rfl)))
    | succ n h =>
        intro K a b _ _ hK hab
        apply S.ext₂ _ (trianglehOfDegreewiseSplit_distinguished _
          (K.shortComplexStupidTruncSplitting
            (ComplexShape.Embedding.embeddingUpInt_areComplementary (a + n) b (by omega))))
        · dsimp
          refine @h _ (a + 1) b (CochainComplex.isStrictlyGE_of_GE _ _ b (by omega))
            inferInstance (fun m h₁ h₂ => ?_) (by omega)
          dsimp
          obtain h₃ | rfl := h₂.lt_or_eq
          · apply S.mem_of_isZero
            apply Functor.map_isZero
            exact CochainComplex.isZero_of_isStrictlyGE _ b _ h₃
          · obtain ⟨k, hk⟩ := Int.eq_add_ofNat_of_le h₂
            refine' mem_of_iso _ ((singleFunctor C 0).mapIso
              ((asIso' (K.isIso_ιStupidTrunc_f (ComplexShape.embeddingUpIntGE m) (i := k)
                  (by dsimp; omega))).symm))
                (hK m (by omega) h₂)
        · dsimp
          refine' @h _ a (a + n) inferInstance inferInstance (fun m h₁ h₂ => ?_) rfl
          obtain ⟨k, hk⟩ := Int.eq_add_ofNat_of_le h₂
          exact mem_of_iso _ ((singleFunctor C 0).mapIso
            (asIso' (K.isIso_πStupidTrunc_f (ComplexShape.embeddingUpIntLE (a + n)) (i := k)
            (by dsimp; omega)))) (hK m h₁ (by omega))

end HomotopyCategory
