import Mathlib.Algebra.Homology.DerivedCategory.Basic

open CategoryTheory Category Limits Pretriangulated Limits

variable {C : Type _} [Category C] [Abelian C]

namespace CochainComplex

open HomologicalComplex

variable (K L : CochainComplex C ℤ) (e : K ≅ L) (n : ℤ)

class IsStrictlyLE : Prop where
  isZero (i : ℤ) (hi : n < i) : IsZero (K.X i)

lemma isZero_of_isStrictlyLE (n i : ℤ) (hi : n < i) [K.IsStrictlyLE n] :
    IsZero (K.X i) := IsStrictlyLE.isZero i hi

class IsStrictlyGE : Prop where
  isZero (i : ℤ) (hi : i < n) : IsZero (K.X i)

lemma isZero_of_isStrictlyGE (i : ℤ) (hi : i < n) [K.IsStrictlyGE n] :
    IsZero (K.X i) := IsStrictlyGE.isZero i hi

class IsLE : Prop where
  isZero (i : ℤ) (hi : n < i) : IsZero (K.homology i)

lemma isZero_of_isLE (i : ℤ) (hi : n < i) [K.IsLE n] :
    IsZero (K.homology i) := IsLE.isZero i hi

class IsGE : Prop where
  isZero (i : ℤ) (hi : i < n) : IsZero (K.homology i)

lemma isZero_of_isGE (i : ℤ) (hi : i < n) [K.IsGE n] :
    IsZero (K.homology i) := IsGE.isZero i hi

instance (K : CochainComplex C ℤ) [K.IsStrictlyLE n] : K.IsLE n := ⟨fun i hi =>
  K.isZero_homology_of_isZero _ (K.isZero_of_isStrictlyLE n i hi)⟩

instance (K : CochainComplex C ℤ) [K.IsStrictlyGE n] : K.IsGE n := ⟨fun i hi =>
  K.isZero_homology_of_isZero _ (K.isZero_of_isStrictlyGE n i hi)⟩

lemma isStrictLE_of_LE (p q : ℤ) (hpq : p ≤ q) [K.IsStrictlyLE p] :
  K.IsStrictlyLE q := ⟨fun i hi => K.isZero_of_isStrictlyLE p i (by linarith)⟩

lemma isStrictLE_of_GE (p q : ℤ) (hpq : p ≤ q) [K.IsStrictlyGE q] :
  K.IsStrictlyGE p := ⟨fun i hi => K.isZero_of_isStrictlyGE q i (by linarith)⟩

lemma isLE_of_LE (p q : ℤ) (hpq : p ≤ q) [K.IsLE p] :
  K.IsLE q := ⟨fun i hi => K.isZero_of_isLE p i (by linarith)⟩

lemma isGE_of_GE (p q : ℤ) (hpq : p ≤ q) [K.IsGE q] :
  K.IsGE p := ⟨fun i hi => K.isZero_of_isGE q i (by linarith)⟩

variable {K L}

lemma isStrictlyLE_of_iso [K.IsStrictlyLE n] : L.IsStrictlyLE n := ⟨fun i hi =>
  IsZero.of_iso (K.isZero_of_isStrictlyLE n i hi)
    ((eval _ _ i).mapIso e.symm)⟩

lemma isStrictlyGE_of_iso [K.IsStrictlyGE n] : L.IsStrictlyGE n := ⟨fun i hi =>
  IsZero.of_iso (K.isZero_of_isStrictlyGE n i hi)
    ((eval _ _ i).mapIso e.symm)⟩

lemma isLE_of_iso [K.IsLE n] : L.IsLE n := ⟨fun i hi =>
  IsZero.of_iso (K.isZero_of_isLE n i hi)
    ((homologyFunctor _ _ i).mapIso e.symm)⟩

lemma isGE_of_iso [K.IsGE n] : L.IsGE n := ⟨fun i hi =>
  IsZero.of_iso (K.isZero_of_isGE n i hi)
    ((homologyFunctor _ _ i).mapIso e.symm)⟩

variable (K)

lemma isStrictlyLE_shift [K.IsStrictlyLE n] (a n' : ℤ) (h : a + n' = n) :
    (K⟦a⟧).IsStrictlyLE n' := ⟨fun i hi =>
  IsZero.of_iso (K.isZero_of_isStrictlyLE n _ (by linarith)) (K.shiftFunctorObjXIso a i _ rfl)⟩

lemma isStrictlyGE_shift [K.IsStrictlyGE n] (a n' : ℤ) (h : a + n' = n) :
    (K⟦a⟧).IsStrictlyGE n' := ⟨fun i hi =>
  IsZero.of_iso (K.isZero_of_isStrictlyGE n _ (by linarith)) (K.shiftFunctorObjXIso a i _ rfl)⟩

lemma isLE_shift [K.IsLE n] (a n' : ℤ) (h : a + n' = n) : (K⟦a⟧).IsLE n' := ⟨fun i hi =>
  IsZero.of_iso (K.isZero_of_isLE n (a+i) (by linarith))
    (((homologyFunctor C _ (0 : ℤ)).shiftIso a i _ rfl).app K)⟩

lemma isGE_shift [K.IsGE n] (a n' : ℤ) (h : a + n' = n) : (K⟦a⟧).IsGE n' := ⟨fun i hi =>
  IsZero.of_iso (K.isZero_of_isGE n (a+i) (by linarith))
    (((homologyFunctor C _ (0 : ℤ)).shiftIso a i _ rfl).app K)⟩

lemma exists_iso_single (n : ℤ) [K.IsStrictlyGE n] [K.IsStrictlyLE n] :
    ∃ (M : C), Nonempty (K ≅ (single _ _ n).obj M) := by
  refine' ⟨K.X n, ⟨_⟩⟩
  refine' HomologicalComplex.Hom.isoOfComponents _ _
  . intro i
    by_cases i = n
    . subst h
      exact (singleObjXSelf _ _ _ _).symm
    . refine' IsZero.isoZero _ ≪≫ (IsZero.isoZero _).symm
      . by_cases hi' : i ≤ n
        . refine' K.isZero_of_isStrictlyGE n i _
          cases hi'.lt_or_eq <;> tauto
        . exact K.isZero_of_isStrictlyLE n i (by linarith)
      . dsimp
        rw [if_neg h]
        exact isZero_zero _
  . intro i j (hij : i + 1 = j)
    simp only [single_obj_d, comp_zero]
    by_cases i < n
    . apply (K.isZero_of_isStrictlyGE n i h).eq_of_src
    . apply IsZero.eq_of_tgt
      dsimp
      rw [if_neg]
      . exact isZero_zero _
      . linarith

instance (A : C) (n : ℤ) :
    IsStrictlyLE ((single C (ComplexShape.up ℤ) n).obj A) n := ⟨fun i hi => by
    dsimp
    rw [if_neg (by linarith)]
    exact isZero_zero _⟩

instance (A : C) (n : ℤ) :
    IsStrictlyLE ((singleFunctor C n).obj A) n :=
  (inferInstance : IsStrictlyLE ((single C (ComplexShape.up ℤ) n).obj A) n)

instance (A : C) (n : ℤ) :
    IsStrictlyGE ((single C (ComplexShape.up ℤ) n).obj A) n := ⟨fun i hi => by
    dsimp
    rw [if_neg (by linarith)]
    exact isZero_zero _⟩

instance (A : C) (n : ℤ) :
    IsStrictlyGE ((singleFunctor C n).obj A) n :=
  (inferInstance : IsStrictlyGE ((single C (ComplexShape.up ℤ) n).obj A) n)

end CochainComplex

namespace DerivedCategory

variable [HasDerivedCategory C]
variable (K L : DerivedCategory C) (e : K ≅ L) (n : ℤ)

class IsLE : Prop where
  isZero (i : ℤ) (hi : n < i) : IsZero ((homologyFunctor _ i).obj K)

lemma isZero_of_isLE (i : ℤ) (hi : n < i) [K.IsLE n] :
    IsZero ((homologyFunctor _ i).obj K) := IsLE.isZero i hi

class IsGE : Prop where
  isZero (i : ℤ) (hi : i < n) : IsZero ((homologyFunctor _ i).obj K)

lemma isZero_of_isGE (i : ℤ) (hi : i < n) [K.IsGE n] :
    IsZero ((homologyFunctor _ i).obj K) := IsGE.isZero i hi

instance (K : CochainComplex C ℤ) (n : ℤ) [K.IsLE n] :
    (Q.obj K).IsLE n :=
  ⟨fun i hi => IsZero.of_iso (K.isZero_of_isLE n i hi) ((homologyFunctorFactors C i).app K)⟩

instance (K : CochainComplex C ℤ) (n : ℤ) [K.IsGE n] :
    (Q.obj K).IsGE n :=
  ⟨fun i hi => IsZero.of_iso (K.isZero_of_isGE n i hi) ((homologyFunctorFactors C i).app K)⟩

lemma isLE_Q_obj_iff (K : CochainComplex C ℤ) (n : ℤ) :
    (Q.obj K).IsLE n ↔ K.IsLE n := by
  constructor
  . intro
    exact ⟨fun i hi => IsZero.of_iso (isZero_of_isLE _ n i hi)
      ((homologyFunctorFactors C i).app K).symm⟩
  . intro
    infer_instance

lemma isGE_Q_obj_iff (K : CochainComplex C ℤ) (n : ℤ) :
    (Q.obj K).IsGE n ↔ K.IsGE n := by
  constructor
  . intro
    exact ⟨fun i hi => IsZero.of_iso (isZero_of_isGE _ n i hi)
      ((homologyFunctorFactors C i).app K).symm⟩
  . intro
    infer_instance

lemma isLE_shift [K.IsLE n] (a n' : ℤ) (h : a + n' = n) : (K⟦a⟧).IsLE n' := ⟨fun i hi =>
  IsZero.of_iso (K.isZero_of_isLE n (a+i) (by linarith))
    (((homologyFunctor C (0 : ℤ)).shiftIso a i _ rfl).app K)⟩

lemma isGE_shift [K.IsGE n] (a n' : ℤ) (h : a + n' = n) : (K⟦a⟧).IsGE n' := ⟨fun i hi =>
  IsZero.of_iso (K.isZero_of_isGE n (a+i) (by linarith))
    (((homologyFunctor C (0 : ℤ)).shiftIso a i _ rfl).app K)⟩

lemma isLE_of_LE (p q : ℤ) (hpq : p ≤ q) [K.IsLE p] :
  K.IsLE q := ⟨fun i hi => K.isZero_of_isLE p i (by linarith)⟩

lemma isGE_of_GE (p q : ℤ) (hpq : p ≤ q) [K.IsGE q] :
  K.IsGE p := ⟨fun i hi => K.isZero_of_isGE q i (by linarith)⟩

variable {K L}

lemma isLE_of_iso [K.IsLE n] : L.IsLE n := ⟨fun i hi =>
  IsZero.of_iso (K.isZero_of_isLE n i hi)
    ((homologyFunctor _ i).mapIso e.symm)⟩

lemma isGE_of_iso [K.IsGE n] : L.IsGE n := ⟨fun i hi =>
  IsZero.of_iso (K.isZero_of_isGE n i hi)
    ((homologyFunctor _ i).mapIso e.symm)⟩

lemma distTriang₃_isGE_iff (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    T.obj₃.IsGE n₁ ↔ (∀ (i : ℤ) (_ : i ≤ n₀), IsIso ((homologyFunctor C i).map T.mor₁)) ∧
      (Mono ((homologyFunctor C n₁).map T.mor₁)) := by
  simp only [HomologySequence.mono_homologyMap_mor₁_iff _ hT n₀ n₁ h]
  constructor
  . simp only [fun (i : ℤ) =>
      HomologySequence.isIso_homologyMap_mor₁_iff _ hT (i-1) i (by linarith)]
    intro H
    constructor
    . intro i hi
      constructor
      . apply IsZero.eq_of_src
        exact T.obj₃.isZero_of_isGE n₁ _ (by linarith)
      . apply IsZero.eq_of_tgt
        exact T.obj₃.isZero_of_isGE n₁ _ (by linarith)
    . apply IsZero.eq_of_src
      exact T.obj₃.isZero_of_isGE n₁ n₀ (by linarith)
  . subst h
    intro ⟨h₀, h₁⟩
    constructor
    intro i hi
    apply (HomologySequence.exact₃ _ hT i (i+1) rfl).isZero_of_both_zeros
    . dsimp
      have h' := h₀ i (by linarith)
      rw [HomologySequence.isIso_homologyMap_mor₁_iff _ hT (i-1) i (by linarith)] at h'
      exact h'.2
    . dsimp
      by_cases i < n₀
      . have h' := h₀ (i+1) (by linarith)
        rw [HomologySequence.isIso_homologyMap_mor₁_iff _ hT i (i+1) (by linarith)] at h'
        exact h'.1
      . obtain rfl : n₀ = i := by linarith
        exact h₁

instance (A : C) (n : ℤ) : IsLE ((singleFunctor C n).obj A) n := by
  have e : (singleFunctor C n).obj A ≅ Q.obj ((CochainComplex.singleFunctor C n).obj A) :=
    ((SingleFunctors.evaluation _ _ n).mapIso (singleFunctorsPostCompQIso C)).app A
  exact isLE_of_iso e.symm n

instance (A : C) (n : ℤ) : IsGE ((singleFunctor C n).obj A) n := by
  have e : (singleFunctor C n).obj A ≅ Q.obj ((CochainComplex.singleFunctor C n).obj A) :=
    ((SingleFunctors.evaluation _ _ n).mapIso (singleFunctorsPostCompQIso C)).app A
  exact isGE_of_iso e.symm n

end DerivedCategory
