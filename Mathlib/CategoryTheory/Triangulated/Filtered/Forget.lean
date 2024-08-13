import Mathlib.CategoryTheory.Triangulated.Filtered.TruncationProp
import Mathlib.Data.Int.Interval
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.Grp.Zero

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

namespace Triangulated

variable {C : Type _} [Category C] [HasZeroObject C]  [Preadditive C] [HasShift C (ℤ × ℤ)]
  [∀ p : ℤ × ℤ, Functor.Additive (CategoryTheory.shiftFunctor C p)]
  [hC : Pretriangulated C] [hP : FilteredTriangulated C] [IsTriangulated C]

namespace FilteredTriangulated

/- More on the `Gr` functors.-/

lemma Gr_zero_of_isLE (X : C) (n : ℤ) [IsLE X n] (m : ℤ) (hm : n < m) :
    IsZero ((Gr'' m).obj X) := by
  dsimp [Gr'']
  refine Limits.IsZero.of_iso ?_ (Functor.mapIso _ ((truncLEGEIsoGELE m m).app X).symm)
  dsimp [truncLEGE]
  have : IsZero ((truncGE m).obj X) := by
    have : IsLE X (m - 1) := isLE_of_LE X n (m - 1) (by linarith [hm])
    exact isZero_truncGE_obj_of_isLE (m - 1) m (by linarith) X
  rw [IsZero.iff_id_eq_zero] at this ⊢
  rw [← Functor.map_id, ← Functor.map_id, this, Functor.map_zero, Functor.map_zero]

lemma Gr_zero_of_isGE (X : C) (n : ℤ) [IsGE X n] (m : ℤ) (hm : m < n) :
    IsZero ((Gr'' m).obj X) := by
  dsimp [Gr'', truncGELE]
  have : IsZero ((truncLE m).obj X) := by
    have : IsGE X (m + 1) := isGE_of_GE X (m + 1) n (by linarith [hm])
    exact isZero_truncLE_obj_of_isGE m (m + 1) (by linarith) X
  rw [IsZero.iff_id_eq_zero] at this ⊢
  rw [← Functor.map_id, ← Functor.map_id, this, Functor.map_zero, Functor.map_zero]

lemma isLE_of_isLE_and_Gr_zero (X : C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) [IsLE X n₁]
    (hX : IsZero ((Gr'' n₁).obj X)) : IsLE X n₀ := by
  rw [isLE_iff_isIso_truncLTπ_app n₀ n₁ h]
  have hz : IsZero ((truncGELE n₁ n₁).obj X) := by
    dsimp [Gr''] at hX
    refine Limits.IsZero.of_iso ?_ (@shiftNegShift _ _ _ _ Shift₂
      ((truncGELE n₁ n₁).obj X) n₁).symm
    rw [IsZero.iff_id_eq_zero] at hX ⊢
    rw [← Functor.map_id, hX, Functor.map_zero]
  have hz' : IsZero (((truncGELE n₁ n₁).obj X)⟦(1 : ℤ)⟧) := by
    rw [IsZero.iff_id_eq_zero] at hz ⊢; rw [← Functor.map_id, hz, Functor.map_zero]
  set φ := Triangle.homMk (Triangle.mk (0 : 0 ⟶ X) (CategoryTheory.CategoryStruct.id X) 0)
    ((triangleGELELTLE n₁ n₁ (le_refl _)).obj X) 0 ((truncLEπ n₁).app X)
    ((truncLTπ n₁).app X) (by simp)
    (by simp only [Triangle.mk_obj₂, triangleGELELTLE_obj_obj₃, Triangle.mk_obj₃,
      Triangle.mk_mor₂, id_comp, triangleGELELTLE_obj_obj₂, triangleGELELTLE_obj_mor₂]
        exact (natTransTruncLTOfGE_π_app (n₁ + 1) n₁ (by linarith) X).symm)
    (Limits.IsTerminal.hom_ext (Limits.IsZero.isTerminal hz') _ _)
  refine isIso₃_of_isIso₁₂ φ (contractible_distinguished₁ X) (triangleGELELTLE_distinguished n₁
    n₁ (le_refl _) X) ?_ ((isLE_iff_isIso_truncLEπ_app n₁ X).mp inferInstance)
  exact Limits.isIso_of_isTerminal Limits.HasZeroObject.zeroIsTerminal
    (Limits.IsZero.isTerminal hz) _

lemma isGE_of_isGE_and_Gr_zero (X : C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) [IsGE X n₀]
    (hX : IsZero ((Gr'' n₀).obj X)) : IsGE X n₁ := by
  rw [isGE_iff_isIso_truncGEι_app]
  have hz : IsZero ((truncLTGE n₀ n₁).obj X) := by
    refine IsZero.of_iso ?_ ((truncLTGEIsoGELT n₀ n₁).app X)
    have heq : n₁ = n₀ + 1 := by linarith
    rw [heq]
    dsimp [Gr''] at hX
    refine Limits.IsZero.of_iso ?_ (@shiftNegShift _ _ _ _ Shift₂
      ((truncGELE n₀ n₀).obj X) n₀).symm
    rw [IsZero.iff_id_eq_zero] at hX ⊢
    rw [← Functor.map_id, hX, Functor.map_zero]
  set φ := Triangle.homMk ((triangleGEGELTGE n₀ n₁ (by linarith)).obj X)
    (contractibleTriangle X) ((truncGEι n₁).app X) ((truncGEι n₀).app X) 0 (by simp) (by simp)
    (Limits.IsInitial.hom_ext (Limits.IsZero.isInitial hz) _ _)
  refine isIso₁_of_isIso₂₃ φ (triangleGEGELTGE_distinguished n₀ n₁ (by linarith) X)
    (contractible_distinguished X) ?_ ?_
  exact (isGE_iff_isIso_truncGEι_app n₀ X).mp inferInstance
  exact Limits.isIso_of_isTerminal (Limits.IsZero.isTerminal hz)
    Limits.HasZeroObject.zeroIsTerminal _

variable [∀ (X : C) (n : ℤ), Decidable (IsZero ((Gr'' n).obj X))]

/- Support of an object `X` of `C`. That's the set of integers `n` such that `Gr'' n X` is nonzero,
and it is finite.-/

lemma isLE_of_big_enough (X : C) : ∃ (n : ℤ), IsLE X n := by
  obtain ⟨n, hn⟩ := hP.LE_exhaustive X
  exact ⟨n, {le := hn}⟩

lemma isGE_of_small_enough (X : C) : ∃ (n : ℤ), IsGE X n := by
  obtain ⟨n, hn⟩ := hP.GE_exhaustive X
  exact ⟨n, {ge := hn}⟩

lemma bounded_above (X : C) : ∃ (n : ℤ), ∀ (m : ℤ), n < m → IsZero ((Gr'' m).obj X) := by
  obtain ⟨r, hr⟩ := isLE_of_big_enough X
  existsi r
  intro m hm
  exact Gr_zero_of_isLE X r m hm

lemma bounded_below (X : C) : ∃ (n : ℤ), ∀ (m : ℤ), m < n → IsZero ((Gr'' m).obj X) := by
  obtain ⟨r, hr⟩ := isGE_of_small_enough X
  existsi r
  intro m hm
  exact Gr_zero_of_isGE X r m hm

lemma support_finite (X : C) : Set.Finite {n | ¬ (IsZero ((Gr'' n).obj X))} := by
  suffices sub : ∃ n m, {n | ¬ (IsZero ((Gr'' n).obj X))} ⊆ Set.Icc n m by
    obtain ⟨n, m, h⟩ := sub
    exact Set.Finite.subset (Set.finite_Icc n m) h
  obtain ⟨m, hm⟩ := bounded_above X
  obtain ⟨n, hn⟩ := bounded_below X
  existsi n, m
  intro r
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  contrapose!
  intro hr
  by_cases h : r < n
  · exact hn r h
  · dsimp [Gr'']
    rw [lt_iff_not_le, not_not] at h
    exact hm r (hr h)

noncomputable def support (X : C) := Set.Finite.toFinset (support_finite X)

lemma support_def (X : C) (n : ℤ) : n ∈ support X ↔ ¬ (IsZero ((Gr'' n).obj X)) := by
  simp only [support, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

lemma support_def' (X : C) (n : ℤ) : n ∉ support X ↔ IsZero ((Gr'' n).obj X) := by
  rw [support_def]; simp only [Decidable.not_not]


lemma isZero_iff_Gr_zero (X : C) : IsZero X ↔ ∀ (n : ℤ), IsZero ((Gr'' n).obj X) := sorry

lemma isLE_iff_Gr_zero (X : C) (n : ℤ) :
    IsLE X n ↔ ∀ (m : ℤ), n < m → IsZero ((Gr'' m).obj X) := by
  constructor
  · intro hX m hm
    dsimp [Gr'']
    refine Limits.IsZero.of_iso ?_ (Functor.mapIso _ ((truncLEGEIsoGELE m m).app X).symm)
    dsimp [truncLEGE]
    have : IsZero ((truncGE m).obj X) := by
      have : IsLE X (m - 1) := by
        exact isLE_of_LE X n (m - 1) (by linarith [hm])
      exact isZero_truncGE_obj_of_isLE (m - 1) m (by linarith) X
    rw [IsZero.iff_id_eq_zero] at this ⊢
    rw [← Functor.map_id, ← Functor.map_id, this, Functor.map_zero, Functor.map_zero]
  · sorry


lemma isLE_iff_support_bounded_above (X : C) (n : ℤ) :
    IsLE X n ↔ (support X).toSet ⊆ Set.Iic n := by
  constructor
  · intro hX m
    simp only [Finset.mem_coe, Set.mem_Iic]
    contrapose!
    rw [support_def']
    intro hn
    sorry
  · sorry

lemma isZero_iff_empty_support (X : C) : IsZero X ↔ support X = ∅ := by
  constructor
  · intro h
    ext n
    simp only [Finset.not_mem_empty, iff_false]
    rw [support_def']
    rw [IsZero.iff_id_eq_zero] at h ⊢
    rw [← Functor.map_id, h, Functor.map_zero]
  · sorry

-- TODO : We have IsLE X n iff all elements of the support are  ≤ n, same for IsGE.
-- If the support is {n}, then s^{-n} X is in the core.
-- Support of a truncation, how to make the support smaller.

/- The functor forgetting filtrations on the subcategory of objects `X` such that `IsLE X 0`.-/

lemma existence_omega_aux (X : C) [IsLE X 0] (n : ℕ) : Finset.card (support X) = n →
    ∃ (Y : hP.Core') (s : X ⟶ Y.1),
    ∀ (Z : C), IsGE Z 0 → IsIso ((preadditiveYoneda.obj Z).map (Quiver.Hom.op s)) := by
  refine Nat.le_induction (m := 0) (fun h ↦ ?_) ?_ n (Nat.zero_le n)
  · existsi 0, 0
    intro Z hZ
    have  h₁: IsZero ((preadditiveYoneda.obj Z).obj (Opposite.op (FullSubcategory.obj
        (0 : hP.Core')))) := by
      simp only [preadditiveYoneda_obj, Functor.comp_obj, preadditiveYonedaObj_obj,
        ModuleCat.forget₂_obj]
      refine @AddCommGrp.isZero_of_subsingleton _ (Subsingleton.intro ?_)
      simp only [AddCommGrp.coe_of]
      change ∀ (a b : (FullSubcategory.obj (0 : hP.Core') ⟶ Z)), a = b
      intro f g
      have h₀ : IsZero (FullSubcategory.obj (0 : hP.Core')) := by
        have : IsZero (0 : hP.Core') := isZero_zero _
        rw [IsZero.iff_id_eq_zero] at this ⊢
        exact this
      rw [Limits.IsZero.eq_zero_of_src h₀ f, Limits.IsZero.eq_zero_of_src h₀ g]
    have h₂: IsZero ((preadditiveYoneda.obj Z).obj (Opposite.op X)) := by
      simp only [preadditiveYoneda_obj, Functor.comp_obj, preadditiveYonedaObj_obj,
        ModuleCat.forget₂_obj]
      have h₀ : IsZero X := by
        rw [isZero_iff_empty_support, ← Finset.card_eq_zero]
        exact h
      refine @AddCommGrp.isZero_of_subsingleton _ (Subsingleton.intro ?_)
      simp only [AddCommGrp.coe_of]
      change ∀ (a b : (X ⟶ Z)), a = b
      intro f g
      rw [Limits.IsZero.eq_zero_of_src h₀ f, Limits.IsZero.eq_zero_of_src h₀ g]
    exact Limits.isIso_of_isInitial h₁.isInitial h₂.isInitial _
  · sorry

lemma existence_omega (X : C) [IsLE X 0] : ∃ (Y : hP.Core') (s : X ⟶ Y.1),
    ∀ (Z : C), IsGE Z 0 → Function.Bijective (fun (f : Y.1 ⟶ Z) ↦ s ≫ f) := sorry


end FilteredTriangulated

end Triangulated

end CategoryTheory
