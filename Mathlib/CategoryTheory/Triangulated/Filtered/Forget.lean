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

variable [∀ (X : C) (n : ℤ), Decidable (IsZero ((Gr'' n).obj X))]

/- Support of an object `X` of `C`. That's the set of integers `n` such that `Gr'' n X` is nonzero,
and it is finite.-/

lemma isLE_of_big_enough (X : C) : ∃ (n : ℤ), IsLE X n := by
  obtain ⟨n, hn⟩ := hP.LE_exhaustive X
  exact ⟨n, {le := hn}⟩

lemma isGE_of_small_enough (X : C) : ∃ (n : ℤ), IsGE X n := by
  obtain ⟨n, hn⟩ := hP.GE_exhaustive X
  exact ⟨n, {ge := hn}⟩

lemma bounded_above (X : C) : ∃ (n : ℤ), ∀ (m : ℤ), n < m → IsZero ((truncGE m).obj X) := by
  obtain ⟨r, hr⟩ := isLE_of_big_enough X
  existsi r
  intro m hm
  have : IsLE X (m - 1) := by
    apply isLE_of_LE X r
    linarith [hm]
  apply isZero_truncGE_obj_of_isLE (m - 1) m (by linarith)

lemma bounded_below (X : C) : ∃ (n : ℤ), ∀ (m : ℤ), m < n → IsZero ((truncLE m).obj X) := by
  obtain ⟨r, hr⟩ := isGE_of_small_enough X
  existsi r
  intro m hm
  have : IsGE X (m + 1) := by
    apply isGE_of_GE X (m + 1) r
    linarith [hm]
  apply isZero_truncLE_obj_of_isGE m (m + 1) rfl

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
  · dsimp [Gr'', truncGELE]
    have := hn r h
    rw [IsZero.iff_id_eq_zero] at this ⊢
    rw [← Functor.map_id, ← Functor.map_id, this, Functor.map_zero, Functor.map_zero]
  · dsimp [Gr'']
    refine Limits.IsZero.of_iso ?_ (Functor.mapIso _ ((truncLEGEIsoGELE r r).app X).symm)
    dsimp [truncLEGE]
    rw [lt_iff_not_le, not_not] at h
    have := hm r (hr h)
    rw [IsZero.iff_id_eq_zero] at this ⊢
    rw [← Functor.map_id, ← Functor.map_id, this, Functor.map_zero, Functor.map_zero]

noncomputable def support (X : C) := Set.Finite.toFinset (support_finite X)

lemma support_def (X : C) (n : ℤ) : n ∈ support X ↔ ¬ (IsZero ((Gr'' n).obj X)) := by
  simp only [support, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

lemma support_def' (X : C) (n : ℤ) : n ∉ support X ↔ IsZero ((Gr'' n).obj X) := by
  rw [support_def]; simp only [Decidable.not_not]

lemma isZero_iff_empty_support (X : C) : IsZero X ↔ support X = ∅ := by
  constructor
  · intro h
    ext n
    simp only [Finset.not_mem_empty, iff_false]
    rw [support_def']
    rw [IsZero.iff_id_eq_zero] at h ⊢
    rw [← Functor.map_id, h, Functor.map_zero]
  · sorry

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
