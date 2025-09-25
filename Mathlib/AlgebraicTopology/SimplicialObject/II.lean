/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# A construction by Gabriel and Zisman

In this file, we construct a cosimplicial object `SimplexCategory.II`
in `SimplexCategoryᵒᵖ`, i.e. a functor `SimplexCategory ⥤ SimplexCategoryᵒᵖ`.
If we identify `SimplexCategory` with the category of finite nonempty
linearly ordered types, this functor could be interpreted as the
contravariant functor which sends a finite nonempty linearly ordered type `T`
to `T →o Fin 2` (with `f ≤ g ↔ ∀ i, g i ≤ f i`, which turns out to
be a linear order); in particular, it sends `Fin (n + 1)` to a linearly
ordered type which is isomorphic to `Fin (n + 2)`. As a result, we define
`SimplexCategory.II` as a functor which sends `⦋n⦌` to `⦋n + 1⦌`: on morphisms,
it sends faces to degeneracies and vice versa. This construction appeared
in *Calculus of fractions and homotopy theory*, chapter III, paragraph 1.1,
by Gabriel and Zisman.

## References

* [P. Gabriel, M. Zisman, *Calculus of fractions and homotopy theory*][gabriel-zisman-1967]

-/

open CategoryTheory Simplicial Opposite

namespace SimplexCategory

namespace II

variable {n m : ℕ}

/-- Auxiliary definition for `map'`. Given `f : Fin (n + 1) →o Fin (m + 1)` and
`x : Fin (m + 2)`, `map' f x` shall be the smallest element in
this `finset f x : Finset (Fin (n + 2))`. -/
def finset (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) : Finset (Fin (n + 2)) :=
  Finset.univ.filter (fun i ↦ i = Fin.last _ ∨
    ∃ (h : i ≠ Fin.last _), x ≤ (f (i.castPred h)).castSucc)

lemma mem_finset_iff (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) (i : Fin (n + 2)) :
    i ∈ finset f x ↔ i = Fin.last _ ∨
      ∃ (h : i ≠ Fin.last _), x ≤ (f (i.castPred h)).castSucc := by
  simp [finset]

@[simp]
lemma last_mem_finset (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) :
    Fin.last _ ∈ finset f x := by
  simp [mem_finset_iff]

@[simp]
lemma castSucc_mem_finset_iff
    (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) (i : Fin (n + 1)) :
    i.castSucc ∈ finset f x ↔ x ≤ (f i).castSucc := by
  simp [mem_finset_iff, Fin.castPred_castSucc]

lemma nonempty_finset (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) :
    (finset f x).Nonempty :=
  ⟨Fin.last _, by simp [mem_finset_iff]⟩

/-- Auxiliary definition for the definition of the action of the
functor `SimplexCategory.II` on morphisms. -/
def map' (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) : Fin (n + 2) :=
  (finset f x).min' (nonempty_finset f x)

lemma map'_eq_last_iff (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) :
    map' f x = Fin.last _ ↔ ∀ (i : Fin (n + 1)), (f i).castSucc < x := by
  simp only [map', Finset.min'_eq_iff, last_mem_finset, Fin.last_le_iff, true_and]
  constructor
  · intro h i
    by_contra!
    exact i.castSucc_ne_last (h i.castSucc (by simpa))
  · intro h i hi
    by_contra!
    obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last this
    simp only [castSucc_mem_finset_iff] at hi
    exact hi.not_gt (h i)

lemma map'_eq_castSucc_iff (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) (y : Fin (n + 1)) :
    map' f x = y.castSucc ↔ x ≤ (f y).castSucc ∧
      ∀ (i : Fin (n + 1)) (_ : i < y), (f i).castSucc < x := by
  simp only [map', Finset.min'_eq_iff, castSucc_mem_finset_iff, and_congr_right_iff]
  intro h
  constructor
  · intro h' i hi
    by_contra!
    exact hi.not_ge (by simpa using h' i.castSucc (by simpa))
  · intro h' i hi
    obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · simp only [Fin.castSucc_le_castSucc_iff]
      by_contra!
      exact (h' i this).not_ge (by simpa using hi)
    · apply Fin.le_last

@[simp]
lemma map'_last (f : Fin (n + 1) →o Fin (m + 1)) :
    map' f (Fin.last _) = Fin.last _ := by
  simp [map'_eq_last_iff]

@[simp]
lemma map'_zero (f : Fin (n + 1) →o Fin (m + 1)) :
    map' f 0 = 0 := by
  simp [← Fin.castSucc_zero, -Fin.castSucc_zero', map'_eq_castSucc_iff]

@[simp]
lemma map'_id (x : Fin (n + 2)) : map' OrderHom.id x = x := by
  obtain ⟨x, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last x
  · rw [map'_eq_castSucc_iff]
    aesop
  · simp

lemma map'_map' {p : ℕ} (f : Fin (n + 1) →o Fin (m + 1))
    (g : Fin (m + 1) →o Fin (p + 1)) (x : Fin (p + 2)) :
    map' f (map' g x) = map' (g.comp f) x := by
  obtain ⟨x, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last x
  · obtain ⟨y, hy⟩ | hx := Fin.eq_castSucc_or_eq_last (map' g x.castSucc)
    · rw [hy]
      rw [map'_eq_castSucc_iff] at hy
      obtain ⟨z, hz⟩ | hz := Fin.eq_castSucc_or_eq_last (map' f y.castSucc)
      · rw [hz, Eq.comm]
        rw [map'_eq_castSucc_iff] at hz ⊢
        constructor
        · refine hy.1.trans ?_
          simp only [OrderHom.comp_coe, Function.comp_apply, Fin.castSucc_le_castSucc_iff]
          exact g.monotone (by simpa using hz.1)
        · intro i hi
          exact hy.2 (f i) (by simpa using hz.2 i hi)
      · rw [hz, Eq.comm]
        rw [map'_eq_last_iff] at hz ⊢
        intro i
        exact hy.2 (f i) (by simpa using hz i)
    · rw [Eq.comm, hx, map'_last]
      rw [map'_eq_last_iff] at hx ⊢
      intro i
      apply hx
  · simp

@[simp]
lemma map'_succAboveOrderEmb {n : ℕ} (i : Fin (n + 2)) (x : Fin (n + 3)) :
    map' i.succAboveOrderEmb.toOrderHom x = i.predAbove x := by
  obtain ⟨x, rfl⟩ | rfl := x.eq_castSucc_or_eq_last
  · by_cases hx : x ≤ i
    · rw [Fin.predAbove_of_le_castSucc _ _ (by simpa), Fin.castPred_castSucc]
      obtain ⟨x, rfl⟩ | rfl := x.eq_castSucc_or_eq_last
      · simp only [map'_eq_castSucc_iff, OrderEmbedding.toOrderHom_coe,
          Fin.succAboveOrderEmb_apply, Fin.castSucc_le_castSucc_iff,
          Fin.castSucc_lt_castSucc_iff]
        constructor
        · obtain hx | rfl := hx.lt_or_eq
          · rwa [Fin.succAbove_of_castSucc_lt]
          · simpa only [Fin.succAbove_castSucc_self] using Fin.castSucc_le_succ x
        · intro j hj
          rwa [Fin.succAbove_of_castSucc_lt _ _ (lt_of_lt_of_le (by simpa) hx),
            Fin.castSucc_lt_castSucc_iff]
      · obtain rfl : i = Fin.last _ := Fin.last_le_iff.1 hx
        simp [map'_eq_last_iff]
    · simp only [not_le] at hx
      obtain ⟨x, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hx)
      rw [Fin.predAbove_of_castSucc_lt _ _ (by simpa [Fin.le_castSucc_iff]),
        Fin.pred_castSucc_succ, map'_eq_castSucc_iff]
      simp only [Fin.succAbove_of_lt_succ _ _ hx,
        OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply,
        le_refl, Fin.castSucc_lt_castSucc_iff, true_and]
      intro j hj
      by_cases h : j.castSucc < i
      · simpa [Fin.succAbove_of_castSucc_lt _ _ h] using hj.le
      · simp only [not_lt] at h
        rwa [Fin.succAbove_of_le_castSucc _ _ h, Fin.succ_lt_succ_iff]
  · simp

@[simp]
lemma map'_predAbove {n : ℕ} (i : Fin (n + 1)) (x : Fin (n + 2)) :
    map' { toFun := i.predAbove, monotone' := Fin.predAbove_right_monotone i } x =
      i.succ.castSucc.succAbove x := by
  obtain ⟨x, rfl⟩ | rfl := x.eq_castSucc_or_eq_last
  · by_cases hi : i.succ ≤ x.castSucc
    · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa), Fin.succ_castSucc, map'_eq_castSucc_iff]
      simp only [OrderHom.coe_mk, Fin.castSucc_le_castSucc_iff, Fin.castSucc_lt_castSucc_iff]
      constructor
      · rw [Fin.succ_le_castSucc_iff] at hi
        rw [Fin.predAbove_of_castSucc_lt _ _
          (by simpa only [Fin.castSucc_lt_succ_iff] using hi.le), Fin.pred_succ]
      · intro j hj
        by_cases h : i.castSucc < j
        · rwa [Fin.predAbove_of_castSucc_lt _ _ h, ← Fin.succ_lt_succ_iff,
            Fin.succ_pred]
        · simp only [not_lt] at h
          rw [Fin.predAbove_of_le_castSucc _ _ h, ← Fin.castSucc_lt_castSucc_iff,
            Fin.castSucc_castPred]
          exact lt_of_le_of_lt h hi
    · simp only [Fin.succ_le_castSucc_iff, not_lt] at hi
      rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa), map'_eq_castSucc_iff]
      simp only [OrderHom.coe_mk, Fin.castSucc_le_castSucc_iff, Fin.castSucc_lt_castSucc_iff]
      constructor
      · simp only [i.predAbove_of_le_castSucc x.castSucc (by simpa),
          Fin.castPred_castSucc, le_refl]
      · intro j hj
        by_cases h : i.castSucc < j
        · rw [Fin.predAbove_of_castSucc_lt _ _ h, ← Fin.succ_lt_succ_iff, Fin.succ_pred]
          exact hj.trans x.castSucc_lt_succ
        · simp only [not_lt] at h
          rwa [Fin.predAbove_of_le_castSucc _ _ h, ← Fin.castSucc_lt_castSucc_iff,
            Fin.castSucc_castPred]
  · simp [map'_last]

lemma monotone_map' (f : Fin (n + 1) →o Fin (m + 1)) :
    Monotone (map' f) := by
  intro x y hxy
  exact Finset.min'_subset _ (fun z hz ↦ by
    obtain ⟨z, rfl⟩ | rfl := z.eq_castSucc_or_eq_last
    · simp only [castSucc_mem_finset_iff] at hz ⊢
      exact hxy.trans hz
    · simp)

end II

/-- The functor `SimplexCategory ⥤ SimplexCategoryᵒᵖ` (i.e. a cosimplicial
object in `SimplexCategoryᵒᵖ`) which sends `⦋n⦌` to the object in `SimplexCategoryᵒᵖ`
that is associated to the linearly ordered type `⦋n + 1⦌` (which could be
identified to the ordered type `⦋n⦌ →o ⦋1⦌`). -/
@[simps obj]
def II : CosimplicialObject SimplexCategoryᵒᵖ where
  obj n := op ⦋n.len + 1⦌
  map f := op (Hom.mk
    { toFun := II.map' f.toOrderHom
      monotone' := II.monotone_map' _ })
  map_id n := Quiver.Hom.unop_inj (by
    ext x : 3
    exact II.map'_id x)
  map_comp {m n p} f g := Quiver.Hom.unop_inj (by
    ext x : 3
    exact (II.map'_map' _ _ _).symm)

@[simp]
lemma II_δ {n : ℕ} (i : Fin (n + 2)) :
    II.δ i = (σ i).op :=
  Quiver.Hom.unop_inj (by ext : 3; apply II.map'_succAboveOrderEmb)

@[simp]
lemma II_σ {n : ℕ} (i : Fin (n + 1)) :
    II.σ i = (δ i.succ.castSucc).op :=
  Quiver.Hom.unop_inj (by ext x : 3; apply II.map'_predAbove)

end SimplexCategory
