/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered

/-! # κ-Filtered colimits in the category of types.

In this file, we show that in a `κ`-filtered colimit of types (where `κ` is a regular cardinal),
any family of elements of size < κ in the colimit can be lifted to a common stage of the
diagram, and that a κ-small family in the diagram that collapses to the same element in the colimit
can be equalized at some stage of the diagram. -/

@[expose] public section

open CategoryTheory Limits ConcreteCategory

universe w v u

namespace CategoryTheory.Limits.Types.FilteredColimit

variable {J : Type*} [Category* J] (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
  (F : J ⥤ Type u)

open IsFiltered in
variable {F} in
/-- In a κ-filtered diagram of types, any κ-small family of elements in the colimit lifts to
a common stage in the diagram. -/
lemma jointly_surjective_of_isColimit_of_hasCardinalLT
    {t : Cocone F} (ht : IsColimit t) {ι : Type*} (hι : HasCardinalLT ι κ) (x : ι → t.pt) :
    ∃ (j : J) (x' : ι → F.obj j), ∀ (i : ι), t.ι.app j (x' i) = x i := by
  choose j₀ x₀ h₀ using fun i ↦ Types.jointly_surjective_of_isColimit ht (x i)
  exact ⟨IsCardinalFiltered.max j₀ hι, fun i ↦ F.map (IsCardinalFiltered.toMax j₀ hι i) (x₀ i),
    by simpa⟩

variable {F} in
/-- In a κ-filtered diagram of types, if a family of size < κ in the `i`-th stage of the diagram
collapses to the same element in the colimit, then it already does at some stage of the colimit. -/
theorem isColimit_eq_iff'_of_hasCardinal_LT
    {t : Cocone F} (ht : IsColimit t) {ι : Type*} (hι : HasCardinalLT ι κ)
    {i : J} (x : ι → F.obj i) :
    (∀ (k k' : ι), t.ι.app i (x k) = t.ι.app i (x k')) ↔
      ∃ (j : _) (f : i ⟶ j), ∀ (k k' : ι), F.map f (x k) = F.map f (x k') := by
  have := isFiltered_of_isCardinalFiltered J κ
  refine ⟨fun h ↦ ?_, fun ⟨j, f, h⟩ k k' ↦ ?_⟩
  · -- every individual equality is explained at some stage in the diagram by ℵ₀-filteredness
    choose p0 p1 p2 hp12 using fun k k' ↦ (isColimit_eq_iff _ ht).mp (h k k')
    -- we then take a "wide span" of all these stages
    choose p0' g1 g2 hg using fun k k' ↦ IsFiltered.span (p1 k k') (p2 k k')
    let q₁ (k k' : ι) := p1 k k' ≫ g1 k k' ≫ IsFiltered.coeqHom (g1 k k') (g2 k k')
    have hq (k k' : ι) : F.map (q₁ k k') (x k) = F.map (q₁ k k') (x k') := by
      dsimp [q₁]
      simp_rw [Functor.map_comp, comp_apply, hp12 k k', ← comp_apply,
        ← Functor.map_comp, Category.assoc, reassoc_of% hg,
        IsFiltered.coeq_condition (g1 k k') (g2 k k')]
    have : HasCardinalLT ((_ : ι) × ι) κ := by
      rw [hasCardinalLT_iff_of_equiv (Equiv.sigmaEquivProd ι ι)]
      exact hasCardinalLT_prod (Cardinal.IsRegular.aleph0_le Fact.out) hι hι
    obtain ⟨m₀, a₀, b₀, hb₀⟩ := IsCardinalFiltered.wideSpan (Sigma.uncurry q₁) this
    use m₀, b₀
    intro k1 k2
    simp [← hb₀ ⟨k1, k2⟩, Sigma.uncurry, hq k1 k2]
  · simp [← dsimp% t.ι.naturality_apply f (x k), h k k']

variable {F} in
/-- In a κ-filtered diagram of types, if a family of size < κ of elements in the diagram collapses
to the same element in the colimit, then it already does at some stage of the colimit. -/
theorem isColimit_eq_iff''_of_hasCardinal_LT
    {t : Cocone F} (ht : IsColimit t) {ι : Type*} (hι : HasCardinalLT ι κ)
    {φ : ι → J} (x : (i : ι) → F.obj (φ i)) :
    (∀ (k k' : ι), t.ι.app _ (x k) = t.ι.app _ (x k')) ↔
      ∃ (j : _) (f : (i : ι) → (φ i) ⟶ j), ∀ (k k' : ι),
        F.map (f k) (x k) = F.map (f k') (x k') := by
  refine ⟨fun h ↦ ?_, fun ⟨j, f, h⟩ k k' ↦ ?_⟩
  · -- We reduce to the case of isColimit_eq_iff'_of_hasCardinal_LT
    let i₀ := IsCardinalFiltered.max φ hι
    let x₀ (i : ι) : F.obj i₀ := F.map (IsCardinalFiltered.toMax φ hι i) (x i)
    have (k k' : ι) : (t.ι.app i₀) (x₀ k) = (t.ι.app i₀) (x₀ k') := by
      simp [i₀, x₀, h k k']
    obtain ⟨j, f₀, hj⟩ := (isColimit_eq_iff'_of_hasCardinal_LT κ ht hι x₀).mp this
    use j, (IsCardinalFiltered.toMax φ hι · ≫ f₀)
    intro k k'
    dsimp [x₀] at hj
    simp [hj k k']
  · simp [← dsimp% t.ι.naturality_apply (f _) (x k), h k k']

end CategoryTheory.Limits.Types.FilteredColimit
