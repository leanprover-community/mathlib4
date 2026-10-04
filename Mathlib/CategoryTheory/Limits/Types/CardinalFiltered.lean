/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered

/-!
# κ-Filtered colimits in the category of types.

In this file, we show that in a `κ`-filtered colimit of types (where κ is a regular cardinal),
any family of elements of size < κ in the colimit can be lifted to a common stage of the
diagram.
-/

@[expose] public section

open CategoryTheory Limits ConcreteCategory

universe v u w

namespace CategoryTheory.Limits.Types.FilteredColimit

variable {J : Type*} [Category* J] (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
  (F : J ⥤ Type u)

attribute [local instance] small_colimitType_of_hasColimit

open IsFiltered in
variable {F} in
lemma jointly_surjective_of_isColimit_of_hasCardinalLT
    {t : Cocone F} (ht : IsColimit t) {ι : Type*} (hι : HasCardinalLT ι κ) (x : ι → t.pt) :
    ∃ (j : J) (x' : ι → F.obj j), ∀ (i : ι), t.ι.app j (x' i) = x i := by
  have (i : ι) := Types.jointly_surjective_of_isColimit ht (x i)
  choose j₀ x₀ h₀ using this
  refine ⟨IsCardinalFiltered.max j₀ hι, fun i ↦ F.map (IsCardinalFiltered.toMax j₀ hι i) (x₀ i),
    by simpa⟩

variable {F} in
theorem isColimit_eq_iff'_of_hasCardinal_LT
    {t : Cocone F} (ht : IsColimit t) {ι : Type*} (hι : HasCardinalLT ι κ)
    {i : J} (x : ι → F.obj i) :
    (∀ (k k' : ι), t.ι.app i (x k) = t.ι.app i (x k')) ↔
      ∃ (j : _) (f : i ⟶ j), ∀ (k k' : ι), F.map f (x k) = F.map f (x k') := by
  have := isFiltered_of_isCardinalFiltered J κ
  refine ⟨fun h ↦ ?_, ?_⟩
  · have (k k' : ι) := (isColimit_eq_iff _ ht).mp (h k k')
    choose p0 p1 p2 hp12 using this
    have (k k' : ι) := IsFiltered.span (p1 k k') (p2 k k')
    choose p0' g1 g2 hg using this
    let u (k k' : ι) := IsFiltered.coeqHom (g1 k k') (g2 k k')
    let q₁ (k k' : ι) := p1 k k' ≫ g1 k k' ≫ IsFiltered.coeqHom (g1 k k') (g2 k k')
    let q₁' := Sigma.uncurry q₁
    have hq (k k' : ι) : F.map (q₁ k k') (x k) = F.map (q₁ k k') (x k') := by
      dsimp [q₁', q₁]
      simp_rw [Functor.map_comp, comp_apply, hp12 k k', ← comp_apply,
        ← Functor.map_comp, Category.assoc, reassoc_of% hg,
        IsFiltered.coeq_condition (g1 k k') (g2 k k')]
    have : HasCardinalLT ((_ : ι) × ι) κ := by
      let e : (_ : ι) × ι ≃ ι × ι := Equiv.sigmaEquivProd ι ι
      rw [hasCardinalLT_iff_of_equiv e]
      exact hasCardinalLT_prod (Cardinal.IsRegular.aleph0_le Fact.out) hι hι
    obtain ⟨m₀, a₀, b₀, hb₀⟩ := IsCardinalFiltered.wideSpan q₁' this
    use m₀, b₀
    intro k1 k2
    conv_lhs => rw [← hb₀ (⟨k1, k2⟩)]
    conv_rhs => rw [← hb₀ (⟨k1, k2⟩)]
    simp [q₁', Sigma.uncurry, hq k1 k2]
  · rintro ⟨j, f, h⟩
    intro k k'
    have := t.ι.naturality_apply f (x k)
    dsimp at this
    simp_rw [← this, h k k']
    simp

end CategoryTheory.Limits.Types.FilteredColimit

