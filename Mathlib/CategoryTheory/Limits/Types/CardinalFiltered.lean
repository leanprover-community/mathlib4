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
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have (k k' : ι) := (isColimit_eq_iff _ ht).mp (h k k')
    choose p0 p1 p2 p3 using this
    let p0' := Function.uncurry p0
    have : HasCardinalLT ((_ : ι) × ι) κ := by
      let e : (_ : ι) × ι ≃ ι × ι := Equiv.sigmaEquivProd ι ι
      rw [hasCardinalLT_iff_of_equiv e]
      exact hasCardinalLT_prod (Cardinal.IsRegular.aleph0_le Fact.out) hι hι
    have : HasCardinalLT (((_ : ι) × ι) ⊕ ((_ : ι) × ι)) κ := sorry
      --have : Prod.equiv := sorry
      -- hasCardinalLT_prod (Cardinal.IsRegular.aleph0_le Fact.out) hι hι
    let p0'' : ((_ : ι) × ι) ⊕ ((_ : ι) × ι) → J := fun x ↦
      Sum.elim (Sigma.uncurry p0) (Sigma.uncurry p0) x
    let q : (p : ((_ : ι) × ι) ⊕ ((_ : ι) × ι)) → (i ⟶ p0'' p) := fun x ↦
      match x with
      | .inl t => p1 t.1 t.2
      | .inr t => p2 t.1 t.2
    #check IsCardinalFiltered.multicoequalizer
    obtain ⟨m₀, a₀, b₀, hb₀⟩ := IsCardinalFiltered.wideSpan q this
    use m₀, b₀
    intro k1 k2
    conv_lhs => rw [← hb₀ (.inl ⟨k1, k2⟩)]
    conv_rhs => rw [← hb₀ (.inr ⟨k1, k2⟩)]
    unfold p0''
    simp [q, p0'', Sigma.uncurry]
    erw? [Functor.map_comp]
    erw? [Functor.map_comp]
    simp [comp_apply, p3 k1 k2]
    simp_rw [comp_apply, Category.assoc, ← Functor.map_comp]
    have := congr($(t.ι.naturality (p2 k1 k2)) (x k2))
    simp_rw [comp_apply] at this

  · rintro ⟨j, f, h⟩
    exact ⟨j, f, f, h⟩

end CategoryTheory.Limits.Types.FilteredColimit

