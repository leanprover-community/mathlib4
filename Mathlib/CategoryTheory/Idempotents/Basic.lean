/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.Basic

#align_import category_theory.idempotents.basic from "leanprover-community/mathlib"@"3a061790136d13594ec10c7c90d202335ac5d854"

/-!
# Idempotent complete categories

In this file, we define the notion of idempotent complete categories
(also known as Karoubian categories, or pseudoabelian in the case of
preadditive categories).

## Main definitions

- `IsIdempotentComplete C` expresses that `C` is idempotent complete, i.e.
all idempotents in `C` split. Other characterisations of idempotent completeness are given
by `isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent` and
`isIdempotentComplete_iff_idempotents_have_kernels`.
- `isIdempotentComplete_of_abelian` expresses that abelian categories are
idempotent complete.
- `isIdempotentComplete_iff_ofEquivalence` expresses that if two categories `C` and `D`
are equivalent, then `C` is idempotent complete iff `D` is.
- `isIdempotentComplete_iff_opposite` expresses that `Cᵒᵖ` is idempotent complete
iff `C` is.

## References
* [Stacks: Karoubian categories] https://stacks.math.columbia.edu/tag/09SF

-/


open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Limits

open CategoryTheory.Preadditive

open Opposite

namespace CategoryTheory

variable (C : Type*) [Category C]

/-- A category is idempotent complete iff all idempotent endomorphisms `p`
split as a composition `p = e ≫ i` with `i ≫ e = 𝟙 _` -/
class IsIdempotentComplete : Prop where
  /-- A category is idempotent complete iff all idempotent endomorphisms `p`
    split as a composition `p = e ≫ i` with `i ≫ e = 𝟙 _` -/
  idempotents_split :
    ∀ (X : C) (p : X ⟶ X), p ≫ p = p → ∃ (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p
#align category_theory.is_idempotent_complete CategoryTheory.IsIdempotentComplete

namespace Idempotents

/-- A category is idempotent complete iff for all idempotent endomorphisms,
the equalizer of the identity and this idempotent exists. -/
theorem isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent :
    IsIdempotentComplete C ↔ ∀ (X : C) (p : X ⟶ X), p ≫ p = p → HasEqualizer (𝟙 X) p := by
  constructor
  -- ⊢ IsIdempotentComplete C → ∀ (X : C) (p : X ⟶ X), p ≫ p = p → HasEqualizer (𝟙  …
  · intro
    -- ⊢ ∀ (X : C) (p : X ⟶ X), p ≫ p = p → HasEqualizer (𝟙 X) p
    intro X p hp
    -- ⊢ HasEqualizer (𝟙 X) p
    rcases IsIdempotentComplete.idempotents_split X p hp with ⟨Y, i, e, ⟨h₁, h₂⟩⟩
    -- ⊢ HasEqualizer (𝟙 X) p
    exact
      ⟨Nonempty.intro
          { cone := Fork.ofι i (show i ≫ 𝟙 X = i ≫ p by rw [comp_id, ← h₂, ← assoc, h₁, id_comp])
            isLimit := by
              apply Fork.IsLimit.mk'
              intro s
              refine' ⟨s.ι ≫ e, _⟩
              constructor
              · erw [assoc, h₂, ← Limits.Fork.condition s, comp_id]
              · intro m hm
                rw [Fork.ι_ofι] at hm
                rw [← hm]
                simp only [← hm, assoc, h₁]
                exact (comp_id m).symm }⟩
  · intro h
    -- ⊢ IsIdempotentComplete C
    refine' ⟨_⟩
    -- ⊢ ∀ (X : C) (p : X ⟶ X), p ≫ p = p → ∃ Y i e, i ≫ e = 𝟙 Y ∧ e ≫ i = p
    intro X p hp
    -- ⊢ ∃ Y i e, i ≫ e = 𝟙 Y ∧ e ≫ i = p
    haveI : HasEqualizer (𝟙 X) p := h X p hp
    -- ⊢ ∃ Y i e, i ≫ e = 𝟙 Y ∧ e ≫ i = p
    refine' ⟨equalizer (𝟙 X) p, equalizer.ι (𝟙 X) p,
      equalizer.lift p (show p ≫ 𝟙 X = p ≫ p by rw [hp, comp_id]), _, equalizer.lift_ι _ _⟩
    ext
    -- ⊢ (equalizer.ι (𝟙 X) p ≫ equalizer.lift p (_ : p ≫ 𝟙 X = p ≫ p)) ≫ equalizer.ι …
    simp only [assoc, limit.lift_π, Eq.ndrec, id_eq, eq_mpr_eq_cast, Fork.ofι_pt,
      Fork.ofι_π_app, id_comp]
    rw [← equalizer.condition, comp_id]
    -- 🎉 no goals
#align category_theory.idempotents.is_idempotent_complete_iff_has_equalizer_of_id_and_idempotent CategoryTheory.Idempotents.isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent

variable {C}

/-- In a preadditive category, when `p : X ⟶ X` is idempotent,
then `𝟙 X - p` is also idempotent. -/
theorem idem_of_id_sub_idem [Preadditive C] {X : C} (p : X ⟶ X) (hp : p ≫ p = p) :
    (𝟙 _ - p) ≫ (𝟙 _ - p) = 𝟙 _ - p := by
  simp only [comp_sub, sub_comp, id_comp, comp_id, hp, sub_self, sub_zero]
  -- 🎉 no goals
#align category_theory.idempotents.idem_of_id_sub_idem CategoryTheory.Idempotents.idem_of_id_sub_idem

variable (C)

/-- A preadditive category is pseudoabelian iff all idempotent endomorphisms have a kernel. -/
theorem isIdempotentComplete_iff_idempotents_have_kernels [Preadditive C] :
    IsIdempotentComplete C ↔ ∀ (X : C) (p : X ⟶ X), p ≫ p = p → HasKernel p := by
  rw [isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent]
  -- ⊢ (∀ (X : C) (p : X ⟶ X), p ≫ p = p → HasEqualizer (𝟙 X) p) ↔ ∀ (X : C) (p : X …
  constructor
  -- ⊢ (∀ (X : C) (p : X ⟶ X), p ≫ p = p → HasEqualizer (𝟙 X) p) → ∀ (X : C) (p : X …
  · intro h X p hp
    -- ⊢ HasKernel p
    haveI : HasEqualizer (𝟙 X) (𝟙 X - p) := h X (𝟙 _ - p) (idem_of_id_sub_idem p hp)
    -- ⊢ HasKernel p
    convert hasKernel_of_hasEqualizer (𝟙 X) (𝟙 X - p)
    -- ⊢ p = 𝟙 X - (𝟙 X - p)
    rw [sub_sub_cancel]
    -- 🎉 no goals
  · intro h X p hp
    -- ⊢ HasEqualizer (𝟙 X) p
    haveI : HasKernel (𝟙 _ - p) := h X (𝟙 _ - p) (idem_of_id_sub_idem p hp)
    -- ⊢ HasEqualizer (𝟙 X) p
    apply Preadditive.hasEqualizer_of_hasKernel
    -- 🎉 no goals
#align category_theory.idempotents.is_idempotent_complete_iff_idempotents_have_kernels CategoryTheory.Idempotents.isIdempotentComplete_iff_idempotents_have_kernels

/-- An abelian category is idempotent complete. -/
instance (priority := 100) isIdempotentComplete_of_abelian (D : Type*) [Category D] [Abelian D] :
    IsIdempotentComplete D := by
  rw [isIdempotentComplete_iff_idempotents_have_kernels]
  -- ⊢ ∀ (X : D) (p : X ⟶ X), p ≫ p = p → HasKernel p
  intros
  -- ⊢ HasKernel p✝
  infer_instance
  -- 🎉 no goals
#align category_theory.idempotents.is_idempotent_complete_of_abelian CategoryTheory.Idempotents.isIdempotentComplete_of_abelian

variable {C}

theorem split_imp_of_iso {X X' : C} (φ : X ≅ X') (p : X ⟶ X) (p' : X' ⟶ X')
    (hpp' : p ≫ φ.hom = φ.hom ≫ p')
    (h : ∃ (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p) :
    ∃ (Y' : C) (i' : Y' ⟶ X') (e' : X' ⟶ Y'), i' ≫ e' = 𝟙 Y' ∧ e' ≫ i' = p' := by
  rcases h with ⟨Y, i, e, ⟨h₁, h₂⟩⟩
  -- ⊢ ∃ Y' i' e', i' ≫ e' = 𝟙 Y' ∧ e' ≫ i' = p'
  use Y, i ≫ φ.hom, φ.inv ≫ e
  -- ⊢ (i ≫ φ.hom) ≫ φ.inv ≫ e = 𝟙 Y ∧ (φ.inv ≫ e) ≫ i ≫ φ.hom = p'
  constructor
  -- ⊢ (i ≫ φ.hom) ≫ φ.inv ≫ e = 𝟙 Y
  · slice_lhs 2 3 => rw [φ.hom_inv_id]
    -- ⊢ i ≫ 𝟙 X ≫ e = 𝟙 Y
    rw [id_comp, h₁]
    -- 🎉 no goals
  · slice_lhs 2 3 => rw [h₂]
    -- ⊢ φ.inv ≫ p ≫ φ.hom = p'
    rw [hpp', ← assoc, φ.inv_hom_id, id_comp]
    -- 🎉 no goals
#align category_theory.idempotents.split_imp_of_iso CategoryTheory.Idempotents.split_imp_of_iso

theorem split_iff_of_iso {X X' : C} (φ : X ≅ X') (p : X ⟶ X) (p' : X' ⟶ X')
    (hpp' : p ≫ φ.hom = φ.hom ≫ p') :
    (∃ (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p) ↔
      ∃ (Y' : C) (i' : Y' ⟶ X') (e' : X' ⟶ Y'), i' ≫ e' = 𝟙 Y' ∧ e' ≫ i' = p' := by
  constructor
  -- ⊢ (∃ Y i e, i ≫ e = 𝟙 Y ∧ e ≫ i = p) → ∃ Y' i' e', i' ≫ e' = 𝟙 Y' ∧ e' ≫ i' = p'
  · exact split_imp_of_iso φ p p' hpp'
    -- 🎉 no goals
  · apply split_imp_of_iso φ.symm p' p
    -- ⊢ p' ≫ φ.symm.hom = φ.symm.hom ≫ p
    rw [← comp_id p, ← φ.hom_inv_id]
    -- ⊢ p' ≫ φ.symm.hom = φ.symm.hom ≫ p ≫ φ.hom ≫ φ.inv
    slice_rhs 2 3 => rw [hpp']
    -- ⊢ p' ≫ φ.symm.hom = φ.symm.hom ≫ (φ.hom ≫ p') ≫ φ.inv
    slice_rhs 1 2 => erw [φ.inv_hom_id]
    -- ⊢ p' ≫ φ.symm.hom = (𝟙 X' ≫ p') ≫ φ.inv
    simp only [id_comp]
    -- ⊢ p' ≫ φ.symm.hom = p' ≫ φ.inv
    rfl
    -- 🎉 no goals
#align category_theory.idempotents.split_iff_of_iso CategoryTheory.Idempotents.split_iff_of_iso

theorem Equivalence.isIdempotentComplete {D : Type*} [Category D] (ε : C ≌ D)
    (h : IsIdempotentComplete C) : IsIdempotentComplete D := by
  refine' ⟨_⟩
  -- ⊢ ∀ (X : D) (p : X ⟶ X), p ≫ p = p → ∃ Y i e, i ≫ e = 𝟙 Y ∧ e ≫ i = p
  intro X' p hp
  -- ⊢ ∃ Y i e, i ≫ e = 𝟙 Y ∧ e ≫ i = p
  let φ := ε.counitIso.symm.app X'
  -- ⊢ ∃ Y i e, i ≫ e = 𝟙 Y ∧ e ≫ i = p
  erw [split_iff_of_iso φ p (φ.inv ≫ p ≫ φ.hom)
      (by
        slice_rhs 1 2 => rw [φ.hom_inv_id]
        rw [id_comp])]
  rcases IsIdempotentComplete.idempotents_split (ε.inverse.obj X') (ε.inverse.map p)
      (by rw [← ε.inverse.map_comp, hp]) with
    ⟨Y, i, e, ⟨h₁, h₂⟩⟩
  use ε.functor.obj Y, ε.functor.map i, ε.functor.map e
  -- ⊢ ε.functor.map i ≫ ε.functor.map e = 𝟙 (ε.functor.obj Y) ∧ ε.functor.map e ≫  …
  constructor
  -- ⊢ ε.functor.map i ≫ ε.functor.map e = 𝟙 (ε.functor.obj Y)
  · rw [← ε.functor.map_comp, h₁, ε.functor.map_id]
    -- 🎉 no goals
  · simp only [← ε.functor.map_comp, h₂, Equivalence.fun_inv_map]
    -- ⊢ NatTrans.app (Equivalence.counit ε) X' ≫ p ≫ NatTrans.app (Equivalence.couni …
    rfl
    -- 🎉 no goals
#align category_theory.idempotents.equivalence.is_idempotent_complete CategoryTheory.Idempotents.Equivalence.isIdempotentComplete

/-- If `C` and `D` are equivalent categories, that `C` is idempotent complete iff `D` is. -/
theorem isIdempotentComplete_iff_of_equivalence {D : Type*} [Category D] (ε : C ≌ D) :
    IsIdempotentComplete C ↔ IsIdempotentComplete D := by
  constructor
  -- ⊢ IsIdempotentComplete C → IsIdempotentComplete D
  · exact Equivalence.isIdempotentComplete ε
    -- 🎉 no goals
  · exact Equivalence.isIdempotentComplete ε.symm
    -- 🎉 no goals
#align category_theory.idempotents.is_idempotent_complete_iff_of_equivalence CategoryTheory.Idempotents.isIdempotentComplete_iff_of_equivalence

theorem isIdempotentComplete_of_isIdempotentComplete_opposite (h : IsIdempotentComplete Cᵒᵖ) :
    IsIdempotentComplete C := by
  refine' ⟨_⟩
  -- ⊢ ∀ (X : C) (p : X ⟶ X), p ≫ p = p → ∃ Y i e, i ≫ e = 𝟙 Y ∧ e ≫ i = p
  intro X p hp
  -- ⊢ ∃ Y i e, i ≫ e = 𝟙 Y ∧ e ≫ i = p
  rcases IsIdempotentComplete.idempotents_split (op X) p.op (by rw [← op_comp, hp]) with
    ⟨Y, i, e, ⟨h₁, h₂⟩⟩
  use Y.unop, e.unop, i.unop
  -- ⊢ e.unop ≫ i.unop = 𝟙 Y.unop ∧ i.unop ≫ e.unop = p
  constructor
  -- ⊢ e.unop ≫ i.unop = 𝟙 Y.unop
  · simp only [← unop_comp, h₁]
    -- ⊢ (𝟙 Y).unop = 𝟙 Y.unop
    rfl
    -- 🎉 no goals
  · simp only [← unop_comp, h₂]
    -- ⊢ p.op.unop = p
    rfl
    -- 🎉 no goals
#align category_theory.idempotents.is_idempotent_complete_of_is_idempotent_complete_opposite CategoryTheory.Idempotents.isIdempotentComplete_of_isIdempotentComplete_opposite

theorem isIdempotentComplete_iff_opposite : IsIdempotentComplete Cᵒᵖ ↔ IsIdempotentComplete C := by
  constructor
  -- ⊢ IsIdempotentComplete Cᵒᵖ → IsIdempotentComplete C
  · exact isIdempotentComplete_of_isIdempotentComplete_opposite
    -- 🎉 no goals
  · intro h
    -- ⊢ IsIdempotentComplete Cᵒᵖ
    apply isIdempotentComplete_of_isIdempotentComplete_opposite
    -- ⊢ IsIdempotentComplete Cᵒᵖᵒᵖ
    rw [isIdempotentComplete_iff_of_equivalence (opOpEquivalence C)]
    -- ⊢ IsIdempotentComplete C
    exact h
    -- 🎉 no goals
#align category_theory.idempotents.is_idempotent_complete_iff_opposite CategoryTheory.Idempotents.isIdempotentComplete_iff_opposite

instance [IsIdempotentComplete C] : IsIdempotentComplete Cᵒᵖ := by
  rwa [isIdempotentComplete_iff_opposite]
  -- 🎉 no goals

end Idempotents

end CategoryTheory
