/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Order.Group.Instances
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Map
import Mathlib.Order.Filter.AtTopBot.Monoid

/-!
# Convergence to ±infinity in ordered commutative groups
-/

variable {α β : Type*}
open Set

namespace Filter

section OrderedGroup

variable [OrderedAddCommGroup β] (l : Filter α) {f g : α → β}

theorem tendsto_atTop_add_left_of_le' (C : β) (hf : ∀ᶠ x in l, C ≤ f x) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x + g x) l atTop :=
  @tendsto_atTop_of_add_bdd_above_left' _ _ _ l (fun x => -f x) (fun x => f x + g x) (-C) (by simpa)
    (by simpa)

theorem tendsto_atBot_add_left_of_ge' (C : β) (hf : ∀ᶠ x in l, f x ≤ C) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x + g x) l atBot :=
  @tendsto_atTop_add_left_of_le' _ βᵒᵈ _ _ _ _ C hf hg

theorem tendsto_atTop_add_left_of_le (C : β) (hf : ∀ x, C ≤ f x) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x + g x) l atTop :=
  tendsto_atTop_add_left_of_le' l C (univ_mem' hf) hg

theorem tendsto_atBot_add_left_of_ge (C : β) (hf : ∀ x, f x ≤ C) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x + g x) l atBot :=
  @tendsto_atTop_add_left_of_le _ βᵒᵈ _ _ _ _ C hf hg

theorem tendsto_atTop_add_right_of_le' (C : β) (hf : Tendsto f l atTop) (hg : ∀ᶠ x in l, C ≤ g x) :
    Tendsto (fun x => f x + g x) l atTop :=
  @tendsto_atTop_of_add_bdd_above_right' _ _ _ l (fun x => f x + g x) (fun x => -g x) (-C)
    (by simp [hg]) (by simp [hf])

theorem tendsto_atBot_add_right_of_ge' (C : β) (hf : Tendsto f l atBot) (hg : ∀ᶠ x in l, g x ≤ C) :
    Tendsto (fun x => f x + g x) l atBot :=
  @tendsto_atTop_add_right_of_le' _ βᵒᵈ _ _ _ _ C hf hg

theorem tendsto_atTop_add_right_of_le (C : β) (hf : Tendsto f l atTop) (hg : ∀ x, C ≤ g x) :
    Tendsto (fun x => f x + g x) l atTop :=
  tendsto_atTop_add_right_of_le' l C hf (univ_mem' hg)

theorem tendsto_atBot_add_right_of_ge (C : β) (hf : Tendsto f l atBot) (hg : ∀ x, g x ≤ C) :
    Tendsto (fun x => f x + g x) l atBot :=
  @tendsto_atTop_add_right_of_le _ βᵒᵈ _ _ _ _ C hf hg

theorem tendsto_atTop_add_const_left (C : β) (hf : Tendsto f l atTop) :
    Tendsto (fun x => C + f x) l atTop :=
  tendsto_atTop_add_left_of_le' l C (univ_mem' fun _ => le_refl C) hf

theorem tendsto_atBot_add_const_left (C : β) (hf : Tendsto f l atBot) :
    Tendsto (fun x => C + f x) l atBot :=
  @tendsto_atTop_add_const_left _ βᵒᵈ _ _ _ C hf

theorem tendsto_atTop_add_const_right (C : β) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x + C) l atTop :=
  tendsto_atTop_add_right_of_le' l C hf (univ_mem' fun _ => le_refl C)

theorem tendsto_atBot_add_const_right (C : β) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x + C) l atBot :=
  @tendsto_atTop_add_const_right _ βᵒᵈ _ _ _ C hf

theorem map_neg_atBot : map (Neg.neg : β → β) atBot = atTop :=
  (OrderIso.neg β).map_atBot

theorem map_neg_atTop : map (Neg.neg : β → β) atTop = atBot :=
  (OrderIso.neg β).map_atTop

theorem comap_neg_atBot : comap (Neg.neg : β → β) atBot = atTop :=
  (OrderIso.neg β).comap_atTop

theorem comap_neg_atTop : comap (Neg.neg : β → β) atTop = atBot :=
  (OrderIso.neg β).comap_atBot

theorem tendsto_neg_atTop_atBot : Tendsto (Neg.neg : β → β) atTop atBot :=
  (OrderIso.neg β).tendsto_atTop

theorem tendsto_neg_atBot_atTop : Tendsto (Neg.neg : β → β) atBot atTop :=
  @tendsto_neg_atTop_atBot βᵒᵈ _

variable {l}

@[simp]
theorem tendsto_neg_atTop_iff : Tendsto (fun x => -f x) l atTop ↔ Tendsto f l atBot :=
  (OrderIso.neg β).tendsto_atBot_iff

@[simp]
theorem tendsto_neg_atBot_iff : Tendsto (fun x => -f x) l atBot ↔ Tendsto f l atTop :=
  (OrderIso.neg β).tendsto_atTop_iff

end OrderedGroup

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α]

/-- $\lim_{x\to+\infty}|x|=+\infty$ -/
theorem tendsto_abs_atTop_atTop : Tendsto (abs : α → α) atTop atTop :=
  tendsto_atTop_mono le_abs_self tendsto_id

/-- $\lim_{x\to-\infty}|x|=+\infty$ -/
theorem tendsto_abs_atBot_atTop : Tendsto (abs : α → α) atBot atTop :=
  tendsto_atTop_mono neg_le_abs tendsto_neg_atBot_atTop

@[simp]
theorem comap_abs_atTop : comap (abs : α → α) atTop = atBot ⊔ atTop := by
  refine
    le_antisymm (((atTop_basis.comap _).le_basis_iff (atBot_basis.sup atTop_basis)).2 ?_)
      (sup_le tendsto_abs_atBot_atTop.le_comap tendsto_abs_atTop_atTop.le_comap)
  rintro ⟨a, b⟩ -
  refine ⟨max (-a) b, trivial, fun x hx => ?_⟩
  rw [mem_preimage, mem_Ici, le_abs', max_le_iff, ← min_neg_neg, le_min_iff, neg_neg] at hx
  exact hx.imp And.left And.right

end LinearOrderedAddCommGroup

end Filter
