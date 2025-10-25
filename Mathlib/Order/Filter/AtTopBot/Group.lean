/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Map
import Mathlib.Order.Filter.AtTopBot.Monoid

/-!
# Convergence to ±infinity in ordered commutative groups
-/

variable {α G : Type*}
open Set

namespace Filter

section OrderedCommGroup

variable [CommGroup G] [PartialOrder G] [IsOrderedMonoid G] (l : Filter α) {f g : α → G}

@[to_additive]
theorem tendsto_atTop_mul_left_of_le' (C : G) (hf : ∀ᶠ x in l, C ≤ f x) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atTop :=
  .atTop_of_isBoundedUnder_le_mul (f := f⁻¹) ⟨C⁻¹, by simpa⟩ (by simpa)

@[to_additive]
theorem tendsto_atBot_mul_left_of_ge' (C : G) (hf : ∀ᶠ x in l, f x ≤ C) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atBot :=
  tendsto_atTop_mul_left_of_le' (G := Gᵒᵈ) _ C hf hg

@[to_additive]
theorem tendsto_atTop_mul_left_of_le (C : G) (hf : ∀ x, C ≤ f x) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atTop :=
  tendsto_atTop_mul_left_of_le' l C (univ_mem' hf) hg

@[to_additive]
theorem tendsto_atBot_mul_left_of_ge (C : G) (hf : ∀ x, f x ≤ C) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atBot :=
  tendsto_atTop_mul_left_of_le (G := Gᵒᵈ) _ C hf hg

@[to_additive]
theorem tendsto_atTop_mul_right_of_le' (C : G) (hf : Tendsto f l atTop) (hg : ∀ᶠ x in l, C ≤ g x) :
    Tendsto (fun x => f x * g x) l atTop :=
  .atTop_of_mul_isBoundedUnder_le (g := g⁻¹) ⟨C⁻¹, by simpa⟩ (by simpa)

@[to_additive]
theorem tendsto_atBot_mul_right_of_ge' (C : G) (hf : Tendsto f l atBot) (hg : ∀ᶠ x in l, g x ≤ C) :
    Tendsto (fun x => f x * g x) l atBot :=
  tendsto_atTop_mul_right_of_le' (G := Gᵒᵈ) _ C hf hg

@[to_additive]
theorem tendsto_atTop_mul_right_of_le (C : G) (hf : Tendsto f l atTop) (hg : ∀ x, C ≤ g x) :
    Tendsto (fun x => f x * g x) l atTop :=
  tendsto_atTop_mul_right_of_le' l C hf (univ_mem' hg)

@[to_additive]
theorem tendsto_atBot_mul_right_of_ge (C : G) (hf : Tendsto f l atBot) (hg : ∀ x, g x ≤ C) :
    Tendsto (fun x => f x * g x) l atBot :=
  tendsto_atTop_mul_right_of_le (G := Gᵒᵈ) _  C hf hg

@[to_additive]
theorem tendsto_atTop_mul_const_left (C : G) (hf : Tendsto f l atTop) :
    Tendsto (fun x => C * f x) l atTop :=
  tendsto_atTop_mul_left_of_le' l C (univ_mem' fun _ => le_refl C) hf

@[to_additive]
theorem tendsto_atBot_mul_const_left (C : G) (hf : Tendsto f l atBot) :
    Tendsto (fun x => C * f x) l atBot :=
  tendsto_atTop_mul_const_left (G := Gᵒᵈ) _ C hf

@[to_additive]
theorem tendsto_atTop_mul_const_right (C : G) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x * C) l atTop :=
  tendsto_atTop_mul_right_of_le' l C hf (univ_mem' fun _ => le_refl C)

@[to_additive]
theorem tendsto_atBot_mul_const_right (C : G) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x * C) l atBot :=
  tendsto_atTop_mul_const_right (G := Gᵒᵈ) _ C hf

@[to_additive]
theorem map_inv_atBot : map (Inv.inv : G → G) atBot = atTop :=
  (OrderIso.inv G).map_atBot

@[to_additive]
theorem map_inv_atTop : map (Inv.inv : G → G) atTop = atBot :=
  (OrderIso.inv G).map_atTop

@[to_additive]
theorem comap_inv_atBot : comap (Inv.inv : G → G) atBot = atTop :=
  (OrderIso.inv G).comap_atTop

@[to_additive]
theorem comap_inv_atTop : comap (Inv.inv : G → G) atTop = atBot :=
  (OrderIso.inv G).comap_atBot

@[to_additive]
theorem tendsto_inv_atTop_atBot : Tendsto (Inv.inv : G → G) atTop atBot :=
  (OrderIso.inv G).tendsto_atTop

@[to_additive]
theorem tendsto_inv_atBot_atTop : Tendsto (Inv.inv : G → G) atBot atTop :=
  tendsto_inv_atTop_atBot (G := Gᵒᵈ)

variable {l}

@[to_additive (attr := simp)]
theorem tendsto_inv_atTop_iff : Tendsto (fun x => (f x)⁻¹) l atTop ↔ Tendsto f l atBot :=
  (OrderIso.inv G).tendsto_atBot_iff

@[to_additive (attr := simp)]
theorem tendsto_inv_atBot_iff : Tendsto (fun x => (f x)⁻¹) l atBot ↔ Tendsto f l atTop :=
  (OrderIso.inv G).tendsto_atTop_iff

end OrderedCommGroup

section LinearOrderedCommGroup

variable [CommGroup G] [LinearOrder G]

/-- $\lim_{x\to+\infty}|x|_m=+\infty$ -/
@[to_additive /-- $\lim_{x\to+\infty}|x|=+\infty$ -/]
theorem tendsto_mabs_atTop_atTop : Tendsto (mabs : G → G) atTop atTop :=
  tendsto_atTop_mono le_mabs_self tendsto_id

/-- $\lim_{x\to\infty^{-1}|x|_m=+\infty$ -/
@[to_additive /-- $\lim_{x\to-\infty}|x|=+\infty$ -/]
theorem tendsto_mabs_atBot_atTop [IsOrderedMonoid G] : Tendsto (mabs : G → G) atBot atTop :=
  tendsto_atTop_mono inv_le_mabs tendsto_inv_atBot_atTop

@[to_additive (attr := simp)]
theorem comap_mabs_atTop [IsOrderedMonoid G] : comap (mabs : G → G) atTop = atBot ⊔ atTop := by
  refine
    le_antisymm (((atTop_basis.comap _).le_basis_iff (atBot_basis.sup atTop_basis)).2 ?_)
      (sup_le tendsto_mabs_atBot_atTop.le_comap tendsto_mabs_atTop_atTop.le_comap)
  rintro ⟨a, b⟩ -
  refine ⟨max (a⁻¹) b, trivial, fun x hx => ?_⟩
  rw [mem_preimage, mem_Ici, le_mabs', max_le_iff, ← min_inv_inv', le_min_iff, inv_inv] at hx
  exact hx.imp And.left And.right

end LinearOrderedCommGroup

end Filter
