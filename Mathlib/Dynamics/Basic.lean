/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module dynamics.fixed_points.basic
! leanprover-community/mathlib commit 550b58538991c8977703fdeb7c9d51a5aa27df11
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Iterate
import Mathlib.GroupTheory.Perm.Basic

/-!
# Fixed points of a self-map

In this file we define

* the predicate `is_fixed_pt f x := f x = x`;
* the set `fixed_points f` of fixed points of a self-map `f`.

We also prove some simple lemmas about `is_fixed_pt` and `∘`, `iterate`, and `semiconj`.

## Tags

fixed point
-/


open Equiv

universe u v

variable {α : Type u} {β : Type v} {f fa g : α → α} {x y : α} {fb : β → β} {m n k : ℕ} {e : Perm α}

namespace Function

/-- A point `x` is a fixed point of `f : α → α` if `f x = x`. -/
def IsFixedPt (f : α → α) (x : α) :=
  f x = x
#align function.is_fixed_pt Function.IsFixedPt

/-- Every point is a fixed point of `id`. -/
theorem is_fixed_pt_id (x : α) : IsFixedPt id x :=
  (rfl : _)
#align function.is_fixed_pt_id Function.is_fixed_pt_id

namespace IsFixedPt

instance [h : DecidableEq α] {f : α → α} {x : α} : Decidable (IsFixedPt f x) :=
  h (f x) x

/-- If `x` is a fixed point of `f`, then `f x = x`. This is useful, e.g., for `rw` or `simp`.-/
protected theorem eq (hf : IsFixedPt f x) : f x = x :=
  hf
#align function.is_fixed_pt.eq Function.IsFixedPt.eq

/-- If `x` is a fixed point of `f` and `g`, then it is a fixed point of `f ∘ g`. -/
protected theorem comp (hf : IsFixedPt f x) (hg : IsFixedPt g x) : IsFixedPt (f ∘ g) x :=
  calc
    f (g x) = f x := congr_arg f hg
    _ = x := hf

#align function.is_fixed_pt.comp Function.IsFixedPt.comp

/-- If `x` is a fixed point of `f`, then it is a fixed point of `f^[n]`. -/
protected theorem iterate (hf : IsFixedPt f x) (n : ℕ) : IsFixedPt (f^[n]) x :=
  iterate_fixed hf n
#align function.is_fixed_pt.iterate Function.IsFixedPt.iterate

/-- If `x` is a fixed point of `f ∘ g` and `g`, then it is a fixed point of `f`. -/
theorem left_of_comp (hfg : IsFixedPt (f ∘ g) x) (hg : IsFixedPt g x) : IsFixedPt f x :=
  calc
    f x = f (g x) := congr_arg f hg.symm
    _ = x := hfg

#align function.is_fixed_pt.left_of_comp Function.IsFixedPt.left_of_comp

/-- If `x` is a fixed point of `f` and `g` is a left inverse of `f`, then `x` is a fixed
point of `g`. -/
theorem to_left_inverse (hf : IsFixedPt f x) (h : LeftInverse g f) : IsFixedPt g x :=
  calc
    g x = g (f x) := congr_arg g hf.symm
    _ = x := h x

#align function.is_fixed_pt.to_left_inverse Function.IsFixedPt.to_left_inverse

/-- If `g` (semi)conjugates `fa` to `fb`, then it sends fixed points of `fa` to fixed points
of `fb`. -/
protected theorem map {x : α} (hx : IsFixedPt fa x) {g : α → β} (h : Semiconj g fa fb) :
    IsFixedPt fb (g x) :=
  calc
    fb (g x) = g (fa x) := (h.Eq x).symm
    _ = g x := congr_arg g hx

#align function.is_fixed_pt.map Function.IsFixedPt.map

protected theorem apply {x : α} (hx : IsFixedPt f x) : IsFixedPt f (f x) := by convert hx
#align function.is_fixed_pt.apply Function.IsFixedPt.apply

theorem preimage_iterate {s : Set α} (h : IsFixedPt (Set.preimage f) s) (n : ℕ) :
    IsFixedPt (Set.preimage (f^[n])) s := by
  rw [Set.preimage_iterate_eq]
  exact h.iterate n
#align function.is_fixed_pt.preimage_iterate Function.IsFixedPt.preimage_iterate

protected theorem equiv_symm (h : IsFixedPt e x) : IsFixedPt e.symm x :=
  h.to_left_inverse e.left_inverse_symm
#align function.is_fixed_pt.equiv_symm Function.IsFixedPt.equiv_symm

protected theorem perm_inv (h : IsFixedPt e x) : IsFixedPt (⇑e⁻¹) x :=
  h.equiv_symm
#align function.is_fixed_pt.perm_inv Function.IsFixedPt.perm_inv

protected theorem perm_pow (h : IsFixedPt e x) (n : ℕ) : IsFixedPt (⇑(e ^ n)) x := by
  rw [← Equiv.Perm.iterate_eq_pow]
  exact h.iterate _
#align function.is_fixed_pt.perm_pow Function.IsFixedPt.perm_pow

protected theorem perm_zpow (h : IsFixedPt e x) : ∀ n : ℤ, IsFixedPt (⇑(e ^ n)) x
  | Int.ofNat n => h.perm_pow _
  | Int.negSucc n => (h.perm_pow <| n + 1).perm_inv
#align function.is_fixed_pt.perm_zpow Function.IsFixedPt.perm_zpow

end IsFixedPt

@[simp]
theorem Injective.is_fixed_pt_apply_iff (hf : Injective f) {x : α} :
    IsFixedPt f (f x) ↔ IsFixedPt f x :=
  ⟨fun h => hf h.Eq, IsFixedPt.apply⟩
#align function.injective.is_fixed_pt_apply_iff Function.Injective.is_fixed_pt_apply_iff

/-- The set of fixed points of a map `f : α → α`. -/
def fixedPoints (f : α → α) : Set α :=
  { x : α | IsFixedPt f x }
#align function.fixed_points Function.fixedPoints

instance fixedPoints.decidable [DecidableEq α] (f : α → α) (x : α) :
    Decidable (x ∈ fixedPoints f) :=
  is_fixed_pt.decidable
#align function.fixed_points.decidable Function.fixedPoints.decidable

@[simp]
theorem mem_fixed_points : x ∈ fixedPoints f ↔ IsFixedPt f x :=
  Iff.rfl
#align function.mem_fixed_points Function.mem_fixed_points

theorem mem_fixed_points_iff {α : Type _} {f : α → α} {x : α} : x ∈ fixedPoints f ↔ f x = x := by
  rfl
#align function.mem_fixed_points_iff Function.mem_fixed_points_iff

@[simp]
theorem fixed_points_id : fixedPoints (@id α) = Set.univ :=
  Set.ext fun _ => by simpa using is_fixed_pt_id _
#align function.fixed_points_id Function.fixed_points_id

theorem fixed_points_subset_range : fixedPoints f ⊆ Set.range f := fun x hx => ⟨x, hx⟩
#align function.fixed_points_subset_range Function.fixed_points_subset_range

/-- If `g` semiconjugates `fa` to `fb`, then it sends fixed points of `fa` to fixed points
of `fb`. -/
theorem Semiconj.maps_to_fixed_pts {g : α → β} (h : Semiconj g fa fb) :
    Set.MapsTo g (fixedPoints fa) (fixedPoints fb) := fun x hx => hx.map h
#align function.semiconj.maps_to_fixed_pts Function.Semiconj.maps_to_fixed_pts

/-- Any two maps `f : α → β` and `g : β → α` are inverse of each other on the sets of fixed points
of `f ∘ g` and `g ∘ f`, respectively. -/
theorem inv_on_fixed_pts_comp (f : α → β) (g : β → α) :
    Set.InvOn f g (fixed_points <| f ∘ g) (fixed_points <| g ∘ f) :=
  ⟨fun x => id, fun x => id⟩
#align function.inv_on_fixed_pts_comp Function.inv_on_fixed_pts_comp

/-- Any map `f` sends fixed points of `g ∘ f` to fixed points of `f ∘ g`. -/
theorem maps_to_fixed_pts_comp (f : α → β) (g : β → α) :
    Set.MapsTo f (fixed_points <| g ∘ f) (fixed_points <| f ∘ g) := fun x hx => hx.map fun x => rfl
#align function.maps_to_fixed_pts_comp Function.maps_to_fixed_pts_comp

/-- Given two maps `f : α → β` and `g : β → α`, `g` is a bijective map between the fixed points
of `f ∘ g` and the fixed points of `g ∘ f`. The inverse map is `f`, see `inv_on_fixed_pts_comp`. -/
theorem bij_on_fixed_pts_comp (f : α → β) (g : β → α) :
    Set.BijOn g (fixed_points <| f ∘ g) (fixed_points <| g ∘ f) :=
  (inv_on_fixed_pts_comp f g).BijOn (maps_to_fixed_pts_comp g f) (maps_to_fixed_pts_comp f g)
#align function.bij_on_fixed_pts_comp Function.bij_on_fixed_pts_comp

/-- If self-maps `f` and `g` commute, then they are inverse of each other on the set of fixed points
of `f ∘ g`. This is a particular case of `function.inv_on_fixed_pts_comp`. -/
theorem Commute.inv_on_fixed_pts_comp (h : Commute f g) :
    Set.InvOn f g (fixed_points <| f ∘ g) (fixed_points <| f ∘ g) := by
  simpa only [h.comp_eq] using inv_on_fixed_pts_comp f g
#align function.commute.inv_on_fixed_pts_comp Function.Commute.inv_on_fixed_pts_comp

/-- If self-maps `f` and `g` commute, then `f` is bijective on the set of fixed points of `f ∘ g`.
This is a particular case of `function.bij_on_fixed_pts_comp`. -/
theorem Commute.left_bij_on_fixed_pts_comp (h : Commute f g) :
    Set.BijOn f (fixed_points <| f ∘ g) (fixed_points <| f ∘ g) := by
  simpa only [h.comp_eq] using bij_on_fixed_pts_comp g f
#align function.commute.left_bij_on_fixed_pts_comp Function.Commute.left_bij_on_fixed_pts_comp

/-- If self-maps `f` and `g` commute, then `g` is bijective on the set of fixed points of `f ∘ g`.
This is a particular case of `function.bij_on_fixed_pts_comp`. -/
theorem Commute.right_bij_on_fixed_pts_comp (h : Commute f g) :
    Set.BijOn g (fixed_points <| f ∘ g) (fixed_points <| f ∘ g) := by
  simpa only [h.comp_eq] using bij_on_fixed_pts_comp f g
#align function.commute.right_bij_on_fixed_pts_comp Function.Commute.right_bij_on_fixed_pts_comp

end Function
