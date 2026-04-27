/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Set.Function
public import Mathlib.Dynamics.FixedPoints.Defs

/-!
# Fixed points of a self-map

We prove some simple lemmas about `IsFixedPt` and `∘`, `iterate`, and `Semiconj`.

## Tags

fixed point
-/

public section

open Equiv

universe u v

variable {α β : Type*} {f fa g : α → α} {x : α} {fb : β → β} {e : Perm α}

namespace Function

open Function (Commute)

namespace IsFixedPt

/-- If `x` is a fixed point of `f` and `g`, then it is a fixed point of `f ∘ g`. -/
protected theorem comp (hf : IsFixedPt f x) (hg : IsFixedPt g x) : IsFixedPt (f ∘ g) x :=
  calc
    f (g x) = f x := congr_arg f hg
    _ = x := hf

/-- If `x` is a fixed point of `f`, then it is a fixed point of `f^[n]`. -/
protected theorem iterate (hf : IsFixedPt f x) (n : ℕ) : IsFixedPt f^[n] x :=
  iterate_fixed hf n

/-- If `x` is a fixed point of `f ∘ g` and `g`, then it is a fixed point of `f`. -/
theorem left_of_comp (hfg : IsFixedPt (f ∘ g) x) (hg : IsFixedPt g x) : IsFixedPt f x :=
  calc
    f x = f (g x) := congr_arg f hg.symm
    _ = x := hfg

/-- If `x` is a fixed point of `f` and `g` is a left inverse of `f`, then `x` is a fixed
point of `g`. -/
theorem to_leftInverse (hf : IsFixedPt f x) (h : LeftInverse g f) : IsFixedPt g x :=
  calc
    g x = g (f x) := congr_arg g hf.symm
    _ = x := h x

/-- If `g` (semi)conjugates `fa` to `fb`, then it sends fixed points of `fa` to fixed points
of `fb`. -/
protected theorem map {x : α} (hx : IsFixedPt fa x) {g : α → β} (h : Semiconj g fa fb) :
    IsFixedPt fb (g x) :=
  calc
    fb (g x) = g (fa x) := (h.eq x).symm
    _ = g x := congr_arg g hx

protected theorem apply {x : α} (hx : IsFixedPt f x) : IsFixedPt f (f x) := by convert hx

theorem preimage_iterate {s : Set α} (h : IsFixedPt (Set.preimage f) s) (n : ℕ) :
    IsFixedPt (Set.preimage f^[n]) s := by
  rw [Set.preimage_iterate_eq]
  exact h.iterate n

lemma image_iterate {s : Set α} (h : IsFixedPt (Set.image f) s) (n : ℕ) :
    IsFixedPt (Set.image f^[n]) s :=
  Set.image_iterate_eq ▸ h.iterate n

protected theorem equiv_symm (h : IsFixedPt e x) : IsFixedPt e.symm x :=
  h.to_leftInverse e.leftInverse_symm

protected theorem perm_inv (h : IsFixedPt e x) : IsFixedPt (⇑e⁻¹) x :=
  h.equiv_symm

protected theorem perm_pow (h : IsFixedPt e x) (n : ℕ) : IsFixedPt (⇑(e ^ n)) x := h.iterate _

protected theorem perm_zpow (h : IsFixedPt e x) : ∀ n : ℤ, IsFixedPt (⇑(e ^ n)) x
  | Int.ofNat _ => h.perm_pow _
  | Int.negSucc n => (h.perm_pow <| n + 1).perm_inv

end IsFixedPt

@[simp]
theorem Injective.isFixedPt_apply_iff (hf : Injective f) {x : α} :
    IsFixedPt f (f x) ↔ IsFixedPt f x :=
  ⟨fun h => hf h.eq, IsFixedPt.apply⟩

/-- If `g` semiconjugates `fa` to `fb`, then it sends fixed points of `fa` to fixed points
of `fb`. -/
theorem Semiconj.mapsTo_fixedPoints {g : α → β} (h : Semiconj g fa fb) :
    Set.MapsTo g (fixedPoints fa) (fixedPoints fb) := fun _ hx => hx.map h

/-- Any two maps `f : α → β` and `g : β → α` are inverse of each other on the sets of fixed points
of `f ∘ g` and `g ∘ f`, respectively. -/
theorem invOn_fixedPoints_comp (f : α → β) (g : β → α) :
    Set.InvOn f g (fixedPoints <| f ∘ g) (fixedPoints <| g ∘ f) :=
  ⟨fun _ => id, fun _ => id⟩

/-- Any map `f` sends fixed points of `g ∘ f` to fixed points of `f ∘ g`. -/
theorem mapsTo_fixedPoints_comp (f : α → β) (g : β → α) :
    Set.MapsTo f (fixedPoints <| g ∘ f) (fixedPoints <| f ∘ g) := fun _ hx => hx.map fun _ => rfl

/-- Given two maps `f : α → β` and `g : β → α`, `g` is a bijective map between the fixed points
of `f ∘ g` and the fixed points of `g ∘ f`. The inverse map is `f`, see `invOn_fixedPoints_comp`. -/
theorem bijOn_fixedPoints_comp (f : α → β) (g : β → α) :
    Set.BijOn g (fixedPoints <| f ∘ g) (fixedPoints <| g ∘ f) :=
  (invOn_fixedPoints_comp f g).bijOn (mapsTo_fixedPoints_comp g f) (mapsTo_fixedPoints_comp f g)

/-- If self-maps `f` and `g` commute, then they are inverse of each other on the set of fixed points
of `f ∘ g`. This is a particular case of `Function.invOn_fixedPoints_comp`. -/
theorem Commute.invOn_fixedPoints_comp (h : Commute f g) :
    Set.InvOn f g (fixedPoints <| f ∘ g) (fixedPoints <| f ∘ g) := by
  simpa only [h.comp_eq] using Function.invOn_fixedPoints_comp f g

/-- If self-maps `f` and `g` commute, then `f` is bijective on the set of fixed points of `f ∘ g`.
This is a particular case of `Function.bijOn_fixedPoints_comp`. -/
theorem Commute.left_bijOn_fixedPoints_comp (h : Commute f g) :
    Set.BijOn f (fixedPoints <| f ∘ g) (fixedPoints <| f ∘ g) := by
  simpa only [h.comp_eq] using bijOn_fixedPoints_comp g f

/-- If self-maps `f` and `g` commute, then `g` is bijective on the set of fixed points of `f ∘ g`.
This is a particular case of `Function.bijOn_fixedPoints_comp`. -/
theorem Commute.right_bijOn_fixedPoints_comp (h : Commute f g) :
    Set.BijOn g (fixedPoints <| f ∘ g) (fixedPoints <| f ∘ g) := by
  simpa only [h.comp_eq] using bijOn_fixedPoints_comp f g

end Function
