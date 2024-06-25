/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.NormedSpace.Ray
import Mathlib.Topology.Order.LocalExtr

#align_import analysis.normed_space.extr from "leanprover-community/mathlib"@"17ef379e997badd73e5eabb4d38f11919ab3c4b3"

/-!
# (Local) maximums in a normed space

In this file we prove the following lemma, see `IsMaxFilter.norm_add_sameRay`. If `f : α → E` is
a function such that `norm ∘ f` has a maximum along a filter `l` at a point `c` and `y` is a vector
on the same ray as `f c`, then the function `fun x => ‖f x + y‖` has a maximum along `l` at `c`.

Then we specialize it to the case `y = f c` and to different special cases of `IsMaxFilter`:
`IsMaxOn`, `IsLocalMaxOn`, and `IsLocalMax`.

## Tags

local maximum, normed space
-/


variable {α X E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]

section

variable {f : α → E} {l : Filter α} {s : Set α} {c : α} {y : E}

/-- If `f : α → E` is a function such that `norm ∘ f` has a maximum along a filter `l` at a point
`c` and `y` is a vector on the same ray as `f c`, then the function `fun x => ‖f x + y‖` has
a maximum along `l` at `c`. -/
theorem IsMaxFilter.norm_add_sameRay (h : IsMaxFilter (norm ∘ f) l c) (hy : SameRay ℝ (f c) y) :
    IsMaxFilter (fun x => ‖f x + y‖) l c :=
  h.mono fun x hx =>
    calc
      ‖f x + y‖ ≤ ‖f x‖ + ‖y‖ := norm_add_le _ _
      _ ≤ ‖f c‖ + ‖y‖ := add_le_add_right hx _
      _ = ‖f c + y‖ := hy.norm_add.symm
#align is_max_filter.norm_add_same_ray IsMaxFilter.norm_add_sameRay

/-- If `f : α → E` is a function such that `norm ∘ f` has a maximum along a filter `l` at a point
`c`, then the function `fun x => ‖f x + f c‖` has a maximum along `l` at `c`. -/
theorem IsMaxFilter.norm_add_self (h : IsMaxFilter (norm ∘ f) l c) :
    IsMaxFilter (fun x => ‖f x + f c‖) l c :=
  IsMaxFilter.norm_add_sameRay h SameRay.rfl
#align is_max_filter.norm_add_self IsMaxFilter.norm_add_self

/-- If `f : α → E` is a function such that `norm ∘ f` has a maximum on a set `s` at a point `c` and
`y` is a vector on the same ray as `f c`, then the function `fun x => ‖f x + y‖` has a maximum
on `s` at `c`. -/
theorem IsMaxOn.norm_add_sameRay (h : IsMaxOn (norm ∘ f) s c) (hy : SameRay ℝ (f c) y) :
    IsMaxOn (fun x => ‖f x + y‖) s c :=
  IsMaxFilter.norm_add_sameRay h hy
#align is_max_on.norm_add_same_ray IsMaxOn.norm_add_sameRay

/-- If `f : α → E` is a function such that `norm ∘ f` has a maximum on a set `s` at a point `c`,
then the function `fun x => ‖f x + f c‖` has a maximum on `s` at `c`. -/
theorem IsMaxOn.norm_add_self (h : IsMaxOn (norm ∘ f) s c) : IsMaxOn (fun x => ‖f x + f c‖) s c :=
  IsMaxFilter.norm_add_self h
#align is_max_on.norm_add_self IsMaxOn.norm_add_self

end

variable {f : X → E} {s : Set X} {c : X} {y : E}

/-- If `f : α → E` is a function such that `norm ∘ f` has a local maximum on a set `s` at a point
`c` and `y` is a vector on the same ray as `f c`, then the function `fun x => ‖f x + y‖` has a local
maximum on `s` at `c`. -/
theorem IsLocalMaxOn.norm_add_sameRay (h : IsLocalMaxOn (norm ∘ f) s c) (hy : SameRay ℝ (f c) y) :
    IsLocalMaxOn (fun x => ‖f x + y‖) s c :=
  IsMaxFilter.norm_add_sameRay h hy
#align is_local_max_on.norm_add_same_ray IsLocalMaxOn.norm_add_sameRay

/-- If `f : α → E` is a function such that `norm ∘ f` has a local maximum on a set `s` at a point
`c`, then the function `fun x => ‖f x + f c‖` has a local maximum on `s` at `c`. -/
theorem IsLocalMaxOn.norm_add_self (h : IsLocalMaxOn (norm ∘ f) s c) :
    IsLocalMaxOn (fun x => ‖f x + f c‖) s c :=
  IsMaxFilter.norm_add_self h
#align is_local_max_on.norm_add_self IsLocalMaxOn.norm_add_self

/-- If `f : α → E` is a function such that `norm ∘ f` has a local maximum at a point `c` and `y` is
a vector on the same ray as `f c`, then the function `fun x => ‖f x + y‖` has a local maximum
at `c`. -/
theorem IsLocalMax.norm_add_sameRay (h : IsLocalMax (norm ∘ f) c) (hy : SameRay ℝ (f c) y) :
    IsLocalMax (fun x => ‖f x + y‖) c :=
  IsMaxFilter.norm_add_sameRay h hy
#align is_local_max.norm_add_same_ray IsLocalMax.norm_add_sameRay

/-- If `f : α → E` is a function such that `norm ∘ f` has a local maximum at a point `c`, then the
function `fun x => ‖f x + f c‖` has a local maximum at `c`. -/
theorem IsLocalMax.norm_add_self (h : IsLocalMax (norm ∘ f) c) :
    IsLocalMax (fun x => ‖f x + f c‖) c :=
  IsMaxFilter.norm_add_self h
#align is_local_max.norm_add_self IsLocalMax.norm_add_self
