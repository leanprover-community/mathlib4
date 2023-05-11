/-
Copyright (c) 2023 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/-! # Extremizing functions on Arrays

This file supplements functions like `min` and `max` on `Array`s.

-/

-- TODO(Thomas): complete the suite of extremizing functions

namespace Array

section Ord

variable [Ord β]

/-- Collect the elements of an array `a` that attain a minimal value under the function `f`.

* `#[[1], [1,1], [3], [5,2,3]].argmins List.length` ⇒ `#[[1], [3]]`
* `#[3, 1, 4, 1, 5].argmins id` ⇒ `#[1, 1]`
* `#[].argmins f` ⇒ `#[]`
-/
def argmins (a : Array α) (f : α → β) : Array α :=
  match a[0]? with
  | some x => a[1:].foldl (argminsAux f) (#[x], f x) |>.1
  | none   => #[]
where
  /-- An auxiliary function for `argmins` which represents a step in processing the input array. It
  maintains an accumulated array of minimal elements and the minimum value encountered so far. -/
  argminsAux (f : α → β) : Array α × β → α → Array α × β
  | (minimals, minVal), x =>
    let fx := f x
    match compare minVal fx with
    | .lt => (minimals, minVal)
    | .eq => (minimals.push x, minVal)
    | .gt => (#[x], fx)

end Ord
