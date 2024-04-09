/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Std.Data.Rat.Basic

/-!
# Datatypes for Simplex Algorithm implementation
-/

namespace Linarith.SimplexAlgo

/--
Structure for matrices over ℚ.

So far it is just a 2d-array carrying dimensions (that supposed to coincide with the actual
dimensions of `data`), but the plan is to add some `Prop`-data and make the structure strict and
safe.

Note: we avoid using the `Matrix` because it is far more efficient to store matrix as its
entries than function between `Fin`-s.
-/
structure Matrix (n m : Nat) where
  /-- The content of the matrix. -/
  data : Array (Array Rat)
  -- hn_pos : n > 0
  -- hm_pos : m > 0
  -- hn : data.size = n
  -- hm (i : Fin n) : data[i].size = m
deriving Repr

instance (n m : Nat) : GetElem (Matrix n m) Nat (Array Rat) fun _ i => i < n where
  getElem mat i _ := mat.data[i]!

/--
`Table` is a structure Simplex Algorithm operates on. The `i`-th row of `mat` expresses the
variable `bound[i]` as a linear combination of variables from `free`.
-/
structure Table where
  /-- Array containing the basic variables' indexes -/
  basic : Array Nat
  /-- Array containig the free variables' indexes -/
  free : Array Nat
  /-- Matrix of coefficients the basic variables expressed through the free ones. -/
  mat : Matrix basic.size free.size

end Linarith.SimplexAlgo
