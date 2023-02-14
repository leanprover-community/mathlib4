/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best

! This file was ported from Lean 3 source module data.finsupp.fintype
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic

/-!

# Finiteness and infiniteness of `Finsupp`

Some lemmas on the combination of `Finsupp`, `Fintype` and `Infinite`.

-/


noncomputable instance Finsupp.fintype {ι π : Sort _} [DecidableEq ι] [Zero π] [Fintype ι]
    [Fintype π] : Fintype (ι →₀ π) :=
  Fintype.ofEquiv _ Finsupp.equivFunOnFinite.symm
#align finsupp.fintype Finsupp.fintype

instance Finsupp.infinite_of_left {ι π : Sort _} [Nontrivial π] [Zero π] [Infinite ι] :
    Infinite (ι →₀ π) :=
  let ⟨_, hm⟩ := exists_ne (0 : π)
  Infinite.of_injective _ <| Finsupp.single_left_injective hm
#align finsupp.infinite_of_left Finsupp.infinite_of_left

instance Finsupp.infinite_of_right {ι π : Sort _} [Infinite π] [Zero π] [Nonempty ι] :
    Infinite (ι →₀ π) :=
  Infinite.of_injective (fun i => Finsupp.single (Classical.arbitrary ι) i)
    (Finsupp.single_injective (Classical.arbitrary ι))
#align finsupp.infinite_of_right Finsupp.infinite_of_right
