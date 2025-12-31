/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Jireh Loreaux
-/
module

public import Mathlib.Algebra.Divisibility.Hom
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Set.Insert

/-!
# Additional lemmas about homomorphisms of semirings and rings

These lemmas were in `Mathlib/Algebra/Ring/Hom/Defs.lean` and have now been deprecated.
-/

@[expose] public section

assert_not_exists RelIso Field

open Function

variable {α β : Type*}

namespace RingHom

section

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α →+* β)

end

section Semiring

variable [Semiring α] [Semiring β]
end Semiring

end RingHom
