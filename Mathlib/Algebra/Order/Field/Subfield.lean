/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Algebra.Order.Field.InjSurj
import Mathlib.Algebra.Field.Subfield.Defs

/-!
# Ordered instances on subfields
-/

namespace SubfieldClass
variable {K S : Type*} [SetLike S K]

-- Prefer subclasses of `Field` over subclasses of `SubfieldClass`.
/-- A subfield of a `LinearOrderedField` is a `LinearOrderedField`. -/
instance (priority := 75) toLinearOrderedField [LinearOrderedField K]
    [SubfieldClass S K] (s : S) : LinearOrderedField s :=
  Subtype.coe_injective.linearOrderedField Subtype.val rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (by intros; rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (by intros; rfl) (fun _ _ => rfl) fun _ _ => rfl

end SubfieldClass

namespace Subfield
variable {K : Type*}

/-- A subfield of a `LinearOrderedField` is a `LinearOrderedField`. -/
instance toLinearOrderedField [LinearOrderedField K] (s : Subfield K) : LinearOrderedField s :=
  Subtype.coe_injective.linearOrderedField Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (by intros; rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (by intros; rfl) (fun _ _ => rfl) fun _ _ => rfl

end Subfield
