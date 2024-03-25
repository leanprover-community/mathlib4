/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.IntermediateField
import Mathlib.Algebra.CharP.ExpChar

/-!

# Characteristic of intermediate fields

This file contains some convenient instances for determining the characteristic of
intermediate fields. Some char zero instances are not provided, since they are already
covered by `SubsemiringClass.instCharZero`.

-/

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

namespace Subfield

variable (L : Subfield F) (p : ℕ)

instance charP [CharP F p] : CharP L p := fast_instance% RingHom.charP _ (algebraMap _ F).injective p

instance expChar [ExpChar F p] : ExpChar L p := fast_instance% RingHom.expChar _ (algebraMap _ F).injective p

end Subfield

namespace IntermediateField

variable (L : IntermediateField F E) (p : ℕ)

instance charZero [CharZero F] : CharZero L := fast_instance%
  charZero_of_injective_algebraMap (algebraMap F _).injective

instance charP [CharP F p] : CharP L p := fast_instance%
  charP_of_injective_algebraMap (algebraMap F _).injective p

instance expChar [ExpChar F p] : ExpChar L p := fast_instance%
  expChar_of_injective_algebraMap (algebraMap F _).injective p

instance charP' [CharP E p] : CharP L p := fast_instance% Subfield.charP L.toSubfield p

instance expChar' [ExpChar E p] : ExpChar L p := fast_instance% Subfield.expChar L.toSubfield p

end IntermediateField
