/-
Copyright (c) 2023 Wen Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wen Yang
-/
import Mathlib.Data.Set.Function

/-!
# APIs For `Function.extend`

## Tags

extend
-/

set_option autoImplicit true
open Function Set
variable {α : Sort u} (f : α → β) (g : α → γ) (e' : β → γ)

namespace Function

/-! ### Properties of `extend f g e'` when `f` is injective -/
section injective

variable (hf_i : Injective f)

theorem Injective.extend_image_eq : range g = (extend f g e') '' (range f) := by
  ext x
  simp [hf_i.extend_apply]

theorem Injective.extend_injOn : Injective g ↔ InjOn (extend f g e') (range f) := by
  rw [@injOn_iff_injective]
  unfold Injective
  simp [hf_i.extend_apply, hf_i.eq_iff]

theorem Injective.extend_surjOn : Surjective g ↔ SurjOn (extend f g e') (range f) univ := by
  rw [@surjOn_iff_surjective]
  unfold Surjective
  simp [hf_i.extend_apply, hf_i.eq_iff]

theorem Injective.extend_bijOn : Bijective g ↔ BijOn (extend f g e') (range f) univ := by
  unfold Bijective BijOn
  rw [← hf_i.extend_injOn, ← hf_i.extend_surjOn]
  simp only [iff_and_self, and_imp]
  exact fun _ _ ↦ mapsTo_univ (extend f g e') (range f)

end injective

end Function
