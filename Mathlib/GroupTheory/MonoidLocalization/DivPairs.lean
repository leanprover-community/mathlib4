/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Mathlib.GroupTheory.MonoidLocalization.Basic

/-!
# Submonoid of pairs with quotient in a submonoid

This file defines the submonoid of pairs whose quotient lies in a submonoid of the localization.
-/

variable {M G H : Type*} [CommMonoid M] [CommGroup G] [CommGroup H]
  {f : (⊤ : Submonoid M).LocalizationMap G} {g : (⊤ : Submonoid M).LocalizationMap H}
  {s : Submonoid G} {x : M × M}

namespace Submonoid

variable (f s) in
/-- Given a commutative monoid `M`, a localization map `f` to its Grothendieck group `G` and
a submonoid `s` of `G`, `s.divPairs f` is the submonoid of pairs `(a, b)`
such that `f a / f b ∈ s`. -/
@[to_additive
"Given an additive commutative monoid `M`, a localization map `f` to its Grothendieck group `G` and
a submonoid `s` of `G`, `s.subPairs f` is the submonoid of pairs `(a, b)`
such that `f a - f b ∈ s`."]
def divPairs : Submonoid (M × M) := s.comap <| divMonoidHom.comp <| f.toMap.prodMap f.toMap

@[to_additive (attr := simp)]
lemma mem_divPairs : x ∈ divPairs f s ↔ f.toMap x.1 / f.toMap x.2 ∈ s := .rfl

--TODO(Yaël): make simp once `LocalizationMap.toMonoidHom` is simp nf
variable (f g s) in
@[to_additive]
lemma divPairs_comap :
    divPairs g (.comap (g.mulEquivOfLocalizations f).toMonoidHom s) = divPairs f s := by
  ext; simp

end Submonoid
