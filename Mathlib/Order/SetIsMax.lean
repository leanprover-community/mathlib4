/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Order.Max
import Mathlib.Data.Set.CoeSort

/-!
# Maximum of a subset

Let `S : Set J` and `m : S`. If `m` is not the maximum of `S`,
then `↑m : J` is not the maxium of `J`.

-/

universe u

namespace Set

variable {J : Type u} [Preorder J] {S : Set J} (m : S)

lemma not_isMax_coe (hm : ¬ IsMax m) :
    ¬ IsMax m.1 :=
  fun h ↦ hm (fun _ hb ↦ h hb)

lemma not_isMin_coe {S : Set J} (m : S) (hm : ¬ IsMin m) :
    ¬ IsMin m.1 :=
  fun h ↦ hm (fun _ hb ↦ h hb)

end Set
