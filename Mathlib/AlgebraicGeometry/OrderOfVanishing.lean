/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# Order of vanishing in a scheme

In this file we define the order of vanishing of an element of the function field of a locally
Noetherian integral scheme at a point of codimension `1`.
-/

@[expose] public section

open WithZero AlgebraicGeometry Order TopologicalSpace CategoryTheory

universe u

variable {X : Scheme.{u}}

namespace AlgebraicGeometry
namespace Scheme

lemma krullDimLE_of_coheight
    {Z : X} {n : ℕ} (hZ : coheight Z = n) : Ring.KrullDimLE n (X.presheaf.stalk Z) := by
  rw [Ring.krullDimLE_iff, ringKrullDim_stalk_eq_coheight Z]
  exact_mod_cast hZ.le

variable [IsIntegral X]

/--
For `f` an element of the function field of `X`, there exists some open set `U ⊆ X` such that
`f` is a unit in `Γ(X, U)`.
-/
lemma exists_isUnit_germ_eq (f : X.functionField) (hf : f ≠ 0) :
    ∃ U : X.Opens, ∃ f' : Γ(X, U), ∃ _ : Nonempty U,
    X.germToFunctionField U f' = f ∧ IsUnit f' := by
  obtain ⟨U, hU, g, hg⟩ := TopCat.Presheaf.germ_exist _ _ f
  have : Nonempty U := ⟨_, hU⟩
  have : Nonempty (X.basicOpen g) := by
    rw [Scheme.Opens.nonempty_iff]
    apply (Opens.ne_bot_iff_nonempty (X.basicOpen g)).mp
    intro a
    simp_all
  refine ⟨X.basicOpen g, X.presheaf.map (X.basicOpen_le g).hom.op g, ‹_›, ?_,
    X.toRingedSpace.isUnit_res_basicOpen g⟩
  rw [germToFunctionField_map, hg]

variable [IsLocallyNoetherian X]

/--
On a locally Noetherian integral scheme, we define the order of vanishing of an element of the
function field `f` at a point `Z` of codimension `1` to be `Ring.ordFrac (X.presheaf.stalk Z) f`.
Because of this definition, `Scheme.ord` is valued in `ℤᵐ⁰`.
-/
noncomputable
def ord (Z : X) (hZ : coheight Z = 1) : X.functionField →*₀ ℤᵐ⁰ :=
  have : Ring.KrullDimLE 1 _ := krullDimLE_of_coheight hZ
  Ring.ordFrac (X.presheaf.stalk Z)

/--
The order of vanishing of a non-zero element of the function field at any point is not zero. Since
`Scheme.ord` is valued in `ℤᵐ⁰`, `0` does not denote a value of `ℤ` but an added `⊥` element.
-/
lemma ord_ne_zero {Z : X} (hZ : coheight Z = 1) {f : X.functionField} (hf : f ≠ 0) :
    Scheme.ord Z hZ f ≠ 0 := (map_ne_zero (Scheme.ord Z hZ)).mpr hf

/--
The order of vanishing of a unit is `1` everywhere.
-/
lemma ord_of_isUnit {U : X.Opens}
    [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f) {x : X} (hx : coheight x = 1) (hx' : x ∈ U) :
    Scheme.ord x hx (X.germToFunctionField U f) = 1 := by
  have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk x) := krullDimLE_of_coheight hx
  rw [germToFunctionField_eq_algebraMap_germ hx']
  exact Ring.ordFrac_of_isUnit (hf.map (X.presheaf.germ U x hx').hom)

end Scheme
end AlgebraicGeometry
