/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.OrderOfVanishing.Properties

/-!
# Order of vansihing in a scheme

In this file we define the order of vanishing of an element of the function field of a locally
Noetherian integral scheme at a point of codimension `1`.
-/

open Multiplicative WithZero AlgebraicGeometry Order TopologicalSpace CategoryTheory

universe u

variable {X : Scheme.{u}}

namespace AlgebraicGeometry
namespace Scheme

/--
This instance seems to not be picked up very easily by the type inference algorithm without further
coaxing.
-/
lemma krullDimLE_of_coheight
    {Z : X} {n : ℕ} (hZ : Order.coheight Z = n) : Ring.KrullDimLE n (X.presheaf.stalk Z) := by
  rw [Ring.krullDimLE_iff, AlgebraicGeometry.stalk_dim_eq_coheight Z, hZ]
  rfl

variable [IsIntegral X]

/--
For `f` an element of the function field of `X`, there exists some open set `U ⊆ X` such that
`f` is a unit in `Γ(X, U)`.
-/
lemma functionField_exists_unit_nhd
    (f : X.functionField) (hf : f ≠ 0) :
    ∃ U : X.Opens, ∃ f' : Γ(X, U), ∃ _ :
    Nonempty U, X.germToFunctionField U f' = f ∧ IsUnit f' := by
  obtain ⟨U, hU, g, hg⟩ := TopCat.Presheaf.germ_exist _ _ f
  refine ⟨AlgebraicGeometry.Scheme.basicOpen X g,
    TopCat.Presheaf.restrict g (AlgebraicGeometry.Scheme.basicOpen_le X g).hom, ?_⟩
  have : Nonempty (X.basicOpen g) := by
    have := basicOpen_eq_bot_iff g
    simp only [Scheme.Opens.nonempty_iff]
    suffices ¬ X.basicOpen g = ⊥ by exact
      (Opens.ne_bot_iff_nonempty (X.basicOpen g)).mp this
    aesop
  use this
  have := TopCat.Presheaf.germ_res X.presheaf (Scheme.basicOpen_le X g).hom
    (genericPoint X) (Scheme.germToFunctionField._proof_1 X (X.basicOpen g))
  exact ⟨hg ▸ this ▸ rfl, AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen X.toRingedSpace g⟩

variable [IsLocallyNoetherian X]

/--
On a locally noetherian integral scheme, we define the order of vanishing of an element of the
function field `f` at a point `Z` of codimension `1` to be `Ring.ordFrac (X.presheaf.stalk Z) f`.
Because of this definition, `Scheme.ord` is valued in `ℤᵐ⁰`.
-/
noncomputable
def ord [IsLocallyNoetherian X]
    (Z : X) (hZ : Order.coheight Z = 1) : X.functionField →*₀ ℤᵐ⁰ :=
  have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk Z) := krullDimLE_of_coheight hZ
  Ring.ordFrac (X.presheaf.stalk Z)

/--
The order of vanishing of a non-zero element of the function field at any point is not zero. Since
`Scheme.ord` is valued in `ℤᵐ⁰`, `0` does not denote a value of `ℤ` but an added `⊥` element.
-/
lemma ord_ne_zero {Z : X} (hZ : Order.coheight Z = 1)
    {f : X.functionField} (hf : f ≠ 0) :
  Scheme.ord Z hZ f ≠ 0 := (map_ne_zero (Scheme.ord Z hZ)).mpr hf

/--
The order of vanishing of a unit is `1` everywhere.
-/
lemma ord_of_isUnit (U : X.Opens)
    [Nonempty U] (f : Γ(X, U)) (hf : IsUnit f) (x : X) (hx : coheight x = 1) (hx' : x ∈ U) :
    Scheme.ord x hx (X.germToFunctionField U f) = 1 := by
  have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk x) := krullDimLE_of_coheight hx
  have : IsUnit <| X.presheaf.germ U x hx' f :=
    RingHom.isUnit_map (ConcreteCategory.hom (X.presheaf.germ U x hx')
      : ↑(X.presheaf.obj (Opposite.op U)) →+* ↑(X.presheaf.stalk x)) hf
  have := ordFrac_of_isUnit (K := X.functionField) (X.presheaf.germ U x hx' f) this
  rw[← this]
  simp[Scheme.ord]
  congr 1
  simp [Scheme.germToFunctionField]
  have : genericPoint X ⤳ x := genericPoint_specializes x
  rw [← TopCat.Presheaf.germ_stalkSpecializes X.presheaf hx' this]
  rfl

end Scheme
end AlgebraicGeometry
