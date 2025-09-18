import Mathlib

/-!
# Order of vansihing in a scheme

In this file we define the order of vanishing of an element of the function field of a locally
Noetherian integral scheme at a point of codimension `1`.
-/


open Multiplicative WithZero AlgebraicGeometry Order

/--
This instance seems to not be picked up very easily by the type inference algorithm without further
coaxing.
-/
lemma krullDimLE_of_coheight {X : Scheme} [IsIntegral X]
    {Z : X} {n : ℕ} (hZ : Order.coheight Z = n) : Ring.KrullDimLE n (X.presheaf.stalk Z) := by
  rw [Ring.krullDimLE_iff, AlgebraicGeometry.stalk_dim_eq_coheight Z, hZ]
  rfl

/--
On a locally noetherian integral scheme, we define the order of vanishing of an element of the
function field `f` at a point `Z` of codimension `1` to be `Ring.ordFrac (X.presheaf.stalk Z) f`.
Because of this definition, `Scheme.ord` is valued in `ℤᵐ⁰`.
-/
noncomputable
def _root_.AlgebraicGeometry.Scheme.ord {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (Z : X) (hZ : Order.coheight Z = 1) : X.functionField →*₀ ℤᵐ⁰ :=
  have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk Z) := krullDimLE_of_coheight hZ
  Ring.ordFrac (X.presheaf.stalk Z)
