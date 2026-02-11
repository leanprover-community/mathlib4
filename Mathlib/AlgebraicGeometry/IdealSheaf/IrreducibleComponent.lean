/-
Copyright (c) 2026 Thomas Browning, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Subscheme structure on an irreducible component

We define the subscheme structure on an irreducible component of a Noetherian scheme. Typically,
one takes the reduced induced subscheme structure, but this will throw away information if the
irreducible component is not already reduced. Instead, we take the closed subscheme defined by
the kernel of the restriction to the complement of the union of the other irreducible components.
For example, if `X` is irreducible then this will give back the original scheme `X`.

## Main definition
* `AlgebraicGeometry.Scheme.irreducibleComponentIdeal`: The ideal sheaf data associated to an
  irreducible component of a Noetherian scheme.
* `AlgebraicGeometry.Scheme.irreducibleComponent`: The subscheme structure on an irreducible
  component of a Noetherian scheme.

## TODO

Prove that for affine schemes this subscheme structure is defined by the kernel of the
localization away from the union of the other minimal prime ideals.

-/

@[expose] public section

namespace AlgebraicGeometry.Scheme

variable (X : Scheme) (Z : Set X) (hZ : Z ∈ irreducibleComponents X) [IsNoetherian X]

/-- The ideal sheaf data associated to an irreducible component of a Noetherian scheme. -/
def irreducibleComponentIdeal : X.IdealSheafData where
  __ := AlgebraicGeometry.Scheme.Hom.ker <| Opens.ι ⟨(⋃₀ (irreducibleComponents X \ {Z}))ᶜ, by
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.diff.isClosed_biUnion
      fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1⟩
  supportSet := Z
  supportSet_eq_iInter_zeroLocus := by
    rw [← IdealSheafData.coe_support_eq_eq_iInter_zeroLocus, Hom.support_ker, Opens.range_ι]
    exact (closure_sUnion_irreducibleComponents_diff_singleton
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents Z hZ).symm

/-- The subscheme structure on an irreducible component of a Noetherian scheme. -/
noncomputable def irreducibleComponent : Scheme :=
  (X.irreducibleComponentIdeal Z hZ).subscheme

noncomputable def irreducibleComponentι : X.irreducibleComponent Z hZ ⟶ X :=
  (X.irreducibleComponentIdeal Z hZ).subschemeι

lemma irreducibleComponentι_apply (x : X.irreducibleComponent Z hZ) :
    X.irreducibleComponentι Z hZ x = x.1 :=
  rfl

instance : IsClosedImmersion (X.irreducibleComponentι Z hZ) :=
  inferInstanceAs (IsClosedImmersion (X.irreducibleComponentIdeal Z hZ).subschemeι)

end AlgebraicGeometry.Scheme
