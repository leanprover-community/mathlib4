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

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (Z : Set X) (hZ : Z ∈ irreducibleComponents X) [IsNoetherian X]

/-- The complement of the irreducible components unequal to `Z` of a Noetherian scheme. -/
def irreducibleComponentOpen : Opens X :=
  ⟨(⋃₀ (irreducibleComponents X \ {Z}))ᶜ, by
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.diff.isClosed_biUnion
      fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1⟩

/-- The ideal sheaf data associated to an irreducible component of a Noetherian scheme. -/
def irreducibleComponentIdeal : X.IdealSheafData where
  __ := (irreducibleComponentOpen X Z).ι.ker
  supportSet := Z
  supportSet_eq_iInter_zeroLocus := by
    rw [← IdealSheafData.coe_support_eq_eq_iInter_zeroLocus, Hom.support_ker, Opens.range_ι]
    exact (closure_sUnion_irreducibleComponents_diff_singleton
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents Z hZ).symm

theorem irreducibleComponentIdeal_def :
    irreducibleComponentIdeal X Z hZ = (irreducibleComponentOpen X Z).ι.ker := by
  ext
  rfl

/-- The subscheme structure on an irreducible component of a Noetherian scheme. -/
noncomputable def irreducibleComponent : Scheme :=
  (X.irreducibleComponentIdeal Z hZ).subscheme

/-- The inclusion from an irreducible component of a Noetherian scheme. -/
noncomputable def irreducibleComponentι : X.irreducibleComponent Z hZ ⟶ X :=
  (X.irreducibleComponentIdeal Z hZ).subschemeι

lemma irreducibleComponentι_apply (x : X.irreducibleComponent Z hZ) :
    X.irreducibleComponentι Z hZ x = x.1 :=
  rfl

instance : IsClosedImmersion (X.irreducibleComponentι Z hZ) :=
  inferInstanceAs (IsClosedImmersion (X.irreducibleComponentIdeal Z hZ).subschemeι)

instance : IrreducibleSpace (X.irreducibleComponent Z hZ) :=
  Subtype.irreducibleSpace hZ.1

include hZ in
theorem irreducibleComponentOpen_eq_top [IrreducibleSpace X] :
    irreducibleComponentOpen X Z = ⊤ := by
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
  simp [irreducibleComponentOpen, irreducibleComponents_eq_singleton, hZ]

instance [IrreducibleSpace X] : CategoryTheory.IsIso (X.irreducibleComponentι Z hZ) := by
  have : CategoryTheory.IsIso (irreducibleComponentOpen X Z).ι := by
    rw [irreducibleComponentOpen_eq_top X Z hZ]
    exact X.topIso.isIso_hom
  rw [irreducibleComponentι, isIso_subschemeι_iff_eq_bot, irreducibleComponentIdeal_def,
    irreducibleComponentOpen_eq_top X Z hZ]
  exact X.topIso.hom.ker_eq_bot_of_isIso

end AlgebraicGeometry.Scheme
