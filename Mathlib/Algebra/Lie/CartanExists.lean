/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Mathlib.Algebra.Lie.EngelSubalgebra
import Mathlib.Algebra.Lie.Rank

namespace LieAlgebra

section CommRing

variable {R L M : Type*}
variable [Field R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [Module.Finite R L] [Module.Free R L]
variable [Module.Finite R M] [Module.Free R M]

open FiniteDimensional Module.Free Polynomial

namespace engel_le_engel

variable (x y : L)

variable (R M)

noncomputable
def lieCharpoly₁ : Polynomial R[X] :=
  letI bL := chooseBasis R L
  letI bM := chooseBasis R M
  (lieCharpoly bL bM).map <| RingHomClass.toRingHom <|
    MvPolynomial.aeval fun i ↦ C (bL.repr y i) * X + C (bL.repr x i)

lemma lieCharpoly₁_monic : (lieCharpoly₁ R M x y).Monic :=
  (lieCharpoly_monic _ _).map _

lemma lieCharpoly₁_natDegree : (lieCharpoly₁ R M x y).natDegree = finrank R M := by
    rw [lieCharpoly₁, (lieCharpoly_monic _ _).natDegree_map, lieCharpoly_natDegree,
      finrank_eq_card_chooseBasisIndex]

end engel_le_engel

end CommRing

section Field

variable {K L : Type*}
variable [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]

open FiniteDimensional LieSubalgebra Module.Free Polynomial

open LieSubalgebra Polynomial in
lemma engel_le_engel (U : LieSubalgebra K L) (x : L) (hx : x ∈ U) (hUx : U ≤ engel K x)
    (hmin : ∀ y : L, y ∈ U → engel K y ≤ engel K x → engel K y = engel K x)
    (y : L) (hy : y ∈ U) :
    engel K x ≤ engel K y := by
  -- let E : LieSubmodule K U L :=
  -- { engel K x with
  --   lie_mem := by rintro ⟨u, hu⟩ y hy; exact (engel K x).lie_mem (hUx hu) hy }
  -- let Q := L ⧸ E
  -- let BU := chooseBasis K U
  -- let BE := chooseBasis K E
  -- let BQ := chooseBasis K Q
  -- let r := finrank K E
  -- let χ : U → Polynomial (K[X]) := fun u₁ ↦
  --   (lieCharpoly BU BE).map (MvPolynomial.aeval fun i ↦
  --     C (BU.repr ⟨x, hx⟩ i) + C (BU.repr u₁ i) * X).toRingHom
  -- let ψ : U → Polynomial (K[X]) := fun u₁ ↦
  --   (lieCharpoly BU BQ).map (MvPolynomial.aeval fun i ↦
  --     C (BU.repr ⟨x, hx⟩ i) + C (BU.repr u₁ i) * X).toRingHom
  sorry

end Field

end LieAlgebra
