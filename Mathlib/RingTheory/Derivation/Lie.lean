/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Andrew Yang
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.Derivation.Basic

#align_import ring_theory.derivation.lie from "leanprover-community/mathlib"@"b608348ffaeb7f557f2fd46876037abafd326ff3"

/-!
# Results

- `Derivation.instLieAlgebra`: The `R`-derivations from `A` to `A` form a Lie algebra over `R`.

-/


namespace Derivation

variable {R : Type*} [CommRing R]

variable {A : Type*} [CommRing A] [Algebra R A]

variable (D : Derivation R A A) {D1 D2 : Derivation R A A} (a : A)

section LieStructures

/-! # Lie structures -/


/-- The commutator of derivations is again a derivation. -/
instance : Bracket (Derivation R A A) (Derivation R A A) :=
  ⟨fun D1 D2 =>
    mk' ⁅(D1 : Module.End R A), (D2 : Module.End R A)⁆ fun a b => by
      simp only [Ring.lie_def, map_add, Algebra.id.smul_eq_mul, LinearMap.mul_apply, leibniz,
        coeFn_coe, LinearMap.sub_apply]
      ring⟩
      -- 🎉 no goals

@[simp]
theorem commutator_coe_linear_map : ↑⁅D1, D2⁆ = ⁅(D1 : Module.End R A), (D2 : Module.End R A)⁆ :=
  rfl
#align derivation.commutator_coe_linear_map Derivation.commutator_coe_linear_map

theorem commutator_apply : ⁅D1, D2⁆ a = D1 (D2 a) - D2 (D1 a) :=
  rfl
#align derivation.commutator_apply Derivation.commutator_apply

instance : LieRing (Derivation R A A) where
  add_lie d e f := by ext a; simp only [commutator_apply, add_apply, map_add]; ring
                      -- ⊢ ↑⁅d + e, f⁆ a = ↑(⁅d, f⁆ + ⁅e, f⁆) a
                             -- ⊢ ↑d (↑f a) + ↑e (↑f a) - (↑f (↑d a) + ↑f (↑e a)) = ↑d (↑f a) - ↑f (↑d a) + (↑ …
                                                                               -- 🎉 no goals
  lie_add d e f := by ext a; simp only [commutator_apply, add_apply, map_add]; ring
                      -- ⊢ ↑⁅d, e + f⁆ a = ↑(⁅d, e⁆ + ⁅d, f⁆) a
                             -- ⊢ ↑d (↑e a) + ↑d (↑f a) - (↑e (↑d a) + ↑f (↑d a)) = ↑d (↑e a) - ↑e (↑d a) + (↑ …
                                                                               -- 🎉 no goals
  lie_self d := by ext a; simp only [commutator_apply, add_apply, map_add]; ring_nf; simp
                   -- ⊢ ↑⁅d, d⁆ a = ↑0 a
                          -- ⊢ ↑d (↑d a) - ↑d (↑d a) = ↑0 a
                                                                            -- ⊢ 0 = ↑0 a
                                                                                     -- 🎉 no goals
  leibniz_lie d e f := by ext a; simp only [commutator_apply, add_apply, sub_apply, map_sub]; ring
                          -- ⊢ ↑⁅d, ⁅e, f⁆⁆ a = ↑(⁅⁅d, e⁆, f⁆ + ⁅e, ⁅d, f⁆⁆) a
                                 -- ⊢ ↑d (↑e (↑f a)) - ↑d (↑f (↑e a)) - (↑e (↑f (↑d a)) - ↑f (↑e (↑d a))) = ↑d (↑e …
                                                                                              -- 🎉 no goals

instance instLieAlgebra: LieAlgebra R (Derivation R A A) :=
  { Derivation.instModule with
    lie_smul := fun r d e => by
      ext a; simp only [commutator_apply, map_smul, smul_sub, smul_apply] }
      -- ⊢ ↑⁅d, r • e⁆ a = ↑(r • ⁅d, e⁆) a
             -- 🎉 no goals

end LieStructures

end Derivation
