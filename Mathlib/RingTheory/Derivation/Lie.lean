/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Andrew Yang
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Lie Algebra Structure on Derivations

## Main statements

- `Derivation.instLieAlgebra`: The `R`-derivations from `A` to `A` form a Lie algebra over `R`.

-/

@[expose] public section


namespace Derivation

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {D1 D2 : Derivation R A A} (a : A)

section LieStructures

/-! ### Lie structures -/


/-- The commutator of derivations is again a derivation. -/
instance : Bracket (Derivation R A A) (Derivation R A A) :=
  ⟨fun D1 D2 =>
    mk' ⁅(D1 : Module.End R A), (D2 : Module.End R A)⁆ fun a b => by
      simp only [Ring.lie_def, map_add, smul_eq_mul, Module.End.mul_apply, leibniz,
        coeFn_coe, LinearMap.sub_apply]
      ring⟩

@[simp]
theorem commutator_coe_linear_map : ↑⁅D1, D2⁆ = ⁅(D1 : Module.End R A), (D2 : Module.End R A)⁆ :=
  rfl

theorem commutator_apply : ⁅D1, D2⁆ a = D1 (D2 a) - D2 (D1 a) :=
  rfl

instance : LieRing (Derivation R A A) where
  add_lie d e f := by ext a; simp only [commutator_apply, add_apply, map_add]; ring
  lie_add d e f := by ext a; simp only [commutator_apply, add_apply, map_add]; ring
  lie_self d := by ext a; simp only [commutator_apply]; ring_nf; simp
  leibniz_lie d e f := by ext a; simp only [commutator_apply, add_apply, map_sub]; ring

instance instLieAlgebra : LieAlgebra R (Derivation R A A) :=
  { Derivation.instModule with
    lie_smul := fun r d e => by
      ext a; simp only [commutator_apply, map_smul, smul_sub, smul_apply] }

instance : LieRingModule (Derivation R A A) A where
  bracket X a := X a
  add_lie _ _ m := add_apply m
  lie_add _ _ _ := Derivation.map_add _ _ _
  leibniz_lie _ _ _ := by rw [commutator_apply]; abel

instance : LieModule R (Derivation R A A) A where
  smul_lie _ _ _ := rfl
  lie_smul _ _ _ := Derivation.map_smul_of_tower _ _ _

@[simp]
lemma bracket_eq_fun (X : Derivation R A A) (a : A) : ⁅X, a⁆ = X a := rfl

end LieStructures

end Derivation
