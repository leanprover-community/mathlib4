/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Order.DirectedInverseSystem
import Mathlib.Tactic.SuppressCompilation

/-!
# Direct limit of modules, abelian groups, rings, and fields.

We introduce all kinds of algebraic instances on `DirectLimit`,
and specialize to the case of modules, rings, and fields.

-/

suppress_compilation

variable {R ι : Type*} [Preorder ι] {G : ι → Type*}
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)] [DirectedSystem G (f · · ·)]
variable [IsDirected ι (· ≤ ·)]

namespace DirectLimit

section ZeroOne
variable [Nonempty ι] [∀ i, One (G i)]

@[to_additive] instance : One (DirectLimit G f) where
  one := fullRec₀ f fun _ ↦ 1

@[to_additive] theorem one_def [∀ i j h, OneHomClass (T h) (G i) (G j)] (i) :
    (1 : DirectLimit G f) = ⟦⟨i, 1⟩⟧ :=
  fullRec₀_spec _ _ (fun _ _ _ ↦ map_one _) _

end ZeroOne

section AddMul
variable [∀ i, Mul (G i)] [∀ i j h, MulHomClass (T h) (G i) (G j)]

@[to_additive] instance : Mul (DirectLimit G f) where
  mul := fullRec₂ f f f (fun _ ↦ (· * ·)) fun _ _ _ ↦ map_mul _

@[to_additive] theorem mul_def (i) (x y : G i) :
    ⟦⟨i, x⟩⟧ * ⟦⟨i, y⟩⟧ = (⟦⟨i, x * y⟩⟧ : DirectLimit G f) :=
  fullRec₂_spec ..

end AddMul

@[to_additive] instance [∀ i, Semigroup (G i)] [∀ i j h, MulHomClass (T h) (G i) (G j)] :
    Semigroup (DirectLimit G f) where
  mul_assoc := DirectLimit.induction₃ _ fun i _ _ _ ↦ by simp_rw [mul_def, mul_assoc]

@[to_additive] instance [∀ i, CommSemigroup (G i)] [∀ i j h, MulHomClass (T h) (G i) (G j)] :
    CommSemigroup (DirectLimit G f) where
  mul_comm := DirectLimit.induction₂ _ fun i _ _ ↦ by simp_rw [mul_def, mul_comm]

section SMul
variable [∀ i, SMul R (G i)] [∀ i j h, MulActionHomClass (T h) R (G i) (G j)]

@[to_additive] instance : SMul R (DirectLimit G f) where
  smul r := fullRec _ _ (fun _ ↦ (r • ·)) fun _ _ _ ↦ map_smul _ r

@[to_additive] theorem smul_def (i x) (r : R) : r • ⟦⟨i, x⟩⟧ = (⟦⟨i, r • x⟩⟧ : DirectLimit G f) :=
  rfl

end SMul

@[to_additive] instance [Monoid R] [∀ i, MulAction R (G i)]
    [∀ i j h, MulActionHomClass (T h) R (G i) (G j)] :
    MulAction R (DirectLimit G f) where
  one_smul := DirectLimit.induction _ fun i _ ↦ by rw [smul_def, one_smul]
  mul_smul _ _ := DirectLimit.induction _ fun i _ ↦ by simp_rw [smul_def, mul_smul]

variable [Nonempty ι]

@[to_additive] instance [∀ i, MulOneClass (G i)] [∀ i j h, MonoidHomClass (T h) (G i) (G j)] :
    MulOneClass (DirectLimit G f) where
  one_mul := DirectLimit.induction _ fun i _ ↦ by simp_rw [one_def i, mul_def, one_mul]
  mul_one := DirectLimit.induction _ fun i _ ↦ by simp_rw [one_def i, mul_def, mul_one]

section Monoid
variable [∀ i, Monoid (G i)] [∀ i j h, MonoidHomClass (T h) (G i) (G j)]

@[to_additive] instance : Monoid (DirectLimit G f) where
  one_mul := one_mul
  mul_one := mul_one
  npow n := fullRec _ _ (fun _ ↦ (· ^ n)) fun _ _ _ x ↦ map_pow _ x n
  npow_zero := DirectLimit.induction _ fun i _ ↦ by simp_rw [fullRec_spec, pow_zero, one_def i]
  npow_succ n := DirectLimit.induction _ fun i _ ↦ by simp_rw [fullRec_spec, pow_succ, mul_def]

@[to_additive] theorem npow_def (i x) (n : ℕ) : ⟦⟨i, x⟩⟧ ^ n = (⟦⟨i, x ^ n⟩⟧ : DirectLimit G f) :=
  rfl

end Monoid

@[to_additive] instance [∀ i, CommMonoid (G i)] [∀ i j h, MonoidHomClass (T h) (G i) (G j)] :
    CommMonoid (DirectLimit G f) where
  mul_comm := mul_comm

section Group
variable [∀ i, Group (G i)] [∀ i j h, MonoidHomClass (T h) (G i) (G j)]

@[to_additive] instance : Group (DirectLimit G f) where
  inv := fullRec _ _ (fun _ ↦ (·⁻¹)) fun _ _ _ ↦ map_inv _
  div := fullRec₂ _ _ _ (fun _ ↦ (· / ·)) fun _ _ _ ↦ map_div _
  zpow n := fullRec _ _ (fun _ ↦ (· ^ n)) fun _ _ _ x ↦ map_zpow _ x n
  div_eq_mul_inv := DirectLimit.induction₂ _ fun i _ _ ↦ show fullRec₂ .. = _ * fullRec .. by
    simp_rw [fullRec₂_spec, fullRec_spec, div_eq_mul_inv, mul_def]
  zpow_zero' := DirectLimit.induction _ fun i _ ↦ by simp_rw [fullRec_spec, zpow_zero, one_def i]
  zpow_succ' n := DirectLimit.induction _ fun i x ↦ by
    simp_rw [fullRec_spec, mul_def]; congr; apply DivInvMonoid.zpow_succ'
  zpow_neg' n := DirectLimit.induction _ fun i x ↦ by
    simp_rw [fullRec_spec]; congr; apply DivInvMonoid.zpow_neg'
  inv_mul_cancel := DirectLimit.induction _ fun i _ ↦ by
    simp_rw [fullRec_spec, mul_def, inv_mul_cancel, one_def i]

@[to_additive] theorem inv_def (i x) : (⟦⟨i, x⟩⟧)⁻¹ = (⟦⟨i, x⁻¹⟩⟧ : DirectLimit G f) := rfl

@[to_additive] theorem div_def (i x y) : ⟦⟨i, x⟩⟧ / ⟦⟨i, y⟩⟧ = (⟦⟨i, x / y⟩⟧ : DirectLimit G f) :=
  fullRec₂_spec ..

@[to_additive] theorem zpow_def (i x) (n : ℤ) : ⟦⟨i, x⟩⟧ ^ n = (⟦⟨i, x ^ n⟩⟧ : DirectLimit G f) :=
  rfl

end Group

instance [∀ i, MulZeroClass (G i)] [∀ i j h, MulHomClass (T h) (G i) (G j)]
    [∀ i j h, ZeroHomClass (T h) (G i) (G j)] :
    MulZeroClass (DirectLimit G f) where
  zero_mul := DirectLimit.induction _ fun i _ ↦ by simp_rw [zero_def i, mul_def, zero_mul]
  mul_zero := DirectLimit.induction _ fun i _ ↦ by simp_rw [zero_def i, mul_def, mul_zero]

section MulZeroOneClass

variable [∀ i, MulZeroOneClass (G i)] [∀ i j h, MonoidWithZeroHomClass (T h) (G i) (G j)]

instance : MulZeroOneClass (DirectLimit G f) where
  zero_mul := zero_mul
  mul_zero := mul_zero

instance [∀ i, Nontrivial (G i)] : Nontrivial (DirectLimit G f) where
  exists_pair_ne := ⟨0, 1, fun h ↦ have ⟨i, _, _, eq⟩ := Quotient.eq.mp h; by simp at eq⟩

end MulZeroOneClass

instance [∀ i, SemigroupWithZero (G i)] [∀ i j h, MulHomClass (T h) (G i) (G j)]
    [∀ i j h, ZeroHomClass (T h) (G i) (G j)] :
    SemigroupWithZero (DirectLimit G f) where
  zero_mul := zero_mul
  mul_zero := mul_zero

instance [∀ i, MonoidWithZero (G i)] [∀ i j h, MonoidWithZeroHomClass (T h) (G i) (G j)] :
    MonoidWithZero (DirectLimit G f) where
  zero_mul := zero_mul
  mul_zero := mul_zero

instance [∀ i, CommMonoidWithZero (G i)] [∀ i j h, MonoidWithZeroHomClass (T h) (G i) (G j)] :
    CommMonoidWithZero (DirectLimit G f) where
  zero_mul := zero_mul
  mul_zero := mul_zero

section GroupWithZero

variable [∀ i, GroupWithZero (G i)] [∀ i j h, MonoidWithZeroHomClass (T h) (G i) (G j)]

instance : GroupWithZero (DirectLimit G f) where
  inv := fullRec _ _ (fun _ ↦ (·⁻¹)) fun _ _ _ ↦ map_inv₀ _
  div := fullRec₂ _ _ _ (fun _ ↦ (· / ·)) fun _ _ _ ↦ map_div₀ _
  zpow n := fullRec _ _ (fun _ ↦ (· ^ n)) fun _ _ _ x ↦ map_zpow₀ _ x n
  div_eq_mul_inv := DirectLimit.induction₂ _ fun i _ _ ↦ show fullRec₂ .. = _ * fullRec .. by
    simp_rw [fullRec₂_spec, fullRec_spec, div_eq_mul_inv, mul_def]
  zpow_zero' := DirectLimit.induction _ fun i _ ↦ by simp_rw [fullRec_spec, zpow_zero, one_def i]
  zpow_succ' n := DirectLimit.induction _ fun i x ↦ by
    simp_rw [fullRec_spec, mul_def]; congr; apply DivInvMonoid.zpow_succ'
  zpow_neg' n := DirectLimit.induction _ fun i x ↦ by
    simp_rw [fullRec_spec]; congr; apply DivInvMonoid.zpow_neg'
  inv_zero := show ⟦_⟧ = ⟦_⟧ by simp_rw [inv_zero]
  mul_inv_cancel := DirectLimit.induction _ fun i x ne ↦ by
    have : x ≠ 0 := by rintro rfl; exact ne (zero_def i).symm
    simp_rw [fullRec_spec, mul_def, mul_inv_cancel₀ this, one_def i]

theorem inv₀_def (i x) : (⟦⟨i, x⟩⟧)⁻¹ = (⟦⟨i, x⁻¹⟩⟧ : DirectLimit G f) := rfl

theorem div₀_def (i x y) : ⟦⟨i, x⟩⟧ / ⟦⟨i, y⟩⟧ = (⟦⟨i, x / y⟩⟧ : DirectLimit G f) :=
  fullRec₂_spec ..

theorem zpow₀_def (i x) (n : ℤ) : ⟦⟨i, x⟩⟧ ^ n = (⟦⟨i, x ^ n⟩⟧ : DirectLimit G f) := rfl

end GroupWithZero

instance [∀ i, CommGroupWithZero (G i)] [∀ i j h, MonoidWithZeroHomClass (T h) (G i) (G j)] :
    CommGroupWithZero (DirectLimit G f) where
  __ : GroupWithZero _ := inferInstance
  mul_comm := mul_comm

section AddMonoidWithOne

variable [∀ i, AddMonoidWithOne (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]

instance : AddMonoidWithOne (DirectLimit G f) where
  natCast n := fullRec₀ _ fun _ ↦ n
  natCast_zero := show ⟦_⟧ = ⟦_⟧ by simp_rw [Nat.cast_zero]
  natCast_succ n := show ⟦_⟧ = ⟦_⟧ + ⟦_⟧ by simp_rw [Nat.cast_succ, add_def]

theorem natCast_def [∀ i j h, OneHomClass (T h) (G i) (G j)] (n : ℕ) (i) :
    (n : DirectLimit G f) = ⟦⟨i, n⟩⟧ :=
  fullRec₀_spec _ _ (fun _ _ _ ↦ map_natCast' _ (map_one _) _) _

end AddMonoidWithOne

section AddGroupWithOne

variable [∀ i, AddGroupWithOne (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]

instance : AddGroupWithOne (DirectLimit G f) where
  __ : AddGroup _ := inferInstance
  intCast n := fullRec₀ _ fun _ ↦ n
  intCast_ofNat n := show ⟦_⟧ = ⟦_⟧ by simp_rw [Int.cast_natCast]
  intCast_negSucc n := show ⟦_⟧ = ⟦_⟧ by simp
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ

theorem intCast_def [∀ i j h, OneHomClass (T h) (G i) (G j)] (n : ℤ) (i) :
    (n : DirectLimit G f) = ⟦⟨i, n⟩⟧ :=
  fullRec₀_spec _ _ (fun _ _ _ ↦ map_intCast' _ (map_one _) _) _

end AddGroupWithOne

instance [∀ i, AddCommMonoidWithOne (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)] :
    AddCommMonoidWithOne (DirectLimit G f) where
  add_comm := add_comm

instance [∀ i, AddCommGroupWithOne (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)] :
    AddCommGroupWithOne (DirectLimit G f) where
  __ : AddGroupWithOne _ := inferInstance
  add_comm := add_comm

instance [∀ i, NonUnitalNonAssocSemiring (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalNonAssocSemiring (DirectLimit G f) where
  left_distrib := DirectLimit.induction₃ _ fun i _ _ _ ↦ by
    simp_rw [add_def, mul_def, left_distrib, add_def]
  right_distrib := DirectLimit.induction₃ _ fun i _ _ _ ↦ by
    simp_rw [add_def, mul_def, right_distrib, add_def]
  zero_mul := zero_mul
  mul_zero := mul_zero

instance [∀ i, NonUnitalSemiring (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalSemiring (DirectLimit G f) where
  mul_assoc := mul_assoc

instance [∀ i, NonAssocSemiring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] :
    NonAssocSemiring (DirectLimit G f) where
  one_mul := one_mul
  mul_one := mul_one
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ

instance [∀ i, Semiring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] :
    Semiring (DirectLimit G f) where
  __ : NonAssocSemiring _ := inferInstance
  __ : Monoid _ := inferInstance

instance [∀ i, Ring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] : Ring (DirectLimit G f) where
  __ : Semiring _ := inferInstance
  __ : AddCommGroupWithOne _ := inferInstance

section Action

instance [∀ i, Zero (G i)] [∀ i, SMulZeroClass R (G i)]
    [∀ i j h, MulActionHomClass (T h) R (G i) (G j)] :
    SMulZeroClass R (DirectLimit G f) where
  smul_zero r := (smul_def _ _ _).trans <| by rw [smul_zero]; rfl

instance [Zero R] [∀ i, Zero (G i)] [∀ i, SMulWithZero R (G i)]
    [∀ i j h, MulActionHomClass (T h) R (G i) (G j)]
    [∀ i j h, ZeroHomClass (T h) (G i) (G j)] :
    SMulWithZero R (DirectLimit G f) where
  zero_smul := DirectLimit.induction _ fun i _ ↦ by simp_rw [smul_def, zero_smul, zero_def i]

instance [∀ i, AddZeroClass (G i)] [∀ i, DistribSMul R (G i)]
    [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]
    [∀ i j h, MulActionHomClass (T h) R (G i) (G j)] :
    DistribSMul R (DirectLimit G f) where
  smul_add r := DirectLimit.induction₂ _ fun i _ _ ↦ by
    simp_rw [add_def, smul_def, smul_add, add_def]

instance [Monoid R] [∀ i, AddMonoid (G i)] [∀ i, DistribMulAction R (G i)]
    [∀ i j h, DistribMulActionHomClass (T h) R (G i) (G j)] :
    DistribMulAction R (DirectLimit G f) :=
  have _ i j h : MulActionHomClass (T h) R (G i) (G j) := inferInstance
  { smul_zero := smul_zero, smul_add := smul_add }

instance [Monoid R] [∀ i, Monoid (G i)] [∀ i, MulDistribMulAction R (G i)]
    [∀ i j h, MonoidHomClass (T h) (G i) (G j)]
    [∀ i j h, MulActionHomClass (T h) R (G i) (G j)] :
    MulDistribMulAction R (DirectLimit G f) where
  smul_mul r := DirectLimit.induction₂ _ fun i _ _ ↦ by
    simp_rw [mul_def, smul_def, MulDistribMulAction.smul_mul, mul_def]
  smul_one r := (smul_def _ _ _).trans <| by rw [smul_one]; rfl

instance [Semiring R] [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
    [∀ i j h, LinearMapClass (T h) R (G i) (G j)] :
    Module R (DirectLimit G f) :=
  have _ i j h : DistribMulActionHomClass (T h) R (G i) (G j) := inferInstance
  { add_smul _ _ := DirectLimit.induction _ fun i _ ↦ by simp_rw [smul_def, add_smul, add_def],
    zero_smul := DirectLimit.induction _ fun i _ ↦ by simp_rw [smul_def, zero_smul, zero_def i] }

end Action

section DivisionSemiring
variable [∀ i, DivisionSemiring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)]

instance : DivisionSemiring (DirectLimit G f) where
  __ : GroupWithZero _ := inferInstance
  __ : Semiring _ := inferInstance
  nnratCast q := fullRec₀ _ fun _ ↦ q
  nnratCast_def q := show ⟦_⟧ = ⟦_⟧ / ⟦_⟧ by simp_rw [div₀_def]; rw [NNRat.cast_def]
  nnqsmul q := fullRec _ _ (fun _ ↦ (q • ·)) fun _ _ _ x ↦ by
    simp_rw [NNRat.smul_def, map_mul, map_nnratCast]
  nnqsmul_def _ := DirectLimit.induction _ fun i x ↦ show ⟦_⟧ = fullRec₀ .. * _ by
    simp_rw [fullRec₀_spec _ _ (fun _ _ _ ↦ map_nnratCast _ _) i, mul_def, NNRat.smul_def]

theorem nnratCast_def (q : ℚ≥0) (i) : (q : DirectLimit G f) = ⟦⟨i, q⟩⟧ :=
  fullRec₀_spec _ _ (fun _ _ _ ↦ map_nnratCast _ _) _

end DivisionSemiring

section DivisionRing
variable [∀ i, DivisionRing (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)]

instance : DivisionRing (DirectLimit G f) where
  __ : DivisionSemiring _ := inferInstance
  __ : Ring _ := inferInstance
  ratCast q := fullRec₀ _ fun _ ↦ q
  ratCast_def q := show ⟦_⟧ = ⟦_⟧ / ⟦_⟧ by simp_rw [div₀_def]; rw [Rat.cast_def]
  qsmul q := fullRec _ _ (fun _ ↦ (q • ·)) fun _ _ _ x ↦ by
    simp_rw [Rat.smul_def, map_mul, map_ratCast]
  qsmul_def _ := DirectLimit.induction _ fun i x ↦ show ⟦_⟧ = fullRec₀ .. * _ by
    simp_rw [fullRec₀_spec _ _ (fun _ _ _ ↦ map_ratCast _ _) i, mul_def, Rat.smul_def]

theorem ratCast_def (q : ℚ) (i) : (q : DirectLimit G f) = ⟦⟨i, q⟩⟧ :=
  fullRec₀_spec _ _ (fun _ _ _ ↦ map_ratCast _ _) _

end DivisionRing

variable [∀ i, Field (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)]

instance : Field (DirectLimit G f) where
  __ : DivisionRing _ := inferInstance
  mul_comm := mul_comm

end DirectLimit

open DirectLimit

variable {G' : ι → Type*} {T' : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f' : ∀ _ _ h, T' h}
variable [∀ i j (h : i ≤ j), FunLike (T' h) (G' i) (G' j)] [DirectedSystem G' (f' · · ·)]
variable {G'' : ι → Type*} {T'' : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f'' : ∀ _ _ h, T'' h}
variable [∀ i j (h : i ≤ j), FunLike (T'' h) (G'' i) (G'' j)] [DirectedSystem G'' (f'' · · ·)]

section AddCommMonoid
variable [∀ i, AddCommMonoid (G i)] [∀ i, AddCommMonoid (G' i)] [∀ i, AddCommMonoid (G'' i)]

namespace Module

variable [Semiring R] [∀ i, Module R (G i)]
variable [∀ i j h, LinearMapClass (T h) R (G i) (G j)]

@[deprecated (since := "2024-12-07")]
alias DirectedSystem.map_self := _root_.DirectedSystem.map_self
@[deprecated (since := "2024-12-07")] alias DirectedSystem.map_map := _root_.DirectedSystem.map_map
@[deprecated (since := "2024-12-07")] alias DirectLimit.Eqv := DirectLimit.setoid
@[deprecated (since := "2024-12-07")] protected alias DirectLimit := _root_.DirectLimit

namespace DirectLimit

variable (R ι G f) [Nonempty ι]

/-- The canonical map from a component to the direct limit. -/
def of (i) : G i →ₗ[R] DirectLimit G f where
  toFun x := ⟦⟨i, x⟩⟧
  map_add' _ _ := (DirectLimit.add_def ..).symm
  map_smul' _ _ := (DirectLimit.smul_def ..).symm

variable {R ι G f}

@[simp]
theorem of_f {i j hij x} : of R ι G f j (f i j hij x) = of R ι G f i x := .symm <| eq_of_le ..

theorem of_apply {i} (x) : of R ι G f i x = ⟦⟨i, x⟩⟧ := rfl

/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
theorem exists_of (z : DirectLimit G f) : ∃ i x, of R ι G f i x = z :=
  DirectLimit.induction _ (fun i x ↦ ⟨i, x, rfl⟩) z

@[elab_as_elim]
protected theorem induction_on {C : DirectLimit G f → Prop}
    (z : DirectLimit G f) (ih : ∀ i x, C (of R ι G f i x)) : C z :=
  DirectLimit.induction _ ih z

variable {P : Type*} [AddCommMonoid P] [Module R P]

variable (R ι G f) in
/-- The universal property of the direct limit: maps from the components to another module
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift (g : ∀ i, G i →ₗ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →ₗ[R] P where
  toFun := DirectLimit.rec _ (g · ·) fun i j h x ↦ (Hg i j h x).symm
  map_add' := DirectLimit.induction₂ _ fun i x y ↦ by simp_rw [add_def, rec_spec, map_add]
  map_smul' r := DirectLimit.induction _ fun i x ↦ by
    simp_rw [smul_def, rec_spec, map_smul, RingHom.id_apply]

variable (g : ∀ i, G i →ₗ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

theorem lift_of {i} (x) : lift R ι G f g Hg (of R ι G f i x) = g i x := rfl

theorem lift_unique (F : DirectLimit G f →ₗ[R] P) (x) :
    F x =
      lift R ι G f (fun i ↦ F.comp <| of R ι G f i)
        (fun i j hij x ↦ by rw [LinearMap.comp_apply, of_f]; rfl) x :=
  DirectLimit.induction_on x (fun i _ ↦ by rw [lift_of]; rfl)

lemma lift_injective (inj : ∀ i, Function.Injective <| g i) :
    Function.Injective (lift R ι G f g Hg) :=
  fun z w eq ↦ by
    induction z, w using DirectLimit.induction₂ with
    | ih i g₁ g₂ => simp_rw [← of_apply, lift_of] at eq; rw [inj _ eq]

/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
theorem of.zero_exact {i x} (H : of R ι G f i x = 0) : ∃ j hij, f i j hij x = (0 : G j) :=
  have ⟨j, hij, _, eq⟩ := Quotient.eq.mp H
  ⟨j, hij, eq.trans <| map_zero _⟩

end DirectLimit

end Module

namespace AddCommMonoid

@[deprecated (since := "2024-12-07")] protected alias DirectLimit := _root_.DirectLimit

variable [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)] [Nonempty ι]

namespace DirectLimit

local instance (i j h) : LinearMapClass (T h) ℕ (G i) (G j) where
  map_smulₛₗ _ _ _ := by rw [map_nsmul]; rfl

variable (G f) in
/-- The canonical map from a component to the direct limit. -/
def of (i) : G i →+ DirectLimit G f :=
  (Module.DirectLimit.of ℕ ι G _ i).toAddMonoidHom

@[simp] theorem of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x :=
  Module.DirectLimit.of_f

theorem of_apply {i} (x) : of G f i x = ⟦⟨i, x⟩⟧ := rfl

@[elab_as_elim]
protected theorem induction_on {C : DirectLimit G f → Prop}
    (z : DirectLimit G f) (ih : ∀ i x, C (of G f i x)) : C z :=
  Module.DirectLimit.induction_on z ih

/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
theorem of.zero_exact (i x) (h : of G f i x = 0) : ∃ j hij, f i j hij x = 0 :=
  Module.DirectLimit.of.zero_exact h

variable (P : Type*) [AddCommMonoid P]
variable (g : ∀ i, G i →+ P)
variable (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
variable (G f)

/-- The universal property of the direct limit: maps from the components to another abelian group
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift : DirectLimit G f →+ P :=
  (Module.DirectLimit.lift ℕ ι G f (fun i ↦ (g i).toNatLinearMap) Hg).toAddMonoidHom

variable {G f}

@[simp]
theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x := rfl

theorem lift_unique (F : DirectLimit G f →+ P) (x) :
    F x = lift G f P (fun i ↦ F.comp (of G f i)) (fun i j hij x ↦ by simp) x :=
  DirectLimit.induction_on x fun i x ↦ by simp

lemma lift_injective (inj : ∀ i, Function.Injective <| g i) :
    Function.Injective (lift G f P g Hg) :=
  Module.DirectLimit.lift_injective (fun i ↦ (g i).toNatLinearMap) Hg inj

end DirectLimit

end AddCommMonoid

end AddCommMonoid

namespace Ring

variable [∀ i, NonAssocSemiring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] [Nonempty ι]

@[deprecated (since := "2024-12-07")] protected alias DirectLimit := _root_.DirectLimit

namespace DirectLimit

variable (G f) in
/-- The canonical map from a component to the direct limit. -/
nonrec def of (i) : G i →+* DirectLimit G f where
  toFun x := ⟦⟨i, x⟩⟧
  map_one' := (one_def i).symm
  map_mul' _ _ := (mul_def ..).symm
  map_zero' := (zero_def i).symm
  map_add' _ _ := (add_def ..).symm

@[simp] theorem of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x := .symm <| eq_of_le ..

theorem of_apply {i} (x) : of G f i x = ⟦⟨i, x⟩⟧ := rfl

/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
theorem exists_of (z : DirectLimit G f) : ∃ i x, of G f i x = z :=
  DirectLimit.induction _ (fun i x ↦ ⟨i, x, rfl⟩) z

@[elab_as_elim]
theorem induction_on {C : DirectLimit G f → Prop}
    (z : DirectLimit G f) (ih : ∀ i x, C (of G f i x)) : C z :=
  DirectLimit.induction _ ih z

/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
theorem of.zero_exact {i x} (hix : of G f i x = 0) : ∃ j hij, f i j hij x = 0 :=
  have ⟨j, hij, _, eq⟩ := Quotient.eq.mp hix
  ⟨j, hij, eq.trans <| map_zero _⟩

/-- If the maps in the directed system are injective, then the canonical maps
from the components to the direct limits are injective. -/
theorem of_injective (hf : ∀ i j hij, Function.Injective (f i j hij)) (i) :
    Function.Injective (of G f i) :=
  fun _ _ eq ↦ have ⟨_, _, _, eq⟩ := Quotient.eq.mp eq; hf _ _ _ eq

variable (P : Type*) [NonAssocSemiring P]

variable (G f) in
/-- The universal property of the direct limit: maps from the components to another ring
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
def lift (g : ∀ i, G i →+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →+* P where
  toFun := DirectLimit.rec _ (g · ·) fun i j h x ↦ (Hg i j h x).symm
  map_one' := by rw [one_def (Classical.arbitrary ι), rec_spec, map_one]
  map_mul' := DirectLimit.induction₂ _ fun i x y ↦ by simp_rw [mul_def, rec_spec, map_mul]
  map_zero' := by simp_rw [zero_def (Classical.arbitrary ι), rec_spec, map_zero]
  map_add' := DirectLimit.induction₂ _ fun i x y ↦ by simp_rw [add_def, rec_spec, map_add]

variable (g : ∀ i, G i →+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

@[simp] theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x := rfl

theorem lift_unique (F : DirectLimit G f →+* P) (x) :
    F x = lift G f P (fun i ↦ F.comp <| of G f i) (fun i j hij x ↦ by simp [of_f]) x :=
  DirectLimit.induction_on x fun i x ↦ by simp [lift_of]

lemma lift_injective (inj : ∀ i, Function.Injective <| g i) :
    Function.Injective (lift G f P g Hg) :=
  fun z w eq ↦ by
    induction z, w using DirectLimit.induction₂ with
    | ih i g₁ g₂ => simp_rw [← of_apply, lift_of] at eq; rw [inj _ eq]

end DirectLimit

end Ring

open Polynomial in
nonrec theorem Ring.DirectLimit.Polynomial.exists_of
    [∀ i, Semiring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] [Nonempty ι]
    (q : (DirectLimit G f)[X]) : ∃ i p, Polynomial.map (of G f i) p = q :=
  Polynomial.induction_on q
    (fun z ↦
      let ⟨i, x, h⟩ := exists_of z
      ⟨i, C x, by rw [map_C, h]⟩)
    (fun q₁ q₂ ⟨i₁, p₁, ih₁⟩ ⟨i₂, p₂, ih₂⟩ =>
      let ⟨i, h1, h2⟩ := exists_ge_ge i₁ i₂
      ⟨i, p₁.map (f i₁ i h1) + p₂.map (f i₂ i h2), by
        rw [Polynomial.map_add, map_map, map_map, ← ih₁, ← ih₂]
        congr 2 <;> ext x <;> simp_rw [RingHom.comp_apply, RingHom.coe_coe, of_f]⟩)
    fun n z _ =>
    let ⟨i, x, h⟩ := exists_of z
    ⟨i, C x * X ^ (n + 1), by rw [Polynomial.map_mul, map_C, h, Polynomial.map_pow, map_X]⟩
