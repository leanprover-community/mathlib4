/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.Hom.Basic

/-!
# Boolean algebra structure on idempotents in a commutative (semi)ring

We show that the idempotent in a commutative ring form a Boolean algebra, with complement given
by `a ↦ 1 - a` and infimum given by multiplication. In a commutative semiring where subtraction
is not available, it is still true that pairs of elements `(a, b)` satisfying `a * b = 0` and
`a + b = 1` form a Boolean algebra (such elements are automatically idempotents, and such a pair
is uniquely determined by either `a` or `b`).
-/

@[expose] public section

variable {R : Type*}

variable (R) in
/-- An `IdempotentPair` is pair `(a, b)` satisfying `a * b = 0` and `a + b = 1`. -/
structure IdempotentPair [CommMonoid R] [AddCommMonoid R] where
  /-- The first element of an `IdempotentPair`. -/
  fst : R
  /-- The second element of an `IdempotentPair`. -/
  snd : R
  mul_eq_zero : fst * snd = 0
  add_eq_one : fst + snd = 1

initialize_simps_projections IdempotentPair (as_prefix fst, as_prefix snd)

namespace IdempotentPair

@[simps]
instance [CommMonoid R] [AddCommMonoid R] : Compl (IdempotentPair R) where
  compl a := ⟨a.snd, a.fst, (mul_comm ..).trans a.mul_eq_zero, (add_comm ..).trans a.add_eq_one⟩

lemma _root_.eq_of_mul_eq_add_eq_one [NonAssocSemiring R] (a : R) {b c : R}
    (mul : a * b = c * a) (add_ab : a + b = 1) (add_ac : a + c = 1) :
    b = c :=
  calc b = (a + c) * b := by rw [add_ac, one_mul]
       _ = c * (a + b) := by rw [add_mul, mul, mul_add]
       _ = c := by rw [add_ab, mul_one]

variable [CommSemiring R] {a b : IdempotentPair R}

@[ext high]
lemma fst_ext (eq : a.fst = b.fst) : a = b := by
  change mk a.fst a.snd _ _ = mk b.fst b.snd _ _
  congr 1
  refine eq_of_mul_eq_add_eq_one a.fst ?_ a.add_eq_one ?_
  · rw [a.mul_eq_zero, mul_comm, eq, b.mul_eq_zero]
  · rw [eq, b.add_eq_one]

@[ext]
lemma snd_ext (eq : a.snd = b.snd) : a = b := by
  refine fst_ext <| eq_of_mul_eq_add_eq_one a.snd ?_ ?_ ?_
  · rw [mul_comm, a.mul_eq_zero, eq, b.mul_eq_zero]
  · rw [add_comm, a.add_eq_one]
  · rw [add_comm, eq, b.add_eq_one]

variable (a) in
lemma isIdempotentElem_fst : IsIdempotentElem a.fst :=
  (IsIdempotentElem.of_mul_add a.mul_eq_zero a.add_eq_one).1

variable (a) in
lemma isIdempotentElem_snd : IsIdempotentElem a.snd :=
  (IsIdempotentElem.of_mul_add a.mul_eq_zero a.add_eq_one).2

instance : PartialOrder (IdempotentPair R) where
  le a b := a.fst * b.fst = a.fst
  le_refl a := a.isIdempotentElem_fst
  le_trans a b c hab hbc := show _ = _ by rw [← hab, mul_assoc, hbc]
  le_antisymm a b hab hba := by ext; rw [← hab, mul_comm, hba]

lemma le_def : a ≤ b ↔ a.fst * b.fst = a.fst :=
  .rfl

instance : SemilatticeSup (IdempotentPair R) where
  sup a b := ⟨a.fst + a.snd * b.fst, a.snd * b.snd, by simp_rw [add_mul, mul_mul_mul_comm _ b.fst,
      b.mul_eq_zero, mul_zero, ← mul_assoc, a.mul_eq_zero, zero_mul, add_zero], by
    simp_rw [add_assoc, ← mul_add, b.add_eq_one, mul_one, a.add_eq_one]⟩
  le_sup_left a b := by
    simp_rw [le_def, mul_add, ← mul_assoc, a.mul_eq_zero, zero_mul, add_zero,
      a.isIdempotentElem_fst.eq]
  le_sup_right a b := by
    simp_rw [le_def, mul_add, mul_comm a.snd, ← mul_assoc, b.isIdempotentElem_fst.eq, ← mul_add,
      a.add_eq_one, mul_one]
  sup_le a b c hac hbc := by simp_rw [(· ≤ ·), add_mul, mul_assoc]; rw [hac, hbc]

@[simp]
lemma fst_sup : (a ⊔ b).fst = a.fst + a.snd * b.fst :=
  rfl

@[simp]
lemma snd_sup : (a ⊔ b).snd = a.snd * b.snd :=
  rfl

instance : Min (IdempotentPair R) where
  min a b := (aᶜ ⊔ bᶜ)ᶜ

@[simp]
lemma fst_inf : (a ⊓ b).fst = a.fst * b.fst :=
  rfl

@[simp]
lemma snd_inf : (a ⊓ b).snd = a.snd + a.fst * b.snd :=
  rfl

instance : SemilatticeInf (IdempotentPair R) where
  inf := min
  inf_le_left a b := by
    simp_rw [le_def, fst_inf, mul_right_comm, a.isIdempotentElem_fst.eq]
  inf_le_right a b := by
    simp_rw [le_def, fst_inf, mul_assoc, b.isIdempotentElem_fst.eq]
  le_inf a b c hab hac := by
    simp_rw [le_def, fst_inf, ← mul_assoc, le_def.mp hab, le_def.mp hac]

@[simps top_fst top_snd bot_fst bot_snd]
instance : BooleanAlgebra (IdempotentPair R) where
  le_sup_inf a b c := Eq.le <| snd_ext <| by
    simp only [fst_sup, snd_sup, snd_inf]
    simp_rw [add_mul, mul_add, mul_mul_mul_comm _ b.fst, a.isIdempotentElem_snd.eq, ← mul_assoc,
      a.mul_eq_zero, zero_mul, zero_add]
  top := ⟨1, 0, mul_zero _, add_zero _⟩
  bot := ⟨0, 1, zero_mul _, zero_add _⟩
  inf_compl_le_bot a := Eq.le <| snd_ext <| by
    simp_rw [snd_inf, snd_compl, a.isIdempotentElem_fst.eq, add_comm, a.add_eq_one]
  top_le_sup_compl a := Eq.le <| fst_ext <| by
    simp_rw [fst_sup, fst_compl, a.isIdempotentElem_snd.eq, a.add_eq_one]
  le_top _ := mul_one _
  bot_le _ := zero_mul _
  sdiff_eq _ _ := rfl
  himp_eq _ _ := rfl

end IdempotentPair

/-- `IdempotentElem` is a type of idempotent elements. Over a commutative ring, this type is
equipped with a `BooleanAlgebra` structure. -/
@[ext]
structure IdempotentElem (M : Type*) [Mul M] where
  /-- The underlying value of `IdempotentElem`. -/
  val : M
  isIdempotentElem : IsIdempotentElem val

namespace IdempotentElem

instance {M : Type*} [Mul M] : Coe (IdempotentElem M) M where
  coe := val

attribute [coe] val

initialize_simps_projections IdempotentElem (val → coe, as_prefix coe)

instance {S : Type*} [CommSemigroup S] : SemilatticeInf (IdempotentElem S) where
  le a b := (a : S) * b = a
  le_refl a := a.isIdempotentElem
  le_trans a b c hab hbc := show _ = _ by rw [← hab, mul_assoc, hbc]
  le_antisymm a b hab hba := by ext; rw [← hab, mul_comm, hba]
  inf a b := ⟨_, a.2.mul b.2⟩
  inf_le_left a b := show _ = _ by simp_rw [mul_right_comm]; rw [a.2]
  inf_le_right a b := show _ = _ by simp_rw [mul_assoc]; rw [b.2]
  le_inf a b c hab hac := by simp_rw [← mul_assoc]; rw [hab, hac]

lemma le_def {S : Type*} [CommSemigroup S] {a b : IdempotentElem S} : a ≤ b ↔ (a : S) * b = a :=
  .rfl

@[simp]
lemma coe_inf {S : Type*} [CommSemigroup S] (a b : IdempotentElem S) : a ⊓ b = (a : S) * b :=
  rfl

@[simps]
instance {M : Type*} [CommMonoid M] : OrderTop (IdempotentElem M) where
  top := ⟨1, .one⟩
  le_top _ := mul_one _

@[simps]
instance {M₀ : Type*} [CommMonoidWithZero M₀] : OrderBot (IdempotentElem M₀) where
  bot := ⟨0, .zero⟩
  bot_le _ := zero_mul _

section CommRing

variable [CommRing R]

instance : Lattice (IdempotentElem R) where
  sup a b := ⟨_, a.2.add_sub_mul b.2⟩
  le_sup_left a b := show _ = _ by
    simp_rw [mul_sub, mul_add]; rw [← mul_assoc, a.2, add_sub_cancel_right]
  le_sup_right a b := show _ = _ by
    simp_rw [mul_sub, mul_add]; rw [← mul_assoc, mul_right_comm, b.2, add_sub_cancel_left]
  sup_le a b c hac hbc := show _ = _ by simp_rw [sub_mul, add_mul, mul_assoc]; rw [hbc, hac]

@[simp]
lemma coe_sup (a b : IdempotentElem R) : a ⊔ b = (a : R) + b - a * b :=
  rfl

@[simps compl_coe]
instance : BooleanAlgebra (IdempotentElem R) where
  __ : DistribLattice _ := .ofInfSupLe fun a b c ↦ Eq.le <| IdempotentElem.ext <| by
    simp only [coe_sup, coe_inf]
    rw [mul_sub, mul_add, mul_mul_mul_comm, a.2.eq]
  __ : OrderTop _ := inferInstance
  __ : OrderBot _ := inferInstance
  compl a := ⟨_, a.2.one_sub⟩
  inf_compl_le_bot a := (mul_zero _).trans ((mul_one_sub ..).trans <| by rw [a.2, sub_self]).symm
  top_le_sup_compl a := by
    simp_rw [le_def, coe_sup, add_sub_cancel, mul_sub, mul_one, a.2.eq, sub_self, sub_zero]
  sdiff_eq _ _ := rfl
  himp a b := ⟨_, (a.2.mul b.2.one_sub).one_sub⟩
  himp_eq a b := by ext; simp_rw [coe_sup, add_comm b.1, add_sub_assoc, mul_sub, mul_one,
    sub_sub_cancel, sub_add, mul_comm]

/-- In a commutative ring, the idempotents are in 1-1 correspondence with pairs of elements
whose product is 0 and whose sum is 1. The correspondence is given by `a ↔ (a, 1 - a)`. -/
def toIdempotentPair : IdempotentElem R ≃o IdempotentPair R where
  toFun a := ⟨a, 1 - a, by simp_rw [mul_sub, mul_one, a.2.eq, sub_self], by rw [add_sub_cancel]⟩
  invFun a := ⟨a.fst, a.isIdempotentElem_fst⟩
  right_inv a := by ext; rfl
  map_rel_iff' := Iff.rfl

@[deprecated (since := "2026-09-07")]
alias _root_.OrderIso.isIdempotentElemMulZeroAddOne := IdempotentElem.toIdempotentPair

end CommRing

end IdempotentElem

section Deprecated

variable [CommSemiring R] {a b : {a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1}}

@[deprecated IdempotentPair.fst_ext (since := "2026-09-07")]
lemma mul_eq_zero_add_eq_one_ext_left (eq : a.1.1 = b.1.1) : a = b := by
  refine Subtype.ext <| Prod.ext_iff.mpr ⟨eq, eq_of_mul_eq_add_eq_one a.1.1 ?_ a.2.2 ?_⟩
  · rw [a.2.1, mul_comm, eq, b.2.1]
  · rw [eq, b.2.2]

@[deprecated IdempotentPair.snd_ext (since := "2026-09-07")]
lemma mul_eq_zero_add_eq_one_ext_right (eq : a.1.2 = b.1.2) : a = b := by
  refine Subtype.ext <| Prod.ext_iff.mpr ⟨eq_of_mul_eq_add_eq_one a.1.2 ?_ ?_ ?_, eq⟩
  · rw [mul_comm, a.2.1, eq, b.2.1]
  · rw [add_comm, a.2.2]
  · rw [add_comm, eq, b.2.2]

end Deprecated
