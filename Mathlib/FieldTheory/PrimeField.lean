/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot, Kenny Lau
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.CharP.Algebra

/-!
# Prime fields

A prime field is a field that does not contain any nontrivial subfield. Prime fields are `ℚ` in
characteristic `0` and `ZMod p` in characteristic `p` with `p` a prime number. Any field `K`
contains a unique prime field: it is the smallest field contained in `K`.

## Results

* The fields `ℚ` and `ZMod p` are prime fields. These are stated as the instances that says that
  the corresponding `Subfield` type is a `Subsingleton`.
* `Subfield.bot_eq_of_charZero` : the smallest subfield of a field of characteristic `0` is (the
  image of) `ℚ`.
* `Subfield.bot_eq_of_zMod_algebra`: the smallest subfield of a field of characteristic `p` is (the
  image of) `ZMod p`.

-/

public section

instance : Subsingleton (Subfield ℚ) := subsingleton_of_top_le_bot fun x _ ↦
  have h := Subsingleton.elim ((⊥ : Subfield ℚ).subtype.comp (Rat.castHom _)) (.id _ : ℚ →+* ℚ)
  (congr($h x) : _ = x) ▸ Subtype.prop _

instance (p : ℕ) [hp : Fact (Nat.Prime p)] : Subsingleton (Subfield (ZMod p)) :=
  subsingleton_of_top_le_bot fun x _ ↦
    have h := Subsingleton.elim ((⊥ : Subfield (ZMod p)).subtype.comp
      (ZMod.castHom dvd_rfl _)) (.id _ : ZMod p →+* ZMod p)
    (congr($h x) : _ = x) ▸ Subtype.prop _

variable {K : Type*} [Field K]

/--
The smallest subfield of a field of characteristic `0` is (the image of) `ℚ`.
-/
theorem Subfield.bot_eq_of_charZero [CharZero K] :
    (⊥ : Subfield K) = (algebraMap ℚ K).fieldRange := by
  rw [eq_comm, eq_bot_iff, ← Subfield.map_bot (algebraMap ℚ K),
    subsingleton_iff_bot_eq_top.mpr inferInstance, ← RingHom.fieldRange_eq_map]

variable (K) in
/--
Equivalence between the smallest subfield of a field of characteristic `0` and `ℚ`.
-/
@[expose] noncomputable
def Subfield.botEquivRat [CharZero K] : (⊥ : Subfield K) ≃+* ℚ :=
  (RingEquiv.subfieldCongr Subfield.bot_eq_of_charZero).trans
    (algebraMap ℚ K).rangeRestrictFieldEquiv.symm

@[simp]
theorem Subfield.botEquivRat_symm_apply [CharZero K] (x : ℚ) :
    (Subfield.botEquivRat K).symm x = algebraMap ℚ (⊥ : Subfield K) x :=
  rfl

theorem Subfield.coe_botEquivRat_symm_apply [CharZero K] (x : ℚ) :
    ↑((Subfield.botEquivRat K).symm x) = algebraMap ℚ K x :=
  rfl

/--
The smallest subfield of a field of characteristic `p` is (the image of) `ZMod p`.
Note that the fact that the field `K` is of characteristic `p` is stated by the fact that it is
`ZMod p`-algebra.
-/
theorem Subfield.bot_eq_of_zMod_algebra (p : ℕ) [hp : Fact (Nat.Prime p)] [Algebra (ZMod p) K] :
    (⊥ : Subfield K) = (algebraMap (ZMod p) K).fieldRange := by
  rw [eq_comm, eq_bot_iff, ← Subfield.map_bot (algebraMap (ZMod p) K),
    subsingleton_iff_bot_eq_top.mpr inferInstance, ← RingHom.fieldRange_eq_map]

variable (K) in
/--
Equivalence between the smallest subfield of a field of characteristic `p` and `ZMod p`.
-/
@[expose] noncomputable
def Subfield.botEquivZMod (p : ℕ) [hp : Fact (Nat.Prime p)] [Algebra (ZMod p) K] :
    (⊥ : Subfield K) ≃+* ZMod p :=
  (RingEquiv.subfieldCongr (Subfield.bot_eq_of_zMod_algebra p)).trans
    (algebraMap (ZMod p) K).rangeRestrictFieldEquiv.symm

@[simp]
theorem Subfield.coe_botEquivZMod_symm_apply (p : ℕ) [hp : Fact (Nat.Prime p)] [Algebra (ZMod p) K]
    (x : ZMod p) :
    ↑((Subfield.botEquivZMod K p).symm x) = algebraMap (ZMod p) K x :=
  rfl
