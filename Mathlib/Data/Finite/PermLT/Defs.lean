/-
Copyright (c) 2024-2025 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
import Mathlib.Tactic.Linter.Style
import Mathlib.Data.Finite.Prod

/-!
# Definition of `PermLT`
-/

/--
`PermLT n` represents permutations of `ℕ` that fix all elements greater than or equal to `n`.
-/
structure PermLT (n : ℕ) where
  /--
  Represents `PermLT` as an vector of size `n`.
  -/
  protected toVector : Vector ℕ n
  /--
  Represents the inverse of `PermLT` as a vector of size `n`.
  -/
  protected invVector : Vector ℕ n
  getElem_toVector_lt {i : ℕ} (hi : i < n := by get_elem_tactic) : toVector[i] < n := by decide
  getElem_invVector_getElem_toVector {i : ℕ} (hi : i < n := by get_elem_tactic) :
      invVector[toVector[i]]'(getElem_toVector_lt hi) = i := by decide
  deriving DecidableEq

namespace PermLT

variable {n m i j : ℕ} {a b : PermLT n}

instance : GetElem (PermLT n) ℕ ℕ fun _ i => i < n where
  getElem a i h := a.toVector[i]

section GetElem

@[simp]
theorem getElem_mk (a b : Vector ℕ n) {ha hab} (hi : i < n) :
  (PermLT.mk a b ha hab)[i] = a[i] := rfl

@[simp]
theorem getElem_lt (hi : i < n := by get_elem_tactic) : a[i] < n :=
  a.getElem_toVector_lt _

@[simp]
theorem getElem_toVector (hi : i < n := by get_elem_tactic) :
  a.toVector[i] = a[i] := rfl

theorem getElem_injective (hi : i < n) (hj : j < n)
    (hij : a[i] = a[j]) : i = j := by
  rw [← a.getElem_invVector_getElem_toVector hi, ← a.getElem_invVector_getElem_toVector hj]
  congr 1

@[simp] theorem getElem_inj (hi : i < n) (hj : j < n) :
    a[i] = a[j] ↔ i = j := ⟨a.getElem_injective hi hj, fun h => h ▸ rfl⟩

theorem getElem_ne_iff (hi : i < n) {j : ℕ} (hj : j < n) :
    a[i] ≠ a[j] ↔ i ≠ j := (a.getElem_inj hi hj).not

theorem getElem_surjective (hi : i < n) :
    ∃ (j : ℕ) (hj : j < n), a[j] = i := by
  have h_inj : Function.Injective (⟨a[·], a.getElem_lt⟩ : Fin n → Fin n) :=
    fun _ _ hij => Fin.ext (a.getElem_injective _ _ (Fin.val_eq_of_eq hij))
  have h_surj := h_inj.surjective_of_fintype (Equiv.refl (Fin n))
  rcases h_surj ⟨i, hi⟩ with ⟨⟨j, hj⟩, ⟨_, _⟩⟩
  exact ⟨j, hj, rfl⟩

end GetElem

@[ext]
theorem ext (h : ∀ (i : ℕ) (hi : i < n), a[i] = b[i]) : a = b := by
  suffices h : a.toVector = b.toVector ∧ a.invVector = b.invVector by
    rcases a; rcases b; simp_rw [mk.injEq]; exact h
  simp_rw [Vector.ext_iff]
  refine ⟨h, fun i hi => ?_⟩
  rcases a.getElem_surjective hi with ⟨j, hj, rfl⟩
  trans j
  · exact a.getElem_invVector_getElem_toVector hj
  · simp_rw [h]
    symm
    exact b.getElem_invVector_getElem_toVector hj

section Ext

instance : Subsingleton (PermLT 0) where
  allEq a b := by simp_rw [PermLT.ext_iff, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true]

instance : Subsingleton (PermLT 1) where
  allEq a b := by
    simp_rw [PermLT.ext_iff]
    intro _ hi
    have ha := a.getElem_lt (hi := hi)
    have hb := b.getElem_lt (hi := hi)
    rw [Nat.lt_one_iff] at ha hb
    exact ha.trans hb.symm

instance : Finite (PermLT n) := Finite.of_injective
  (fun a => (⟨a[·], a.getElem_lt⟩ : Fin n → Fin n)) <| fun a b => by
    simp_rw [funext_iff, Fin.ext_iff, PermLT.ext_iff, Fin.forall_iff,
      Fin.getElem_fin, imp_self]

end Ext

instance : One (PermLT n) where
  one := PermLT.mk (Vector.range n) (Vector.range n)
    (by simp_rw [Vector.getElem_range, imp_self, implies_true])
    (by simp_rw [Vector.getElem_range, implies_true])

section One

@[simp]
theorem getElem_one (hi : i < n) : (1 : PermLT n)[i] = i := Vector.getElem_range _

instance : Inhabited (PermLT n) := ⟨1⟩

@[simp]
theorem default_eq : (default : PermLT n) = 1 := rfl

instance : Unique (PermLT 0) := Unique.mk' _

instance : Unique (PermLT 1) := Unique.mk' _

end One

instance : Inv (PermLT n) where
  inv a := PermLT.mk
    (toVector := a.invVector)
    (invVector := a.toVector)
    (getElem_toVector_lt := fun hi => by
      rcases a.getElem_surjective hi with ⟨j, hj, rfl⟩
      exact hj.trans_eq' (a.getElem_invVector_getElem_toVector _))
    (getElem_invVector_getElem_toVector := fun hi => by
      rcases a.getElem_surjective hi with ⟨j, hj, rfl⟩
      congr 1
      exact a.getElem_invVector_getElem_toVector _)

section Inv

@[simp]
theorem getElem_inv_mk (a b : Vector ℕ n) {ha hab} (hi : i < n) :
  (PermLT.mk a b ha hab)⁻¹[i] = b[i] := rfl

@[simp]
theorem getElem_invVector (hi : i < n) :
  a.invVector[i] = a⁻¹[i] := rfl

@[simp]
theorem getElem_inv_getElem (hi : i < n) :
    a⁻¹[a[i]] = i := a.getElem_invVector_getElem_toVector _

@[simp]
theorem getElem_getElem_inv (hi : i < n) :
  a[a⁻¹[i]] = i := (a⁻¹).getElem_invVector_getElem_toVector _

theorem eq_getElem_inv_iff (hi : i < n) (hj : j < n) :
    i = a⁻¹[j] ↔ a[i] = j := by
  rw [← (a⁻¹).getElem_inj (a.getElem_lt) hj, getElem_inv_getElem]

theorem ne_getElem_inv_iff (hi : i < n) (hj : j < n) :
    i ≠ a⁻¹[j] ↔ a[i] ≠ j := (a.eq_getElem_inv_iff _ _).ne

theorem getElem_inv_eq_iff (hi : i < n) (hj : j < n) :
    a⁻¹[i] = j ↔ i = a[j] := by
  rw [← a.getElem_inj (a⁻¹.getElem_lt) hj, getElem_getElem_inv]

theorem getElem_inv_ne_iff (hi : i < n) (hj : j < n) :
    a⁻¹[i] ≠ j ↔ i ≠ a[j] := (a.getElem_inv_eq_iff _ _).ne

end Inv

instance : Mul (PermLT n) where
  mul a b := {
    toVector := Vector.ofFn (fun i => a.toVector[b[(i : ℕ)]])
    invVector := Vector.ofFn (fun i => b⁻¹.toVector[a⁻¹[(i : ℕ)]])
    getElem_toVector_lt := fun {i} hi => by
      simp_rw [Vector.getElem_ofFn, getElem_toVector, getElem_lt]
    getElem_invVector_getElem_toVector := fun {i} hi => by
      simp_rw [Vector.getElem_ofFn, getElem_toVector, getElem_inv_getElem]}

section Mul

@[simp]
theorem getElem_mul (hi : i < n) :
    (a * b)[i] = a[b[i]] := Vector.getElem_ofFn _

end Mul

instance : SMul (PermLT n) ℕ where
  smul a i := a[i]?.getD i

section SMulNat

theorem smul_eq_dite (i : ℕ) :
    a • i = if h : i < n then a[i]'h else i :=
  apply_dite (fun (o : Option ℕ) => o.getD i) _ _ _

theorem smul_of_lt (h : i < n) : a • i = a[i] := by
  simp_rw [smul_eq_dite, dif_pos h]

theorem smul_of_ge (h : n ≤ i) : a • i = i := by
  simp_rw [smul_eq_dite, dif_neg h.not_lt]

@[simp] theorem smul_fin {i : Fin n} : a • i = a[i.1] := a.smul_of_lt i.isLt

@[simp]
theorem smul_getElem (h : i < n) : a • b[i] = a[b[i]] :=
  a.smul_of_lt _

theorem smul_eq_iff :
    a • i = j ↔ (∀ (hi : i < n), a[i] = j) ∧ (n ≤ i → i = j) := by
  rcases lt_or_le i n with hi | hi
  · simp_rw [a.smul_of_lt hi, hi, hi.not_le, false_implies, forall_true_left, and_true]
  · simp_rw [a.smul_of_ge hi, hi, hi.not_lt, IsEmpty.forall_iff, forall_true_left, true_and]

theorem eq_smul_iff :
    i = a • j ↔ (∀ (hj : j < n), i = a[j]) ∧ (n ≤ j → i = j) := by
  simp_rw [eq_comm (a := i), smul_eq_iff]

theorem smul_eq_self_iff :
    a • i = i ↔ ∀ (hi : i < n), a[i] = i := by
  simp_rw [smul_eq_iff, implies_true, and_true]

theorem self_eq_smul_iff :
    i = a • i ↔ ∀ (hi : i < n), i = a[i] := by
  simp_rw [eq_comm (a := i), smul_eq_self_iff]

theorem smul_eq_getElem_iff (hj : j < n) :
    a • i = a[j] ↔ i = j := by
  simp_rw [smul_eq_iff, getElem_inj]
  rcases lt_or_le i n with hi | hi
  · simp_rw [hi, hi.not_le, false_imp_iff, true_imp_iff, and_true]
  · simp_rw [ne_of_gt (hi.trans_lt' getElem_lt), (hi.trans_lt' hj).ne',
      hi.not_lt, hi, imp_self, imp_false, and_not_self_iff]

theorem getElem_eq_smul_iff (hi : i < n) :
    a[i] = a • j ↔ i = j := by simp_rw [eq_comm, smul_eq_getElem_iff, eq_comm]

@[simp]
theorem smul_lt_iff_lt : a • i < n ↔ i < n := by
  rcases lt_or_le i n with h | h
  · simp_rw [h, iff_true, a.smul_of_lt h, getElem_lt]
  · simp_rw [h.not_lt, iff_false, not_lt, a.smul_of_ge h, h]

theorem smul_lt_of_lt (h : i < n) : a • i < n := a.smul_lt_iff_lt.mpr h

theorem lt_of_smul_lt (h : a • i < n) : i < n := a.smul_lt_iff_lt.mp h

theorem smul_fin_lt {i : Fin n} : a • i < n := a.smul_lt_of_lt i.isLt

theorem smul_eq_smul_same_iff :
  a • i = b • i ↔ (hi : i < n) → a[i] = b[i] := by
  rcases lt_or_le i n with hi | hi
  · simp_rw [smul_of_lt hi, hi, forall_true_left]
  · simp_rw [smul_of_ge hi, hi.not_lt, IsEmpty.forall_iff]

theorem smul_right_inj {i j : ℕ} : a • i = a • j ↔ i = j := by
  rcases lt_or_le i n with hi | hi <;>
  rcases lt_or_le j n with hj | hj
  · simp_rw [a.smul_of_lt hi, a.smul_of_lt hj, a.getElem_inj]
  · simp_rw [a.smul_of_lt hi, a.smul_of_ge hj, (hi.trans_le hj).ne,
      (hj.trans_lt' a.getElem_lt).ne]
  · simp_rw [a.smul_of_ge hi, a.smul_of_lt hj, (hj.trans_le hi).ne',
      (hi.trans_lt' a.getElem_lt).ne']
  · simp_rw [a.smul_of_ge hi, a.smul_of_ge hj]

theorem smul_right_surj : ∃ j, a • j = i := by
  rcases lt_or_le i n with hi | hi
  · rcases a.getElem_surjective hi with ⟨j, hj, rfl⟩
    exact ⟨j, smul_of_lt _⟩
  · exact ⟨i, smul_of_ge hi⟩

theorem eq_iff_smul_eq_smul_lt : a = b ↔ ∀ {i : ℕ}, i < n → a • i = b • i := by
  simp_rw [smul_eq_smul_same_iff, PermLT.ext_iff, imp_forall_iff_forall]

theorem eq_iff_smul_eq_smul :
    a = b ↔ ∀ {i : ℕ}, a • i = b • i := by
  simp_rw [smul_eq_smul_same_iff, PermLT.ext_iff]

end SMulNat

end PermLT
