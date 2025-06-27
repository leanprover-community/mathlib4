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
  getElem_toVector_lt' {i : ℕ} (hi : i < n := by get_elem_tactic) : toVector[i] < n := by decide
  getElem_invVector_getElem_toVector' {i : ℕ} (hi : i < n := by get_elem_tactic) :
      invVector[toVector[i]]'(getElem_toVector_lt' hi) = i := by decide
  deriving DecidableEq

open Set Function

namespace PermLT

variable {n m i j : ℕ} {a b : PermLT n}

theorem getElem_toVector_lt {i : ℕ} (hi : i < n := by get_elem_tactic) : a.toVector[i] < n :=
  a.getElem_toVector_lt'

theorem getElem_invVector_getElem_toVector {i : ℕ} (hi : i < n := by get_elem_tactic) :
    a.invVector[a.toVector[i]]'(a.getElem_toVector_lt hi) = i :=
  a.getElem_invVector_getElem_toVector'

def get (a : PermLT n) : Fin n → Fin n :=
  fun i => Fin.mk (a.toVector[(i : ℕ)]) (getElem_toVector_lt _)

section Get

theorem toVector_eq_iff_get_eq : a.toVector = b.toVector ↔ a.get = b.get := by
  simp_rw [Vector.ext_iff, funext_iff, Fin.forall_iff, Fin.ext_iff]
  exact Iff.rfl

theorem get_injective : a.get.Injective := fun i j hij => Fin.ext <| by
  rw [← a.getElem_invVector_getElem_toVector i.isLt, ← a.getElem_invVector_getElem_toVector j.isLt]
  congr 1
  exact Fin.val_eq_of_eq hij

theorem get_bijective : a.get.Bijective := get_injective.bijective_of_finite

theorem get_surjective : a.get.Surjective := get_bijective.surjective

end Get

theorem getElem_invVector_lt {i : ℕ} (hi : i < n := by get_elem_tactic) : a.invVector[i] < n := by
  rcases a.get_surjective ⟨i, hi⟩ with ⟨j, hj⟩
  simp_rw [Fin.ext_iff] at hj; cases hj
  exact (getElem_invVector_getElem_toVector _).trans_lt j.isLt

theorem getElem_toVector_getElem_invVector {i : ℕ} (hi : i < n := by get_elem_tactic) :
    a.toVector[a.invVector[i]]'(getElem_invVector_lt hi) = i := by
  rcases a.get_surjective ⟨i, hi⟩ with ⟨j, hj⟩
  simp_rw [Fin.ext_iff] at hj; cases hj
  congr 1
  exact getElem_invVector_getElem_toVector _

def invGet (a : PermLT n) : Fin n → Fin n :=
    fun i => Fin.mk (a.invVector[(i : ℕ)]) (getElem_invVector_lt _)

section InvGet

theorem invVector_eq_iff_invGet_eq : a.invVector = b.invVector ↔ a.invGet = b.invGet := by
  simp_rw [Vector.ext_iff, funext_iff, Fin.forall_iff, Fin.ext_iff]
  exact Iff.rfl

theorem invGet_injective : a.invGet.Injective := fun i j hij => Fin.ext <| by
  rw [← a.getElem_toVector_getElem_invVector i.isLt, ← a.getElem_toVector_getElem_invVector j.isLt]
  congr 1
  exact Fin.val_eq_of_eq hij

theorem invGet_bijective : a.invGet.Bijective := invGet_injective.bijective_of_finite

theorem invGet_surjective : a.invGet.Surjective := invGet_bijective.surjective

theorem leftInverse_invGet_get : LeftInverse a.invGet a.get :=
  fun _ => Fin.ext (getElem_invVector_getElem_toVector)

theorem rightInverse_invGet_get : RightInverse a.invGet a.get :=
  fun _ => Fin.ext (getElem_toVector_getElem_invVector)

theorem invGet_eq_iff_get_eq : a.invGet = b.invGet ↔ a.get = b.get := by
  constructor
  · exact fun h => a.rightInverse_invGet_get.eq_rightInverse (h ▸ leftInverse_invGet_get)
  · exact fun h => a.leftInverse_invGet_get.eq_rightInverse (h ▸ rightInverse_invGet_get)

end InvGet

instance : Inv (PermLT n) where
  inv a := PermLT.mk (a.invVector) (a.toVector)
    (getElem_toVector_lt' := fun _ => getElem_invVector_lt)
    (getElem_invVector_getElem_toVector' := fun _ => getElem_toVector_getElem_invVector)

instance : GetElem (PermLT n) ℕ ℕ fun _ i => i < n where
  getElem a i h := a.toVector[i]

section GetElem

@[simp] theorem coe_get {i : Fin n} : (a.get i : ℕ) = a[(i : ℕ)] := rfl
@[simp] theorem coe_invGet {i : Fin n} : (a.invGet i : ℕ) = a⁻¹[(i : ℕ)] := rfl

@[simp]
theorem getElem_mk (a b : Vector ℕ n) {ha hab} (hi : i < n) :
  (PermLT.mk a b ha hab)[i] = a[i] := rfl

@[simp]
theorem getElem_inv_mk (a b : Vector ℕ n) {ha hab} (hi : i < n) :
  (PermLT.mk a b ha hab)⁻¹[i] = b[i] := rfl

@[simp]
theorem getElem_lt (hi : i < n := by get_elem_tactic) : a[i] < n :=
  a.getElem_toVector_lt _

@[simp]
theorem getElem_toVector (hi : i < n := by get_elem_tactic) :
  a.toVector[i] = a[i] := rfl

@[simp]
theorem getElem_invVector (hi : i < n := by get_elem_tactic) :
  a.invVector[i] = a⁻¹[i] := rfl

@[simp]
theorem getElem_inv_getElem (hi : i < n := by get_elem_tactic) :
    a⁻¹[a[i]] = i := a.getElem_invVector_getElem_toVector

@[simp]
theorem getElem_getElem_inv (hi : i < n := by get_elem_tactic) :
  a[a⁻¹[i]] = i := a.getElem_toVector_getElem_invVector

theorem getElem_injective (hi : i < n := by get_elem_tactic) (hj : j < n := by get_elem_tactic)
    : a[i] = a[j] → i = j := by
  simpa only [Fin.ext_iff] using (a.get_injective.eq_iff (a := ⟨i, hi⟩) (b := ⟨j, hj⟩)).mp

@[simp] theorem getElem_inj (hi : i < n) (hj : j < n) :
    a[i] = a[j] ↔ i = j := ⟨a.getElem_injective hi hj, fun h => h ▸ rfl⟩

theorem getElem_ne_iff (hi : i < n) {j : ℕ} (hj : j < n) :
    a[i] ≠ a[j] ↔ i ≠ j := (a.getElem_inj hi hj).not

theorem getElem_surjective (hi : i < n) :
    ∃ (j : ℕ) (hj : j < n), a[j] = i := ⟨a⁻¹[i], getElem_lt, getElem_getElem_inv⟩

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

end GetElem

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

end One

instance : Mul (PermLT n) where
  mul a b := {
    toVector := Vector.ofFn (fun i => a.toVector[b[(i : ℕ)]])
    invVector := Vector.ofFn (fun i => b⁻¹.toVector[a⁻¹[(i : ℕ)]])
    getElem_toVector_lt' := fun {i} hi => by
      simp_rw [Vector.getElem_ofFn, getElem_toVector, getElem_lt]
    getElem_invVector_getElem_toVector' := fun {i} hi => by
      simp_rw [Vector.getElem_ofFn, getElem_toVector, getElem_inv_getElem]}

section Mul

@[simp]
theorem getElem_mul (hi : i < n) :
    (a * b)[i] = a[b[i]] := Vector.getElem_ofFn _

end Mul

@[ext]
theorem ext (h : ∀ (i : ℕ) (hi : i < n), a[i] = b[i]) : a = b := by
  suffices h : a.toVector = b.toVector ∧ a.invVector = b.invVector by
    rcases a; rcases b; simp_rw [mk.injEq]; exact h
  simp_rw [toVector_eq_iff_get_eq, invVector_eq_iff_invGet_eq,
    invGet_eq_iff_get_eq, and_self, funext_iff, Fin.ext_iff, coe_get, h, implies_true]

section Ext

theorem get_eq_iff_eq : a.get = b.get ↔ a = b := by
  simp_rw [funext_iff, Fin.ext_iff, PermLT.ext_iff, Fin.forall_iff, coe_get]

theorem injective_get : Injective (get (n := n)) := fun _ _ => get_eq_iff_eq.mp

theorem invGet_eq_iff_eq : a.invGet = b.invGet ↔ a = b := by
  simp_rw [invGet_eq_iff_get_eq, get_eq_iff_eq]

theorem injective_invGet : Injective (invGet (n := n)) := fun _ _ => invGet_eq_iff_eq.mp

instance : Finite (PermLT n) := Finite.of_injective get injective_get

instance : Subsingleton (PermLT 0) where
  allEq a b := by simp_rw [← get_eq_iff_eq, funext_iff, IsEmpty.forall_iff]

instance : Subsingleton (PermLT 1) where
  allEq a b := by
    simp_rw [PermLT.ext_iff]
    intro _ hi
    have ha := a.getElem_lt (hi := hi)
    have hb := b.getElem_lt (hi := hi)
    rw [Nat.lt_one_iff] at ha hb
    exact ha.trans hb.symm

instance : Unique (PermLT 0) := Unique.mk' _

instance : Unique (PermLT 1) := Unique.mk' _

instance : EquivLike (PermLT n) (Fin n) (Fin n) where
  coe a := a.get
  inv a := a.invGet
  left_inv _ := leftInverse_invGet_get
  right_inv _ := rightInverse_invGet_get
  coe_injective' _ _ hab₁ _ := ext <| fun _ hi => Fin.val_eq_of_eq (congrFun hab₁ ⟨_, hi⟩)

end Ext

instance : EquivLike (PermLT n) ℕ ℕ where
  coe a i := a[i]?.getD i
  inv a i := a⁻¹[i]?.getD i
  left_inv a i := (i.lt_or_ge n).by_cases
    (fun hi => by simp only [hi, getElem?_pos, Option.getD_some, getElem_lt, getElem_inv_getElem])
    (fun hi => by simp only [not_lt, hi, getElem?_neg, Option.getD_none])
  right_inv a i := (i.lt_or_ge n).by_cases
    (fun hi => by simp only [hi, getElem?_pos, Option.getD_some, getElem_lt, getElem_getElem_inv])
    (fun hi => by simp only [not_lt, hi, getElem?_neg, Option.getD_none])
  coe_injective' a b hab₁ _ := ext <| fun i hi => by
    simpa only [hi, getElem?_pos, Option.getD_some] using congrFun hab₁ i

instance : SMul (PermLT n) ℕ where
  smul a i := a[i]?.getD i

section SMulNat

theorem smul_eq_dite (i : ℕ) :
    a • i = if h : i < n then a[i]'h else i :=
  apply_dite (fun (o : Option ℕ) => o.getD i) _ _ _

theorem smul_of_lt (h : i < n) : a • i = a[i] := by
  simp_rw [smul_eq_dite, dif_pos h]

theorem smul_of_ge (h : n ≤ i) : a • i = i := by
  simp_rw [smul_eq_dite, dif_neg h.not_gt]

@[simp] theorem smul_fin {i : Fin n} : a • i = a[i.1] := a.smul_of_lt i.isLt

@[simp] theorem smul_add_left : a • (i + n) = i + n := a.smul_of_ge (Nat.le_add_left _ _)

@[simp] theorem smul_add_right : a • (n + i) = n + i := a.smul_of_ge (Nat.le_add_right _ _)

@[simp]
theorem smul_getElem (h : i < n) : a • b[i] = a[b[i]] :=
  a.smul_of_lt _

theorem smul_eq_iff :
    a • i = j ↔ (∀ (hi : i < n), a[i] = j) ∧ (n ≤ i → i = j) := by
  rcases lt_or_ge i n with hi | hi
  · simp_rw [a.smul_of_lt hi, hi, hi.not_ge, false_implies, forall_true_left, and_true]
  · simp_rw [a.smul_of_ge hi, hi, hi.not_gt, IsEmpty.forall_iff, forall_true_left, true_and]

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
  rcases lt_or_ge i n with hi | hi
  · simp_rw [hi, hi.not_ge, false_imp_iff, true_imp_iff, and_true]
  · simp_rw [ne_of_gt (hi.trans_lt' getElem_lt), (hi.trans_lt' hj).ne',
      hi.not_gt, hi, imp_self, imp_false, and_not_self_iff]

theorem getElem_eq_smul_iff (hi : i < n) :
    a[i] = a • j ↔ i = j := by simp_rw [eq_comm, smul_eq_getElem_iff, eq_comm]

@[simp]
theorem smul_lt_iff_lt : a • i < n ↔ i < n := by
  rcases lt_or_ge i n with h | h
  · simp_rw [h, iff_true, a.smul_of_lt h, getElem_lt]
  · simp_rw [h.not_gt, iff_false, not_lt, a.smul_of_ge h, h]

theorem smul_lt_of_lt (h : i < n) : a • i < n := a.smul_lt_iff_lt.mpr h

theorem lt_of_smul_lt (h : a • i < n) : i < n := a.smul_lt_iff_lt.mp h

theorem smul_fin_lt {i : Fin n} : a • i < n := a.smul_lt_of_lt i.isLt

theorem smul_eq_smul_same_iff :
  a • i = b • i ↔ (hi : i < n) → a[i] = b[i] := by
  rcases lt_or_ge i n with hi | hi
  · simp_rw [smul_of_lt hi, hi, forall_true_left]
  · simp_rw [smul_of_ge hi, hi.not_gt, IsEmpty.forall_iff]

theorem smul_right_inj {i j : ℕ} : a • i = a • j ↔ i = j := by
  rcases lt_or_ge i n with hi | hi <;>
  rcases lt_or_ge j n with hj | hj
  · simp_rw [a.smul_of_lt hi, a.smul_of_lt hj, a.getElem_inj]
  · simp_rw [a.smul_of_lt hi, a.smul_of_ge hj, (hi.trans_le hj).ne,
      (hj.trans_lt' a.getElem_lt).ne]
  · simp_rw [a.smul_of_ge hi, a.smul_of_lt hj, (hj.trans_le hi).ne',
      (hi.trans_lt' a.getElem_lt).ne']
  · simp_rw [a.smul_of_ge hi, a.smul_of_ge hj]

theorem smul_right_surj : ∃ j, a • j = i := by
  rcases lt_or_ge i n with hi | hi
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
