/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# (Pre)images of set intervals under `Fin` operations

In this file we prove basic lemmas about preimages and images of the intervals
under the following operations:

- `Fin.val`,
- `Fin.castLE` (preimages only),
- `Fin.castAdd`,
- `Fin.cast`,
- `Fin.castSucc`,
- `Fin.natAdd`,
- `Fin.addNat`,
- `Fin.succ`,
- `Fin.rev`.
-/

open Function Set

namespace Fin

variable {m n : ℕ}

/-!
### (Pre)images under `Fin.val`
-/

@[simp]
theorem range_val : range ((↑) : Fin n → ℕ) = Set.Iio n := by ext; simp [Fin.exists_iff]

@[simp] theorem preimage_val_Ici_val (i : Fin n) : (↑) ⁻¹' Ici (i : ℕ) = Ici i := rfl
@[simp] theorem preimage_val_Ioi_val (i : Fin n) : (↑) ⁻¹' Ioi (i : ℕ) = Ioi i := rfl
@[simp] theorem preimage_val_Iic_val (i : Fin n) : (↑) ⁻¹' Iic (i : ℕ) = Iic i := rfl
@[simp] theorem preimage_val_Iio_val (i : Fin n) : (↑) ⁻¹' Iio (i : ℕ) = Iio i := rfl

@[simp] theorem preimage_val_Icc_val (i j : Fin n) : (↑) ⁻¹' Icc (i : ℕ) j = Icc i j := rfl
@[simp] theorem preimage_val_Ico_val (i j : Fin n) : (↑) ⁻¹' Ico (i : ℕ) j = Ico i j := rfl
@[simp] theorem preimage_val_Ioc_val (i j : Fin n) : (↑) ⁻¹' Ioc (i : ℕ) j = Ioc i j := rfl
@[simp] theorem preimage_val_Ioo_val (i j : Fin n) : (↑) ⁻¹' Ioo (i : ℕ) j = Ioo i j := rfl
@[simp] theorem preimage_val_uIcc_val (i j : Fin n) : (↑) ⁻¹' uIcc (i : ℕ) j = uIcc i j := rfl
@[simp] theorem preimage_val_uIoc_val (i j : Fin n) : (↑) ⁻¹' uIoc (i : ℕ) j = uIoc i j := rfl
@[simp] theorem preimage_val_uIoo_val (i j : Fin n) : (↑) ⁻¹' uIoo (i : ℕ) j = uIoo i j := rfl

@[simp]
theorem image_val_Ici (i : Fin n) : (↑) '' Ici i = Ico (i : ℕ) n := by
  rw [← preimage_val_Ici_val, image_preimage_eq_inter_range, range_val, Ici_inter_Iio]

@[simp]
theorem image_val_Iic (i : Fin n) : (↑) '' Iic i = Iic (i : ℕ) := by
  rw [← preimage_val_Iic_val, image_preimage_eq_of_subset]
  simp [range_val]

@[simp]
theorem image_val_Ioi (i : Fin n) : (↑) '' Ioi i = Ioo (i : ℕ) n := by
  rw [← preimage_val_Ioi_val, image_preimage_eq_inter_range, range_val, Ioi_inter_Iio]

@[simp]
theorem image_val_Iio (i : Fin n) : (↑) '' Iio i = Iio (i : ℕ) := by
  rw [← preimage_val_Iio_val, image_preimage_eq_inter_range, range_val, inter_eq_left]
  exact Iio_subset_Iio i.is_lt.le

@[simp]
theorem image_val_Icc (i j : Fin n) : (↑) '' Icc i j = Icc (i : ℕ) j := by
  rw [← preimage_val_Icc_val, image_preimage_eq_inter_range, range_val, inter_eq_left]
  exact fun k hk ↦ hk.2.trans_lt j.is_lt

@[simp]
theorem image_val_Ico (i j : Fin n) : (↑) '' Ico i j = Ico (i : ℕ) j := by
  rw [← preimage_val_Ico_val, image_preimage_eq_inter_range, range_val, inter_eq_left]
  exact fun k hk ↦ hk.2.trans j.is_lt

@[simp]
theorem image_val_Ioc (i j : Fin n) : (↑) '' Ioc i j = Ioc (i : ℕ) j := by
  rw [← preimage_val_Ioc_val, image_preimage_eq_inter_range, range_val, inter_eq_left]
  exact fun k hk ↦ hk.2.trans_lt j.is_lt

@[simp]
theorem image_val_Ioo (i j : Fin n) : (↑) '' Ioo i j = Ioo (i : ℕ) j := by
  rw [← preimage_val_Ioo_val, image_preimage_eq_inter_range, range_val, inter_eq_left]
  exact fun k hk ↦ hk.2.trans j.is_lt

@[simp] theorem image_val_uIcc (i j : Fin n) : (↑) '' uIcc i j = uIcc (i : ℕ) j := by simp [uIcc]
@[simp] theorem image_val_uIoc (i j : Fin n) : (↑) '' uIoc i j = uIoc (i : ℕ) j := by simp [uIoc]
@[simp] theorem image_val_uIoo (i j : Fin n) : (↑) '' uIoo i j = uIoo (i : ℕ) j := by simp [uIoo]

/-!
### Preimages under `Fin.castLE`
-/

@[simp]
theorem preimage_castLE_Ici_castLE (i : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' Ici (castLE h i) = Ici i :=
  rfl

@[simp]
theorem preimage_castLE_Ioi_castLE (i : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' Ioi (castLE h i) = Ioi i :=
  rfl

@[simp]
theorem preimage_castLE_Iic_castLE (i : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' Iic (castLE h i) = Iic i :=
  rfl

@[simp]
theorem preimage_castLE_Iio_castLE (i : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' Iio (castLE h i) = Iio i :=
  rfl

@[simp]
theorem preimage_castLE_Icc_castLE (i j : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' Icc (castLE h i) (castLE h j) = Icc i j :=
  rfl

@[simp]
theorem preimage_castLE_Ico_castLE (i j : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' Ico (castLE h i) (castLE h j) = Ico i j :=
  rfl

@[simp]
theorem preimage_castLE_Ioc_castLE (i j : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' Ioc (castLE h i) (castLE h j) = Ioc i j :=
  rfl

@[simp]
theorem preimage_castLE_Ioo_castLE (i j : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' Ioo (castLE h i) (castLE h j) = Ioo i j :=
  rfl

@[simp]
theorem preimage_castLE_uIcc_castLE (i j : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' uIcc (castLE h i) (castLE h j) = uIcc i j :=
  rfl

@[simp]
theorem preimage_castLE_uIoc_castLE (i j : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' uIoc (castLE h i) (castLE h j) = uIoc i j :=
  rfl

@[simp]
theorem preimage_castLE_uIoo_castLE (i j : Fin m) (h : m ≤ n) :
    castLE h ⁻¹' uIoo (castLE h i) (castLE h j) = uIoo i j :=
  rfl

@[simp]
theorem image_castLE_Iic (i : Fin m) (h : m ≤ n) : castLE h '' Iic i = Iic (castLE h i) :=
  val_injective.image_injective <| by simp [image_image]

@[simp]
theorem image_castLE_Iio (i : Fin m) (h : m ≤ n) : castLE h '' Iio i = Iio (castLE h i) :=
  val_injective.image_injective <| by simp [image_image]

@[simp]
theorem image_castLE_Icc (i j : Fin m) (h : m ≤ n) :
    castLE h '' Icc i j = Icc (castLE h i) (castLE h j) :=
  val_injective.image_injective <| by simp [image_image]

@[simp]
theorem image_castLE_Ico (i j : Fin m) (h : m ≤ n) :
    castLE h '' Ico i j = Ico (castLE h i) (castLE h j) :=
  val_injective.image_injective <| by simp [image_image]

@[simp]
theorem image_castLE_Ioc (i j : Fin m) (h : m ≤ n) :
    castLE h '' Ioc i j = Ioc (castLE h i) (castLE h j) :=
  val_injective.image_injective <| by simp [image_image]

@[simp]
theorem image_castLE_Ioo (i j : Fin m) (h : m ≤ n) :
    castLE h '' Ioo i j = Ioo (castLE h i) (castLE h j) :=
  val_injective.image_injective <| by simp [image_image]

@[simp]
theorem image_castLE_uIcc (i j : Fin m) (h : m ≤ n) :
    castLE h '' uIcc i j = uIcc (castLE h i) (castLE h j) :=
  val_injective.image_injective <| by simp [image_image]

@[simp]
theorem image_castLE_uIoc (i j : Fin m) (h : m ≤ n) :
    castLE h '' uIoc i j = uIoc (castLE h i) (castLE h j) :=
  val_injective.image_injective <| by simp [image_image]

@[simp]
theorem image_castLE_uIoo (i j : Fin m) (h : m ≤ n) :
    castLE h '' uIoo i j = uIoo (castLE h i) (castLE h j) :=
  val_injective.image_injective <| by simp [image_image]

/-!
### (Pre)images under `Fin.castAdd`
-/

@[simp]
theorem range_castAdd [NeZero m] : range (castAdd m : Fin n → Fin (n + m)) = Iio (natAdd n 0) :=
  val_injective.image_injective <| by simp [← range_comp, comp_def]

@[simp]
theorem preimage_castAdd_Ici_castAdd (m) (i : Fin n) : castAdd m ⁻¹' Ici (castAdd m i) = Ici i :=
  rfl

@[simp]
theorem preimage_castAdd_Ioi_castAdd (m) (i : Fin n) : castAdd m ⁻¹' Ioi (castAdd m i) = Ioi i :=
  rfl

@[simp]
theorem preimage_castAdd_Iic_castAdd (m) (i : Fin n) : castAdd m ⁻¹' Iic (castAdd m i) = Iic i :=
  rfl

@[simp]
theorem preimage_castAdd_Iio_castAdd (m) (i : Fin n) : castAdd m ⁻¹' Iio (castAdd m i) = Iio i :=
  rfl

@[simp]
theorem preimage_castAdd_Icc_castAdd (m) (i j : Fin n) :
    castAdd m ⁻¹' Icc (castAdd m i) (castAdd m j) = Icc i j :=
  rfl

@[simp]
theorem preimage_castAdd_Ico_castAdd (m) (i j : Fin n) :
    castAdd m ⁻¹' Ico (castAdd m i) (castAdd m j) = Ico i j :=
  rfl

@[simp]
theorem preimage_castAdd_Ioc_castAdd (m) (i j : Fin n) :
    castAdd m ⁻¹' Ioc (castAdd m i) (castAdd m j) = Ioc i j :=
  rfl

@[simp]
theorem preimage_castAdd_Ioo_castAdd (m) (i j : Fin n) :
    castAdd m ⁻¹' Ioo (castAdd m i) (castAdd m j) = Ioo i j :=
  rfl

@[simp]
theorem preimage_castAdd_uIcc_castAdd (m) (i j : Fin n) :
    castAdd m ⁻¹' uIcc (castAdd m i) (castAdd m j) = uIcc i j :=
  rfl

@[simp]
theorem preimage_castAdd_uIoc_castAdd (m) (i j : Fin n) :
    castAdd m ⁻¹' uIoc (castAdd m i) (castAdd m j) = uIoc i j :=
  rfl

@[simp]
theorem preimage_castAdd_uIoo_castAdd (m) (i j : Fin n) :
    castAdd m ⁻¹' uIoo (castAdd m i) (castAdd m j) = uIoo i j :=
  rfl

@[simp]
theorem image_castAdd_Ici (m) [NeZero m] (i : Fin n) :
    castAdd m '' Ici i = Ico (castAdd m i) (natAdd n 0) :=
  val_injective.image_injective <| by simp [← image_comp]

@[simp]
theorem image_castAdd_Ioi (m) [NeZero m] (i : Fin n) :
    castAdd m '' Ioi i = Ioo (castAdd m i) (natAdd n 0) :=
  val_injective.image_injective <| by simp [← image_comp]

@[simp]
theorem image_castAdd_Iic (m) (i : Fin n) : castAdd m '' Iic i = Iic (castAdd m i) :=
  image_castLE_Iic i _

@[simp]
theorem image_castAdd_Iio (m) (i : Fin n) : castAdd m '' Iio i = Iio (castAdd m i) :=
  image_castLE_Iio ..

@[simp]
theorem image_castAdd_Icc (m) (i j : Fin n) :
    castAdd m '' Icc i j = Icc (castAdd m i) (castAdd m j) :=
  image_castLE_Icc ..

@[simp]
theorem image_castAdd_Ico (m) (i j : Fin n) :
    castAdd m '' Ico i j = Ico (castAdd m i) (castAdd m j) :=
  image_castLE_Ico ..

@[simp]
theorem image_castAdd_Ioc (m) (i j : Fin n) :
    castAdd m '' Ioc i j = Ioc (castAdd m i) (castAdd m j) :=
  image_castLE_Ioc ..

@[simp]
theorem image_castAdd_Ioo (m) (i j : Fin n) :
    castAdd m '' Ioo i j = Ioo (castAdd m i) (castAdd m j) :=
  image_castLE_Ioo ..

@[simp]
theorem image_castAdd_uIcc (m) (i j : Fin n) :
    castAdd m '' uIcc i j = uIcc (castAdd m i) (castAdd m j) :=
  image_castLE_uIcc ..

@[simp]
theorem image_castAdd_uIoc (m) (i j : Fin n) :
    castAdd m '' uIoc i j = uIoc (castAdd m i) (castAdd m j) :=
  image_castLE_uIoc ..

@[simp]
theorem image_castAdd_uIoo (m) (i j : Fin n) :
    castAdd m '' uIoo i j = uIoo (castAdd m i) (castAdd m j) :=
  image_castLE_uIoo ..

/-!
### (Pre)images under `Fin.cast`
-/

theorem image_cast (h : m = n) (s : Set (Fin m)) : Fin.cast h '' s = Fin.cast h.symm ⁻¹' s :=
  (finCongr h).image_eq_preimage _

@[simp]
theorem image_cast_fun (h : m = n) : image (Fin.cast h) = preimage (Fin.cast h.symm) :=
  funext <| image_cast h

@[simp]
theorem preimage_cast_Ici (h : m = n) (i : Fin n) : .cast h ⁻¹' Ici i = Ici (i.cast h.symm) := rfl

@[simp]
theorem preimage_cast_Ioi (h : m = n) (i : Fin n) : .cast h ⁻¹' Ioi i = Ioi (i.cast h.symm) := rfl

@[simp]
theorem preimage_cast_Iic (h : m = n) (i : Fin n) : .cast h ⁻¹' Iic i = Iic (i.cast h.symm) := rfl

@[simp]
theorem preimage_cast_Iio (h : m = n) (i : Fin n) : .cast h ⁻¹' Iio i = Iio (i.cast h.symm) := rfl

@[simp]
theorem preimage_cast_Icc (h : m = n) (i j : Fin n) :
    .cast h ⁻¹' Icc i j = Icc (i.cast h.symm) (j.cast h.symm) :=
  rfl

@[simp]
theorem preimage_cast_Ico (h : m = n) (i j : Fin n) :
    .cast h ⁻¹' Ico i j = Ico (i.cast h.symm) (j.cast h.symm) :=
  rfl

@[simp]
theorem preimage_cast_Ioc (h : m = n) (i j : Fin n) :
    .cast h ⁻¹' Ioc i j = Ioc (i.cast h.symm) (j.cast h.symm) :=
  rfl

@[simp]
theorem preimage_cast_Ioo (h : m = n) (i j : Fin n) :
    .cast h ⁻¹' Ioo i j = Ioo (i.cast h.symm) (j.cast h.symm) :=
  rfl

@[simp]
theorem preimage_cast_uIcc (h : m = n) (i j : Fin n) :
    .cast h ⁻¹' uIcc i j = uIcc (i.cast h.symm) (j.cast h.symm) :=
  rfl

@[simp]
theorem preimage_cast_uIoc (h : m = n) (i j : Fin n) :
    .cast h ⁻¹' uIoc i j = uIoc (i.cast h.symm) (j.cast h.symm) :=
  rfl

@[simp]
theorem preimage_cast_uIoo (h : m = n) (i j : Fin n) :
    .cast h ⁻¹' uIoo i j = uIoo (i.cast h.symm) (j.cast h.symm) :=
  rfl

/-!
### `Fin.castSucc`
-/

@[simp]
theorem preimage_castSucc_Ici_castSucc (i : Fin n) : castSucc ⁻¹' Ici i.castSucc = Ici i := rfl

@[simp]
theorem preimage_castSucc_Ioi_castSucc (i : Fin n) : castSucc ⁻¹' Ioi i.castSucc = Ioi i := rfl

@[simp]
theorem preimage_castSucc_Iic_castSucc (i : Fin n) : castSucc ⁻¹' Iic i.castSucc = Iic i := rfl

@[simp]
theorem preimage_castSucc_Iio_castSucc (i : Fin n) : castSucc ⁻¹' Iio i.castSucc = Iio i := rfl

@[simp]
theorem preimage_castSucc_Icc_castSucc (i j : Fin n) :
    castSucc ⁻¹' Icc i.castSucc j.castSucc = Icc i j :=
  rfl

@[simp]
theorem preimage_castSucc_Ico_castSucc (i j : Fin n) :
    castSucc ⁻¹' Ico i.castSucc j.castSucc = Ico i j :=
  rfl

@[simp]
theorem preimage_castSucc_Ioc_castSucc (i j : Fin n) :
    castSucc ⁻¹' Ioc i.castSucc j.castSucc = Ioc i j :=
  rfl

@[simp]
theorem preimage_castSucc_Ioo_castSucc (i j : Fin n) :
    castSucc ⁻¹' Ioo i.castSucc j.castSucc = Ioo i j :=
  rfl

@[simp]
theorem preimage_castSucc_uIcc_castSucc (i j : Fin n) :
    castSucc ⁻¹' uIcc i.castSucc j.castSucc = uIcc i j :=
  rfl

@[simp]
theorem preimage_castSucc_uIoc_castSucc (i j : Fin n) :
    castSucc ⁻¹' uIoc i.castSucc j.castSucc = uIoc i j :=
  rfl

@[simp]
theorem preimage_castSucc_uIoo_castSucc (i j : Fin n) :
    castSucc ⁻¹' uIoo i.castSucc j.castSucc = uIoo i j :=
  rfl

@[simp]
theorem image_castSucc_Ici (i : Fin n) : castSucc '' Ici i = Ico i.castSucc (.last n) :=
  image_castAdd_Ici ..

@[simp]
theorem image_castSucc_Ioi (i : Fin n) : castSucc '' Ioi i = Ioo i.castSucc (.last n) :=
  image_castAdd_Ioi ..

@[simp]
theorem image_castSucc_Iic (i : Fin n) : castSucc '' Iic i = Iic i.castSucc :=
  image_castAdd_Iic ..

@[simp]
theorem image_castSucc_Iio (i : Fin n) : castSucc '' Iio i = Iio i.castSucc :=
  image_castAdd_Iio ..

@[simp]
theorem image_castSucc_Icc (i j : Fin n) : castSucc '' Icc i j = Icc i.castSucc j.castSucc :=
  image_castAdd_Icc ..

@[simp]
theorem image_castSucc_Ico (i j : Fin n) : castSucc '' Ico i j = Ico i.castSucc j.castSucc :=
  image_castAdd_Ico ..

@[simp]
theorem image_castSucc_Ioc (i j : Fin n) : castSucc '' Ioc i j = Ioc i.castSucc j.castSucc :=
  image_castAdd_Ioc ..

@[simp]
theorem image_castSucc_Ioo (i j : Fin n) : castSucc '' Ioo i j = Ioo i.castSucc j.castSucc :=
  image_castAdd_Ioo ..

@[simp]
theorem image_castSucc_uIcc (i j : Fin n) : castSucc '' uIcc i j = uIcc i.castSucc j.castSucc :=
  image_castAdd_uIcc ..

@[simp]
theorem image_castSucc_uIoc (i j : Fin n) : castSucc '' uIoc i j = uIoc i.castSucc j.castSucc :=
  image_castAdd_uIoc ..

@[simp]
theorem image_castSucc_uIoo (i j : Fin n) : castSucc '' uIoo i j = uIoo i.castSucc j.castSucc :=
  image_castAdd_uIoo ..

/-!
### `Fin.natAdd`
-/

theorem range_natAdd (m n : ℕ) : range (natAdd m : Fin n → Fin (m + n)) = {i | m ≤ i.1} := by
  ext i
  constructor
  · rintro ⟨i, rfl⟩
    apply le_coe_natAdd
  · refine fun (hi : m ≤ i) ↦ ⟨⟨i - m, by cutsat⟩, ?_⟩
    ext
    simp [hi]

theorem range_natAdd_eq_Ici (m n : ℕ) [NeZero n] :
    range (natAdd m : Fin n → Fin (m + n)) = Ici (natAdd m 0) :=
  range_natAdd m n

theorem range_natAdd_eq_Ioi (m n : ℕ) [NeZero m] :
    range (natAdd m : Fin n → Fin (m + n)) = Ioi (castAdd n ⊤) := by
  ext ⟨_, _⟩
  simp [range_natAdd, lt_def, ← Nat.succ_le_iff, Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)]

@[simp]
theorem preimage_natAdd_Ici_natAdd (m) (i : Fin n) : natAdd m ⁻¹' Ici (natAdd m i) = Ici i := by
  ext; simp

@[simp]
theorem preimage_natAdd_Ioi_natAdd (m) (i : Fin n) : natAdd m ⁻¹' Ioi (natAdd m i) = Ioi i := by
  ext; simp

@[simp]
theorem preimage_natAdd_Iic_natAdd (m) (i : Fin n) : natAdd m ⁻¹' Iic (natAdd m i) = Iic i := by
  ext; simp

@[simp]
theorem preimage_natAdd_Iio_natAdd (m) (i : Fin n) : natAdd m ⁻¹' Iio (natAdd m i) = Iio i := by
  ext; simp

@[simp]
theorem preimage_natAdd_Icc_natAdd (m) (i j : Fin n) :
    natAdd m ⁻¹' Icc (natAdd m i) (natAdd m j) = Icc i j := by
  ext; simp

@[simp]
theorem preimage_natAdd_Ico_natAdd (m) (i j : Fin n) :
    natAdd m ⁻¹' Ico (natAdd m i) (natAdd m j) = Ico i j := by
  ext; simp

@[simp]
theorem preimage_natAdd_Ioc_natAdd (m) (i j : Fin n) :
    natAdd m ⁻¹' Ioc (natAdd m i) (natAdd m j) = Ioc i j := by
  ext; simp

@[simp]
theorem preimage_natAdd_Ioo_natAdd (m) (i j : Fin n) :
    natAdd m ⁻¹' Ioo (natAdd m i) (natAdd m j) = Ioo i j := by
  ext; simp

@[simp]
theorem preimage_natAdd_uIcc_natAdd (m) (i j : Fin n) :
    natAdd m ⁻¹' uIcc (natAdd m i) (natAdd m j) = uIcc i j := by
  simp [uIcc, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]
theorem preimage_natAdd_uIoc_natAdd (m) (i j : Fin n) :
    natAdd m ⁻¹' uIoc (natAdd m i) (natAdd m j) = uIoc i j := by
  simp [uIoc, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]
theorem preimage_natAdd_uIoo_natAdd (m) (i j : Fin n) :
    natAdd m ⁻¹' uIoo (natAdd m i) (natAdd m j) = uIoo i j := by
  simp [uIoo, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]
theorem image_natAdd_Ici (m) (i : Fin n) : natAdd m '' Ici i = Ici (natAdd m i) := by
  rw [← preimage_natAdd_Ici_natAdd, image_preimage_eq_of_subset]
  rw [range_natAdd]
  exact fun j hj ↦ Nat.le_trans (le_coe_natAdd ..) hj

@[simp]
theorem image_natAdd_Ioi (m) (i : Fin n) : natAdd m '' Ioi i = Ioi (natAdd m i) := by
  rw [← preimage_natAdd_Ioi_natAdd, image_preimage_eq_of_subset]
  exact Ioi_subset_Ici_self.trans <| image_natAdd_Ici m i ▸ image_subset_range _ _

@[simp]
theorem image_natAdd_Icc (m) (i j : Fin n) :
    natAdd m '' Icc i j = Icc (natAdd m i) (natAdd m j) := by
  rw [← preimage_natAdd_Icc_natAdd, image_preimage_eq_of_subset]
  exact Icc_subset_Ici_self.trans <| image_natAdd_Ici m i ▸ image_subset_range _ _

@[simp]
theorem image_natAdd_Ico (m) (i j : Fin n) :
    natAdd m '' Ico i j = Ico (natAdd m i) (natAdd m j) := by
  rw [← preimage_natAdd_Ico_natAdd, image_preimage_eq_of_subset]
  exact Ico_subset_Ici_self.trans <| image_natAdd_Ici m i ▸ image_subset_range _ _

@[simp]
theorem image_natAdd_Ioc (m) (i j : Fin n) :
    natAdd m '' Ioc i j = Ioc (natAdd m i) (natAdd m j) := by
  rw [← preimage_natAdd_Ioc_natAdd, image_preimage_eq_of_subset]
  exact Ioc_subset_Ioi_self.trans <| image_natAdd_Ioi m i ▸ image_subset_range _ _

@[simp]
theorem image_natAdd_Ioo (m) (i j : Fin n) :
    natAdd m '' Ioo i j = Ioo (natAdd m i) (natAdd m j) := by
  rw [← preimage_natAdd_Ioo_natAdd, image_preimage_eq_of_subset]
  exact Ioo_subset_Ioi_self.trans <| image_natAdd_Ioi m i ▸ image_subset_range _ _

@[simp]
theorem image_natAdd_uIcc (m) (i j : Fin n) :
    natAdd m '' uIcc i j = uIcc (natAdd m i) (natAdd m j) := by
  simp [uIcc, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]
theorem image_natAdd_uIoc (m) (i j : Fin n) :
    natAdd m '' uIoc i j = uIoc (natAdd m i) (natAdd m j) := by
  simp [uIoc, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

@[simp]
theorem image_natAdd_uIoo (m) (i j : Fin n) :
    natAdd m '' uIoo i j = uIoo (natAdd m i) (natAdd m j) := by
  simp [uIoo, ← (strictMono_natAdd m).monotone.map_max, ← (strictMono_natAdd m).monotone.map_min]

/-!
### `Fin.addNat`
-/

@[simp]
theorem preimage_addNat_Ici_addNat (m) (i : Fin n) : (addNat · m) ⁻¹' Ici (i.addNat m) = Ici i := by
  ext; simp

@[simp]
theorem preimage_addNat_Ioi_addNat (m) (i : Fin n) : (addNat · m) ⁻¹' Ioi (i.addNat m) = Ioi i := by
  ext; simp

@[simp]
theorem preimage_addNat_Iic_addNat (m) (i : Fin n) : (addNat · m) ⁻¹' Iic (i.addNat m) = Iic i := by
  ext; simp

@[simp]
theorem preimage_addNat_Iio_addNat (m) (i : Fin n) : (addNat · m) ⁻¹' Iio (i.addNat m) = Iio i := by
  ext; simp

@[simp]
theorem preimage_addNat_Icc_addNat (m) (i j : Fin n) :
    (addNat · m) ⁻¹' Icc (i.addNat m) (j.addNat m) = Icc i j := by
  ext; simp

@[simp]
theorem preimage_addNat_Ico_addNat (m) (i j : Fin n) :
    (addNat · m) ⁻¹' Ico (i.addNat m) (j.addNat m) = Ico i j := by
  ext; simp

@[simp]
theorem preimage_addNat_Ioc_addNat (m) (i j : Fin n) :
    (addNat · m) ⁻¹' Ioc (i.addNat m) (j.addNat m) = Ioc i j := by
  ext; simp

@[simp]
theorem preimage_addNat_Ioo_addNat (m) (i j : Fin n) :
    (addNat · m) ⁻¹' Ioo (i.addNat m) (j.addNat m) = Ioo i j := by
  ext; simp

@[simp]
theorem preimage_addNat_uIcc_addNat (m) (i j : Fin n) :
    (addNat · m) ⁻¹' uIcc (i.addNat m) (j.addNat m) = uIcc i j := by
  simp [uIcc, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]
theorem preimage_addNat_uIoc_addNat (m) (i j : Fin n) :
    (addNat · m) ⁻¹' uIoc (i.addNat m) (j.addNat m) = uIoc i j := by
  simp [uIoc, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]
theorem preimage_addNat_uIoo_addNat (m) (i j : Fin n) :
    (addNat · m) ⁻¹' uIoo (i.addNat m) (j.addNat m) = uIoo i j := by
  simp [uIoo, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]
theorem image_addNat_Ici (m) (i : Fin n) : (addNat · m) '' Ici i = Ici (i.addNat m) := by
  rw [← preimage_addNat_Ici_addNat, image_preimage_eq_of_subset]
  intro j hj
  have : (i : ℕ) + m ≤ j := hj
  refine ⟨⟨j - m, by cutsat⟩, ?_⟩
  simp (disch := omega)

@[simp]
theorem image_addNat_Ioi (m) (i : Fin n) : (addNat · m) '' Ioi i = Ioi (i.addNat m) := by
  rw [← preimage_addNat_Ioi_addNat, image_preimage_eq_of_subset]
  exact Ioi_subset_Ici_self.trans <| image_addNat_Ici m i ▸ image_subset_range _ _

@[simp]
theorem image_addNat_Icc (m) (i j : Fin n) :
    (addNat · m) '' Icc i j = Icc (i.addNat m) (j.addNat m) := by
  rw [← preimage_addNat_Icc_addNat, image_preimage_eq_of_subset]
  exact Icc_subset_Ici_self.trans <| image_addNat_Ici m i ▸ image_subset_range _ _

@[simp]
theorem image_addNat_Ico (m) (i j : Fin n) :
    (addNat · m) '' Ico i j = Ico (i.addNat m) (j.addNat m) := by
  rw [← preimage_addNat_Ico_addNat, image_preimage_eq_of_subset]
  exact Ico_subset_Ici_self.trans <| image_addNat_Ici m i ▸ image_subset_range _ _

@[simp]
theorem image_addNat_Ioc (m) (i j : Fin n) :
    (addNat · m) '' Ioc i j = Ioc (i.addNat m) (j.addNat m) := by
  rw [← preimage_addNat_Ioc_addNat, image_preimage_eq_of_subset]
  exact Ioc_subset_Ioi_self.trans <| image_addNat_Ioi m i ▸ image_subset_range _ _

@[simp]
theorem image_addNat_Ioo (m) (i j : Fin n) :
    (addNat · m) '' Ioo i j = Ioo (i.addNat m) (j.addNat m) := by
  rw [← preimage_addNat_Ioo_addNat, image_preimage_eq_of_subset]
  exact Ioo_subset_Ioi_self.trans <| image_addNat_Ioi m i ▸ image_subset_range _ _

@[simp]
theorem image_addNat_uIcc (m) (i j : Fin n) :
    (addNat · m) '' uIcc i j = uIcc (i.addNat m) (j.addNat m) := by
  simp [uIcc, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]
theorem image_addNat_uIoc (m) (i j : Fin n) :
    (addNat · m) '' uIoc i j = uIoc (i.addNat m) (j.addNat m) := by
  simp [uIoc, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

@[simp]
theorem image_addNat_uIoo (m) (i j : Fin n) :
    (addNat · m) '' uIoo i j = uIoo (i.addNat m) (j.addNat m) := by
  simp [uIoo, ← (strictMono_addNat m).monotone.map_max, ← (strictMono_addNat m).monotone.map_min]

/-!
### `Fin.succ`
-/

@[simp]
theorem preimage_succ_Ici_succ (i : Fin n) : succ ⁻¹' Ici i.succ = Ici i :=
  preimage_addNat_Ici_addNat ..

@[simp]
theorem preimage_succ_Ioi_succ (i : Fin n) : succ ⁻¹' Ioi i.succ = Ioi i :=
  preimage_addNat_Ioi_addNat ..

@[simp]
theorem preimage_succ_Iic_succ (i : Fin n) : succ ⁻¹' Iic i.succ = Iic i :=
  preimage_addNat_Iic_addNat ..

@[simp]
theorem preimage_succ_Iio_succ (i : Fin n) : succ ⁻¹' Iio i.succ = Iio i :=
  preimage_addNat_Iio_addNat ..

@[simp]
theorem preimage_succ_Icc_succ (i j : Fin n) : succ ⁻¹' Icc i.succ j.succ = Icc i j :=
  preimage_addNat_Icc_addNat ..

@[simp]
theorem preimage_succ_Ico_succ (i j : Fin n) : succ ⁻¹' Ico i.succ j.succ = Ico i j :=
  preimage_addNat_Ico_addNat ..

@[simp]
theorem preimage_succ_Ioc_succ (i j : Fin n) : succ ⁻¹' Ioc i.succ j.succ = Ioc i j :=
  preimage_addNat_Ioc_addNat ..

@[simp]
theorem preimage_succ_Ioo_succ (i j : Fin n) : succ ⁻¹' Ioo i.succ j.succ = Ioo i j :=
  preimage_addNat_Ioo_addNat ..

@[simp]
theorem preimage_succ_uIcc_succ (i j : Fin n) : succ ⁻¹' uIcc i.succ j.succ = uIcc i j :=
  preimage_addNat_uIcc_addNat ..

@[simp]
theorem preimage_succ_uIoc_succ (i j : Fin n) : succ ⁻¹' uIoc i.succ j.succ = uIoc i j :=
  preimage_addNat_uIoc_addNat ..

@[simp]
theorem preimage_succ_uIoo_succ (i j : Fin n) : succ ⁻¹' uIoo i.succ j.succ = uIoo i j :=
  preimage_addNat_uIoo_addNat ..

@[simp] theorem image_succ_Ici (i : Fin n) : succ '' Ici i = Ici i.succ := image_addNat_Ici ..
@[simp] theorem image_succ_Ioi (i : Fin n) : succ '' Ioi i = Ioi i.succ := image_addNat_Ioi ..

@[simp]
theorem image_succ_Iic (i : Fin n) : succ '' Iic i = Ioc 0 i.succ := by
  refine Subset.antisymm (image_subset_iff.mpr fun j hj ↦ ⟨j.succ_pos, succ_le_succ_iff.2 hj⟩) ?_
  rintro j ⟨hj₀, hj⟩
  rcases exists_succ_eq_of_ne_zero hj₀.ne' with ⟨j, rfl⟩
  exact mem_image_of_mem _ <| succ_le_succ_iff.mp hj

@[simp]
theorem image_succ_Iio (i : Fin n) : succ '' Iio i = Ioo 0 i.succ := by
  refine Subset.antisymm (image_subset_iff.mpr fun j hj ↦ ⟨j.succ_pos, succ_lt_succ_iff.2 hj⟩) ?_
  rintro j ⟨hj₀, hj⟩
  rcases exists_succ_eq_of_ne_zero hj₀.ne' with ⟨j, rfl⟩
  exact mem_image_of_mem _ <| succ_lt_succ_iff.mp hj

@[simp]
theorem image_succ_Icc (i j : Fin n) : succ '' Icc i j = Icc i.succ j.succ := image_addNat_Icc ..

@[simp]
theorem image_succ_Ico (i j : Fin n) : succ '' Ico i j = Ico i.succ j.succ := image_addNat_Ico ..

@[simp]
theorem image_succ_Ioc (i j : Fin n) : succ '' Ioc i j = Ioc i.succ j.succ := image_addNat_Ioc ..

@[simp]
theorem image_succ_Ioo (i j : Fin n) : succ '' Ioo i j = Ioo i.succ j.succ := image_addNat_Ioo ..

@[simp]
theorem image_succ_uIcc (i j : Fin n) : succ '' uIcc i j = uIcc i.succ j.succ :=
  image_addNat_uIcc ..

@[simp]
theorem image_succ_uIoc (i j : Fin n) : succ '' uIoc i j = uIoc i.succ j.succ :=
  image_addNat_uIoc ..

@[simp]
theorem image_succ_uIoo (i j : Fin n) : succ '' uIoo i j = uIoo i.succ j.succ :=
  image_addNat_uIoo ..

/-!
### `Fin.rev`
-/

@[simp]
theorem range_rev : range (rev : Fin n → Fin n) = univ := rev_surjective.range_eq

theorem image_rev (s : Set (Fin n)) : rev '' s = rev ⁻¹' s := revPerm.image_eq_preimage s

@[simp]
theorem image_rev_fun : image (@rev n) = preimage rev := funext image_rev

@[simp]
theorem preimage_rev_Ici (i : Fin n) : rev ⁻¹' Ici i = Iic i.rev := by ext; simp [le_rev_iff]

@[simp]
theorem preimage_rev_Ioi (i : Fin n) : rev ⁻¹' Ioi i = Iio i.rev := by ext; simp [lt_rev_iff]

@[simp]
theorem preimage_rev_Iic (i : Fin n) : rev ⁻¹' Iic i = Ici i.rev := by ext; simp [rev_le_iff]

@[simp]
theorem preimage_rev_Iio (i : Fin n) : rev ⁻¹' Iio i = Ioi i.rev := by ext; simp [rev_lt_iff]

@[simp]
theorem preimage_rev_Icc (i j : Fin n) : rev ⁻¹' Icc i j = Icc j.rev i.rev := by
  ext; simp [le_rev_iff, rev_le_iff, and_comm]

@[simp]
theorem preimage_rev_Ico (i j : Fin n) : rev ⁻¹' Ico i j = Ioc j.rev i.rev := by
  ext; simp [le_rev_iff, rev_lt_iff, and_comm]

@[simp]
theorem preimage_rev_Ioc (i j : Fin n) : rev ⁻¹' Ioc i j = Ico j.rev i.rev := by
  ext; simp [lt_rev_iff, rev_le_iff, and_comm]

@[simp]
theorem preimage_rev_Ioo (i j : Fin n) : rev ⁻¹' Ioo i j = Ioo j.rev i.rev := by
  ext; simp [lt_rev_iff, rev_lt_iff, and_comm]

@[simp]
theorem preimage_rev_uIcc (i j : Fin n) : rev ⁻¹' uIcc i j = uIcc i.rev j.rev := by
  simp [uIcc, ← rev_anti.map_min, ← rev_anti.map_max]

@[simp]
theorem preimage_rev_uIoo (i j : Fin n) : rev ⁻¹' uIoo i j = uIoo i.rev j.rev := by
  simp [uIoo, ← rev_anti.map_min, ← rev_anti.map_max]

end Fin
