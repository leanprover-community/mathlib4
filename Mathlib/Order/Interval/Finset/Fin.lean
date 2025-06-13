/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Yury Kudryashov
-/
import Mathlib.Data.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Fin

/-!
# Finite intervals in `Fin n`

This file proves that `Fin n` is a `LocallyFiniteOrder` and calculates the cardinality of its
intervals as Finsets and Fintypes.
-/

assert_not_exists MonoidWithZero

open Finset Function

namespace Fin

variable (n : ℕ)

/-!
### Locally finite order etc instances
-/

instance instLocallyFiniteOrder (n : ℕ) : LocallyFiniteOrder (Fin n) where
  finsetIcc a b := attachFin (Icc a b) fun x hx ↦ (mem_Icc.mp hx).2.trans_lt b.2
  finsetIco a b := attachFin (Ico a b) fun x hx ↦ (mem_Ico.mp hx).2.trans b.2
  finsetIoc a b := attachFin (Ioc a b) fun x hx ↦ (mem_Ioc.mp hx).2.trans_lt b.2
  finsetIoo a b := attachFin (Ioo a b) fun x hx ↦ (mem_Ioo.mp hx).2.trans b.2
  finset_mem_Icc a b := by simp
  finset_mem_Ico a b := by simp
  finset_mem_Ioc a b := by simp
  finset_mem_Ioo a b := by simp

instance instLocallyFiniteOrderBot : ∀ n, LocallyFiniteOrderBot (Fin n)
  | 0 => IsEmpty.toLocallyFiniteOrderBot
  | _ + 1 => inferInstance

instance instLocallyFiniteOrderTop : ∀ n, LocallyFiniteOrderTop (Fin n)
  | 0 => IsEmpty.toLocallyFiniteOrderTop
  | _ + 1 => inferInstance

variable {n}
variable {m : ℕ} (a b : Fin n)

@[simp]
theorem attachFin_Icc :
    attachFin (Icc a b) (fun _x hx ↦ (mem_Icc.mp hx).2.trans_lt b.2) = Icc a b :=
  rfl

@[simp]
theorem attachFin_Ico :
    attachFin (Ico a b) (fun _x hx ↦ (mem_Ico.mp hx).2.trans b.2) = Ico a b :=
  rfl

@[simp]
theorem attachFin_Ioc :
    attachFin (Ioc a b) (fun _x hx ↦ (mem_Ioc.mp hx).2.trans_lt b.2) = Ioc a b :=
  rfl

@[simp]
theorem attachFin_Ioo :
    attachFin (Ioo a b) (fun _x hx ↦ (mem_Ioo.mp hx).2.trans b.2) = Ioo a b :=
  rfl

@[simp]
theorem attachFin_uIcc :
    attachFin (uIcc a b) (fun _x hx ↦ (mem_Icc.mp hx).2.trans_lt (max a b).2) = uIcc a b :=
  rfl

@[simp]
theorem attachFin_Ico_eq_Ici : attachFin (Ico a n) (fun _x hx ↦ (mem_Ico.mp hx).2) = Ici a := by
  ext; simp

@[simp]
theorem attachFin_Ioo_eq_Ioi : attachFin (Ioo a n) (fun _x hx ↦ (mem_Ioo.mp hx).2) = Ioi a := by
  ext; simp

@[simp]
theorem attachFin_Iic : attachFin (Iic a) (fun _x hx ↦ (mem_Iic.mp hx).trans_lt a.2) = Iic a := by
  ext; simp

@[simp]
theorem attachFin_Iio : attachFin (Iio a) (fun _x hx ↦ (mem_Iio.mp hx).trans a.2) = Iio a := by
  ext; simp

section deprecated

set_option linter.deprecated false in
@[deprecated attachFin_Icc (since := "2025-04-06")]
theorem Icc_eq_finset_subtype : Icc a b = (Icc (a : ℕ) b).fin n := attachFin_eq_fin _

set_option linter.deprecated false in
@[deprecated attachFin_Ico (since := "2025-04-06")]
theorem Ico_eq_finset_subtype : Ico a b = (Ico (a : ℕ) b).fin n := attachFin_eq_fin _

set_option linter.deprecated false in
@[deprecated attachFin_Ioc (since := "2025-04-06")]
theorem Ioc_eq_finset_subtype : Ioc a b = (Ioc (a : ℕ) b).fin n := attachFin_eq_fin _

set_option linter.deprecated false in
@[deprecated attachFin_Ioo (since := "2025-04-06")]
theorem Ioo_eq_finset_subtype : Ioo a b = (Ioo (a : ℕ) b).fin n := attachFin_eq_fin _

set_option linter.deprecated false in
@[deprecated attachFin_uIcc (since := "2025-04-06")]
theorem uIcc_eq_finset_subtype : uIcc a b = (uIcc (a : ℕ) b).fin n := Icc_eq_finset_subtype _ _

set_option linter.deprecated false in
@[deprecated attachFin_Ico_eq_Ici (since := "2025-04-06")]
theorem Ici_eq_finset_subtype : Ici a = (Ico (a : ℕ) n).fin n := by ext; simp

set_option linter.deprecated false in
@[deprecated attachFin_Ioo_eq_Ioi (since := "2025-04-06")]
theorem Ioi_eq_finset_subtype : Ioi a = (Ioo (a : ℕ) n).fin n := by ext; simp

set_option linter.deprecated false in
@[deprecated attachFin_Iic (since := "2025-04-06")]
theorem Iic_eq_finset_subtype : Iic b = (Iic (b : ℕ)).fin n := by ext; simp

set_option linter.deprecated false in
@[deprecated attachFin_Iio (since := "2025-04-06")]
theorem Iio_eq_finset_subtype : Iio b = (Iio (b : ℕ)).fin n := by ext; simp

end deprecated

section val

/-!
### Images under `Fin.val`
-/

@[simp]
theorem finsetImage_val_Icc : (Icc a b).image val = Icc (a : ℕ) b :=
  image_val_attachFin _

@[simp]
theorem finsetImage_val_Ico : (Ico a b).image val = Ico (a : ℕ) b :=
  image_val_attachFin _

@[simp]
theorem finsetImage_val_Ioc : (Ioc a b).image val = Ioc (a : ℕ) b :=
  image_val_attachFin _

@[simp]
theorem finsetImage_val_Ioo : (Ioo a b).image val = Ioo (a : ℕ) b :=
  image_val_attachFin _

@[simp]
theorem finsetImage_val_uIcc : (uIcc a b).image val = uIcc (a : ℕ) b :=
  finsetImage_val_Icc _ _

@[simp]
theorem finsetImage_val_Ici : (Ici a).image val = Ico (a : ℕ) n := by simp [← coe_inj]

@[simp]
theorem finsetImage_val_Ioi : (Ioi a).image val = Ioo (a : ℕ) n := by simp [← coe_inj]

@[simp]
theorem finsetImage_val_Iic : (Iic a).image val = Iic (a : ℕ) := by simp [← coe_inj]

@[simp]
theorem finsetImage_val_Iio : (Iio b).image val = Iio (b : ℕ) := by simp [← coe_inj]

/-!
### `Finset.map` along `Fin.valEmbedding`
-/

@[simp]
theorem map_valEmbedding_Icc : (Icc a b).map Fin.valEmbedding = Icc (a : ℕ) b :=
  map_valEmbedding_attachFin _

@[simp]
theorem map_valEmbedding_Ico : (Ico a b).map Fin.valEmbedding = Ico (a : ℕ) b :=
  map_valEmbedding_attachFin _

@[simp]
theorem map_valEmbedding_Ioc : (Ioc a b).map Fin.valEmbedding = Ioc (a : ℕ) b :=
  map_valEmbedding_attachFin _

@[simp]
theorem map_valEmbedding_Ioo : (Ioo a b).map Fin.valEmbedding = Ioo (a : ℕ) b :=
  map_valEmbedding_attachFin _

@[simp]
theorem map_valEmbedding_uIcc : (uIcc a b).map valEmbedding = uIcc (a : ℕ) b :=
  map_valEmbedding_Icc _ _

@[deprecated (since := "2025-04-08")]
alias map_subtype_embedding_uIcc := map_valEmbedding_uIcc

@[simp]
theorem map_valEmbedding_Ici : (Ici a).map Fin.valEmbedding = Ico (a : ℕ) n := by
  rw [← attachFin_Ico_eq_Ici, map_valEmbedding_attachFin]

@[simp]
theorem map_valEmbedding_Ioi : (Ioi a).map Fin.valEmbedding = Ioo (a : ℕ) n := by
  rw [← attachFin_Ioo_eq_Ioi, map_valEmbedding_attachFin]

@[simp]
theorem map_valEmbedding_Iic : (Iic a).map Fin.valEmbedding = Iic (a : ℕ) := by
  rw [← attachFin_Iic, map_valEmbedding_attachFin]

@[simp]
theorem map_valEmbedding_Iio : (Iio a).map Fin.valEmbedding = Iio (a : ℕ) := by
  rw [← attachFin_Iio, map_valEmbedding_attachFin]

end val

section castLE

/-!
### Image under `Fin.castLE`
-/

@[simp]
theorem finsetImage_castLE_Icc (h : n ≤ m) :
    (Icc a b).image (castLE h) = Icc (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
theorem finsetImage_castLE_Ico (h : n ≤ m) :
    (Ico a b).image (castLE h) = Ico (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
theorem finsetImage_castLE_Ioc (h : n ≤ m) :
    (Ioc a b).image (castLE h) = Ioc (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
theorem finsetImage_castLE_Ioo (h : n ≤ m) :
    (Ioo a b).image (castLE h) = Ioo (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
theorem finsetImage_castLE_uIcc (h : n ≤ m) :
    (uIcc a b).image (castLE h) = uIcc (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
theorem finsetImage_castLE_Iic (h : n ≤ m) :
    (Iic a).image (castLE h) = Iic (castLE h a) := by simp [← coe_inj]

@[simp]
theorem finsetImage_castLE_Iio (h : n ≤ m) :
    (Iio a).image (castLE h) = Iio (castLE h a) := by simp [← coe_inj]

/-!
### `Finset.map` along `Fin.castLEEmb`
-/

@[simp]
theorem map_castLEEmb_Icc (h : n ≤ m) :
    (Icc a b).map (castLEEmb h) = Icc (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
theorem map_castLEEmb_Ico (h : n ≤ m) :
    (Ico a b).map (castLEEmb h) = Ico (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
theorem map_castLEEmb_Ioc (h : n ≤ m) :
    (Ioc a b).map (castLEEmb h) = Ioc (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
theorem map_castLEEmb_Ioo (h : n ≤ m) :
    (Ioo a b).map (castLEEmb h) = Ioo (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
theorem map_castLEEmb_uIcc (h : n ≤ m) :
    (uIcc a b).map (castLEEmb h) = uIcc (castLE h a) (castLE h b) := by simp [← coe_inj]

@[simp]
theorem map_castLEEmb_Iic (h : n ≤ m) :
    (Iic a).map (castLEEmb h) = Iic (castLE h a) := by simp [← coe_inj]

@[simp]
theorem map_castLEEmb_Iio (h : n ≤ m) :
    (Iio a).map (castLEEmb h) = Iio (castLE h a) := by simp [← coe_inj]

end castLE

section castAdd

/-!
### Images under `Fin.castAdd`
-/

@[simp]
theorem finsetImage_castAdd_Icc (m) (i j : Fin n) :
    (Icc i j).image (castAdd m) = Icc (castAdd m i) (castAdd m j) :=
  finsetImage_castLE_Icc ..

@[simp]
theorem finsetImage_castAdd_Ico (m) (i j : Fin n) :
    (Ico i j).image (castAdd m) = Ico (castAdd m i) (castAdd m j) :=
  finsetImage_castLE_Ico ..

@[simp]
theorem finsetImage_castAdd_Ioc (m) (i j : Fin n) :
    (Ioc i j).image (castAdd m) = Ioc (castAdd m i) (castAdd m j) :=
  finsetImage_castLE_Ioc ..

@[simp]
theorem finsetImage_castAdd_Ioo (m) (i j : Fin n) :
    (Ioo i j).image (castAdd m) = Ioo (castAdd m i) (castAdd m j) :=
  finsetImage_castLE_Ioo ..

@[simp]
theorem finsetImage_castAdd_uIcc (m) (i j : Fin n) :
    (uIcc i j).image (castAdd m) = uIcc (castAdd m i) (castAdd m j) :=
  finsetImage_castLE_uIcc ..

@[simp]
theorem finsetImage_castAdd_Ici (m) [NeZero m] (i : Fin n) :
    (Ici i).image (castAdd m) = Ico (castAdd m i) (natAdd n 0) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_castAdd_Ioi (m) [NeZero m] (i : Fin n) :
    (Ioi i).image (castAdd m) = Ioo (castAdd m i) (natAdd n 0) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_castAdd_Iic (m) (i : Fin n) : (Iic i).image (castAdd m) = Iic (castAdd m i) :=
  finsetImage_castLE_Iic i _

@[simp]
theorem finsetImage_castAdd_Iio (m) (i : Fin n) : (Iio i).image (castAdd m) = Iio (castAdd m i) :=
  finsetImage_castLE_Iio ..

/-!
### `Finset.map` along `Fin.castAddEmb`
-/

@[simp]
theorem map_castAddEmb_Icc (m) (i j : Fin n) :
    (Icc i j).map (castAddEmb m) = Icc (castAdd m i) (castAdd m j) :=
  map_castLEEmb_Icc ..

@[simp]
theorem map_castAddEmb_Ico (m) (i j : Fin n) :
    (Ico i j).map (castAddEmb m) = Ico (castAdd m i) (castAdd m j) :=
  map_castLEEmb_Ico ..

@[simp]
theorem map_castAddEmb_Ioc (m) (i j : Fin n) :
    (Ioc i j).map (castAddEmb m) = Ioc (castAdd m i) (castAdd m j) :=
  map_castLEEmb_Ioc ..

@[simp]
theorem map_castAddEmb_Ioo (m) (i j : Fin n) :
    (Ioo i j).map (castAddEmb m) = Ioo (castAdd m i) (castAdd m j) :=
  map_castLEEmb_Ioo ..

@[simp]
theorem map_castAddEmb_uIcc (m) (i j : Fin n) :
    (uIcc i j).map (castAddEmb m) = uIcc (castAdd m i) (castAdd m j) :=
  map_castLEEmb_uIcc ..

@[simp]
theorem map_castAddEmb_Ici (m) [NeZero m] (i : Fin n) :
    (Ici i).map (castAddEmb m) = Ico (castAdd m i) (natAdd n 0) := by
  simp [map_eq_image]

@[simp]
theorem map_castAddEmb_Ioi (m) [NeZero m] (i : Fin n) :
    (Ioi i).map (castAddEmb m) = Ioo (castAdd m i) (natAdd n 0) := by
  simp [← coe_inj]

@[simp]
theorem map_castAddEmb_Iic (m) (i : Fin n) : (Iic i).map (castAddEmb m) = Iic (castAdd m i) :=
  map_castLEEmb_Iic i _

@[simp]
theorem map_castAddEmb_Iio (m) (i : Fin n) : (Iio i).map (castAddEmb m) = Iio (castAdd m i) :=
  map_castLEEmb_Iio ..

end castAdd

section cast

/-!
### Images under `Fin.cast`
-/

@[simp]
theorem finsetImage_cast_Icc (h : n = m) (i j : Fin n) :
    (Icc i j).image (.cast h) = Icc (i.cast h) (j.cast h) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_cast_Ico (h : n = m) (i j : Fin n) :
    (Ico i j).image (.cast h) = Ico (i.cast h) (j.cast h) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_cast_Ioc (h : n = m) (i j : Fin n) :
    (Ioc i j).image (.cast h) = Ioc (i.cast h) (j.cast h) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_cast_Ioo (h : n = m) (i j : Fin n) :
    (Ioo i j).image (.cast h) = Ioo (i.cast h) (j.cast h) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_cast_uIcc (h : n = m) (i j : Fin n) :
    (uIcc i j).image (.cast h) = uIcc (i.cast h) (j.cast h) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_cast_Ici (h : n = m) (i : Fin n) :
    (Ici i).image (.cast h) = Ici (i.cast h) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_cast_Ioi (h : n = m) (i : Fin n) :
    (Ioi i).image (.cast h) = Ioi (i.cast h) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_cast_Iic (h : n = m) (i : Fin n) :
    (Iic i).image (.cast h) = Iic (i.cast h) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_cast_Iio (h : n = m) (i : Fin n) :
    (Iio i).image (.cast h) = Iio (i.cast h) := by
  simp [← coe_inj]

/-!
### `Finset.map` along `finCongr`
-/

@[simp]
theorem map_finCongr_Icc (h : n = m) (i j : Fin n) :
    (Icc i j).map (finCongr h).toEmbedding = Icc (i.cast h) (j.cast h) := by
  simp [← coe_inj]

@[simp]
theorem map_finCongr_Ico (h : n = m) (i j : Fin n) :
    (Ico i j).map (finCongr h).toEmbedding = Ico (i.cast h) (j.cast h) := by
  simp [← coe_inj]

@[simp]
theorem map_finCongr_Ioc (h : n = m) (i j : Fin n) :
    (Ioc i j).map (finCongr h).toEmbedding = Ioc (i.cast h) (j.cast h) := by
  simp [← coe_inj]

@[simp]
theorem map_finCongr_Ioo (h : n = m) (i j : Fin n) :
    (Ioo i j).map (finCongr h).toEmbedding = Ioo (i.cast h) (j.cast h) := by
  simp [← coe_inj]

@[simp]
theorem map_finCongr_uIcc (h : n = m) (i j : Fin n) :
    (uIcc i j).map (finCongr h).toEmbedding = uIcc (i.cast h) (j.cast h) := by
  simp [← coe_inj]

@[simp]
theorem map_finCongr_Ici (h : n = m) (i : Fin n) :
    (Ici i).map (finCongr h).toEmbedding = Ici (i.cast h) := by
  simp [← coe_inj]

@[simp]
theorem map_finCongr_Ioi (h : n = m) (i : Fin n) :
    (Ioi i).map (finCongr h).toEmbedding = Ioi (i.cast h) := by
  simp [← coe_inj]

@[simp]
theorem map_finCongr_Iic (h : n = m) (i : Fin n) :
    (Iic i).map (finCongr h).toEmbedding = Iic (i.cast h) := by
  simp [← coe_inj]

@[simp]
theorem map_finCongr_Iio (h : n = m) (i : Fin n) :
    (Iio i).map (finCongr h).toEmbedding = Iio (i.cast h) := by
  simp [← coe_inj]

end cast

section castSucc

/-!
### Images under `Fin.castSucc`
-/

@[simp]
theorem finsetImage_castSucc_Icc (i j : Fin n) :
    (Icc i j).image castSucc = Icc i.castSucc j.castSucc :=
  finsetImage_castAdd_Icc ..

@[simp]
theorem finsetImage_castSucc_Ico (i j : Fin n) :
    (Ico i j).image castSucc = Ico i.castSucc j.castSucc :=
  finsetImage_castAdd_Ico ..

@[simp]
theorem finsetImage_castSucc_Ioc (i j : Fin n) :
    (Ioc i j).image castSucc = Ioc i.castSucc j.castSucc :=
  finsetImage_castAdd_Ioc ..

@[simp]
theorem finsetImage_castSucc_Ioo (i j : Fin n) :
    (Ioo i j).image castSucc = Ioo i.castSucc j.castSucc :=
  finsetImage_castAdd_Ioo ..

@[simp]
theorem finsetImage_castSucc_uIcc (i j : Fin n) :
    (uIcc i j).image castSucc = uIcc i.castSucc j.castSucc :=
  finsetImage_castAdd_uIcc ..

@[simp]
theorem finsetImage_castSucc_Ici (i : Fin n) : (Ici i).image castSucc = Ico i.castSucc (.last n) :=
  finsetImage_castAdd_Ici ..

@[simp]
theorem finsetImage_castSucc_Ioi (i : Fin n) : (Ioi i).image castSucc = Ioo i.castSucc (.last n) :=
  finsetImage_castAdd_Ioi ..

@[simp]
theorem finsetImage_castSucc_Iic (i : Fin n) : (Iic i).image castSucc = Iic i.castSucc :=
  finsetImage_castAdd_Iic ..

@[simp]
theorem finsetImage_castSucc_Iio (i : Fin n) : (Iio i).image castSucc = Iio i.castSucc :=
  finsetImage_castAdd_Iio ..

/-!
### `Finset.map` along `Fin.castSuccEmb`
-/

@[simp]
theorem map_castSuccEmb_Icc (i j : Fin n) :
    (Icc i j).map castSuccEmb = Icc i.castSucc j.castSucc :=
  map_castAddEmb_Icc ..

@[simp]
theorem map_castSuccEmb_Ico (i j : Fin n) :
    (Ico i j).map castSuccEmb = Ico i.castSucc j.castSucc :=
  map_castAddEmb_Ico ..

@[simp]
theorem map_castSuccEmb_Ioc (i j : Fin n) :
    (Ioc i j).map castSuccEmb = Ioc i.castSucc j.castSucc :=
  map_castAddEmb_Ioc ..

@[simp]
theorem map_castSuccEmb_Ioo (i j : Fin n) :
    (Ioo i j).map castSuccEmb = Ioo i.castSucc j.castSucc :=
  map_castAddEmb_Ioo ..

@[simp]
theorem map_castSuccEmb_uIcc (i j : Fin n) :
    (uIcc i j).map castSuccEmb = uIcc i.castSucc j.castSucc :=
  map_castAddEmb_uIcc ..

@[simp]
theorem map_castSuccEmb_Ici (i : Fin n) : (Ici i).map castSuccEmb = Ico i.castSucc (.last n) :=
  map_castAddEmb_Ici ..

@[simp]
theorem map_castSuccEmb_Ioi (i : Fin n) : (Ioi i).map castSuccEmb = Ioo i.castSucc (.last n) :=
  map_castAddEmb_Ioi ..

@[simp]
theorem map_castSuccEmb_Iic (i : Fin n) : (Iic i).map castSuccEmb = Iic i.castSucc :=
  map_castAddEmb_Iic ..

@[simp]
theorem map_castSuccEmb_Iio (i : Fin n) : (Iio i).map castSuccEmb = Iio i.castSucc :=
  map_castAddEmb_Iio ..

end castSucc

section natAdd

/-!
### Images under `Fin.natAdd`
-/

@[simp]
theorem finsetImage_natAdd_Icc (m) (i j : Fin n) :
    (Icc i j).image (natAdd m) = Icc (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_natAdd_Ico (m) (i j : Fin n) :
    (Ico i j).image (natAdd m) = Ico (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_natAdd_Ioc (m) (i j : Fin n) :
    (Ioc i j).image (natAdd m) = Ioc (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_natAdd_Ioo (m) (i j : Fin n) :
    (Ioo i j).image (natAdd m) = Ioo (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_natAdd_uIcc (m) (i j : Fin n) :
    (uIcc i j).image (natAdd m) = uIcc (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_natAdd_Ici (m) (i : Fin n) : (Ici i).image (natAdd m) = Ici (natAdd m i) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_natAdd_Ioi (m) (i : Fin n) : (Ioi i).image (natAdd m) = Ioi (natAdd m i) := by
  simp [← coe_inj]

/-!
### `Finset.map` along `Fin.natAddEmb`
-/

@[simp]
theorem map_natAddEmb_Icc (m) (i j : Fin n) :
    (Icc i j).map (natAddEmb m) = Icc (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

@[simp]
theorem map_natAddEmb_Ico (m) (i j : Fin n) :
    (Ico i j).map (natAddEmb m) = Ico (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

@[simp]
theorem map_natAddEmb_Ioc (m) (i j : Fin n) :
    (Ioc i j).map (natAddEmb m) = Ioc (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

@[simp]
theorem map_natAddEmb_Ioo (m) (i j : Fin n) :
    (Ioo i j).map (natAddEmb m) = Ioo (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

@[simp]
theorem map_natAddEmb_uIcc (m) (i j : Fin n) :
    (uIcc i j).map (natAddEmb m) = uIcc (natAdd m i) (natAdd m j) := by
  simp [← coe_inj]

@[simp]
theorem map_natAddEmb_Ici (m) (i : Fin n) : (Ici i).map (natAddEmb m) = Ici (natAdd m i) := by
  simp [← coe_inj]

@[simp]
theorem map_natAddEmb_Ioi (m) (i : Fin n) : (Ioi i).map (natAddEmb m) = Ioi (natAdd m i) := by
  simp [← coe_inj]

end natAdd

section addNat

/-!
### Images under `Fin.addNat`
-/

@[simp]
theorem finsetImage_addNat_Icc (m) (i j : Fin n) :
    (Icc i j).image (addNat · m) = Icc (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_addNat_Ico (m) (i j : Fin n) :
    (Ico i j).image (addNat · m) = Ico (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_addNat_Ioc (m) (i j : Fin n) :
    (Ioc i j).image (addNat · m) = Ioc (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_addNat_Ioo (m) (i j : Fin n) :
    (Ioo i j).image (addNat · m) = Ioo (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_addNat_uIcc (m) (i j : Fin n) :
    (uIcc i j).image (addNat · m) = uIcc (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_addNat_Ici (m) (i : Fin n) : (Ici i).image (addNat · m) = Ici (i.addNat m) := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_addNat_Ioi (m) (i : Fin n) : (Ioi i).image (addNat · m) = Ioi (i.addNat m) := by
  simp [← coe_inj]

/-!
### `Finset.map` along `Fin.addNatEmb`
-/

@[simp]
theorem map_addNatEmb_Icc (m) (i j : Fin n) :
    (Icc i j).map (addNatEmb m) = Icc (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

@[simp]
theorem map_addNatEmb_Ico (m) (i j : Fin n) :
    (Ico i j).map (addNatEmb m) = Ico (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

@[simp]
theorem map_addNatEmb_Ioc (m) (i j : Fin n) :
    (Ioc i j).map (addNatEmb m) = Ioc (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

@[simp]
theorem map_addNatEmb_Ioo (m) (i j : Fin n) :
    (Ioo i j).map (addNatEmb m) = Ioo (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

@[simp]
theorem map_addNatEmb_uIcc (m) (i j : Fin n) :
    (uIcc i j).map (addNatEmb m) = uIcc (i.addNat m) (j.addNat m) := by
  simp [← coe_inj]

@[simp]
theorem map_addNatEmb_Ici (m) (i : Fin n) : (Ici i).map (addNatEmb m) = Ici (i.addNat m) := by
  simp [← coe_inj]

@[simp]
theorem map_addNatEmb_Ioi (m) (i : Fin n) : (Ioi i).map (addNatEmb m) = Ioi (i.addNat m) := by
  simp [← coe_inj]

end addNat

section succ

/-!
### Images under `Fin.succ`
-/

@[simp]
theorem finsetImage_succ_Icc (i j : Fin n) : (Icc i j).image succ = Icc i.succ j.succ :=
  finsetImage_addNat_Icc ..

@[simp]
theorem finsetImage_succ_Ico (i j : Fin n) : (Ico i j).image succ = Ico i.succ j.succ :=
  finsetImage_addNat_Ico ..

@[simp]
theorem finsetImage_succ_Ioc (i j : Fin n) : (Ioc i j).image succ = Ioc i.succ j.succ :=
  finsetImage_addNat_Ioc ..

@[simp]
theorem finsetImage_succ_Ioo (i j : Fin n) : (Ioo i j).image succ = Ioo i.succ j.succ :=
  finsetImage_addNat_Ioo ..

@[simp]
theorem finsetImage_succ_uIcc (i j : Fin n) : (uIcc i j).image succ = uIcc i.succ j.succ :=
  finsetImage_addNat_uIcc ..

@[simp]
theorem finsetImage_succ_Ici (i : Fin n) : (Ici i).image succ = Ici i.succ :=
  finsetImage_addNat_Ici ..

@[simp]
theorem finsetImage_succ_Ioi (i : Fin n) : (Ioi i).image succ = Ioi i.succ :=
  finsetImage_addNat_Ioi ..

@[simp]
theorem finsetImage_succ_Iic (i : Fin n) : (Iic i).image succ = Ioc 0 i.succ := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_succ_Iio (i : Fin n) : (Iio i).image succ = Ioo 0 i.succ := by
  simp [← coe_inj]

/-!
### `Finset.map` along `Fin.succEmb`
-/

@[simp]
theorem map_succEmb_Icc (i j : Fin n) : (Icc i j).map (succEmb n) = Icc i.succ j.succ :=
  map_addNatEmb_Icc ..

@[simp]
theorem map_succEmb_Ico (i j : Fin n) : (Ico i j).map (succEmb n) = Ico i.succ j.succ :=
  map_addNatEmb_Ico ..

@[simp]
theorem map_succEmb_Ioc (i j : Fin n) : (Ioc i j).map (succEmb n) = Ioc i.succ j.succ :=
  map_addNatEmb_Ioc ..

@[simp]
theorem map_succEmb_Ioo (i j : Fin n) : (Ioo i j).map (succEmb n) = Ioo i.succ j.succ :=
  map_addNatEmb_Ioo ..

@[simp]
theorem map_succEmb_uIcc (i j : Fin n) : (uIcc i j).map (succEmb n) = uIcc i.succ j.succ :=
  map_addNatEmb_uIcc ..

@[simp]
theorem map_succEmb_Ici (i : Fin n) : (Ici i).map (succEmb n) = Ici i.succ :=
  map_addNatEmb_Ici ..

@[simp]
theorem map_succEmb_Ioi (i : Fin n) : (Ioi i).map (succEmb n) = Ioi i.succ :=
  map_addNatEmb_Ioi ..

@[simp]
theorem map_succEmb_Iic (i : Fin n) : (Iic i).map (succEmb n) = Ioc 0 i.succ := by
  simp [← coe_inj]

@[simp]
theorem map_succEmb_Iio (i : Fin n) : (Iio i).map (succEmb n) = Ioo 0 i.succ := by
  simp [← coe_inj]

end succ

section rev

/-!
### Images under `Fin.rev`
-/

@[simp]
theorem finsetImage_rev_Icc (i j : Fin n) : (Icc i j).image rev = Icc j.rev i.rev := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_rev_Ico (i j : Fin n) : (Ico i j).image rev = Ioc j.rev i.rev := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_rev_Ioc (i j : Fin n) : (Ioc i j).image rev = Ico j.rev i.rev := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_rev_Ioo (i j : Fin n) : (Ioo i j).image rev = Ioo j.rev i.rev := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_rev_uIcc (i j : Fin n) : (uIcc i j).image rev = uIcc i.rev j.rev := by
  simp [← coe_inj]

@[simp]
theorem finsetImage_rev_Ici (i : Fin n) : (Ici i).image rev = Iic i.rev := by simp [← coe_inj]

@[simp]
theorem finsetImage_rev_Ioi (i : Fin n) : (Ioi i).image rev = Iio i.rev := by simp [← coe_inj]

@[simp]
theorem finsetImage_rev_Iic (i : Fin n) : (Iic i).image rev = Ici i.rev := by simp [← coe_inj]

@[simp]
theorem finsetImage_rev_Iio (i : Fin n) : (Iio i).image rev = Ioi i.rev := by simp [← coe_inj]

/-!
### `Finset.map` along `revPerm`
-/

@[simp]
theorem map_revPerm_Icc (i j : Fin n) : (Icc i j).map revPerm.toEmbedding = Icc j.rev i.rev := by
  simp [← coe_inj]

@[simp]
theorem map_revPerm_Ico (i j : Fin n) : (Ico i j).map revPerm.toEmbedding = Ioc j.rev i.rev := by
  simp [← coe_inj]

@[simp]
theorem map_revPerm_Ioc (i j : Fin n) : (Ioc i j).map revPerm.toEmbedding = Ico j.rev i.rev := by
  simp [← coe_inj]

@[simp]
theorem map_revPerm_Ioo (i j : Fin n) : (Ioo i j).map revPerm.toEmbedding = Ioo j.rev i.rev := by
  simp [← coe_inj]

@[simp]
theorem map_revPerm_uIcc (i j : Fin n) : (uIcc i j).map revPerm.toEmbedding = uIcc i.rev j.rev := by
  simp [← coe_inj]

@[simp]
theorem map_revPerm_Ici (i : Fin n) : (Ici i).map revPerm.toEmbedding = Iic i.rev := by
  simp [← coe_inj]

@[simp]
theorem map_revPerm_Ioi (i : Fin n) : (Ioi i).map revPerm.toEmbedding = Iio i.rev := by
  simp [← coe_inj]

@[simp]
theorem map_revPerm_Iic (i : Fin n) : (Iic i).map revPerm.toEmbedding = Ici i.rev := by
  simp [← coe_inj]

@[simp]
theorem map_revPerm_Iio (i : Fin n) : (Iio i).map revPerm.toEmbedding = Ioi i.rev := by
  simp [← coe_inj]

end rev

/-!
### Cardinalities of the intervals
-/

section card

@[simp]
lemma card_Icc : #(Icc a b) = b + 1 - a := by rw [← Nat.card_Icc, ← map_valEmbedding_Icc, card_map]

@[simp]
lemma card_Ico : #(Ico a b) = b - a := by rw [← Nat.card_Ico, ← map_valEmbedding_Ico, card_map]

@[simp]
lemma card_Ioc : #(Ioc a b) = b - a := by rw [← Nat.card_Ioc, ← map_valEmbedding_Ioc, card_map]

@[simp]
lemma card_Ioo : #(Ioo a b) = b - a - 1 := by rw [← Nat.card_Ioo, ← map_valEmbedding_Ioo, card_map]

@[simp]
theorem card_uIcc : #(uIcc a b) = (b - a : ℤ).natAbs + 1 := by
  rw [← Nat.card_uIcc, ← map_valEmbedding_uIcc, card_map]

@[simp]
theorem card_Ici : #(Ici a) = n - a := by
  rw [← attachFin_Ico_eq_Ici, card_attachFin, Nat.card_Ico]

@[simp]
theorem card_Ioi : #(Ioi a) = n - 1 - a := by
  rw [← card_map, map_valEmbedding_Ioi, Nat.card_Ioo, Nat.sub_right_comm]

@[simp]
theorem card_Iic : #(Iic b) = b + 1 := by rw [← Nat.card_Iic b, ← map_valEmbedding_Iic, card_map]

@[simp]
theorem card_Iio : #(Iio b) = b := by rw [← Nat.card_Iio b, ← map_valEmbedding_Iio, card_map]

@[deprecated Fintype.card_Icc (since := "2025-03-28")]
theorem card_fintypeIcc : Fintype.card (Set.Icc a b) = b + 1 - a := by simp

@[deprecated Fintype.card_Ico (since := "2025-03-28")]
theorem card_fintypeIco : Fintype.card (Set.Ico a b) = b - a := by simp

@[deprecated Fintype.card_Ioc (since := "2025-03-28")]
theorem card_fintypeIoc : Fintype.card (Set.Ioc a b) = b - a := by simp

@[deprecated Fintype.card_Ioo (since := "2025-03-28")]
theorem card_fintypeIoo : Fintype.card (Set.Ioo a b) = b - a - 1 := by simp

@[deprecated Fintype.card_uIcc (since := "2025-03-28")]
theorem card_fintype_uIcc : Fintype.card (Set.uIcc a b) = (b - a : ℤ).natAbs + 1 := by simp

@[deprecated Fintype.card_Ici (since := "2025-03-28")]
theorem card_fintypeIci : Fintype.card (Set.Ici a) = n - a := by simp

@[deprecated Fintype.card_Ioi (since := "2025-03-28")]
theorem card_fintypeIoi : Fintype.card (Set.Ioi a) = n - 1 - a := by simp

@[deprecated Fintype.card_Iic (since := "2025-03-28")]
theorem card_fintypeIic : Fintype.card (Set.Iic b) = b + 1 := by simp

@[deprecated Fintype.card_Iio (since := "2025-03-28")]
theorem card_fintypeIio : Fintype.card (Set.Iio b) = b := by simp

end card

end Fin
