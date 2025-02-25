/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import Mathlib.Order.SuccPred.Basic
import Mathlib.Data.Finset.Interval

/-!
This file contains some basic results about finite intervals in linear locally finite `SuccOrder`s
and `PredOrder`s.
-/

section LocallyFinite

open Finset Order
namespace Finset

variable {α : Type*} [LinearOrder α] [SuccOrder α] (a b : α)

theorem Iio_succ_of_not_isMax [LocallyFiniteOrderBot α] (ha : ¬IsMax a) :
    Iio (succ a) = Iic a := by
  rwa [←Finset.coe_inj, Finset.coe_Iio, Finset.coe_Iic, Order.Iio_succ_of_not_isMax]

theorem Ico_succ_right_of_not_isMax [LocallyFiniteOrder α] (hb : ¬IsMax b) :
    Ico a (succ b) = Icc a b := by
  rwa [←Finset.coe_inj, Finset.coe_Ico, Finset.coe_Icc, Order.Ico_succ_right_of_not_isMax]

theorem Ioo_succ_right_of_not_isMax [LocallyFiniteOrder α] (hb : ¬IsMax b) :
    Ioo a (succ b) = Ioc a b := by
  rwa [←Finset.coe_inj, Finset.coe_Ioo, Finset.coe_Ioc, Order.Ioo_succ_right_of_not_isMax]

theorem Iic_succ [LocallyFiniteOrderBot α] (a : α) : Iic (succ a) = insert (succ a) (Iic a) := by
  rw [←Finset.coe_inj, Finset.coe_insert, Finset.coe_Iic, Finset.coe_Iic, Order.Iic_succ]

theorem Icc_succ_right [LocallyFiniteOrder α]
    (h : a ≤ succ b) : Icc a (succ b) = insert (succ b) (Icc a b) := by
  rwa [←Finset.coe_inj, Finset.coe_Icc, Finset.coe_insert, Finset.coe_Icc, Order.Icc_succ_right]

theorem Ioc_succ_right [LocallyFiniteOrder α] (h : a < succ b) :
    Ioc a (succ b) = insert (succ b) (Ioc a b) := by
  rwa [←Finset.coe_inj, Finset.coe_Ioc, Finset.coe_insert, Finset.coe_Ioc, Order.Ioc_succ_right]

theorem Iio_succ_eq_insert_of_not_isMax  [LocallyFiniteOrderBot α] (h : ¬IsMax a) :
    Iio (succ a) = insert a (Iio a) := by
  rwa [←Finset.coe_inj, Finset.coe_Iio, Finset.coe_insert, Finset.coe_Iio,
    Order.Iio_succ_eq_insert_of_not_isMax]

theorem Ico_succ_right_eq_insert_of_not_isMax [LocallyFiniteOrder α] (h₁ : a ≤ b) (h₂ : ¬IsMax b) :
    Ico a (succ b) = insert b (Ico a b) := by
  rw [←Finset.coe_inj, Finset.coe_Ico, Finset.coe_insert, Finset.coe_Ico,
    Order.Ico_succ_right_eq_insert_of_not_isMax h₁ h₂]

theorem Ioo_succ_right_eq_insert_of_not_isMax [LocallyFiniteOrder α] (h₁ : a < b) (h₂ : ¬IsMax b) :
    Ioo a (succ b) = insert b (Ioo a b) := by
  rw [←Finset.coe_inj, Finset.coe_Ioo, Finset.coe_insert, Finset.coe_Ioo,
    Order.Ioo_succ_right_eq_insert_of_not_isMax h₁ h₂]

end Finset

end LocallyFinite
