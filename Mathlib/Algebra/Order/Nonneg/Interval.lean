/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Nonneg.Lattice
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Intervals in the type of nonnegative elements

This file computes the image under the coercion `Nonneg M → M` of the intervals of `Nonneg M`.
-/

public section

open Set

variable {M : Type*} [Zero M]

namespace Nonneg

section Preorder
variable [Preorder M] {a b : Nonneg M}

@[simp] lemma image_val_Ici (a : Nonneg M) : val '' Ici a = Ici a.val :=
  Set.ext fun _ ↦ ⟨fun ⟨_, hb, hx⟩ ↦ hx ▸ hb, fun hx ↦ ⟨⟨_, a.val_nonneg.trans hx⟩, hx, rfl⟩⟩

@[simp] lemma image_val_Ioi (a : Nonneg M) : val '' Ioi a = Ioi a.val :=
  Set.ext fun _ ↦ ⟨fun ⟨_, hb, hx⟩ ↦ hx ▸ hb, fun hx ↦ ⟨⟨_, a.val_nonneg.trans hx.le⟩, hx, rfl⟩⟩

@[simp] lemma image_val_Iic (a : Nonneg M) : val '' Iic a = Icc 0 a.val :=
  Set.ext fun _ ↦ ⟨fun ⟨b, hb, hx⟩ ↦ hx ▸ ⟨b.val_nonneg, hb⟩, fun hx ↦ ⟨⟨_, hx.1⟩, hx.2, rfl⟩⟩

@[simp] lemma image_val_Iio (a : Nonneg M) : val '' Iio a = Ico 0 a.val :=
  Set.ext fun _ ↦ ⟨fun ⟨b, hb, hx⟩ ↦ hx ▸ ⟨b.val_nonneg, hb⟩, fun hx ↦ ⟨⟨_, hx.1⟩, hx.2, rfl⟩⟩

@[simp] lemma image_val_Icc (a b : Nonneg M) : val '' Icc a b = Icc a.val b.val :=
  Set.ext fun _ ↦ ⟨fun ⟨_, hc, hx⟩ ↦ hx ▸ hc,
    fun hx ↦ ⟨⟨_, a.val_nonneg.trans hx.1⟩, hx, rfl⟩⟩

@[simp] lemma image_val_Ico (a b : Nonneg M) : val '' Ico a b = Ico a.val b.val :=
  Set.ext fun _ ↦ ⟨fun ⟨_, hc, hx⟩ ↦ hx ▸ hc,
    fun hx ↦ ⟨⟨_, a.val_nonneg.trans hx.1⟩, hx, rfl⟩⟩

@[simp] lemma image_val_Ioc (a b : Nonneg M) : val '' Ioc a b = Ioc a.val b.val :=
  Set.ext fun _ ↦ ⟨fun ⟨_, hc, hx⟩ ↦ hx ▸ hc,
    fun hx ↦ ⟨⟨_, a.val_nonneg.trans hx.1.le⟩, hx, rfl⟩⟩

@[simp] lemma image_val_Ioo (a b : Nonneg M) : val '' Ioo a b = Ioo a.val b.val :=
  Set.ext fun _ ↦ ⟨fun ⟨_, hc, hx⟩ ↦ hx ▸ hc,
    fun hx ↦ ⟨⟨_, a.val_nonneg.trans hx.1.le⟩, hx, rfl⟩⟩

end Preorder

section Lattice
variable [Lattice M] (a b : Nonneg M)

@[simp] lemma image_val_uIcc : val '' uIcc a b = uIcc a.val b.val := by
  rw [uIcc, image_val_Icc, coe_inf, coe_sup, uIcc]

end Lattice

section LinearOrder
variable [LinearOrder M] (a b : Nonneg M)

@[simp] lemma image_val_uIoc : val '' uIoc a b = uIoc a.val b.val := by
  rw [uIoc, image_val_Ioc, coe_inf, coe_sup, uIoc]

@[simp] lemma image_val_uIoo : val '' uIoo a b = uIoo a.val b.val := by
  rw [uIoo, image_val_Ioo, coe_inf, coe_sup, uIoo]

end LinearOrder

end Nonneg
