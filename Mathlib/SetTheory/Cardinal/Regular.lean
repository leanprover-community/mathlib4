/-
Copyright (c) 2018 Nir Paz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nir Paz
-/
import Mathlib.SetTheory.Cardinal.Cofinality

/-!
# Regular cardinals

We define singular cardinals and prove theorems about singular and regular cardinals.

## Main definitions and results

* `Cardinal.IsSingular c` means that `c` is an infinite cardinal which is not regular. That is,
  its cofinality is smaller than itself.
-/


open Ordinal Cardinal

namespace Cardinal

section Singular

variable {c : Cardinal}

/-- A cardinal is singular if it is infinite and not regular. -/
def IsSingular (c : Cardinal) : Prop :=
  ℵ₀ ≤ c ∧ ¬c.IsRegular

theorem IsSingular.aleph0_le (H : c.IsSingular) : ℵ₀ ≤ c :=
  H.1

theorem IsSingular.not_isRegular (H : c.IsSingular) : ¬c.IsRegular :=
  H.2

theorem IsSingular.cof_ord_lt (H : c.IsSingular) : c.ord.cof < c :=
  lt_of_le_of_ne (cof_ord_le c) (fun h ↦ H.2 ⟨H.1, h.symm.le⟩)

theorem IsSingular.natCast_lt (H : c.IsSingular) (n : ℕ) : n < c :=
  (nat_lt_aleph0 n).trans_le H.aleph0_le

theorem IsSingular.pos (H : c.IsSingular) : 0 < c :=
  H.natCast_lt 0

theorem IsRegular.not_isSingular (H : c.IsRegular) : ¬c.IsSingular :=
  fun h ↦ h.2 H

theorem isSingular_iff_cof_lt (h : ℵ₀ ≤ c) : c.IsSingular ↔ c.ord.cof < c :=
  ⟨fun h ↦ h.cof_ord_lt, fun h' ↦ ⟨h, fun h ↦ h'.ne h.cof_eq⟩⟩

theorem isRegular_or_isSingular (h : ℵ₀ ≤ c) : c.IsRegular ∨ c.IsSingular := by
  rw [IsSingular]
  tauto

theorem isRegular_or_isSingular_or_lt_aleph0 :
    c.IsRegular ∨ c.IsSingular ∨ c < ℵ₀ := by
  rw [lt_iff_not_ge]
  tauto

theorem isRegular.of_not_isSingular (h : ℵ₀ ≤ c) (H : ¬c.IsSingular) :
    c.IsRegular := by
  rw [IsSingular] at H
  tauto

theorem isSingular_aleph_iff {o : Ordinal} (ho : o.IsLimit) :
    (aleph o).IsSingular ↔ o.cof < aleph o := by
  constructor <;> intro h
  · have := h.cof_ord_lt
    rwa [aleph_cof ho] at this
  · exact (isSingular_iff_cof_lt (aleph0_le_aleph o)).mpr ((aleph_cof ho) ▸ h)

theorem isSingular_aleph_omega : (aleph ω).IsSingular := by
  rw [isSingular_aleph_iff omega0_isLimit, cof_omega0, ← aleph_zero, aleph_lt]
  exact omega0_pos

end Singular
end Cardinal
