/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Data.Multiset.FinsetOps
import Mathlib.Data.Multiset.Fold

#align_import algebra.gcd_monoid.multiset from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"

/-!
# GCD and LCM operations on multisets

## Main definitions

- `Multiset.gcd` - the greatest common denominator of a `Multiset` of elements of a `GCDMonoid`
- `Multiset.lcm` - the least common multiple of a `Multiset` of elements of a `GCDMonoid`

## Implementation notes

TODO: simplify with a tactic and `Data.Multiset.Lattice`

## Tags

multiset, gcd
-/

namespace Multiset

variable {α : Type*} [CancelCommMonoidWithZero α] [NormalizedGCDMonoid α]

/-! ### LCM -/


section lcm

/-- Least common multiple of a multiset -/
def lcm (s : Multiset α) : α :=
  s.fold GCDMonoid.lcm 1
#align multiset.lcm Multiset.lcm

@[simp]
theorem lcm_zero : (0 : Multiset α).lcm = 1 :=
  fold_zero _ _
#align multiset.lcm_zero Multiset.lcm_zero

@[simp]
theorem lcm_cons (a : α) (s : Multiset α) : (a ::ₘ s).lcm = GCDMonoid.lcm a s.lcm :=
  fold_cons_left _ _ _ _
#align multiset.lcm_cons Multiset.lcm_cons

@[simp]
theorem lcm_singleton {a : α} : ({a} : Multiset α).lcm = normalize a :=
  (fold_singleton _ _ _).trans <| lcm_one_right _
#align multiset.lcm_singleton Multiset.lcm_singleton

@[simp]
theorem lcm_add (s₁ s₂ : Multiset α) : (s₁ + s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm :=
  Eq.trans (by simp [lcm]) (fold_add _ _ _ _ _)
               -- 🎉 no goals
#align multiset.lcm_add Multiset.lcm_add

theorem lcm_dvd {s : Multiset α} {a : α} : s.lcm ∣ a ↔ ∀ b ∈ s, b ∣ a :=
  Multiset.induction_on s (by simp)
                              -- 🎉 no goals
    (by simp (config := { contextual := true }) [or_imp, forall_and, lcm_dvd_iff])
        -- 🎉 no goals
#align multiset.lcm_dvd Multiset.lcm_dvd

theorem dvd_lcm {s : Multiset α} {a : α} (h : a ∈ s) : a ∣ s.lcm :=
  lcm_dvd.1 dvd_rfl _ h
#align multiset.dvd_lcm Multiset.dvd_lcm

theorem lcm_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₁.lcm ∣ s₂.lcm :=
  lcm_dvd.2 fun _ hb ↦ dvd_lcm (h hb)
#align multiset.lcm_mono Multiset.lcm_mono

/- Porting note: Following `Algebra.GCDMonoid.Basic`'s version of `normalize_gcd`, I'm giving
this lower priority to avoid linter complaints about simp-normal form -/
/- Porting note: Mathport seems to be replacing `Multiset.induction_on s $` with
`(Multiset.induction_on s)`, when it should be `Multiset.induction_on s <|`. -/
@[simp 1100]
theorem normalize_lcm (s : Multiset α) : normalize s.lcm = s.lcm :=
  Multiset.induction_on s (by simp) <| fun a s _ ↦ by simp
                              -- 🎉 no goals
                                                      -- 🎉 no goals
#align multiset.normalize_lcm Multiset.normalize_lcm

@[simp]
nonrec theorem lcm_eq_zero_iff [Nontrivial α] (s : Multiset α) : s.lcm = 0 ↔ (0 : α) ∈ s := by
  induction' s using Multiset.induction_on with a s ihs
  -- ⊢ lcm 0 = 0 ↔ 0 ∈ 0
  · simp only [lcm_zero, one_ne_zero, not_mem_zero]
    -- 🎉 no goals
  · simp only [mem_cons, lcm_cons, lcm_eq_zero_iff, ihs, @eq_comm _ a]
    -- 🎉 no goals
#align multiset.lcm_eq_zero_iff Multiset.lcm_eq_zero_iff

variable [DecidableEq α]

@[simp]
theorem lcm_dedup (s : Multiset α) : (dedup s).lcm = s.lcm :=
  Multiset.induction_on s (by simp) <| fun a s IH ↦ by
                              -- 🎉 no goals
    by_cases h : a ∈ s <;> simp [IH, h]
    -- ⊢ lcm (dedup (a ::ₘ s)) = lcm (a ::ₘ s)
                           -- ⊢ lcm s = GCDMonoid.lcm a (lcm s)
                           -- 🎉 no goals
    unfold lcm
    -- ⊢ fold GCDMonoid.lcm 1 s = GCDMonoid.lcm a (fold GCDMonoid.lcm 1 s)
    rw [← cons_erase h, fold_cons_left, ← lcm_assoc, lcm_same]
    -- ⊢ GCDMonoid.lcm a (fold GCDMonoid.lcm 1 (erase s a)) = GCDMonoid.lcm (↑normali …
    apply lcm_eq_of_associated_left (associated_normalize _)
    -- 🎉 no goals
#align multiset.lcm_dedup Multiset.lcm_dedup

@[simp]
theorem lcm_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm := by
  rw [← lcm_dedup, dedup_ext.2, lcm_dedup, lcm_add]
  -- ⊢ ∀ (a : α), a ∈ ndunion s₁ s₂ ↔ a ∈ s₁ + s₂
  simp
  -- 🎉 no goals
#align multiset.lcm_ndunion Multiset.lcm_ndunion

@[simp]
theorem lcm_union (s₁ s₂ : Multiset α) : (s₁ ∪ s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm := by
  rw [← lcm_dedup, dedup_ext.2, lcm_dedup, lcm_add]
  -- ⊢ ∀ (a : α), a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ + s₂
  simp
  -- 🎉 no goals
#align multiset.lcm_union Multiset.lcm_union

@[simp]
theorem lcm_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).lcm = GCDMonoid.lcm a s.lcm := by
  rw [← lcm_dedup, dedup_ext.2, lcm_dedup, lcm_cons]
  -- ⊢ ∀ (a_1 : α), a_1 ∈ ndinsert a s ↔ a_1 ∈ a ::ₘ s
  simp
  -- 🎉 no goals
#align multiset.lcm_ndinsert Multiset.lcm_ndinsert

end lcm

/-! ### GCD -/


section gcd

/-- Greatest common divisor of a multiset -/
def gcd (s : Multiset α) : α :=
  s.fold GCDMonoid.gcd 0
#align multiset.gcd Multiset.gcd

@[simp]
theorem gcd_zero : (0 : Multiset α).gcd = 0 :=
  fold_zero _ _
#align multiset.gcd_zero Multiset.gcd_zero

@[simp]
theorem gcd_cons (a : α) (s : Multiset α) : (a ::ₘ s).gcd = GCDMonoid.gcd a s.gcd :=
  fold_cons_left _ _ _ _
#align multiset.gcd_cons Multiset.gcd_cons

@[simp]
theorem gcd_singleton {a : α} : ({a} : Multiset α).gcd = normalize a :=
  (fold_singleton _ _ _).trans <| gcd_zero_right _
#align multiset.gcd_singleton Multiset.gcd_singleton

@[simp]
theorem gcd_add (s₁ s₂ : Multiset α) : (s₁ + s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd :=
  Eq.trans (by simp [gcd]) (fold_add _ _ _ _ _)
               -- 🎉 no goals
#align multiset.gcd_add Multiset.gcd_add

theorem dvd_gcd {s : Multiset α} {a : α} : a ∣ s.gcd ↔ ∀ b ∈ s, a ∣ b :=
  Multiset.induction_on s (by simp)
                              -- 🎉 no goals
    (by simp (config := { contextual := true }) [or_imp, forall_and, dvd_gcd_iff])
        -- 🎉 no goals
#align multiset.dvd_gcd Multiset.dvd_gcd

theorem gcd_dvd {s : Multiset α} {a : α} (h : a ∈ s) : s.gcd ∣ a :=
  dvd_gcd.1 dvd_rfl _ h
#align multiset.gcd_dvd Multiset.gcd_dvd

theorem gcd_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₂.gcd ∣ s₁.gcd :=
  dvd_gcd.2 fun _ hb ↦ gcd_dvd (h hb)
#align multiset.gcd_mono Multiset.gcd_mono

/- Porting note: Following `Algebra.GCDMonoid.Basic`'s version of `normalize_gcd`, I'm giving
this lower priority to avoid linter complaints about simp-normal form -/
@[simp 1100]
theorem normalize_gcd (s : Multiset α) : normalize s.gcd = s.gcd :=
  Multiset.induction_on s (by simp) <| fun a s _ ↦ by simp
                              -- 🎉 no goals
                                                      -- 🎉 no goals
#align multiset.normalize_gcd Multiset.normalize_gcd

theorem gcd_eq_zero_iff (s : Multiset α) : s.gcd = 0 ↔ ∀ x : α, x ∈ s → x = 0 := by
  constructor
  -- ⊢ gcd s = 0 → ∀ (x : α), x ∈ s → x = 0
  · intro h x hx
    -- ⊢ x = 0
    apply eq_zero_of_zero_dvd
    -- ⊢ 0 ∣ x
    rw [← h]
    -- ⊢ gcd s ∣ x
    apply gcd_dvd hx
    -- 🎉 no goals
  · refine' s.induction_on _ _
    -- ⊢ (∀ (x : α), x ∈ 0 → x = 0) → gcd 0 = 0
    · simp
      -- 🎉 no goals
    intro a s sgcd h
    -- ⊢ gcd (a ::ₘ s) = 0
    simp [h a (mem_cons_self a s), sgcd fun x hx ↦ h x (mem_cons_of_mem hx)]
    -- 🎉 no goals
#align multiset.gcd_eq_zero_iff Multiset.gcd_eq_zero_iff

theorem gcd_map_mul (a : α) (s : Multiset α) : (s.map ((· * ·) a)).gcd = normalize a * s.gcd := by
  refine' s.induction_on _ fun b s ih ↦ _
  -- ⊢ gcd (map ((fun x x_1 => x * x_1) a) 0) = ↑normalize a * gcd 0
  · simp_rw [map_zero, gcd_zero, mul_zero]
    -- 🎉 no goals
  · simp_rw [map_cons, gcd_cons, ← gcd_mul_left]
    -- ⊢ GCDMonoid.gcd (a * b) (gcd (map (fun x => a * x) s)) = GCDMonoid.gcd (a * b) …
    rw [ih]
    -- ⊢ GCDMonoid.gcd (a * b) (↑normalize a * gcd s) = GCDMonoid.gcd (a * b) (a * gc …
    apply ((normalize_associated a).mul_right _).gcd_eq_right
    -- 🎉 no goals
#align multiset.gcd_map_mul Multiset.gcd_map_mul

section

variable [DecidableEq α]

@[simp]
theorem gcd_dedup (s : Multiset α) : (dedup s).gcd = s.gcd :=
  Multiset.induction_on s (by simp) <| fun a s IH ↦ by
                              -- 🎉 no goals
    by_cases h : a ∈ s <;> simp [IH, h]
    -- ⊢ gcd (dedup (a ::ₘ s)) = gcd (a ::ₘ s)
                           -- ⊢ gcd s = GCDMonoid.gcd a (gcd s)
                           -- 🎉 no goals
    unfold gcd
    -- ⊢ fold GCDMonoid.gcd 0 s = GCDMonoid.gcd a (fold GCDMonoid.gcd 0 s)
    rw [← cons_erase h, fold_cons_left, ← gcd_assoc, gcd_same]
    -- ⊢ GCDMonoid.gcd a (fold GCDMonoid.gcd 0 (erase s a)) = GCDMonoid.gcd (↑normali …
    apply (associated_normalize _).gcd_eq_left
    -- 🎉 no goals
#align multiset.gcd_dedup Multiset.gcd_dedup

@[simp]
theorem gcd_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd := by
  rw [← gcd_dedup, dedup_ext.2, gcd_dedup, gcd_add]
  -- ⊢ ∀ (a : α), a ∈ ndunion s₁ s₂ ↔ a ∈ s₁ + s₂
  simp
  -- 🎉 no goals
#align multiset.gcd_ndunion Multiset.gcd_ndunion

@[simp]
theorem gcd_union (s₁ s₂ : Multiset α) : (s₁ ∪ s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd := by
  rw [← gcd_dedup, dedup_ext.2, gcd_dedup, gcd_add]
  -- ⊢ ∀ (a : α), a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ + s₂
  simp
  -- 🎉 no goals
#align multiset.gcd_union Multiset.gcd_union

@[simp]
theorem gcd_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).gcd = GCDMonoid.gcd a s.gcd := by
  rw [← gcd_dedup, dedup_ext.2, gcd_dedup, gcd_cons]
  -- ⊢ ∀ (a_1 : α), a_1 ∈ ndinsert a s ↔ a_1 ∈ a ::ₘ s
  simp
  -- 🎉 no goals
#align multiset.gcd_ndinsert Multiset.gcd_ndinsert

end

theorem extract_gcd' (s t : Multiset α) (hs : ∃ x, x ∈ s ∧ x ≠ (0 : α))
    (ht : s = t.map ((· * ·) s.gcd)) : t.gcd = 1 :=
  ((@mul_right_eq_self₀ _ _ s.gcd _).1 <| by
        conv_lhs => rw [← normalize_gcd, ← gcd_map_mul, ← ht]).resolve_right <| by
        -- 🎉 no goals
    contrapose! hs
    -- ⊢ ∀ (x : α), x ∈ s → x = 0
    exact s.gcd_eq_zero_iff.1 hs
    -- 🎉 no goals
#align multiset.extract_gcd' Multiset.extract_gcd'

/- Porting note: Deprecated lemmas like `map_repeat` and `eq_repeat` weren't "officially"
converted to `Multiset.replicate` format yet, so I made some ad hoc ones in `Data.Multiset.Basic`
using the originals. -/
/- Porting note: The old proof used a strange form
`have := _, refine ⟨s.pmap @f (λ _, id), this, extract_gcd' s _ h this⟩,`
so I rearranged the proof slightly. -/
theorem extract_gcd (s : Multiset α) (hs : s ≠ 0) :
    ∃ t : Multiset α, s = t.map ((· * ·) s.gcd) ∧ t.gcd = 1 := by
  classical
    by_cases h : ∀ x ∈ s, x = (0 : α)
    · use replicate (card s) 1
      simp only
      rw [map_replicate, eq_replicate, mul_one, s.gcd_eq_zero_iff.2 h, ← nsmul_singleton,
    ← gcd_dedup, dedup_nsmul (card_pos.2 hs).ne', dedup_singleton, gcd_singleton]
      exact ⟨⟨rfl, h⟩, normalize_one⟩
    · choose f hf using @gcd_dvd _ _ _ s
      push_neg at h
      refine' ⟨s.pmap @f fun _ ↦ id, _, extract_gcd' s _ h _⟩ <;>
      · rw [map_pmap]
        conv_lhs => rw [← s.map_id, ← s.pmap_eq_map _ _ fun _ ↦ id]
        congr with (x hx)
        simp only
        rw [id]
        rw [← hf hx]
#align multiset.extract_gcd Multiset.extract_gcd

end gcd

end Multiset
