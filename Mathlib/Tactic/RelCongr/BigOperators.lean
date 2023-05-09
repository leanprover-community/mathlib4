import Mathlib.Algebra.BigOperators.Order
import Mathlib.Tactic.RelCongr.Basic

/-! # ≤, ∑ -/

-- a variant statement of `Finset.sum_le_sum`, since it doesn't match the attribute pattern in the
-- library statement:
theorem RelCongr.Finset.sum_le_sum [OrderedAddCommMonoid N] {f g : ι → N} {s : Finset ι}
    (h : ∀ (i : ι), i ∈ s → f i ≤ g i) : s.sum f ≤ s.sum g :=
  s.sum_le_sum h

attribute [rel_congr]
  RelCongr.Finset.sum_le_sum

/-! # <, ∑ -/

-- a variant statement of `Finset.sum_lt_sum`, since it doesn't match the attribute pattern in the
-- library statement:
theorem RelCongr.Finset.sum_lt_sum_of_nonempty [OrderedCancelAddCommMonoid M]
    {f g : ι → M} {s : Finset ι} (hs : Finset.Nonempty s) (Hlt : ∀ (i : ι), i ∈ s → f i < g i) :
    s.sum f < s.sum g :=
  s.sum_lt_sum_of_nonempty hs Hlt

attribute [rel_congr]
  RelCongr.Finset.sum_lt_sum_of_nonempty

/-! # ≤, ∏ -/

-- a variant statement of `Finset.prod_le_prod'`, since it doesn't match the attribute pattern in
-- the library statement:
theorem RelCongr.Finset.prod_le_prod' [OrderedCommMonoid N] {f g : ι → N} {s : Finset ι}
    (h : ∀ (i : ι), i ∈ s → f i ≤ g i) : s.prod f ≤ s.prod g :=
  s.prod_le_prod' h

-- a variant statement of `Finset.prod_le_prod`, since it doesn't match the attribute pattern in the
-- library statement:
theorem RelCongr.Finset.prod_le_prod [OrderedCommSemiring R] {f g : ι → R}
    {s : Finset ι} (h0 : ∀ (i : ι), i ∈ s → 0 ≤ f i) (h1 : ∀ (i : ι), i ∈ s → f i ≤ g i) :
    s.prod f ≤ s.prod g :=
  s.prod_le_prod h0 h1

attribute [rel_congr]
  RelCongr.Finset.prod_le_prod' RelCongr.Finset.prod_le_prod

/-! # <, ∏ -/

-- a variant statement of `Finset.prod_lt_prod_of_nonempty'`, since it doesn't match the attribute
-- pattern in the library statement:
theorem RelCongr.Finset.prod_lt_prod_of_nonempty' [OrderedCancelCommMonoid M]
    {f g : ι → M} {s : Finset ι} (hs : Finset.Nonempty s) (Hlt : ∀ (i : ι), i ∈ s → f i < g i) :
    s.prod f < s.prod g :=
  s.prod_lt_prod_of_nonempty' hs Hlt

attribute [rel_congr]
  RelCongr.Finset.prod_lt_prod_of_nonempty'
