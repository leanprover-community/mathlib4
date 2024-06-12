/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Group.WithTop
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.Valuation.Basic

#align_import ring_theory.hahn_series from "leanprover-community/mathlib"@"a484a7d0eade4e1268f4fb402859b6686037f965"

/-!
# Hahn Series
If `Γ` is ordered and `R` has zero, then `HahnSeries Γ R` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. With further structure on `R` and
`Γ`, we can add further structure on `HahnSeries Γ R`.  We introduce valuations and a notion of
summability for possibly infinite families of series.

## Main Definitions
  * `HahnSeries.addVal Γ R` defines an `AddValuation` on `HahnSeries Γ R` when `Γ` is linearly
    ordered.
  * A `HahnSeries.SummableFamily` is a family of Hahn series such that the union of their supports
  is well-founded and only finitely many are nonzero at any given coefficient. They have a formal
  sum, `HahnSeries.SummableFamily.hsum`, which can be bundled as a `LinearMap` as
  `HahnSeries.SummableFamily.lsum`. Note that this is different from `Summable` in the valuation
  topology, because there are topologically summable families that do not satisfy the axioms of
  `HahnSeries.SummableFamily`, and formally summable families whose sums do not converge
  topologically.

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

set_option linter.uppercaseLean3 false

open Finset Function

open scoped Classical
open Pointwise

noncomputable section

variable {Γ : Type*} {R : Type*}

namespace HahnSeries

section Valuation

variable (Γ R) [LinearOrderedCancelAddCommMonoid Γ] [Ring R] [IsDomain R]

/-- The additive valuation on `HahnSeries Γ R`, returning the smallest index at which
  a Hahn Series has a nonzero coefficient, or `⊤` for the 0 series.  -/
def addVal : AddValuation (HahnSeries Γ R) (WithTop Γ) :=
  AddValuation.of (fun x => if x = (0 : HahnSeries Γ R) then (⊤ : WithTop Γ) else x.order)
    (if_pos rfl) ((if_neg one_ne_zero).trans (by simp [order_of_ne]))
    (fun x y => by
      by_cases hx : x = 0
      · by_cases hy : y = 0 <;> · simp [hx, hy]
      · by_cases hy : y = 0
        · simp [hx, hy]
        · simp only [hx, hy, support_nonempty_iff, if_neg, not_false_iff, isWF_support]
          by_cases hxy : x + y = 0
          · simp [hxy]
          rw [if_neg hxy, ← WithTop.coe_min, WithTop.coe_le_coe]
          exact min_order_le_order_add hxy)
    fun x y => by
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    dsimp only
    rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← WithTop.coe_add, WithTop.coe_eq_coe,
      order_mul hx hy]
#align hahn_series.add_val HahnSeries.addVal

variable {Γ} {R}

theorem addVal_apply {x : HahnSeries Γ R} :
    addVal Γ R x = if x = (0 : HahnSeries Γ R) then (⊤ : WithTop Γ) else x.order :=
  AddValuation.of_apply _
#align hahn_series.add_val_apply HahnSeries.addVal_apply

@[simp]
theorem addVal_apply_of_ne {x : HahnSeries Γ R} (hx : x ≠ 0) : addVal Γ R x = x.order :=
  if_neg hx
#align hahn_series.add_val_apply_of_ne HahnSeries.addVal_apply_of_ne

theorem addVal_le_of_coeff_ne_zero {x : HahnSeries Γ R} {g : Γ} (h : x.coeff g ≠ 0) :
    addVal Γ R x ≤ g := by
  rw [addVal_apply_of_ne (ne_zero_of_coeff_ne_zero h), WithTop.coe_le_coe]
  exact order_le_of_coeff_ne_zero h
#align hahn_series.add_val_le_of_coeff_ne_zero HahnSeries.addVal_le_of_coeff_ne_zero

end Valuation
theorem isPWO_iUnion_support_powers [LinearOrderedCancelAddCommMonoid Γ] [Ring R] [IsDomain R]
    {x : HahnSeries Γ R} (hx : 0 < addVal Γ R x) : (⋃ n : ℕ, (x ^ n).support).IsPWO := by
  apply (x.isWF_support.isPWO.addSubmonoid_closure _).mono _
  · exact fun g hg => WithTop.coe_le_coe.1 (le_trans (le_of_lt hx) (addVal_le_of_coeff_ne_zero hg))
  refine Set.iUnion_subset fun n => ?_
  induction' n with n ih <;> intro g hn
  · simp only [Nat.zero_eq, pow_zero, support_one, Set.mem_singleton_iff] at hn
    rw [hn, SetLike.mem_coe]
    exact AddSubmonoid.zero_mem _
  · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset_add_support hn
    exact SetLike.mem_coe.2 (AddSubmonoid.add_mem _ (ih hi) (AddSubmonoid.subset_closure hj))
#align hahn_series.is_pwo_Union_support_powers HahnSeries.isPWO_iUnion_support_powers

section

variable (Γ) (R) [PartialOrder Γ] [AddCommMonoid R]

/-- An infinite family of Hahn series which has a formal coefficient-wise sum.
  The requirements for this are that the union of the supports of the series is well-founded,
  and that only finitely many series are nonzero at any given coefficient. -/
structure SummableFamily (α : Type*) where
  toFun : α → HahnSeries Γ R
  isPWO_iUnion_support' : Set.IsPWO (⋃ a : α, (toFun a).support)
  finite_co_support' : ∀ g : Γ, { a | (toFun a).coeff g ≠ 0 }.Finite
#align hahn_series.summable_family HahnSeries.SummableFamily

end

namespace SummableFamily

section AddCommMonoid

variable [PartialOrder Γ] [AddCommMonoid R] {α : Type*}

instance : FunLike (SummableFamily Γ R α) α (HahnSeries Γ R) where
  coe := toFun
  coe_injective' | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

theorem isPWO_iUnion_support (s : SummableFamily Γ R α) : Set.IsPWO (⋃ a : α, (s a).support) :=
  s.isPWO_iUnion_support'
#align hahn_series.summable_family.is_pwo_Union_support HahnSeries.SummableFamily.isPWO_iUnion_support

theorem finite_co_support (s : SummableFamily Γ R α) (g : Γ) :
    (Function.support fun a => (s a).coeff g).Finite :=
  s.finite_co_support' g
#align hahn_series.summable_family.finite_co_support HahnSeries.SummableFamily.finite_co_support

theorem coe_injective : @Function.Injective (SummableFamily Γ R α) (α → HahnSeries Γ R) (⇑) :=
  DFunLike.coe_injective
#align hahn_series.summable_family.coe_injective HahnSeries.SummableFamily.coe_injective

@[ext]
theorem ext {s t : SummableFamily Γ R α} (h : ∀ a : α, s a = t a) : s = t :=
  DFunLike.ext s t h
#align hahn_series.summable_family.ext HahnSeries.SummableFamily.ext

instance : Add (SummableFamily Γ R α) :=
  ⟨fun x y =>
    { toFun := x + y
      isPWO_iUnion_support' :=
        (x.isPWO_iUnion_support.union y.isPWO_iUnion_support).mono
          (by
            rw [← Set.iUnion_union_distrib]
            exact Set.iUnion_mono fun a => support_add_subset)
      finite_co_support' := fun g =>
        ((x.finite_co_support g).union (y.finite_co_support g)).subset
          (by
            intro a ha
            change (x a).coeff g + (y a).coeff g ≠ 0 at ha
            rw [Set.mem_union, Function.mem_support, Function.mem_support]
            contrapose! ha
            rw [ha.1, ha.2, add_zero]) }⟩

instance : Zero (SummableFamily Γ R α) :=
  ⟨⟨0, by simp, by simp⟩⟩

instance : Inhabited (SummableFamily Γ R α) :=
  ⟨0⟩

@[simp]
theorem coe_add {s t : SummableFamily Γ R α} : ⇑(s + t) = s + t :=
  rfl
#align hahn_series.summable_family.coe_add HahnSeries.SummableFamily.coe_add

theorem add_apply {s t : SummableFamily Γ R α} {a : α} : (s + t) a = s a + t a :=
  rfl
#align hahn_series.summable_family.add_apply HahnSeries.SummableFamily.add_apply

@[simp]
theorem coe_zero : ((0 : SummableFamily Γ R α) : α → HahnSeries Γ R) = 0 :=
  rfl
#align hahn_series.summable_family.coe_zero HahnSeries.SummableFamily.coe_zero

theorem zero_apply {a : α} : (0 : SummableFamily Γ R α) a = 0 :=
  rfl
#align hahn_series.summable_family.zero_apply HahnSeries.SummableFamily.zero_apply

instance : AddCommMonoid (SummableFamily Γ R α) where
  zero := 0
  nsmul := nsmulRec
  zero_add s := by
    ext
    apply zero_add
  add_zero s := by
    ext
    apply add_zero
  add_comm s t := by
    ext
    apply add_comm
  add_assoc r s t := by
    ext
    apply add_assoc

/-- The infinite sum of a `SummableFamily` of Hahn series. -/
def hsum (s : SummableFamily Γ R α) : HahnSeries Γ R where
  coeff g := ∑ᶠ i, (s i).coeff g
  isPWO_support' :=
    s.isPWO_iUnion_support.mono fun g => by
      contrapose
      rw [Set.mem_iUnion, not_exists, Function.mem_support, Classical.not_not]
      simp_rw [mem_support, Classical.not_not]
      intro h
      rw [finsum_congr h, finsum_zero]
#align hahn_series.summable_family.hsum HahnSeries.SummableFamily.hsum

@[simp]
theorem hsum_coeff {s : SummableFamily Γ R α} {g : Γ} : s.hsum.coeff g = ∑ᶠ i, (s i).coeff g :=
  rfl
#align hahn_series.summable_family.hsum_coeff HahnSeries.SummableFamily.hsum_coeff

theorem support_hsum_subset {s : SummableFamily Γ R α} : s.hsum.support ⊆ ⋃ a : α, (s a).support :=
  fun g hg => by
  rw [mem_support, hsum_coeff, finsum_eq_sum _ (s.finite_co_support _)] at hg
  obtain ⟨a, _, h2⟩ := exists_ne_zero_of_sum_ne_zero hg
  rw [Set.mem_iUnion]
  exact ⟨a, h2⟩
#align hahn_series.summable_family.support_hsum_subset HahnSeries.SummableFamily.support_hsum_subset

@[simp]
theorem hsum_add {s t : SummableFamily Γ R α} : (s + t).hsum = s.hsum + t.hsum := by
  ext g
  simp only [hsum_coeff, add_coeff, add_apply]
  exact finsum_add_distrib (s.finite_co_support _) (t.finite_co_support _)
#align hahn_series.summable_family.hsum_add HahnSeries.SummableFamily.hsum_add

end AddCommMonoid

section AddCommGroup

variable [PartialOrder Γ] [AddCommGroup R] {α : Type*} {s t : SummableFamily Γ R α} {a : α}

instance : Neg (SummableFamily Γ R α) :=
  ⟨fun s =>
    { toFun := fun a => -s a
      isPWO_iUnion_support' := by
        simp_rw [support_neg]
        exact s.isPWO_iUnion_support
      finite_co_support' := fun g => by
        simp only [neg_coeff', Pi.neg_apply, Ne, neg_eq_zero]
        exact s.finite_co_support g }⟩

instance : AddCommGroup (SummableFamily Γ R α) :=
  { inferInstanceAs (AddCommMonoid (SummableFamily Γ R α)) with
    zsmul := zsmulRec
    add_left_neg := fun a => by
      ext
      apply add_left_neg }

@[simp]
theorem coe_neg : ⇑(-s) = -s :=
  rfl
#align hahn_series.summable_family.coe_neg HahnSeries.SummableFamily.coe_neg

theorem neg_apply : (-s) a = -s a :=
  rfl
#align hahn_series.summable_family.neg_apply HahnSeries.SummableFamily.neg_apply

@[simp]
theorem coe_sub : ⇑(s - t) = s - t :=
  rfl
#align hahn_series.summable_family.coe_sub HahnSeries.SummableFamily.coe_sub

theorem sub_apply : (s - t) a = s a - t a :=
  rfl
#align hahn_series.summable_family.sub_apply HahnSeries.SummableFamily.sub_apply

end AddCommGroup

section Semiring

variable [OrderedCancelAddCommMonoid Γ] [Semiring R] {α : Type*}

instance : SMul (HahnSeries Γ R) (SummableFamily Γ R α) where
  smul x s :=
    { toFun := fun a => x * s a
      isPWO_iUnion_support' := by
        apply (x.isPWO_support.add s.isPWO_iUnion_support).mono
        refine Set.Subset.trans (Set.iUnion_mono fun a => support_mul_subset_add_support) ?_
        intro g
        simp only [Set.mem_iUnion, exists_imp]
        exact fun a ha => (Set.add_subset_add (Set.Subset.refl _) (Set.subset_iUnion _ a)) ha
      finite_co_support' := fun g => by
        apply ((addAntidiagonal x.isPWO_support s.isPWO_iUnion_support g).finite_toSet.biUnion'
            fun ij _ => ?_).subset fun a ha => ?_
        · exact fun ij _ => Function.support fun a => (s a).coeff ij.2
        · apply s.finite_co_support
        · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset_add_support ha
          simp only [exists_prop, Set.mem_iUnion, mem_addAntidiagonal, mul_coeff, mem_support,
            isPWO_support, Prod.exists]
          exact ⟨i, j, mem_coe.2 (mem_addAntidiagonal.2 ⟨hi, Set.mem_iUnion.2 ⟨a, hj⟩, rfl⟩), hj⟩ }

@[simp]
theorem smul_apply {x : HahnSeries Γ R} {s : SummableFamily Γ R α} {a : α} : (x • s) a = x * s a :=
  rfl
#align hahn_series.summable_family.smul_apply HahnSeries.SummableFamily.smul_apply

instance : Module (HahnSeries Γ R) (SummableFamily Γ R α) where
  smul := (· • ·)
  smul_zero _ := ext fun _ => mul_zero _
  zero_smul _ := ext fun _ => zero_mul _
  one_smul _ := ext fun _ => one_mul _
  add_smul _ _ _  := ext fun _ => add_mul _ _ _
  smul_add _ _ _ := ext fun _ => mul_add _ _ _
  mul_smul _ _ _ := ext fun _ => mul_assoc _ _ _

@[simp]
theorem hsum_smul {x : HahnSeries Γ R} {s : SummableFamily Γ R α} : (x • s).hsum = x * s.hsum := by
  ext g
  simp only [mul_coeff, hsum_coeff, smul_apply]
  refine
    (Eq.trans (finsum_congr fun a => ?_)
          (finsum_sum_comm (addAntidiagonal x.isPWO_support s.isPWO_iUnion_support g)
            (fun i ij => x.coeff (Prod.fst ij) * (s i).coeff ij.snd) ?_)).trans
      ?_
  · refine sum_subset (addAntidiagonal_mono_right
      (Set.subset_iUnion (fun j => support (toFun s j)) a)) ?_
    rintro ⟨i, j⟩ hU ha
    rw [mem_addAntidiagonal] at *
    rw [Classical.not_not.1 fun con => ha ⟨hU.1, con, hU.2.2⟩, mul_zero]
  · rintro ⟨i, j⟩ _
    refine (s.finite_co_support j).subset ?_
    simp_rw [Function.support_subset_iff', Function.mem_support, Classical.not_not]
    intro a ha
    rw [ha, mul_zero]
  · refine (sum_congr rfl ?_).trans (sum_subset (addAntidiagonal_mono_right ?_) ?_).symm
    · rintro ⟨i, j⟩ _
      rw [mul_finsum]
      apply s.finite_co_support
    · intro x hx
      simp only [Set.mem_iUnion, Ne, mem_support]
      contrapose! hx
      simp [hx]
    · rintro ⟨i, j⟩ hU ha
      rw [mem_addAntidiagonal] at *
      rw [← hsum_coeff, Classical.not_not.1 fun con => ha ⟨hU.1, con, hU.2.2⟩,
        mul_zero]
#align hahn_series.summable_family.hsum_smul HahnSeries.SummableFamily.hsum_smul

/-- The summation of a `summable_family` as a `LinearMap`. -/
@[simps]
def lsum : SummableFamily Γ R α →ₗ[HahnSeries Γ R] HahnSeries Γ R where
  toFun := hsum
  map_add' _ _ := hsum_add
  map_smul' _ _ := hsum_smul
#align hahn_series.summable_family.lsum HahnSeries.SummableFamily.lsum

@[simp]
theorem hsum_sub {R : Type*} [Ring R] {s t : SummableFamily Γ R α} :
    (s - t).hsum = s.hsum - t.hsum := by
  rw [← lsum_apply, LinearMap.map_sub, lsum_apply, lsum_apply]
#align hahn_series.summable_family.hsum_sub HahnSeries.SummableFamily.hsum_sub

end Semiring

section OfFinsupp

variable [PartialOrder Γ] [AddCommMonoid R] {α : Type*}

/-- A family with only finitely many nonzero elements is summable. -/
def ofFinsupp (f : α →₀ HahnSeries Γ R) : SummableFamily Γ R α where
  toFun := f
  isPWO_iUnion_support' := by
    apply (f.support.isPWO_bUnion.2 fun a _ => (f a).isPWO_support).mono
    refine Set.iUnion_subset_iff.2 fun a g hg => ?_
    have haf : a ∈ f.support := by
      rw [Finsupp.mem_support_iff, ← support_nonempty_iff]
      exact ⟨g, hg⟩
    exact Set.mem_biUnion haf hg
  finite_co_support' g := by
    refine f.support.finite_toSet.subset fun a ha => ?_
    simp only [coeff.addMonoidHom_apply, mem_coe, Finsupp.mem_support_iff, Ne,
      Function.mem_support]
    contrapose! ha
    simp [ha]
#align hahn_series.summable_family.of_finsupp HahnSeries.SummableFamily.ofFinsupp

@[simp]
theorem coe_ofFinsupp {f : α →₀ HahnSeries Γ R} : ⇑(SummableFamily.ofFinsupp f) = f :=
  rfl
#align hahn_series.summable_family.coe_of_finsupp HahnSeries.SummableFamily.coe_ofFinsupp

@[simp]
theorem hsum_ofFinsupp {f : α →₀ HahnSeries Γ R} : (ofFinsupp f).hsum = f.sum fun _ => id := by
  ext g
  simp only [hsum_coeff, coe_ofFinsupp, Finsupp.sum, Ne]
  simp_rw [← coeff.addMonoidHom_apply, id]
  rw [map_sum, finsum_eq_sum_of_support_subset]
  intro x h
  simp only [coeff.addMonoidHom_apply, mem_coe, Finsupp.mem_support_iff, Ne]
  contrapose! h
  simp [h]
#align hahn_series.summable_family.hsum_of_finsupp HahnSeries.SummableFamily.hsum_ofFinsupp

end OfFinsupp

section EmbDomain

variable [PartialOrder Γ] [AddCommMonoid R] {α β : Type*}

/-- A summable family can be reindexed by an embedding without changing its sum. -/
def embDomain (s : SummableFamily Γ R α) (f : α ↪ β) : SummableFamily Γ R β where
  toFun b := if h : b ∈ Set.range f then s (Classical.choose h) else 0
  isPWO_iUnion_support' := by
    refine s.isPWO_iUnion_support.mono (Set.iUnion_subset fun b g h => ?_)
    by_cases hb : b ∈ Set.range f
    · dsimp only at h
      rw [dif_pos hb] at h
      exact Set.mem_iUnion.2 ⟨Classical.choose hb, h⟩
    · simp [-Set.mem_range, dif_neg hb] at h
  finite_co_support' g :=
    ((s.finite_co_support g).image f).subset
      (by
        intro b h
        by_cases hb : b ∈ Set.range f
        · simp only [Ne, Set.mem_setOf_eq, dif_pos hb] at h
          exact ⟨Classical.choose hb, h, Classical.choose_spec hb⟩
        · simp only [Ne, Set.mem_setOf_eq, dif_neg hb, zero_coeff, not_true_eq_false] at h)
#align hahn_series.summable_family.emb_domain HahnSeries.SummableFamily.embDomain

variable (s : SummableFamily Γ R α) (f : α ↪ β) {a : α} {b : β}

theorem embDomain_apply :
    s.embDomain f b = if h : b ∈ Set.range f then s (Classical.choose h) else 0 :=
  rfl
#align hahn_series.summable_family.emb_domain_apply HahnSeries.SummableFamily.embDomain_apply

@[simp]
theorem embDomain_image : s.embDomain f (f a) = s a := by
  rw [embDomain_apply, dif_pos (Set.mem_range_self a)]
  exact congr rfl (f.injective (Classical.choose_spec (Set.mem_range_self a)))
#align hahn_series.summable_family.emb_domain_image HahnSeries.SummableFamily.embDomain_image

@[simp]
theorem embDomain_notin_range (h : b ∉ Set.range f) : s.embDomain f b = 0 := by
  rw [embDomain_apply, dif_neg h]
#align hahn_series.summable_family.emb_domain_notin_range HahnSeries.SummableFamily.embDomain_notin_range

@[simp]
theorem hsum_embDomain : (s.embDomain f).hsum = s.hsum := by
  ext g
  simp only [hsum_coeff, embDomain_apply, apply_dite HahnSeries.coeff, dite_apply, zero_coeff]
  exact finsum_emb_domain f fun a => (s a).coeff g
#align hahn_series.summable_family.hsum_emb_domain HahnSeries.SummableFamily.hsum_embDomain

end EmbDomain

section powers

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R] [IsDomain R]

/-- The powers of an element of positive valuation form a summable family. -/
def powers (x : HahnSeries Γ R) (hx : 0 < addVal Γ R x) : SummableFamily Γ R ℕ where
  toFun n := x ^ n
  isPWO_iUnion_support' := isPWO_iUnion_support_powers hx
  finite_co_support' g := by
    have hpwo := isPWO_iUnion_support_powers hx
    by_cases hg : g ∈ ⋃ n : ℕ, { g | (x ^ n).coeff g ≠ 0 }
    swap; · exact Set.finite_empty.subset fun n hn => hg (Set.mem_iUnion.2 ⟨n, hn⟩)
    apply hpwo.isWF.induction hg
    intro y ys hy
    refine
      ((((addAntidiagonal x.isPWO_support hpwo y).finite_toSet.biUnion fun ij hij =>
                    hy ij.snd ?_ ?_).image
                Nat.succ).union
            (Set.finite_singleton 0)).subset
        ?_
    · exact (mem_addAntidiagonal.1 (mem_coe.1 hij)).2.1
    · obtain ⟨hi, _, rfl⟩ := mem_addAntidiagonal.1 (mem_coe.1 hij)
      rw [← zero_add ij.snd, ← add_assoc, add_zero]
      exact
        add_lt_add_right (WithTop.coe_lt_coe.1 (lt_of_lt_of_le hx (addVal_le_of_coeff_ne_zero hi)))
          _
    · rintro (_ | n) hn
      · exact Set.mem_union_right _ (Set.mem_singleton 0)
      · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset_add_support hn
        refine Set.mem_union_left _ ⟨n, Set.mem_iUnion.2 ⟨⟨j, i⟩, Set.mem_iUnion.2 ⟨?_, hi⟩⟩, rfl⟩
        simp only [and_true_iff, Set.mem_iUnion, mem_addAntidiagonal, mem_coe, eq_self_iff_true,
          Ne, mem_support, Set.mem_setOf_eq]
        exact ⟨hj, ⟨n, hi⟩, add_comm j i⟩
#align hahn_series.summable_family.powers HahnSeries.SummableFamily.powers

variable {x : HahnSeries Γ R} (hx : 0 < addVal Γ R x)

@[simp]
theorem coe_powers : ⇑(powers x hx) = HPow.hPow x :=
  rfl
#align hahn_series.summable_family.coe_powers HahnSeries.SummableFamily.coe_powers

theorem embDomain_succ_smul_powers :
    (x • powers x hx).embDomain ⟨Nat.succ, Nat.succ_injective⟩ =
      powers x hx - ofFinsupp (Finsupp.single 0 1) := by
  apply SummableFamily.ext
  rintro (_ | n)
  · rw [embDomain_notin_range, sub_apply, coe_powers, pow_zero, coe_ofFinsupp,
      Finsupp.single_eq_same, sub_self]
    rw [Set.mem_range, not_exists]
    exact Nat.succ_ne_zero
  · refine Eq.trans (embDomain_image _ ⟨Nat.succ, Nat.succ_injective⟩) ?_
    simp only [pow_succ', coe_powers, coe_sub, smul_apply, coe_ofFinsupp, Pi.sub_apply]
    rw [Finsupp.single_eq_of_ne n.succ_ne_zero.symm, sub_zero]
#align hahn_series.summable_family.emb_domain_succ_smul_powers HahnSeries.SummableFamily.embDomain_succ_smul_powers

theorem one_sub_self_mul_hsum_powers : (1 - x) * (powers x hx).hsum = 1 := by
  rw [← hsum_smul, sub_smul 1 x (powers x hx), one_smul, hsum_sub, ←
    hsum_embDomain (x • powers x hx) ⟨Nat.succ, Nat.succ_injective⟩, embDomain_succ_smul_powers]
  simp
#align hahn_series.summable_family.one_sub_self_mul_hsum_powers HahnSeries.SummableFamily.one_sub_self_mul_hsum_powers

end powers

end SummableFamily

section Inversion

variable [LinearOrderedAddCommGroup Γ]

section IsDomain

variable [CommRing R] [IsDomain R]

theorem unit_aux (x : HahnSeries Γ R) {r : R} (hr : r * x.coeff x.order = 1) :
    0 < addVal Γ R (1 - C r * single (-x.order) 1 * x) := by
  have h10 : (1 : R) ≠ 0 := one_ne_zero
  have x0 : x ≠ 0 := ne_zero_of_coeff_ne_zero (right_ne_zero_of_mul_eq_one hr)
  refine lt_of_le_of_ne ((addVal Γ R).map_le_sub (ge_of_eq (addVal Γ R).map_one) ?_) ?_
  · simp only [AddValuation.map_mul]
    rw [addVal_apply_of_ne x0, addVal_apply_of_ne (single_ne_zero h10), addVal_apply_of_ne _,
      order_C, order_single h10, WithTop.coe_zero, zero_add, ← WithTop.coe_add, neg_add_self,
      WithTop.coe_zero]
    exact C_ne_zero (left_ne_zero_of_mul_eq_one hr)
  · rw [addVal_apply, ← WithTop.coe_zero]
    split_ifs with h
    · apply WithTop.coe_ne_top
    rw [Ne, WithTop.coe_eq_coe]
    intro con
    apply coeff_order_ne_zero h
    rw [← con, mul_assoc, sub_coeff, one_coeff, if_pos rfl, C_mul_eq_smul, smul_coeff, smul_eq_mul,
      ← add_neg_self x.order, single_mul_coeff_add, one_mul, hr, sub_self]
#align hahn_series.unit_aux HahnSeries.unit_aux

theorem isUnit_iff {x : HahnSeries Γ R} : IsUnit x ↔ IsUnit (x.coeff x.order) := by
  constructor
  · rintro ⟨⟨u, i, ui, iu⟩, rfl⟩
    refine
      isUnit_of_mul_eq_one (u.coeff u.order) (i.coeff i.order)
        ((mul_coeff_order_add_order u i).symm.trans ?_)
    rw [ui, one_coeff, if_pos]
    rw [← order_mul (left_ne_zero_of_mul_eq_one ui) (right_ne_zero_of_mul_eq_one ui), ui, order_one]
  · rintro ⟨⟨u, i, ui, iu⟩, h⟩
    rw [Units.val_mk] at h
    rw [h] at iu
    have h := SummableFamily.one_sub_self_mul_hsum_powers (unit_aux x iu)
    rw [sub_sub_cancel] at h
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_eq_one _ _ h)
#align hahn_series.is_unit_iff HahnSeries.isUnit_iff

end IsDomain

instance instField [Field R] : Field (HahnSeries Γ R) where
  __ : IsDomain (HahnSeries Γ R) := inferInstance
  inv x :=
    if x0 : x = 0 then 0
    else
      C (x.coeff x.order)⁻¹ * (single (-x.order)) 1 *
        (SummableFamily.powers _ (unit_aux x (inv_mul_cancel (coeff_order_ne_zero x0)))).hsum
  inv_zero := dif_pos rfl
  mul_inv_cancel x x0 := (congr rfl (dif_neg x0)).trans $ by
    have h :=
      SummableFamily.one_sub_self_mul_hsum_powers
        (unit_aux x (inv_mul_cancel (coeff_order_ne_zero x0)))
    rw [sub_sub_cancel] at h
    rw [← mul_assoc, mul_comm x, h]
  nnqsmul := _
  qsmul := _

end Inversion

end HahnSeries
