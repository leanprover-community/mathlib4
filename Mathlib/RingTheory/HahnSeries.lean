/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module ring_theory.hahn_series
! leanprover-community/mathlib commit a484a7d0eade4e1268f4fb402859b6686037f965
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.WellFoundedSet
import Mathbin.Algebra.BigOperators.Finprod
import Mathbin.RingTheory.Valuation.Basic
import Mathbin.RingTheory.PowerSeries.Basic
import Mathbin.Data.Finsupp.Pwo
import Mathbin.Data.Finset.MulAntidiagonal
import Mathbin.Algebra.Order.Group.WithTop

/-!
# Hahn Series
If `Γ` is ordered and `R` has zero, then `hahn_series Γ R` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. With further structure on `R` and
`Γ`, we can add further structure on `hahn_series Γ R`, with the most studied case being when `Γ` is
a linearly ordered abelian group and `R` is a field, in which case `hahn_series Γ R` is a
valued field, with value group `Γ`.

These generalize Laurent series (with value group `ℤ`), and Laurent series are implemented that way
in the file `ring_theory/laurent_series`.

## Main Definitions
  * If `Γ` is ordered and `R` has zero, then `hahn_series Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are partially well-ordered.
  * If `R` is a (commutative) additive monoid or group, then so is `hahn_series Γ R`.
  * If `R` is a (comm_)(semi)ring, then so is `hahn_series Γ R`.
  * `hahn_series.add_val Γ R` defines an `add_valuation` on `hahn_series Γ R` when `Γ` is linearly
    ordered.
  * A `hahn_series.summable_family` is a family of Hahn series such that the union of their supports
  is well-founded and only finitely many are nonzero at any given coefficient. They have a formal
  sum, `hahn_series.summable_family.hsum`, which can be bundled as a `linear_map` as
  `hahn_series.summable_family.lsum`. Note that this is different from `summable` in the valuation
  topology, because there are topologically summable families that do not satisfy the axioms of
  `hahn_series.summable_family`, and formally summable families whose sums do not converge
  topologically.
  * Laurent series over `R` are implemented as `hahn_series ℤ R` in the file
    `ring_theory/laurent_series`.

## TODO
  * Build an API for the variable `X` (defined to be `single 1 1 : hahn_series Γ R`) in analogy to
    `X : R[X]` and `X : power_series R`

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]

-/


open Finset Function

open BigOperators Classical Pointwise Polynomial

noncomputable section

/-- If `Γ` is linearly ordered and `R` has zero, then `hahn_series Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are well-founded. -/
@[ext]
structure HahnSeries (Γ : Type _) (R : Type _) [PartialOrder Γ] [Zero R] where
  coeff : Γ → R
  isPwo_support' : (support coeff).IsPwo
#align hahn_series HahnSeries

variable {Γ : Type _} {R : Type _}

namespace HahnSeries

section Zero

variable [PartialOrder Γ] [Zero R]

theorem coeff_injective : Injective (coeff : HahnSeries Γ R → Γ → R) :=
  ext
#align hahn_series.coeff_injective HahnSeries.coeff_injective

@[simp]
theorem coeff_inj {x y : HahnSeries Γ R} : x.coeff = y.coeff ↔ x = y :=
  coeff_injective.eq_iff
#align hahn_series.coeff_inj HahnSeries.coeff_inj

/-- The support of a Hahn series is just the set of indices whose coefficients are nonzero.
  Notably, it is well-founded. -/
def support (x : HahnSeries Γ R) : Set Γ :=
  support x.coeff
#align hahn_series.support HahnSeries.support

@[simp]
theorem isPwo_support (x : HahnSeries Γ R) : x.support.IsPwo :=
  x.isPwo_support'
#align hahn_series.is_pwo_support HahnSeries.isPwo_support

@[simp]
theorem isWf_support (x : HahnSeries Γ R) : x.support.IsWf :=
  x.isPwo_support.IsWf
#align hahn_series.is_wf_support HahnSeries.isWf_support

@[simp]
theorem mem_support (x : HahnSeries Γ R) (a : Γ) : a ∈ x.support ↔ x.coeff a ≠ 0 :=
  Iff.refl _
#align hahn_series.mem_support HahnSeries.mem_support

instance : Zero (HahnSeries Γ R) :=
  ⟨{  coeff := 0
      isPwo_support' := by simp }⟩

instance : Inhabited (HahnSeries Γ R) :=
  ⟨0⟩

instance [Subsingleton R] : Subsingleton (HahnSeries Γ R) :=
  ⟨fun a b => a.ext b (Subsingleton.elim _ _)⟩

@[simp]
theorem zero_coeff {a : Γ} : (0 : HahnSeries Γ R).coeff a = 0 :=
  rfl
#align hahn_series.zero_coeff HahnSeries.zero_coeff

@[simp]
theorem coeff_fun_eq_zero_iff {x : HahnSeries Γ R} : x.coeff = 0 ↔ x = 0 :=
  coeff_injective.eq_iff' rfl
#align hahn_series.coeff_fun_eq_zero_iff HahnSeries.coeff_fun_eq_zero_iff

theorem ne_zero_of_coeff_ne_zero {x : HahnSeries Γ R} {g : Γ} (h : x.coeff g ≠ 0) : x ≠ 0 :=
  mt (fun x0 => (x0.symm ▸ zero_coeff : x.coeff g = 0)) h
#align hahn_series.ne_zero_of_coeff_ne_zero HahnSeries.ne_zero_of_coeff_ne_zero

@[simp]
theorem support_zero : support (0 : HahnSeries Γ R) = ∅ :=
  Function.support_zero
#align hahn_series.support_zero HahnSeries.support_zero

@[simp]
theorem support_nonempty_iff {x : HahnSeries Γ R} : x.support.Nonempty ↔ x ≠ 0 := by
  rw [support, support_nonempty_iff, Ne.def, coeff_fun_eq_zero_iff]
#align hahn_series.support_nonempty_iff HahnSeries.support_nonempty_iff

@[simp]
theorem support_eq_empty_iff {x : HahnSeries Γ R} : x.support = ∅ ↔ x = 0 :=
  support_eq_empty_iff.trans coeff_fun_eq_zero_iff
#align hahn_series.support_eq_empty_iff HahnSeries.support_eq_empty_iff

/-- `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise. -/
def single (a : Γ) : ZeroHom R (HahnSeries Γ R)
    where
  toFun r :=
    { coeff := Pi.single a r
      isPwo_support' := (Set.isPwo_singleton a).mono Pi.support_single_subset }
  map_zero' := ext _ _ (Pi.single_zero _)
#align hahn_series.single HahnSeries.single

variable {a b : Γ} {r : R}

@[simp]
theorem single_coeff_same (a : Γ) (r : R) : (single a r).coeff a = r :=
  Pi.single_eq_same a r
#align hahn_series.single_coeff_same HahnSeries.single_coeff_same

@[simp]
theorem single_coeff_of_ne (h : b ≠ a) : (single a r).coeff b = 0 :=
  Pi.single_eq_of_ne h r
#align hahn_series.single_coeff_of_ne HahnSeries.single_coeff_of_ne

theorem single_coeff : (single a r).coeff b = if b = a then r else 0 := by
  split_ifs with h <;> simp [h]
#align hahn_series.single_coeff HahnSeries.single_coeff

@[simp]
theorem support_single_of_ne (h : r ≠ 0) : support (single a r) = {a} :=
  Pi.support_single_of_ne h
#align hahn_series.support_single_of_ne HahnSeries.support_single_of_ne

theorem support_single_subset : support (single a r) ⊆ {a} :=
  Pi.support_single_subset
#align hahn_series.support_single_subset HahnSeries.support_single_subset

theorem eq_of_mem_support_single {b : Γ} (h : b ∈ support (single a r)) : b = a :=
  support_single_subset h
#align hahn_series.eq_of_mem_support_single HahnSeries.eq_of_mem_support_single

@[simp]
theorem single_eq_zero : single a (0 : R) = 0 :=
  (single a).map_zero
#align hahn_series.single_eq_zero HahnSeries.single_eq_zero

theorem single_injective (a : Γ) : Function.Injective (single a : R → HahnSeries Γ R) :=
  fun r s rs => by rw [← single_coeff_same a r, ← single_coeff_same a s, rs]
#align hahn_series.single_injective HahnSeries.single_injective

theorem single_ne_zero (h : r ≠ 0) : single a r ≠ 0 := fun con =>
  h (single_injective a (Con.trans single_eq_zero.symm))
#align hahn_series.single_ne_zero HahnSeries.single_ne_zero

@[simp]
theorem single_eq_zero_iff {a : Γ} {r : R} : single a r = 0 ↔ r = 0 :=
  by
  constructor
  · contrapose!
    exact single_ne_zero
  · simp (config := { contextual := true })
#align hahn_series.single_eq_zero_iff HahnSeries.single_eq_zero_iff

instance [Nonempty Γ] [Nontrivial R] : Nontrivial (HahnSeries Γ R) :=
  ⟨by
    obtain ⟨r, s, rs⟩ := exists_pair_ne R
    inhabit Γ
    refine' ⟨single (Inhabited.default Γ) r, single (Inhabited.default Γ) s, fun con => rs _⟩
    rw [← single_coeff_same (Inhabited.default Γ) r, Con, single_coeff_same]⟩

section Order

variable [Zero Γ]

/-- The order of a nonzero Hahn series `x` is a minimal element of `Γ` where `x` has a
  nonzero coefficient, the order of 0 is 0. -/
def order (x : HahnSeries Γ R) : Γ :=
  if h : x = 0 then 0 else x.isWf_support.min (support_nonempty_iff.2 h)
#align hahn_series.order HahnSeries.order

@[simp]
theorem order_zero : order (0 : HahnSeries Γ R) = 0 :=
  dif_pos rfl
#align hahn_series.order_zero HahnSeries.order_zero

theorem order_of_ne {x : HahnSeries Γ R} (hx : x ≠ 0) :
    order x = x.isWf_support.min (support_nonempty_iff.2 hx) :=
  dif_neg hx
#align hahn_series.order_of_ne HahnSeries.order_of_ne

theorem coeff_order_ne_zero {x : HahnSeries Γ R} (hx : x ≠ 0) : x.coeff x.order ≠ 0 :=
  by
  rw [order_of_ne hx]
  exact x.is_wf_support.min_mem (support_nonempty_iff.2 hx)
#align hahn_series.coeff_order_ne_zero HahnSeries.coeff_order_ne_zero

theorem order_le_of_coeff_ne_zero {Γ} [LinearOrderedCancelAddCommMonoid Γ] {x : HahnSeries Γ R}
    {g : Γ} (h : x.coeff g ≠ 0) : x.order ≤ g :=
  le_trans (le_of_eq (order_of_ne (ne_zero_of_coeff_ne_zero h)))
    (Set.IsWf.min_le _ _ ((mem_support _ _).2 h))
#align hahn_series.order_le_of_coeff_ne_zero HahnSeries.order_le_of_coeff_ne_zero

@[simp]
theorem order_single (h : r ≠ 0) : (single a r).order = a :=
  (order_of_ne (single_ne_zero h)).trans
    (support_single_subset
      ((single a r).isWf_support.min_mem (support_nonempty_iff.2 (single_ne_zero h))))
#align hahn_series.order_single HahnSeries.order_single

theorem coeff_eq_zero_of_lt_order {x : HahnSeries Γ R} {i : Γ} (hi : i < x.order) : x.coeff i = 0 :=
  by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  contrapose! hi
  rw [← Ne.def, ← mem_support] at hi
  rw [order_of_ne hx]
  exact Set.IsWf.not_lt_min _ _ hi
#align hahn_series.coeff_eq_zero_of_lt_order HahnSeries.coeff_eq_zero_of_lt_order

end Order

section Domain

variable {Γ' : Type _} [PartialOrder Γ']

/-- Extends the domain of a `hahn_series` by an `order_embedding`. -/
def embDomain (f : Γ ↪o Γ') : HahnSeries Γ R → HahnSeries Γ' R := fun x =>
  { coeff := fun b : Γ' => if h : b ∈ f '' x.support then x.coeff (Classical.choose h) else 0
    isPwo_support' :=
      (x.isPwo_support.image_of_monotone f.Monotone).mono fun b hb =>
        by
        contrapose! hb
        rw [Function.mem_support, dif_neg hb, Classical.not_not] }
#align hahn_series.emb_domain HahnSeries.embDomain

@[simp]
theorem embDomain_coeff {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {a : Γ} :
    (embDomain f x).coeff (f a) = x.coeff a :=
  by
  rw [emb_domain]
  dsimp only
  by_cases ha : a ∈ x.support
  · rw [dif_pos (Set.mem_image_of_mem f ha)]
    exact congr rfl (f.injective (Classical.choose_spec (Set.mem_image_of_mem f ha)).2)
  · rw [dif_neg, Classical.not_not.1 fun c => ha ((mem_support _ _).2 c)]
    contrapose! ha
    obtain ⟨b, hb1, hb2⟩ := (Set.mem_image _ _ _).1 ha
    rwa [f.injective hb2] at hb1
#align hahn_series.emb_domain_coeff HahnSeries.embDomain_coeff

@[simp]
theorem embDomain_mk_coeff {f : Γ → Γ'} (hfi : Function.Injective f)
    (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') {x : HahnSeries Γ R} {a : Γ} :
    (embDomain ⟨⟨f, hfi⟩, hf⟩ x).coeff (f a) = x.coeff a :=
  embDomain_coeff
#align hahn_series.emb_domain_mk_coeff HahnSeries.embDomain_mk_coeff

theorem embDomain_notin_image_support {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {b : Γ'}
    (hb : b ∉ f '' x.support) : (embDomain f x).coeff b = 0 :=
  dif_neg hb
#align hahn_series.emb_domain_notin_image_support HahnSeries.embDomain_notin_image_support

theorem support_embDomain_subset {f : Γ ↪o Γ'} {x : HahnSeries Γ R} :
    support (embDomain f x) ⊆ f '' x.support :=
  by
  intro g hg
  contrapose! hg
  rw [mem_support, emb_domain_notin_image_support hg, Classical.not_not]
#align hahn_series.support_emb_domain_subset HahnSeries.support_embDomain_subset

theorem embDomain_notin_range {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {b : Γ'} (hb : b ∉ Set.range f) :
    (embDomain f x).coeff b = 0 :=
  embDomain_notin_image_support fun con => hb (Set.image_subset_range _ _ Con)
#align hahn_series.emb_domain_notin_range HahnSeries.embDomain_notin_range

@[simp]
theorem embDomain_zero {f : Γ ↪o Γ'} : embDomain f (0 : HahnSeries Γ R) = 0 :=
  by
  ext
  simp [emb_domain_notin_image_support]
#align hahn_series.emb_domain_zero HahnSeries.embDomain_zero

@[simp]
theorem embDomain_single {f : Γ ↪o Γ'} {g : Γ} {r : R} :
    embDomain f (single g r) = single (f g) r :=
  by
  ext g'
  by_cases h : g' = f g
  · simp [h]
  rw [emb_domain_notin_image_support, single_coeff_of_ne h]
  by_cases hr : r = 0
  · simp [hr]
  rwa [support_single_of_ne hr, Set.image_singleton, Set.mem_singleton_iff]
#align hahn_series.emb_domain_single HahnSeries.embDomain_single

theorem embDomain_injective {f : Γ ↪o Γ'} :
    Function.Injective (embDomain f : HahnSeries Γ R → HahnSeries Γ' R) := fun x y xy =>
  by
  ext g
  rw [ext_iff, Function.funext_iff] at xy
  have xyg := xy (f g)
  rwa [emb_domain_coeff, emb_domain_coeff] at xyg
#align hahn_series.emb_domain_injective HahnSeries.embDomain_injective

end Domain

end Zero

section Addition

variable [PartialOrder Γ]

section AddMonoid

variable [AddMonoid R]

instance : Add (HahnSeries Γ R)
    where add x y :=
    { coeff := x.coeff + y.coeff
      isPwo_support' := (x.isPwo_support.union y.isPwo_support).mono (Function.support_add _ _) }

instance : AddMonoid (HahnSeries Γ R) where
  zero := 0
  add := (· + ·)
  add_assoc x y z := by
    ext
    apply add_assoc
  zero_add x := by
    ext
    apply zero_add
  add_zero x := by
    ext
    apply add_zero

@[simp]
theorem add_coeff' {x y : HahnSeries Γ R} : (x + y).coeff = x.coeff + y.coeff :=
  rfl
#align hahn_series.add_coeff' HahnSeries.add_coeff'

theorem add_coeff {x y : HahnSeries Γ R} {a : Γ} : (x + y).coeff a = x.coeff a + y.coeff a :=
  rfl
#align hahn_series.add_coeff HahnSeries.add_coeff

theorem support_add_subset {x y : HahnSeries Γ R} : support (x + y) ⊆ support x ∪ support y :=
  fun a ha => by
  rw [mem_support, add_coeff] at ha
  rw [Set.mem_union, mem_support, mem_support]
  contrapose! ha
  rw [ha.1, ha.2, add_zero]
#align hahn_series.support_add_subset HahnSeries.support_add_subset

theorem min_order_le_order_add {Γ} [LinearOrderedCancelAddCommMonoid Γ] {x y : HahnSeries Γ R}
    (hxy : x + y ≠ 0) : min x.order y.order ≤ (x + y).order :=
  by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [order_of_ne hx, order_of_ne hy, order_of_ne hxy]
  refine' le_trans _ (Set.IsWf.min_le_min_of_subset support_add_subset)
  · exact x.is_wf_support.union y.is_wf_support
  · exact Set.Nonempty.mono (Set.subset_union_left _ _) (support_nonempty_iff.2 hx)
  rw [Set.IsWf.min_union]
#align hahn_series.min_order_le_order_add HahnSeries.min_order_le_order_add

/-- `single` as an additive monoid/group homomorphism -/
@[simps]
def single.addMonoidHom (a : Γ) : R →+ HahnSeries Γ R :=
  { single a with
    map_add' := fun x y => by
      ext b
      by_cases h : b = a <;> simp [h] }
#align hahn_series.single.add_monoid_hom HahnSeries.single.addMonoidHom

/-- `coeff g` as an additive monoid/group homomorphism -/
@[simps]
def coeff.addMonoidHom (g : Γ) : HahnSeries Γ R →+ R
    where
  toFun f := f.coeff g
  map_zero' := zero_coeff
  map_add' x y := add_coeff
#align hahn_series.coeff.add_monoid_hom HahnSeries.coeff.addMonoidHom

section Domain

variable {Γ' : Type _} [PartialOrder Γ']

theorem embDomain_add (f : Γ ↪o Γ') (x y : HahnSeries Γ R) :
    embDomain f (x + y) = embDomain f x + embDomain f y :=
  by
  ext g
  by_cases hg : g ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hg
    simp
  · simp [emb_domain_notin_range, hg]
#align hahn_series.emb_domain_add HahnSeries.embDomain_add

end Domain

end AddMonoid

instance [AddCommMonoid R] : AddCommMonoid (HahnSeries Γ R) :=
  { HahnSeries.addMonoid with
    add_comm := fun x y => by
      ext
      apply add_comm }

section AddGroup

variable [AddGroup R]

instance : AddGroup (HahnSeries Γ R) :=
  {
    HahnSeries.addMonoid with
    neg := fun x =>
      { coeff := fun a => -x.coeff a
        isPwo_support' := by
          rw [Function.support_neg]
          exact x.is_pwo_support }
    add_left_neg := fun x => by
      ext
      apply add_left_neg }

@[simp]
theorem neg_coeff' {x : HahnSeries Γ R} : (-x).coeff = -x.coeff :=
  rfl
#align hahn_series.neg_coeff' HahnSeries.neg_coeff'

theorem neg_coeff {x : HahnSeries Γ R} {a : Γ} : (-x).coeff a = -x.coeff a :=
  rfl
#align hahn_series.neg_coeff HahnSeries.neg_coeff

@[simp]
theorem support_neg {x : HahnSeries Γ R} : (-x).support = x.support :=
  by
  ext
  simp
#align hahn_series.support_neg HahnSeries.support_neg

@[simp]
theorem sub_coeff' {x y : HahnSeries Γ R} : (x - y).coeff = x.coeff - y.coeff :=
  by
  ext
  simp [sub_eq_add_neg]
#align hahn_series.sub_coeff' HahnSeries.sub_coeff'

theorem sub_coeff {x y : HahnSeries Γ R} {a : Γ} : (x - y).coeff a = x.coeff a - y.coeff a := by
  simp
#align hahn_series.sub_coeff HahnSeries.sub_coeff

@[simp]
theorem order_neg [Zero Γ] {f : HahnSeries Γ R} : (-f).order = f.order :=
  by
  by_cases hf : f = 0
  · simp only [hf, neg_zero]
  simp only [order, support_neg, neg_eq_zero]
#align hahn_series.order_neg HahnSeries.order_neg

end AddGroup

instance [AddCommGroup R] : AddCommGroup (HahnSeries Γ R) :=
  { HahnSeries.addCommMonoid, HahnSeries.addGroup with }

end Addition

section DistribMulAction

variable [PartialOrder Γ] {V : Type _} [Monoid R] [AddMonoid V] [DistribMulAction R V]

instance : SMul R (HahnSeries Γ V) :=
  ⟨fun r x =>
    { coeff := r • x.coeff
      isPwo_support' := x.isPwo_support.mono (Function.support_smul_subset_right r x.coeff) }⟩

@[simp]
theorem smul_coeff {r : R} {x : HahnSeries Γ V} {a : Γ} : (r • x).coeff a = r • x.coeff a :=
  rfl
#align hahn_series.smul_coeff HahnSeries.smul_coeff

instance : DistribMulAction R (HahnSeries Γ V)
    where
  smul := (· • ·)
  one_smul _ := by
    ext
    simp
  smul_zero _ := by
    ext
    simp
  smul_add _ _ _ := by
    ext
    simp [smul_add]
  mul_smul _ _ _ := by
    ext
    simp [mul_smul]

variable {S : Type _} [Monoid S] [DistribMulAction S V]

instance [SMul R S] [IsScalarTower R S V] : IsScalarTower R S (HahnSeries Γ V) :=
  ⟨fun r s a => by
    ext
    simp⟩

instance [SMulCommClass R S V] : SMulCommClass R S (HahnSeries Γ V) :=
  ⟨fun r s a => by
    ext
    simp [smul_comm]⟩

end DistribMulAction

section Module

variable [PartialOrder Γ] [Semiring R] {V : Type _} [AddCommMonoid V] [Module R V]

instance : Module R (HahnSeries Γ V) :=
  {
    HahnSeries.distribMulAction with
    zero_smul := fun _ => by
      ext
      simp
    add_smul := fun _ _ _ => by
      ext
      simp [add_smul] }

/-- `single` as a linear map -/
@[simps]
def single.linearMap (a : Γ) : R →ₗ[R] HahnSeries Γ R :=
  { single.addMonoidHom a with
    map_smul' := fun r s => by
      ext b
      by_cases h : b = a <;> simp [h] }
#align hahn_series.single.linear_map HahnSeries.single.linearMap

/-- `coeff g` as a linear map -/
@[simps]
def coeff.linearMap (g : Γ) : HahnSeries Γ R →ₗ[R] R :=
  { coeff.addMonoidHom g with map_smul' := fun r s => rfl }
#align hahn_series.coeff.linear_map HahnSeries.coeff.linearMap

section Domain

variable {Γ' : Type _} [PartialOrder Γ']

theorem embDomain_smul (f : Γ ↪o Γ') (r : R) (x : HahnSeries Γ R) :
    embDomain f (r • x) = r • embDomain f x := by
  ext g
  by_cases hg : g ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hg
    simp
  · simp [emb_domain_notin_range, hg]
#align hahn_series.emb_domain_smul HahnSeries.embDomain_smul

/-- Extending the domain of Hahn series is a linear map. -/
@[simps]
def embDomainLinearMap (f : Γ ↪o Γ') : HahnSeries Γ R →ₗ[R] HahnSeries Γ' R
    where
  toFun := embDomain f
  map_add' := embDomain_add f
  map_smul' := embDomain_smul f
#align hahn_series.emb_domain_linear_map HahnSeries.embDomainLinearMap

end Domain

end Module

section Multiplication

variable [OrderedCancelAddCommMonoid Γ]

instance [Zero R] [One R] : One (HahnSeries Γ R) :=
  ⟨single 0 1⟩

@[simp]
theorem one_coeff [Zero R] [One R] {a : Γ} :
    (1 : HahnSeries Γ R).coeff a = if a = 0 then 1 else 0 :=
  single_coeff
#align hahn_series.one_coeff HahnSeries.one_coeff

@[simp]
theorem single_zero_one [Zero R] [One R] : single 0 (1 : R) = 1 :=
  rfl
#align hahn_series.single_zero_one HahnSeries.single_zero_one

@[simp]
theorem support_one [MulZeroOneClass R] [Nontrivial R] : support (1 : HahnSeries Γ R) = {0} :=
  support_single_of_ne one_ne_zero
#align hahn_series.support_one HahnSeries.support_one

@[simp]
theorem order_one [MulZeroOneClass R] : order (1 : HahnSeries Γ R) = 0 :=
  by
  cases' subsingleton_or_nontrivial R with h h <;> haveI := h
  · rw [Subsingleton.elim (1 : HahnSeries Γ R) 0, order_zero]
  · exact order_single one_ne_zero
#align hahn_series.order_one HahnSeries.order_one

instance [NonUnitalNonAssocSemiring R] : Mul (HahnSeries Γ R)
    where mul x y :=
    { coeff := fun a =>
        ∑ ij in addAntidiagonal x.isPwo_support y.isPwo_support a, x.coeff ij.fst * y.coeff ij.snd
      isPwo_support' :=
        haveI h :
          { a : Γ |
              (∑ ij : Γ × Γ in add_antidiagonal x.is_pwo_support y.is_pwo_support a,
                  x.coeff ij.fst * y.coeff ij.snd) ≠
                0 } ⊆
            { a : Γ | (add_antidiagonal x.is_pwo_support y.is_pwo_support a).Nonempty } :=
          by
          intro a ha
          contrapose! ha
          simp [not_nonempty_iff_eq_empty.1 ha]
        is_pwo_support_add_antidiagonal.mono h }

@[simp]
theorem mul_coeff [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} {a : Γ} :
    (x * y).coeff a =
      ∑ ij in addAntidiagonal x.isPwo_support y.isPwo_support a, x.coeff ij.fst * y.coeff ij.snd :=
  rfl
#align hahn_series.mul_coeff HahnSeries.mul_coeff

theorem mul_coeff_right' [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} {a : Γ} {s : Set Γ}
    (hs : s.IsPwo) (hys : y.support ⊆ s) :
    (x * y).coeff a =
      ∑ ij in addAntidiagonal x.isPwo_support hs a, x.coeff ij.fst * y.coeff ij.snd :=
  by
  rw [mul_coeff]
  apply sum_subset_zero_on_sdiff (add_antidiagonal_mono_right hys) _ fun _ _ => rfl
  intro b hb
  simp only [not_and, mem_sdiff, mem_add_antidiagonal, mem_support, not_imp_not] at hb
  rw [hb.2 hb.1.1 hb.1.2.2, MulZeroClass.mul_zero]
#align hahn_series.mul_coeff_right' HahnSeries.mul_coeff_right'

theorem mul_coeff_left' [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} {a : Γ} {s : Set Γ}
    (hs : s.IsPwo) (hxs : x.support ⊆ s) :
    (x * y).coeff a =
      ∑ ij in addAntidiagonal hs y.isPwo_support a, x.coeff ij.fst * y.coeff ij.snd :=
  by
  rw [mul_coeff]
  apply sum_subset_zero_on_sdiff (add_antidiagonal_mono_left hxs) _ fun _ _ => rfl
  intro b hb
  simp only [not_and', mem_sdiff, mem_add_antidiagonal, mem_support, not_ne_iff] at hb
  rw [hb.2 ⟨hb.1.2.1, hb.1.2.2⟩, MulZeroClass.zero_mul]
#align hahn_series.mul_coeff_left' HahnSeries.mul_coeff_left'

instance [NonUnitalNonAssocSemiring R] : Distrib (HahnSeries Γ R) :=
  { HahnSeries.hasMul,
    HahnSeries.hasAdd with
    left_distrib := fun x y z => by
      ext a
      have hwf := y.is_pwo_support.union z.is_pwo_support
      rw [mul_coeff_right' hwf, add_coeff, mul_coeff_right' hwf (Set.subset_union_right _ _),
        mul_coeff_right' hwf (Set.subset_union_left _ _)]
      · simp only [add_coeff, mul_add, sum_add_distrib]
      · intro b
        simp only [add_coeff, Ne.def, Set.mem_union, Set.mem_setOf_eq, mem_support]
        contrapose!
        intro h
        rw [h.1, h.2, add_zero]
    right_distrib := fun x y z => by
      ext a
      have hwf := x.is_pwo_support.union y.is_pwo_support
      rw [mul_coeff_left' hwf, add_coeff, mul_coeff_left' hwf (Set.subset_union_right _ _),
        mul_coeff_left' hwf (Set.subset_union_left _ _)]
      · simp only [add_coeff, add_mul, sum_add_distrib]
      · intro b
        simp only [add_coeff, Ne.def, Set.mem_union, Set.mem_setOf_eq, mem_support]
        contrapose!
        intro h
        rw [h.1, h.2, add_zero] }

theorem single_mul_coeff_add [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ}
    {b : Γ} : (single b r * x).coeff (a + b) = r * x.coeff a :=
  by
  by_cases hr : r = 0
  · simp [hr]
  simp only [hr, smul_coeff, mul_coeff, support_single_of_ne, Ne.def, not_false_iff, smul_eq_mul]
  by_cases hx : x.coeff a = 0
  · simp only [hx, MulZeroClass.mul_zero]
    rw [sum_congr _ fun _ _ => rfl, sum_empty]
    ext ⟨a1, a2⟩
    simp only [not_mem_empty, not_and, Set.mem_singleton_iff, Classical.not_not,
      mem_add_antidiagonal, Set.mem_setOf_eq, iff_false_iff]
    rintro rfl h2 h1
    rw [add_comm] at h1
    rw [← add_right_cancel h1] at hx
    exact h2 hx
  trans ∑ ij : Γ × Γ in {(b, a)}, (single b r).coeff ij.fst * x.coeff ij.snd
  · apply sum_congr _ fun _ _ => rfl
    ext ⟨a1, a2⟩
    simp only [Set.mem_singleton_iff, Prod.mk.inj_iff, mem_add_antidiagonal, mem_singleton,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨rfl, h2, h1⟩
      rw [add_comm] at h1
      refine' ⟨rfl, add_right_cancel h1⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, by simp [hx], add_comm _ _⟩
  · simp
#align hahn_series.single_mul_coeff_add HahnSeries.single_mul_coeff_add

theorem mul_single_coeff_add [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ}
    {b : Γ} : (x * single b r).coeff (a + b) = x.coeff a * r :=
  by
  by_cases hr : r = 0
  · simp [hr]
  simp only [hr, smul_coeff, mul_coeff, support_single_of_ne, Ne.def, not_false_iff, smul_eq_mul]
  by_cases hx : x.coeff a = 0
  · simp only [hx, MulZeroClass.zero_mul]
    rw [sum_congr _ fun _ _ => rfl, sum_empty]
    ext ⟨a1, a2⟩
    simp only [not_mem_empty, not_and, Set.mem_singleton_iff, Classical.not_not,
      mem_add_antidiagonal, Set.mem_setOf_eq, iff_false_iff]
    rintro h2 rfl h1
    rw [← add_right_cancel h1] at hx
    exact h2 hx
  trans ∑ ij : Γ × Γ in {(a, b)}, x.coeff ij.fst * (single b r).coeff ij.snd
  · apply sum_congr _ fun _ _ => rfl
    ext ⟨a1, a2⟩
    simp only [Set.mem_singleton_iff, Prod.mk.inj_iff, mem_add_antidiagonal, mem_singleton,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨h2, rfl, h1⟩
      refine' ⟨add_right_cancel h1, rfl⟩
    · rintro ⟨rfl, rfl⟩
      simp [hx]
  · simp
#align hahn_series.mul_single_coeff_add HahnSeries.mul_single_coeff_add

@[simp]
theorem mul_single_zero_coeff [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ} :
    (x * single 0 r).coeff a = x.coeff a * r := by rw [← add_zero a, mul_single_coeff_add, add_zero]
#align hahn_series.mul_single_zero_coeff HahnSeries.mul_single_zero_coeff

theorem single_zero_mul_coeff [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ} :
    (single 0 r * x).coeff a = r * x.coeff a := by rw [← add_zero a, single_mul_coeff_add, add_zero]
#align hahn_series.single_zero_mul_coeff HahnSeries.single_zero_mul_coeff

@[simp]
theorem single_zero_mul_eq_smul [Semiring R] {r : R} {x : HahnSeries Γ R} :
    single 0 r * x = r • x := by
  ext
  exact single_zero_mul_coeff
#align hahn_series.single_zero_mul_eq_smul HahnSeries.single_zero_mul_eq_smul

theorem support_mul_subset_add_support [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} :
    support (x * y) ⊆ support x + support y :=
  by
  apply Set.Subset.trans (fun x hx => _) support_add_antidiagonal_subset_add
  · exact x.is_pwo_support
  · exact y.is_pwo_support
  contrapose! hx
  simp only [not_nonempty_iff_eq_empty, Ne.def, Set.mem_setOf_eq] at hx
  simp [hx]
#align hahn_series.support_mul_subset_add_support HahnSeries.support_mul_subset_add_support

theorem mul_coeff_order_add_order {Γ} [LinearOrderedCancelAddCommMonoid Γ]
    [NonUnitalNonAssocSemiring R] (x y : HahnSeries Γ R) :
    (x * y).coeff (x.order + y.order) = x.coeff x.order * y.coeff y.order :=
  by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [order_of_ne hx, order_of_ne hy, mul_coeff, Finset.addAntidiagonal_min_add_min,
    Finset.sum_singleton]
#align hahn_series.mul_coeff_order_add_order HahnSeries.mul_coeff_order_add_order

private theorem mul_assoc' [NonUnitalSemiring R] (x y z : HahnSeries Γ R) :
    x * y * z = x * (y * z) := by
  ext b
  rw [mul_coeff_left' (x.is_pwo_support.add y.is_pwo_support) support_mul_subset_add_support,
    mul_coeff_right' (y.is_pwo_support.add z.is_pwo_support) support_mul_subset_add_support]
  simp only [mul_coeff, add_coeff, sum_mul, mul_sum, sum_sigma']
  refine' sum_bij_ne_zero (fun a has ha0 => ⟨⟨a.2.1, a.2.2 + a.1.2⟩, ⟨a.2.2, a.1.2⟩⟩) _ _ _ _
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ H1 H2
    simp only [and_true_iff, Set.image2_add, eq_self_iff_true, mem_add_antidiagonal, Ne.def,
      Set.image_prod, mem_sigma, Set.mem_setOf_eq] at H1 H2⊢
    obtain ⟨⟨H3, nz, rfl⟩, nx, ny, rfl⟩ := H1
    exact ⟨⟨nx, Set.add_mem_add ny nz, (add_assoc _ _ _).symm⟩, ny, nz⟩
  · rintro ⟨⟨i1, j1⟩, k1, l1⟩ ⟨⟨i2, j2⟩, k2, l2⟩ H1 H2 H3 H4 H5
    simp only [Set.image2_add, Prod.mk.inj_iff, mem_add_antidiagonal, Ne.def, Set.image_prod,
      mem_sigma, Set.mem_setOf_eq, heq_iff_eq] at H1 H3 H5
    obtain ⟨⟨rfl, H⟩, rfl, rfl⟩ := H5
    simp only [and_true_iff, Prod.mk.inj_iff, eq_self_iff_true, heq_iff_eq, ← H1.2.2.2, ← H3.2.2.2]
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ H1 H2
    simp only [exists_prop, Set.image2_add, Prod.mk.inj_iff, mem_add_antidiagonal, Sigma.exists,
      Ne.def, Set.image_prod, mem_sigma, Set.mem_setOf_eq, heq_iff_eq, Prod.exists] at H1 H2⊢
    obtain ⟨⟨nx, H, rfl⟩, ny, nz, rfl⟩ := H1
    exact
      ⟨i + k, l, i, k, ⟨⟨Set.add_mem_add nx ny, nz, add_assoc _ _ _⟩, nx, ny, rfl⟩, fun con =>
        H2 ((mul_assoc _ _ _).symm.trans Con), ⟨rfl, rfl⟩, rfl, rfl⟩
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ H1 H2
    simp [mul_assoc]
#align hahn_series.mul_assoc' hahn_series.mul_assoc'

instance [NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring (HahnSeries Γ R) :=
  { HahnSeries.addCommMonoid,
    HahnSeries.distrib with
    zero := 0
    add := (· + ·)
    mul := (· * ·)
    zero_mul := fun _ => by
      ext
      simp
    mul_zero := fun _ => by
      ext
      simp }

instance [NonUnitalSemiring R] : NonUnitalSemiring (HahnSeries Γ R) :=
  { HahnSeries.nonUnitalNonAssocSemiring with
    zero := 0
    add := (· + ·)
    mul := (· * ·)
    mul_assoc := mul_assoc' }

instance [NonAssocSemiring R] : NonAssocSemiring (HahnSeries Γ R) :=
  { AddMonoidWithOne.unary,
    HahnSeries.nonUnitalNonAssocSemiring with
    zero := 0
    one := 1
    add := (· + ·)
    mul := (· * ·)
    one_mul := fun x => by
      ext
      exact single_zero_mul_coeff.trans (one_mul _)
    mul_one := fun x => by
      ext
      exact mul_single_zero_coeff.trans (mul_one _) }

instance [Semiring R] : Semiring (HahnSeries Γ R) :=
  { HahnSeries.nonAssocSemiring,
    HahnSeries.nonUnitalSemiring with
    zero := 0
    one := 1
    add := (· + ·)
    mul := (· * ·) }

instance [NonUnitalCommSemiring R] : NonUnitalCommSemiring (HahnSeries Γ R) :=
  { HahnSeries.nonUnitalSemiring with
    mul_comm := fun x y => by
      ext
      simp_rw [mul_coeff, mul_comm]
      refine'
          sum_bij (fun a ha => a.symm) (fun a ha => _) (fun a ha => rfl)
            (fun _ _ _ _ => Prod.swap_inj.1) fun a ha => ⟨a.symm, _, a.swap_swap.symm⟩ <;>
        rwa [swap_mem_add_antidiagonal] }

instance [CommSemiring R] : CommSemiring (HahnSeries Γ R) :=
  { HahnSeries.nonUnitalCommSemiring, HahnSeries.semiring with }

instance [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing (HahnSeries Γ R) :=
  { HahnSeries.nonUnitalNonAssocSemiring, HahnSeries.addGroup with }

instance [NonUnitalRing R] : NonUnitalRing (HahnSeries Γ R) :=
  { HahnSeries.nonUnitalNonAssocRing, HahnSeries.nonUnitalSemiring with }

instance [NonAssocRing R] : NonAssocRing (HahnSeries Γ R) :=
  { HahnSeries.nonUnitalNonAssocRing, HahnSeries.nonAssocSemiring with }

instance [Ring R] : Ring (HahnSeries Γ R) :=
  { HahnSeries.semiring, HahnSeries.addCommGroup with }

instance [NonUnitalCommRing R] : NonUnitalCommRing (HahnSeries Γ R) :=
  { HahnSeries.nonUnitalCommSemiring, HahnSeries.nonUnitalRing with }

instance [CommRing R] : CommRing (HahnSeries Γ R) :=
  { HahnSeries.commSemiring, HahnSeries.ring with }

instance {Γ} [LinearOrderedCancelAddCommMonoid Γ] [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] :
    NoZeroDivisors (HahnSeries Γ R)
    where eq_zero_or_eq_zero_of_mul_eq_zero x y xy :=
    by
    by_cases hx : x = 0
    · left
      exact hx
    right
    contrapose! xy
    rw [HahnSeries.ext_iff, Function.funext_iff, not_forall]
    refine' ⟨x.order + y.order, _⟩
    rw [mul_coeff_order_add_order x y, zero_coeff, mul_eq_zero]
    simp [coeff_order_ne_zero, hx, xy]

instance {Γ} [LinearOrderedCancelAddCommMonoid Γ] [Ring R] [IsDomain R] :
    IsDomain (HahnSeries Γ R) :=
  NoZeroDivisors.to_isDomain _

@[simp]
theorem order_mul {Γ} [LinearOrderedCancelAddCommMonoid Γ] [NonUnitalNonAssocSemiring R]
    [NoZeroDivisors R] {x y : HahnSeries Γ R} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * y).order = x.order + y.order := by
  apply le_antisymm
  · apply order_le_of_coeff_ne_zero
    rw [mul_coeff_order_add_order x y]
    exact mul_ne_zero (coeff_order_ne_zero hx) (coeff_order_ne_zero hy)
  · rw [order_of_ne hx, order_of_ne hy, order_of_ne (mul_ne_zero hx hy), ← Set.IsWf.min_add]
    exact Set.IsWf.min_le_min_of_subset support_mul_subset_add_support
#align hahn_series.order_mul HahnSeries.order_mul

@[simp]
theorem order_pow {Γ} [LinearOrderedCancelAddCommMonoid Γ] [Semiring R] [NoZeroDivisors R]
    (x : HahnSeries Γ R) (n : ℕ) : (x ^ n).order = n • x.order :=
  by
  induction' n with h IH
  · simp
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  rw [pow_succ', order_mul (pow_ne_zero _ hx) hx, succ_nsmul', IH]
#align hahn_series.order_pow HahnSeries.order_pow

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring R]

@[simp]
theorem single_mul_single {a b : Γ} {r s : R} : single a r * single b s = single (a + b) (r * s) :=
  by
  ext x
  by_cases h : x = a + b
  · rw [h, mul_single_coeff_add]
    simp
  · rw [single_coeff_of_ne h, mul_coeff, sum_eq_zero]
    simp_rw [mem_add_antidiagonal]
    rintro ⟨y, z⟩ ⟨hy, hz, rfl⟩
    rw [eq_of_mem_support_single hy, eq_of_mem_support_single hz] at h
    exact (h rfl).elim
#align hahn_series.single_mul_single HahnSeries.single_mul_single

end NonUnitalNonAssocSemiring

section NonAssocSemiring

variable [NonAssocSemiring R]

/-- `C a` is the constant Hahn Series `a`. `C` is provided as a ring homomorphism. -/
@[simps]
def c : R →+* HahnSeries Γ R where
  toFun := single 0
  map_zero' := single_eq_zero
  map_one' := rfl
  map_add' x y := by
    ext a
    by_cases h : a = 0 <;> simp [h]
  map_mul' x y := by rw [single_mul_single, zero_add]
#align hahn_series.C HahnSeries.c

@[simp]
theorem c_zero : c (0 : R) = (0 : HahnSeries Γ R) :=
  c.map_zero
#align hahn_series.C_zero HahnSeries.c_zero

@[simp]
theorem c_one : c (1 : R) = (1 : HahnSeries Γ R) :=
  c.map_one
#align hahn_series.C_one HahnSeries.c_one

theorem c_injective : Function.Injective (c : R → HahnSeries Γ R) :=
  by
  intro r s rs
  rw [ext_iff, Function.funext_iff] at rs
  have h := rs 0
  rwa [C_apply, single_coeff_same, C_apply, single_coeff_same] at h
#align hahn_series.C_injective HahnSeries.c_injective

theorem c_ne_zero {r : R} (h : r ≠ 0) : (c r : HahnSeries Γ R) ≠ 0 :=
  by
  contrapose! h
  rw [← C_zero] at h
  exact C_injective h
#align hahn_series.C_ne_zero HahnSeries.c_ne_zero

theorem order_c {r : R} : order (c r : HahnSeries Γ R) = 0 :=
  by
  by_cases h : r = 0
  · rw [h, C_zero, order_zero]
  · exact order_single h
#align hahn_series.order_C HahnSeries.order_c

end NonAssocSemiring

section Semiring

variable [Semiring R]

theorem c_mul_eq_smul {r : R} {x : HahnSeries Γ R} : c r * x = r • x :=
  single_zero_mul_eq_smul
#align hahn_series.C_mul_eq_smul HahnSeries.c_mul_eq_smul

end Semiring

section Domain

variable {Γ' : Type _} [OrderedCancelAddCommMonoid Γ']

theorem embDomain_mul [NonUnitalNonAssocSemiring R] (f : Γ ↪o Γ')
    (hf : ∀ x y, f (x + y) = f x + f y) (x y : HahnSeries Γ R) :
    embDomain f (x * y) = embDomain f x * embDomain f y :=
  by
  ext g
  by_cases hg : g ∈ Set.range f
  · obtain ⟨g, rfl⟩ := hg
    simp only [mul_coeff, emb_domain_coeff]
    trans
      ∑ ij in
        (add_antidiagonal x.is_pwo_support y.is_pwo_support g).map
          (Function.Embedding.prodMap f.to_embedding f.to_embedding),
        (emb_domain f x).coeff ij.1 * (emb_domain f y).coeff ij.2
    · simp
    apply sum_subset
    · rintro ⟨i, j⟩ hij
      simp only [exists_prop, mem_map, Prod.mk.inj_iff, mem_add_antidiagonal,
        Function.Embedding.coe_prodMap, mem_support, Prod.exists] at hij
      obtain ⟨i, j, ⟨hx, hy, rfl⟩, rfl, rfl⟩ := hij
      simp [hx, hy, hf]
    · rintro ⟨_, _⟩ h1 h2
      contrapose! h2
      obtain ⟨i, hi, rfl⟩ := support_emb_domain_subset (ne_zero_and_ne_zero_of_mul h2).1
      obtain ⟨j, hj, rfl⟩ := support_emb_domain_subset (ne_zero_and_ne_zero_of_mul h2).2
      simp only [exists_prop, mem_map, Prod.mk.inj_iff, mem_add_antidiagonal,
        Function.Embedding.coe_prodMap, mem_support, Prod.exists]
      simp only [mem_add_antidiagonal, emb_domain_coeff, mem_support, ← hf,
        OrderEmbedding.eq_iff_eq] at h1
      exact ⟨i, j, h1, rfl⟩
  · rw [emb_domain_notin_range hg, eq_comm]
    contrapose! hg
    obtain ⟨_, _, hi, hj, rfl⟩ := support_mul_subset_add_support ((mem_support _ _).2 hg)
    obtain ⟨i, hi, rfl⟩ := support_emb_domain_subset hi
    obtain ⟨j, hj, rfl⟩ := support_emb_domain_subset hj
    refine' ⟨i + j, hf i j⟩
#align hahn_series.emb_domain_mul HahnSeries.embDomain_mul

theorem embDomain_one [NonAssocSemiring R] (f : Γ ↪o Γ') (hf : f 0 = 0) :
    embDomain f (1 : HahnSeries Γ R) = (1 : HahnSeries Γ' R) :=
  embDomain_single.trans <| hf.symm ▸ rfl
#align hahn_series.emb_domain_one HahnSeries.embDomain_one

/-- Extending the domain of Hahn series is a ring homomorphism. -/
@[simps]
def embDomainRingHom [NonAssocSemiring R] (f : Γ →+ Γ') (hfi : Function.Injective f)
    (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') : HahnSeries Γ R →+* HahnSeries Γ' R
    where
  toFun := embDomain ⟨⟨f, hfi⟩, hf⟩
  map_one' := embDomain_one _ f.map_zero
  map_mul' := embDomain_mul _ f.map_add
  map_zero' := embDomain_zero
  map_add' := embDomain_add _
#align hahn_series.emb_domain_ring_hom HahnSeries.embDomainRingHom

theorem embDomainRingHom_c [NonAssocSemiring R] {f : Γ →+ Γ'} {hfi : Function.Injective f}
    {hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g'} {r : R} : embDomainRingHom f hfi hf (c r) = c r :=
  embDomain_single.trans (by simp)
#align hahn_series.emb_domain_ring_hom_C HahnSeries.embDomainRingHom_c

end Domain

section Algebra

variable [CommSemiring R] {A : Type _} [Semiring A] [Algebra R A]

instance : Algebra R (HahnSeries Γ A)
    where
  toRingHom := c.comp (algebraMap R A)
  smul_def' r x := by
    ext
    simp
  commutes' r x := by
    ext
    simp only [smul_coeff, single_zero_mul_eq_smul, RingHom.coe_comp, RingHom.toFun_eq_coe, C_apply,
      Function.comp_apply, algebraMap_smul, mul_single_zero_coeff]
    rw [← Algebra.commutes, Algebra.smul_def]

theorem c_eq_algebraMap : c = algebraMap R (HahnSeries Γ R) :=
  rfl
#align hahn_series.C_eq_algebra_map HahnSeries.c_eq_algebraMap

theorem algebraMap_apply {r : R} : algebraMap R (HahnSeries Γ A) r = c (algebraMap R A r) :=
  rfl
#align hahn_series.algebra_map_apply HahnSeries.algebraMap_apply

instance [Nontrivial Γ] [Nontrivial R] : Nontrivial (Subalgebra R (HahnSeries Γ R)) :=
  ⟨⟨⊥, ⊤, by
      rw [Ne.def, SetLike.ext_iff, not_forall]
      obtain ⟨a, ha⟩ := exists_ne (0 : Γ)
      refine' ⟨single a 1, _⟩
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true_iff, Algebra.mem_top]
      intro x
      rw [ext_iff, Function.funext_iff, not_forall]
      refine' ⟨a, _⟩
      rw [single_coeff_same, algebraMap_apply, C_apply, single_coeff_of_ne ha]
      exact zero_ne_one⟩⟩

section Domain

variable {Γ' : Type _} [OrderedCancelAddCommMonoid Γ']

/-- Extending the domain of Hahn series is an algebra homomorphism. -/
@[simps]
def embDomainAlgHom (f : Γ →+ Γ') (hfi : Function.Injective f)
    (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') : HahnSeries Γ A →ₐ[R] HahnSeries Γ' A :=
  { embDomainRingHom f hfi hf with commutes' := fun r => embDomainRingHom_c }
#align hahn_series.emb_domain_alg_hom HahnSeries.embDomainAlgHom

end Domain

end Algebra

end Multiplication

section Semiring

variable [Semiring R]

/-- The ring `hahn_series ℕ R` is isomorphic to `power_series R`. -/
@[simps]
def toPowerSeries : HahnSeries ℕ R ≃+* PowerSeries R
    where
  toFun f := PowerSeries.mk f.coeff
  invFun f := ⟨fun n => PowerSeries.coeff R n f, (Nat.lt_wfRel.IsWf _).IsPwo⟩
  left_inv f := by
    ext
    simp
  right_inv f := by
    ext
    simp
  map_add' f g := by
    ext
    simp
  map_mul' f g := by
    ext n
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, mul_coeff, is_pwo_support]
    classical
      refine' sum_filter_ne_zero.symm.trans ((sum_congr _ fun _ _ => rfl).trans sum_filter_ne_zero)
      ext m
      simp only [nat.mem_antidiagonal, mem_add_antidiagonal, and_congr_left_iff, mem_filter,
        mem_support]
      rintro h
      rw [and_iff_right (left_ne_zero_of_mul h), and_iff_right (right_ne_zero_of_mul h)]
#align hahn_series.to_power_series HahnSeries.toPowerSeries

theorem coeff_toPowerSeries {f : HahnSeries ℕ R} {n : ℕ} :
    PowerSeries.coeff R n f.toPowerSeries = f.coeff n :=
  PowerSeries.coeff_mk _ _
#align hahn_series.coeff_to_power_series HahnSeries.coeff_toPowerSeries

theorem coeff_toPowerSeries_symm {f : PowerSeries R} {n : ℕ} :
    (HahnSeries.toPowerSeries.symm f).coeff n = PowerSeries.coeff R n f :=
  rfl
#align hahn_series.coeff_to_power_series_symm HahnSeries.coeff_toPowerSeries_symm

variable (Γ R) [StrictOrderedSemiring Γ]

/-- Casts a power series as a Hahn series with coefficients from an `strict_ordered_semiring`. -/
def ofPowerSeries : PowerSeries R →+* HahnSeries Γ R :=
  (HahnSeries.embDomainRingHom (Nat.castAddMonoidHom Γ) Nat.strictMono_cast.Injective fun _ _ =>
        Nat.cast_le).comp
    (RingEquiv.toRingHom toPowerSeries.symm)
#align hahn_series.of_power_series HahnSeries.ofPowerSeries

variable {Γ} {R}

theorem ofPowerSeries_injective : Function.Injective (ofPowerSeries Γ R) :=
  embDomain_injective.comp toPowerSeries.symm.Injective
#align hahn_series.of_power_series_injective HahnSeries.ofPowerSeries_injective

@[simp]
theorem ofPowerSeries_apply (x : PowerSeries R) :
    ofPowerSeries Γ R x =
      HahnSeries.embDomain
        ⟨⟨(coe : ℕ → Γ), Nat.strictMono_cast.Injective⟩, fun a b =>
          by
          simp only [Function.Embedding.coeFn_mk]
          exact Nat.cast_le⟩
        (toPowerSeries.symm x) :=
  rfl
#align hahn_series.of_power_series_apply HahnSeries.ofPowerSeries_apply

theorem ofPowerSeries_apply_coeff (x : PowerSeries R) (n : ℕ) :
    (ofPowerSeries Γ R x).coeff n = PowerSeries.coeff R n x := by simp
#align hahn_series.of_power_series_apply_coeff HahnSeries.ofPowerSeries_apply_coeff

@[simp]
theorem ofPowerSeries_c (r : R) : ofPowerSeries Γ R (PowerSeries.C R r) = HahnSeries.c r :=
  by
  ext n
  simp only [C, single_coeff, of_power_series_apply, RingHom.coe_mk]
  split_ifs with hn hn
  · subst hn
    convert@emb_domain_coeff _ _ _ _ _ _ _ _ 0 <;> simp
  · rw [emb_domain_notin_image_support]
    simp only [not_exists, Set.mem_image, to_power_series_symm_apply_coeff, mem_support,
      PowerSeries.coeff_C]
    intro
    simp (config := { contextual := true }) [Ne.symm hn]
#align hahn_series.of_power_series_C HahnSeries.ofPowerSeries_c

@[simp]
theorem ofPowerSeries_x : ofPowerSeries Γ R PowerSeries.X = single 1 1 :=
  by
  ext n
  simp only [single_coeff, of_power_series_apply, RingHom.coe_mk]
  split_ifs with hn hn
  · rw [hn]
    convert@emb_domain_coeff _ _ _ _ _ _ _ _ 1 <;> simp
  · rw [emb_domain_notin_image_support]
    simp only [not_exists, Set.mem_image, to_power_series_symm_apply_coeff, mem_support,
      PowerSeries.coeff_X]
    intro
    simp (config := { contextual := true }) [Ne.symm hn]
#align hahn_series.of_power_series_X HahnSeries.ofPowerSeries_x

@[simp]
theorem ofPowerSeries_x_pow {R} [CommSemiring R] (n : ℕ) :
    ofPowerSeries Γ R (PowerSeries.X ^ n) = single (n : Γ) 1 :=
  by
  rw [RingHom.map_pow]
  induction' n with n ih
  · simp
    rfl
  rw [pow_succ, ih, of_power_series_X, mul_comm, single_mul_single, one_mul, Nat.cast_succ]
#align hahn_series.of_power_series_X_pow HahnSeries.ofPowerSeries_x_pow

-- Lemmas about converting hahn_series over fintype to and from mv_power_series
/-- The ring `hahn_series (σ →₀ ℕ) R` is isomorphic to `mv_power_series σ R` for a `fintype` `σ`.
We take the index set of the hahn series to be `finsupp` rather than `pi`,
even though we assume `fintype σ` as this is more natural for alignment with `mv_power_series`.
After importing `algebra.order.pi` the ring `hahn_series (σ → ℕ) R` could be constructed instead.
 -/
@[simps]
def toMvPowerSeries {σ : Type _} [Fintype σ] : HahnSeries (σ →₀ ℕ) R ≃+* MvPowerSeries σ R
    where
  toFun f := f.coeff
  invFun f := ⟨(f : (σ →₀ ℕ) → R), Finsupp.isPwo _⟩
  left_inv f := by
    ext
    simp
  right_inv f := by
    ext
    simp
  map_add' f g := by
    ext
    simp
  map_mul' f g := by
    ext n
    simp only [MvPowerSeries.coeff_mul]
    classical
      change (f * g).coeff n = _
      simp_rw [mul_coeff]
      refine' sum_filter_ne_zero.symm.trans ((sum_congr _ fun _ _ => rfl).trans sum_filter_ne_zero)
      ext m
      simp only [and_congr_left_iff, mem_add_antidiagonal, mem_filter, mem_support,
        Finsupp.mem_antidiagonal]
      rintro h
      rw [and_iff_right (left_ne_zero_of_mul h), and_iff_right (right_ne_zero_of_mul h)]
#align hahn_series.to_mv_power_series HahnSeries.toMvPowerSeries

variable {σ : Type _} [Fintype σ]

theorem coeff_toMvPowerSeries {f : HahnSeries (σ →₀ ℕ) R} {n : σ →₀ ℕ} :
    MvPowerSeries.coeff R n f.toMvPowerSeries = f.coeff n :=
  rfl
#align hahn_series.coeff_to_mv_power_series HahnSeries.coeff_toMvPowerSeries

theorem coeff_toMvPowerSeries_symm {f : MvPowerSeries σ R} {n : σ →₀ ℕ} :
    (HahnSeries.toMvPowerSeries.symm f).coeff n = MvPowerSeries.coeff R n f :=
  rfl
#align hahn_series.coeff_to_mv_power_series_symm HahnSeries.coeff_toMvPowerSeries_symm

end Semiring

section Algebra

variable (R) [CommSemiring R] {A : Type _} [Semiring A] [Algebra R A]

/-- The `R`-algebra `hahn_series ℕ A` is isomorphic to `power_series A`. -/
@[simps]
def toPowerSeriesAlg : HahnSeries ℕ A ≃ₐ[R] PowerSeries A :=
  { toPowerSeries with
    commutes' := fun r => by
      ext n
      simp only [algebraMap_apply, PowerSeries.algebraMap_apply, [anonymous], C_apply,
        coeff_to_power_series]
      cases n
      · simp only [PowerSeries.coeff_zero_eq_constantCoeff, single_coeff_same]
        rfl
      · simp only [n.succ_ne_zero, Ne.def, not_false_iff, single_coeff_of_ne]
        rw [PowerSeries.coeff_C, if_neg n.succ_ne_zero] }
#align hahn_series.to_power_series_alg HahnSeries.toPowerSeriesAlg

variable (Γ R) [StrictOrderedSemiring Γ]

/-- Casting a power series as a Hahn series with coefficients from an `strict_ordered_semiring`
  is an algebra homomorphism. -/
@[simps]
def ofPowerSeriesAlg : PowerSeries A →ₐ[R] HahnSeries Γ A :=
  (HahnSeries.embDomainAlgHom (Nat.castAddMonoidHom Γ) Nat.strictMono_cast.Injective fun _ _ =>
        Nat.cast_le).comp
    (AlgEquiv.toAlgHom (toPowerSeriesAlg R).symm)
#align hahn_series.of_power_series_alg HahnSeries.ofPowerSeriesAlg

instance powerSeriesAlgebra {S : Type _} [CommSemiring S] [Algebra S (PowerSeries R)] :
    Algebra S (HahnSeries Γ R) :=
  RingHom.toAlgebra <| (ofPowerSeries Γ R).comp (algebraMap S (PowerSeries R))
#align hahn_series.power_series_algebra HahnSeries.powerSeriesAlgebra

variable {R} {S : Type _} [CommSemiring S] [Algebra S (PowerSeries R)]

theorem algebraMap_apply' (x : S) :
    algebraMap S (HahnSeries Γ R) x = ofPowerSeries Γ R (algebraMap S (PowerSeries R) x) :=
  rfl
#align hahn_series.algebra_map_apply' HahnSeries.algebraMap_apply'

@[simp]
theorem Polynomial.algebraMap_hahnSeries_apply (f : R[X]) :
    algebraMap R[X] (HahnSeries Γ R) f = ofPowerSeries Γ R f :=
  rfl
#align polynomial.algebra_map_hahn_series_apply Polynomial.algebraMap_hahnSeries_apply

theorem Polynomial.algebraMap_hahnSeries_injective :
    Function.Injective (algebraMap R[X] (HahnSeries Γ R)) :=
  ofPowerSeries_injective.comp (Polynomial.coe_injective R)
#align polynomial.algebra_map_hahn_series_injective Polynomial.algebraMap_hahnSeries_injective

end Algebra

section Valuation

variable (Γ R) [LinearOrderedCancelAddCommMonoid Γ] [Ring R] [IsDomain R]

/-- The additive valuation on `hahn_series Γ R`, returning the smallest index at which
  a Hahn Series has a nonzero coefficient, or `⊤` for the 0 series.  -/
def addVal : AddValuation (HahnSeries Γ R) (WithTop Γ) :=
  AddValuation.of (fun x => if x = (0 : HahnSeries Γ R) then (⊤ : WithTop Γ) else x.order)
    (if_pos rfl) ((if_neg one_ne_zero).trans (by simp [order_of_ne]))
    (fun x y => by
      by_cases hx : x = 0
      · by_cases hy : y = 0 <;> · simp [hx, hy]
      · by_cases hy : y = 0
        · simp [hx, hy]
        · simp only [hx, hy, support_nonempty_iff, if_neg, not_false_iff, is_wf_support]
          by_cases hxy : x + y = 0
          · simp [hxy]
          rw [if_neg hxy, ← WithTop.coe_min, WithTop.coe_le_coe]
          exact min_order_le_order_add hxy)
    fun x y => by
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
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
    addVal Γ R x ≤ g :=
  by
  rw [add_val_apply_of_ne (ne_zero_of_coeff_ne_zero h), WithTop.coe_le_coe]
  exact order_le_of_coeff_ne_zero h
#align hahn_series.add_val_le_of_coeff_ne_zero HahnSeries.addVal_le_of_coeff_ne_zero

end Valuation

theorem isPwo_iUnion_support_powers [LinearOrderedCancelAddCommMonoid Γ] [Ring R] [IsDomain R]
    {x : HahnSeries Γ R} (hx : 0 < addVal Γ R x) : (⋃ n : ℕ, (x ^ n).support).IsPwo :=
  by
  apply (x.is_wf_support.is_pwo.add_submonoid_closure fun g hg => _).mono _
  · exact WithTop.coe_le_coe.1 (le_trans (le_of_lt hx) (add_val_le_of_coeff_ne_zero hg))
  refine' Set.iUnion_subset fun n => _
  induction' n with n ih <;> intro g hn
  · simp only [exists_prop, and_true_iff, Set.mem_singleton_iff, Set.setOf_eq_eq_singleton,
      mem_support, ite_eq_right_iff, Ne.def, not_false_iff, one_ne_zero, pow_zero, not_forall,
      one_coeff] at hn
    rw [hn, SetLike.mem_coe]
    exact AddSubmonoid.zero_mem _
  · obtain ⟨i, j, hi, hj, rfl⟩ := support_mul_subset_add_support hn
    exact SetLike.mem_coe.2 (AddSubmonoid.add_mem _ (AddSubmonoid.subset_closure hi) (ih hj))
#align hahn_series.is_pwo_Union_support_powers HahnSeries.isPwo_iUnion_support_powers

section

variable (Γ) (R) [PartialOrder Γ] [AddCommMonoid R]

/-- An infinite family of Hahn series which has a formal coefficient-wise sum.
  The requirements for this are that the union of the supports of the series is well-founded,
  and that only finitely many series are nonzero at any given coefficient. -/
structure SummableFamily (α : Type _) where
  toFun : α → HahnSeries Γ R
  isPwo_iUnion_support' : Set.IsPwo (⋃ a : α, (to_fun a).support)
  finite_co_support' : ∀ g : Γ, { a | (to_fun a).coeff g ≠ 0 }.Finite
#align hahn_series.summable_family HahnSeries.SummableFamily

end

namespace SummableFamily

section AddCommMonoid

variable [PartialOrder Γ] [AddCommMonoid R] {α : Type _}

instance : CoeFun (SummableFamily Γ R α) fun _ => α → HahnSeries Γ R :=
  ⟨toFun⟩

theorem isPwo_iUnion_support (s : SummableFamily Γ R α) : Set.IsPwo (⋃ a : α, (s a).support) :=
  s.isPwo_iUnion_support'
#align hahn_series.summable_family.is_pwo_Union_support HahnSeries.SummableFamily.isPwo_iUnion_support

theorem finite_co_support (s : SummableFamily Γ R α) (g : Γ) :
    (Function.support fun a => (s a).coeff g).Finite :=
  s.finite_co_support' g
#align hahn_series.summable_family.finite_co_support HahnSeries.SummableFamily.finite_co_support

theorem coe_injective : @Function.Injective (SummableFamily Γ R α) (α → HahnSeries Γ R) coeFn
  | ⟨f1, hU1, hf1⟩, ⟨f2, hU2, hf2⟩, h => by
    change f1 = f2 at h
    subst h
#align hahn_series.summable_family.coe_injective HahnSeries.SummableFamily.coe_injective

@[ext]
theorem ext {s t : SummableFamily Γ R α} (h : ∀ a : α, s a = t a) : s = t :=
  coe_injective <| funext h
#align hahn_series.summable_family.ext HahnSeries.SummableFamily.ext

instance : Add (SummableFamily Γ R α) :=
  ⟨fun x y =>
    { toFun := x + y
      isPwo_iUnion_support' :=
        (x.isPwo_iUnion_support.union y.isPwo_iUnion_support).mono
          (by
            rw [← Set.iUnion_union_distrib]
            exact Set.iUnion_mono fun a => support_add_subset)
      finite_co_support' := fun g =>
        ((x.finite_co_support g).union (y.finite_co_support g)).Subset
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

instance : AddCommMonoid (SummableFamily Γ R α)
    where
  add := (· + ·)
  zero := 0
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

/-- The infinite sum of a `summable_family` of Hahn series. -/
def hsum (s : SummableFamily Γ R α) : HahnSeries Γ R
    where
  coeff g := ∑ᶠ i, (s i).coeff g
  isPwo_support' :=
    s.isPwo_iUnion_support.mono fun g => by
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
  fun g hg =>
  by
  rw [mem_support, hsum_coeff, finsum_eq_sum _ (s.finite_co_support _)] at hg
  obtain ⟨a, h1, h2⟩ := exists_ne_zero_of_sum_ne_zero hg
  rw [Set.mem_iUnion]
  exact ⟨a, h2⟩
#align hahn_series.summable_family.support_hsum_subset HahnSeries.SummableFamily.support_hsum_subset

@[simp]
theorem hsum_add {s t : SummableFamily Γ R α} : (s + t).hsum = s.hsum + t.hsum :=
  by
  ext g
  simp only [hsum_coeff, add_coeff, add_apply]
  exact finsum_add_distrib (s.finite_co_support _) (t.finite_co_support _)
#align hahn_series.summable_family.hsum_add HahnSeries.SummableFamily.hsum_add

end AddCommMonoid

section AddCommGroup

variable [PartialOrder Γ] [AddCommGroup R] {α : Type _} {s t : SummableFamily Γ R α} {a : α}

instance : AddCommGroup (SummableFamily Γ R α) :=
  {
    SummableFamily.addCommMonoid with
    neg := fun s =>
      { toFun := fun a => -s a
        isPwo_iUnion_support' := by
          simp_rw [support_neg]
          exact s.is_pwo_Union_support'
        finite_co_support' := fun g =>
          by
          simp only [neg_coeff', Pi.neg_apply, Ne.def, neg_eq_zero]
          exact s.finite_co_support g }
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

variable [OrderedCancelAddCommMonoid Γ] [Semiring R] {α : Type _}

instance : SMul (HahnSeries Γ R) (SummableFamily Γ R α)
    where smul x s :=
    { toFun := fun a => x * s a
      isPwo_iUnion_support' :=
        by
        apply (x.is_pwo_support.add s.is_pwo_Union_support).mono
        refine' Set.Subset.trans (Set.iUnion_mono fun a => support_mul_subset_add_support) _
        intro g
        simp only [Set.mem_iUnion, exists_imp]
        exact fun a ha => (Set.add_subset_add (Set.Subset.refl _) (Set.subset_iUnion _ a)) ha
      finite_co_support' := fun g =>
        by
        refine'
          ((add_antidiagonal x.is_pwo_support s.is_pwo_Union_support g).finite_toSet.biUnion'
                fun ij hij => _).Subset
            fun a ha => _
        · exact fun ij hij => Function.support fun a => (s a).coeff ij.2
        · apply s.finite_co_support
        · obtain ⟨i, j, hi, hj, rfl⟩ := support_mul_subset_add_support ha
          simp only [exists_prop, Set.mem_iUnion, mem_add_antidiagonal, mul_coeff, mem_support,
            is_pwo_support, Prod.exists]
          exact ⟨i, j, mem_coe.2 (mem_add_antidiagonal.2 ⟨hi, Set.mem_iUnion.2 ⟨a, hj⟩, rfl⟩), hj⟩ }

@[simp]
theorem smul_apply {x : HahnSeries Γ R} {s : SummableFamily Γ R α} {a : α} : (x • s) a = x * s a :=
  rfl
#align hahn_series.summable_family.smul_apply HahnSeries.SummableFamily.smul_apply

instance : Module (HahnSeries Γ R) (SummableFamily Γ R α)
    where
  smul := (· • ·)
  smul_zero x := ext fun a => MulZeroClass.mul_zero _
  zero_smul x := ext fun a => MulZeroClass.zero_mul _
  one_smul x := ext fun a => one_mul _
  add_smul x y s := ext fun a => add_mul _ _ _
  smul_add x s t := ext fun a => mul_add _ _ _
  mul_smul x y s := ext fun a => mul_assoc _ _ _

@[simp]
theorem hsum_smul {x : HahnSeries Γ R} {s : SummableFamily Γ R α} : (x • s).hsum = x * s.hsum :=
  by
  ext g
  simp only [mul_coeff, hsum_coeff, smul_apply]
  have h : ∀ i, (s i).support ⊆ ⋃ j, (s j).support := Set.subset_iUnion _
  refine'
    (Eq.trans (finsum_congr fun a => _)
          (finsum_sum_comm (add_antidiagonal x.is_pwo_support s.is_pwo_Union_support g)
            (fun i ij => x.coeff (Prod.fst ij) * (s i).coeff ij.snd) _)).trans
      _
  · refine' sum_subset (add_antidiagonal_mono_right (Set.subset_iUnion _ a)) _
    rintro ⟨i, j⟩ hU ha
    rw [mem_add_antidiagonal] at *
    rw [Classical.not_not.1 fun con => ha ⟨hU.1, Con, hU.2.2⟩, MulZeroClass.mul_zero]
  · rintro ⟨i, j⟩ hij
    refine' (s.finite_co_support j).Subset _
    simp_rw [Function.support_subset_iff', Function.mem_support, Classical.not_not]
    intro a ha
    rw [ha, MulZeroClass.mul_zero]
  · refine' (sum_congr rfl _).trans (sum_subset (add_antidiagonal_mono_right _) _).symm
    · rintro ⟨i, j⟩ hij
      rw [mul_finsum]
      apply s.finite_co_support
    · intro x hx
      simp only [Set.mem_iUnion, Ne.def, mem_support]
      contrapose! hx
      simp [hx]
    · rintro ⟨i, j⟩ hU ha
      rw [mem_add_antidiagonal] at *
      rw [← hsum_coeff, Classical.not_not.1 fun con => ha ⟨hU.1, Con, hU.2.2⟩,
        MulZeroClass.mul_zero]
#align hahn_series.summable_family.hsum_smul HahnSeries.SummableFamily.hsum_smul

/-- The summation of a `summable_family` as a `linear_map`. -/
@[simps]
def lsum : SummableFamily Γ R α →ₗ[HahnSeries Γ R] HahnSeries Γ R
    where
  toFun := hsum
  map_add' _ _ := hsum_add
  map_smul' _ _ := hsum_smul
#align hahn_series.summable_family.lsum HahnSeries.SummableFamily.lsum

@[simp]
theorem hsum_sub {R : Type _} [Ring R] {s t : SummableFamily Γ R α} :
    (s - t).hsum = s.hsum - t.hsum := by
  rw [← lsum_apply, LinearMap.map_sub, lsum_apply, lsum_apply]
#align hahn_series.summable_family.hsum_sub HahnSeries.SummableFamily.hsum_sub

end Semiring

section OfFinsupp

variable [PartialOrder Γ] [AddCommMonoid R] {α : Type _}

/-- A family with only finitely many nonzero elements is summable. -/
def ofFinsupp (f : α →₀ HahnSeries Γ R) : SummableFamily Γ R α
    where
  toFun := f
  isPwo_iUnion_support' :=
    by
    apply (f.support.is_pwo_bUnion.2 fun a ha => (f a).isPwo_support).mono
    refine' Set.iUnion_subset_iff.2 fun a g hg => _
    have haf : a ∈ f.support :=
      by
      rw [Finsupp.mem_support_iff, ← support_nonempty_iff]
      exact ⟨g, hg⟩
    exact Set.mem_biUnion haf hg
  finite_co_support' g :=
    by
    refine' f.support.finite_to_set.subset fun a ha => _
    simp only [coeff.add_monoid_hom_apply, mem_coe, Finsupp.mem_support_iff, Ne.def,
      Function.mem_support]
    contrapose! ha
    simp [ha]
#align hahn_series.summable_family.of_finsupp HahnSeries.SummableFamily.ofFinsupp

@[simp]
theorem coe_ofFinsupp {f : α →₀ HahnSeries Γ R} : ⇑(SummableFamily.ofFinsupp f) = f :=
  rfl
#align hahn_series.summable_family.coe_of_finsupp HahnSeries.SummableFamily.coe_ofFinsupp

@[simp]
theorem hsum_ofFinsupp {f : α →₀ HahnSeries Γ R} : (ofFinsupp f).hsum = f.Sum fun a => id :=
  by
  ext g
  simp only [hsum_coeff, coe_of_finsupp, Finsupp.sum, Ne.def]
  simp_rw [← coeff.add_monoid_hom_apply, id.def]
  rw [AddMonoidHom.map_sum, finsum_eq_sum_of_support_subset]
  intro x h
  simp only [coeff.add_monoid_hom_apply, mem_coe, Finsupp.mem_support_iff, Ne.def]
  contrapose! h
  simp [h]
#align hahn_series.summable_family.hsum_of_finsupp HahnSeries.SummableFamily.hsum_ofFinsupp

end OfFinsupp

section EmbDomain

variable [PartialOrder Γ] [AddCommMonoid R] {α β : Type _}

/-- A summable family can be reindexed by an embedding without changing its sum. -/
def embDomain (s : SummableFamily Γ R α) (f : α ↪ β) : SummableFamily Γ R β
    where
  toFun b := if h : b ∈ Set.range f then s (Classical.choose h) else 0
  isPwo_iUnion_support' :=
    by
    refine' s.is_pwo_Union_support.mono (Set.iUnion_subset fun b g h => _)
    by_cases hb : b ∈ Set.range f
    · rw [dif_pos hb] at h
      exact Set.mem_iUnion.2 ⟨Classical.choose hb, h⟩
    · contrapose! h
      simp [hb]
  finite_co_support' g :=
    ((s.finite_co_support g).image f).Subset
      (by
        intro b h
        by_cases hb : b ∈ Set.range f
        · simp only [Ne.def, Set.mem_setOf_eq, dif_pos hb] at h
          exact ⟨Classical.choose hb, h, Classical.choose_spec hb⟩
        · contrapose! h
          simp only [Ne.def, Set.mem_setOf_eq, dif_neg hb, Classical.not_not, zero_coeff])
#align hahn_series.summable_family.emb_domain HahnSeries.SummableFamily.embDomain

variable (s : SummableFamily Γ R α) (f : α ↪ β) {a : α} {b : β}

theorem embDomain_apply :
    s.embDomain f b = if h : b ∈ Set.range f then s (Classical.choose h) else 0 :=
  rfl
#align hahn_series.summable_family.emb_domain_apply HahnSeries.SummableFamily.embDomain_apply

@[simp]
theorem embDomain_image : s.embDomain f (f a) = s a :=
  by
  rw [emb_domain_apply, dif_pos (Set.mem_range_self a)]
  exact congr rfl (f.injective (Classical.choose_spec (Set.mem_range_self a)))
#align hahn_series.summable_family.emb_domain_image HahnSeries.SummableFamily.embDomain_image

@[simp]
theorem embDomain_notin_range (h : b ∉ Set.range f) : s.embDomain f b = 0 := by
  rw [emb_domain_apply, dif_neg h]
#align hahn_series.summable_family.emb_domain_notin_range HahnSeries.SummableFamily.embDomain_notin_range

@[simp]
theorem hsum_embDomain : (s.embDomain f).hsum = s.hsum :=
  by
  ext g
  simp only [hsum_coeff, emb_domain_apply, apply_dite HahnSeries.coeff, dite_apply, zero_coeff]
  exact finsum_emb_domain f fun a => (s a).coeff g
#align hahn_series.summable_family.hsum_emb_domain HahnSeries.SummableFamily.hsum_embDomain

end EmbDomain

section powers

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R] [IsDomain R]

/-- The powers of an element of positive valuation form a summable family. -/
def powers (x : HahnSeries Γ R) (hx : 0 < addVal Γ R x) : SummableFamily Γ R ℕ
    where
  toFun n := x ^ n
  isPwo_iUnion_support' := isPwo_iUnion_support_powers hx
  finite_co_support' g := by
    have hpwo := is_pwo_Union_support_powers hx
    by_cases hg : g ∈ ⋃ n : ℕ, { g | (x ^ n).coeff g ≠ 0 }
    swap; · exact set.finite_empty.subset fun n hn => hg (Set.mem_iUnion.2 ⟨n, hn⟩)
    apply hpwo.is_wf.induction hg
    intro y ys hy
    refine'
      ((((add_antidiagonal x.is_pwo_support hpwo y).finite_toSet.biUnion fun ij hij =>
                    hy ij.snd _ _).image
                Nat.succ).union
            (Set.finite_singleton 0)).Subset
        _
    · exact (mem_add_antidiagonal.1 (mem_coe.1 hij)).2.1
    · obtain ⟨hi, hj, rfl⟩ := mem_add_antidiagonal.1 (mem_coe.1 hij)
      rw [← zero_add ij.snd, ← add_assoc, add_zero]
      exact
        add_lt_add_right (WithTop.coe_lt_coe.1 (lt_of_lt_of_le hx (add_val_le_of_coeff_ne_zero hi)))
          _
    · rintro (_ | n) hn
      · exact Set.mem_union_right _ (Set.mem_singleton 0)
      · obtain ⟨i, j, hi, hj, rfl⟩ := support_mul_subset_add_support hn
        refine' Set.mem_union_left _ ⟨n, Set.mem_iUnion.2 ⟨⟨i, j⟩, Set.mem_iUnion.2 ⟨_, hj⟩⟩, rfl⟩
        simp only [and_true_iff, Set.mem_iUnion, mem_add_antidiagonal, mem_coe, eq_self_iff_true,
          Ne.def, mem_support, Set.mem_setOf_eq]
        exact ⟨hi, n, hj⟩
#align hahn_series.summable_family.powers HahnSeries.SummableFamily.powers

variable {x : HahnSeries Γ R} (hx : 0 < addVal Γ R x)

@[simp]
theorem coe_powers : ⇑(powers x hx) = pow x :=
  rfl
#align hahn_series.summable_family.coe_powers HahnSeries.SummableFamily.coe_powers

theorem embDomain_succ_smul_powers :
    (x • powers x hx).embDomain ⟨Nat.succ, Nat.succ_injective⟩ =
      powers x hx - ofFinsupp (Finsupp.single 0 1) :=
  by
  apply summable_family.ext fun n => _
  cases n
  · rw [emb_domain_notin_range, sub_apply, coe_powers, pow_zero, coe_of_finsupp,
      Finsupp.single_eq_same, sub_self]
    rw [Set.mem_range, not_exists]
    exact Nat.succ_ne_zero
  · refine' Eq.trans (emb_domain_image _ ⟨Nat.succ, Nat.succ_injective⟩) _
    simp only [pow_succ, coe_powers, coe_sub, smul_apply, coe_of_finsupp, Pi.sub_apply]
    rw [Finsupp.single_eq_of_ne n.succ_ne_zero.symm, sub_zero]
#align hahn_series.summable_family.emb_domain_succ_smul_powers HahnSeries.SummableFamily.embDomain_succ_smul_powers

theorem one_sub_self_mul_hsum_powers : (1 - x) * (powers x hx).hsum = 1 :=
  by
  rw [← hsum_smul, sub_smul, one_smul, hsum_sub, ←
    hsum_emb_domain (x • powers x hx) ⟨Nat.succ, Nat.succ_injective⟩, emb_domain_succ_smul_powers]
  simp
#align hahn_series.summable_family.one_sub_self_mul_hsum_powers HahnSeries.SummableFamily.one_sub_self_mul_hsum_powers

end powers

end SummableFamily

section Inversion

variable [LinearOrderedAddCommGroup Γ]

section IsDomain

variable [CommRing R] [IsDomain R]

theorem unit_aux (x : HahnSeries Γ R) {r : R} (hr : r * x.coeff x.order = 1) :
    0 < addVal Γ R (1 - c r * single (-x.order) 1 * x) :=
  by
  have h10 : (1 : R) ≠ 0 := one_ne_zero
  have x0 : x ≠ 0 := ne_zero_of_coeff_ne_zero (right_ne_zero_of_mul_eq_one hr)
  refine' lt_of_le_of_ne ((add_val Γ R).map_le_sub (ge_of_eq (add_val Γ R).map_one) _) _
  · simp only [AddValuation.map_mul]
    rw [add_val_apply_of_ne x0, add_val_apply_of_ne (single_ne_zero h10), add_val_apply_of_ne _,
      order_C, order_single h10, WithTop.coe_zero, zero_add, ← WithTop.coe_add, neg_add_self,
      WithTop.coe_zero]
    · exact le_refl 0
    · exact C_ne_zero (left_ne_zero_of_mul_eq_one hr)
  · rw [add_val_apply, ← WithTop.coe_zero]
    split_ifs
    · apply WithTop.coe_ne_top
    rw [Ne.def, WithTop.coe_eq_coe]
    intro con
    apply coeff_order_ne_zero h
    rw [← Con, mul_assoc, sub_coeff, one_coeff, if_pos rfl, C_mul_eq_smul, smul_coeff, smul_eq_mul,
      ← add_neg_self x.order, single_mul_coeff_add, one_mul, hr, sub_self]
#align hahn_series.unit_aux HahnSeries.unit_aux

theorem isUnit_iff {x : HahnSeries Γ R} : IsUnit x ↔ IsUnit (x.coeff x.order) :=
  by
  constructor
  · rintro ⟨⟨u, i, ui, iu⟩, rfl⟩
    refine'
      isUnit_of_mul_eq_one (u.coeff u.order) (i.coeff i.order)
        ((mul_coeff_order_add_order u i).symm.trans _)
    rw [ui, one_coeff, if_pos]
    rw [← order_mul (left_ne_zero_of_mul_eq_one ui) (right_ne_zero_of_mul_eq_one ui), ui, order_one]
  · rintro ⟨⟨u, i, ui, iu⟩, h⟩
    rw [Units.val_mk] at h
    rw [h] at iu
    have h := summable_family.one_sub_self_mul_hsum_powers (unit_aux x iu)
    rw [sub_sub_cancel] at h
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_eq_one _ _ h)
#align hahn_series.is_unit_iff HahnSeries.isUnit_iff

end IsDomain

instance [Field R] : Field (HahnSeries Γ R) :=
  { HahnSeries.isDomain,
    HahnSeries.commRing with
    inv := fun x =>
      if x0 : x = 0 then 0
      else
        c (x.coeff x.order)⁻¹ * (single (-x.order)) 1 *
          (SummableFamily.powers _ (unit_aux x (inv_mul_cancel (coeff_order_ne_zero x0)))).hsum
    inv_zero := dif_pos rfl
    mul_inv_cancel := fun x x0 =>
      by
      refine' (congr rfl (dif_neg x0)).trans _
      have h :=
        summable_family.one_sub_self_mul_hsum_powers
          (unit_aux x (inv_mul_cancel (coeff_order_ne_zero x0)))
      rw [sub_sub_cancel] at h
      rw [← mul_assoc, mul_comm x, h] }

end Inversion

end HahnSeries

