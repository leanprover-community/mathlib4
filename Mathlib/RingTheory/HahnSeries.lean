/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Order.WellFoundedSet
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Finset.MulAntidiagonal
import Mathlib.Algebra.Order.Group.WithTop

#align_import ring_theory.hahn_series from "leanprover-community/mathlib"@"a484a7d0eade4e1268f4fb402859b6686037f965"

/-!
# Hahn Series
If `Γ` is ordered and `R` has zero, then `HahnSeries Γ R` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. With further structure on `R` and
`Γ`, we can add further structure on `HahnSeries Γ R`, with the most studied case being when `Γ` is
a linearly ordered abelian group and `R` is a field, in which case `HahnSeries Γ R` is a
valued field, with value group `Γ`.

These generalize Laurent series (with value group `ℤ`), and Laurent series are implemented that way
in the file `RingTheory/LaurentSeries`.

## Main Definitions
  * If `Γ` is ordered and `R` has zero, then `HahnSeries Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are partially well-ordered.
  * If `R` is a (commutative) additive monoid or group, then so is `HahnSeries Γ R`.
  * If `R` is a (commutative) (semi-)ring, then so is `HahnSeries Γ R`.
  * `HahnSeries.addVal Γ R` defines an `AddValuation` on `HahnSeries Γ R` when `Γ` is linearly
    ordered.
  * A `HahnSeries.SummableFamily` is a family of Hahn series such that the union of their supports
  is well-founded and only finitely many are nonzero at any given coefficient. They have a formal
  sum, `HahnSeries.SummableFamily.hsum`, which can be bundled as a `LinearMap` as
  `HahnSeries.SummableFamily.lsum`. Note that this is different from `Summable` in the valuation
  topology, because there are topologically summable families that do not satisfy the axioms of
  `HahnSeries.SummableFamily`, and formally summable families whose sums do not converge
  topologically.
  * Laurent series over `R` are implemented as `HahnSeries ℤ R` in the file
    `RingTheory/LaurentSeries`.

## TODO
  * Build an API for the variable `X` (defined to be `single 1 1 : HahnSeries Γ R`) in analogy to
    `X : R[X]` and `X : PowerSeries R`

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]

-/

set_option linter.uppercaseLean3 false

open Finset Function

open BigOperators Classical Pointwise Polynomial

noncomputable section

/-- If `Γ` is linearly ordered and `R` has zero, then `HahnSeries Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are well-founded. -/
@[ext]
structure HahnSeries (Γ : Type*) (R : Type*) [PartialOrder Γ] [Zero R] where
  coeff : Γ → R
  isPWO_support' : (Function.support coeff).IsPWO
#align hahn_series HahnSeries

variable {Γ : Type*} {R : Type*}

namespace HahnSeries

section Zero

variable [PartialOrder Γ] [Zero R]

theorem coeff_injective : Injective (coeff : HahnSeries Γ R → Γ → R) :=
  HahnSeries.ext
#align hahn_series.coeff_injective HahnSeries.coeff_injective

@[simp]
theorem coeff_inj {x y : HahnSeries Γ R} : x.coeff = y.coeff ↔ x = y :=
  coeff_injective.eq_iff
#align hahn_series.coeff_inj HahnSeries.coeff_inj

/-- The support of a Hahn series is just the set of indices whose coefficients are nonzero.
  Notably, it is well-founded. -/
nonrec def support (x : HahnSeries Γ R) : Set Γ :=
  support x.coeff
#align hahn_series.support HahnSeries.support

@[simp]
theorem isPWO_support (x : HahnSeries Γ R) : x.support.IsPWO :=
  x.isPWO_support'
#align hahn_series.is_pwo_support HahnSeries.isPWO_support

@[simp]
theorem isWF_support (x : HahnSeries Γ R) : x.support.IsWF :=
  x.isPWO_support.isWF
#align hahn_series.is_wf_support HahnSeries.isWF_support

@[simp]
theorem mem_support (x : HahnSeries Γ R) (a : Γ) : a ∈ x.support ↔ x.coeff a ≠ 0 :=
  Iff.refl _
#align hahn_series.mem_support HahnSeries.mem_support

instance : Zero (HahnSeries Γ R) :=
  ⟨{  coeff := 0
      isPWO_support' := by simp }⟩

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
nonrec theorem support_nonempty_iff {x : HahnSeries Γ R} : x.support.Nonempty ↔ x ≠ 0 := by
  rw [support, support_nonempty_iff, Ne.def, coeff_fun_eq_zero_iff]
#align hahn_series.support_nonempty_iff HahnSeries.support_nonempty_iff

@[simp]
theorem support_eq_empty_iff {x : HahnSeries Γ R} : x.support = ∅ ↔ x = 0 :=
  support_eq_empty_iff.trans coeff_fun_eq_zero_iff
#align hahn_series.support_eq_empty_iff HahnSeries.support_eq_empty_iff

/-- `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise. -/
def single (a : Γ) : ZeroHom R (HahnSeries Γ R) where
  toFun r :=
    { coeff := Pi.single a r
      isPWO_support' := (Set.isPWO_singleton a).mono Pi.support_single_subset }
  map_zero' := HahnSeries.ext _ _ (Pi.single_zero _)
#align hahn_series.single HahnSeries.single

variable {a b : Γ} {r : R}

@[simp]
theorem single_coeff_same (a : Γ) (r : R) : (single a r).coeff a = r :=
  Pi.single_eq_same (f := fun _ => R) a r
#align hahn_series.single_coeff_same HahnSeries.single_coeff_same

@[simp]
theorem single_coeff_of_ne (h : b ≠ a) : (single a r).coeff b = 0 :=
  Pi.single_eq_of_ne (f := fun _ => R) h r
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

--@[simp] Porting note: simp can prove it
theorem single_eq_zero : single a (0 : R) = 0 :=
  (single a).map_zero
#align hahn_series.single_eq_zero HahnSeries.single_eq_zero

theorem single_injective (a : Γ) : Function.Injective (single a : R → HahnSeries Γ R) :=
  fun r s rs => by rw [← single_coeff_same a r, ← single_coeff_same a s, rs]
#align hahn_series.single_injective HahnSeries.single_injective

theorem single_ne_zero (h : r ≠ 0) : single a r ≠ 0 := fun con =>
  h (single_injective a (con.trans single_eq_zero.symm))
#align hahn_series.single_ne_zero HahnSeries.single_ne_zero

@[simp]
theorem single_eq_zero_iff {a : Γ} {r : R} : single a r = 0 ↔ r = 0 :=
  map_eq_zero_iff _ <| single_injective a
#align hahn_series.single_eq_zero_iff HahnSeries.single_eq_zero_iff

instance [Nonempty Γ] [Nontrivial R] : Nontrivial (HahnSeries Γ R) :=
  ⟨by
    obtain ⟨r, s, rs⟩ := exists_pair_ne R
    inhabit Γ
    refine' ⟨single default r, single default s, fun con => rs _⟩
    rw [← single_coeff_same (default : Γ) r, con, single_coeff_same]⟩

section Order

variable [Zero Γ]

/-- The order of a nonzero Hahn series `x` is a minimal element of `Γ` where `x` has a
  nonzero coefficient, the order of 0 is 0. -/
def order (x : HahnSeries Γ R) : Γ :=
  if h : x = 0 then 0 else x.isWF_support.min (support_nonempty_iff.2 h)
#align hahn_series.order HahnSeries.order

@[simp]
theorem order_zero : order (0 : HahnSeries Γ R) = 0 :=
  dif_pos rfl
#align hahn_series.order_zero HahnSeries.order_zero

theorem order_of_ne {x : HahnSeries Γ R} (hx : x ≠ 0) :
    order x = x.isWF_support.min (support_nonempty_iff.2 hx) :=
  dif_neg hx
#align hahn_series.order_of_ne HahnSeries.order_of_ne

theorem coeff_order_ne_zero {x : HahnSeries Γ R} (hx : x ≠ 0) : x.coeff x.order ≠ 0 := by
  rw [order_of_ne hx]
  exact x.isWF_support.min_mem (support_nonempty_iff.2 hx)
#align hahn_series.coeff_order_ne_zero HahnSeries.coeff_order_ne_zero

theorem order_le_of_coeff_ne_zero {Γ} [LinearOrderedCancelAddCommMonoid Γ] {x : HahnSeries Γ R}
    {g : Γ} (h : x.coeff g ≠ 0) : x.order ≤ g :=
  le_trans (le_of_eq (order_of_ne (ne_zero_of_coeff_ne_zero h)))
    (Set.IsWF.min_le _ _ ((mem_support _ _).2 h))
#align hahn_series.order_le_of_coeff_ne_zero HahnSeries.order_le_of_coeff_ne_zero

@[simp]
theorem order_single (h : r ≠ 0) : (single a r).order = a :=
  (order_of_ne (single_ne_zero h)).trans
    (support_single_subset
      ((single a r).isWF_support.min_mem (support_nonempty_iff.2 (single_ne_zero h))))
#align hahn_series.order_single HahnSeries.order_single

theorem coeff_eq_zero_of_lt_order {x : HahnSeries Γ R} {i : Γ} (hi : i < x.order) :
    x.coeff i = 0 := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  contrapose! hi
  rw [← mem_support] at hi
  rw [order_of_ne hx]
  exact Set.IsWF.not_lt_min _ _ hi
#align hahn_series.coeff_eq_zero_of_lt_order HahnSeries.coeff_eq_zero_of_lt_order

end Order

section Domain

variable {Γ' : Type*} [PartialOrder Γ']

/-- Extends the domain of a `HahnSeries` by an `OrderEmbedding`. -/
def embDomain (f : Γ ↪o Γ') : HahnSeries Γ R → HahnSeries Γ' R := fun x =>
  { coeff := fun b : Γ' => if h : b ∈ f '' x.support then x.coeff (Classical.choose h) else 0
    isPWO_support' :=
      (x.isPWO_support.image_of_monotone f.monotone).mono fun b hb => by
        contrapose! hb
        rw [Function.mem_support, dif_neg hb, Classical.not_not] }
#align hahn_series.emb_domain HahnSeries.embDomain

@[simp]
theorem embDomain_coeff {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {a : Γ} :
    (embDomain f x).coeff (f a) = x.coeff a := by
  rw [embDomain]
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
    (embDomain ⟨⟨f, hfi⟩, hf _ _⟩ x).coeff (f a) = x.coeff a :=
  embDomain_coeff
#align hahn_series.emb_domain_mk_coeff HahnSeries.embDomain_mk_coeff

theorem embDomain_notin_image_support {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {b : Γ'}
    (hb : b ∉ f '' x.support) : (embDomain f x).coeff b = 0 :=
  dif_neg hb
#align hahn_series.emb_domain_notin_image_support HahnSeries.embDomain_notin_image_support

theorem support_embDomain_subset {f : Γ ↪o Γ'} {x : HahnSeries Γ R} :
    support (embDomain f x) ⊆ f '' x.support := by
  intro g hg
  contrapose! hg
  rw [mem_support, embDomain_notin_image_support hg, Classical.not_not]
#align hahn_series.support_emb_domain_subset HahnSeries.support_embDomain_subset

theorem embDomain_notin_range {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {b : Γ'} (hb : b ∉ Set.range f) :
    (embDomain f x).coeff b = 0 :=
  embDomain_notin_image_support fun con => hb (Set.image_subset_range _ _ con)
#align hahn_series.emb_domain_notin_range HahnSeries.embDomain_notin_range

@[simp]
theorem embDomain_zero {f : Γ ↪o Γ'} : embDomain f (0 : HahnSeries Γ R) = 0 := by
  ext
  simp [embDomain_notin_image_support]
#align hahn_series.emb_domain_zero HahnSeries.embDomain_zero

@[simp]
theorem embDomain_single {f : Γ ↪o Γ'} {g : Γ} {r : R} :
    embDomain f (single g r) = single (f g) r := by
  ext g'
  by_cases h : g' = f g
  · simp [h]
  rw [embDomain_notin_image_support, single_coeff_of_ne h]
  by_cases hr : r = 0
  · simp [hr]
  rwa [support_single_of_ne hr, Set.image_singleton, Set.mem_singleton_iff]
#align hahn_series.emb_domain_single HahnSeries.embDomain_single

theorem embDomain_injective {f : Γ ↪o Γ'} :
    Function.Injective (embDomain f : HahnSeries Γ R → HahnSeries Γ' R) := fun x y xy => by
  ext g
  rw [HahnSeries.ext_iff, Function.funext_iff] at xy
  have xyg := xy (f g)
  rwa [embDomain_coeff, embDomain_coeff] at xyg
#align hahn_series.emb_domain_injective HahnSeries.embDomain_injective

end Domain

end Zero

section Addition

variable [PartialOrder Γ]

section AddMonoid

variable [AddMonoid R]

instance : Add (HahnSeries Γ R) where
  add x y :=
    { coeff := x.coeff + y.coeff
      isPWO_support' := (x.isPWO_support.union y.isPWO_support).mono (Function.support_add _ _) }

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
    (hxy : x + y ≠ 0) : min x.order y.order ≤ (x + y).order := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [order_of_ne hx, order_of_ne hy, order_of_ne hxy]
  refine' le_of_eq_of_le _ (Set.IsWF.min_le_min_of_subset (support_add_subset (x := x) (y := y)))
  exact (Set.IsWF.min_union _ _ _ _).symm
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
def coeff.addMonoidHom (g : Γ) : HahnSeries Γ R →+ R where
  toFun f := f.coeff g
  map_zero' := zero_coeff
  map_add' _ _ := add_coeff
#align hahn_series.coeff.add_monoid_hom HahnSeries.coeff.addMonoidHom

section Domain

variable {Γ' : Type*} [PartialOrder Γ']

theorem embDomain_add (f : Γ ↪o Γ') (x y : HahnSeries Γ R) :
    embDomain f (x + y) = embDomain f x + embDomain f y := by
  ext g
  by_cases hg : g ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hg
    simp
  · simp [embDomain_notin_range hg]
#align hahn_series.emb_domain_add HahnSeries.embDomain_add

end Domain

end AddMonoid

instance [AddCommMonoid R] : AddCommMonoid (HahnSeries Γ R) :=
  { inferInstanceAs (AddMonoid (HahnSeries Γ R)) with
    add_comm := fun x y => by
      ext
      apply add_comm }

section AddGroup

variable [AddGroup R]

instance : AddGroup (HahnSeries Γ R) :=
  { inferInstanceAs (AddMonoid (HahnSeries Γ R)) with
    neg := fun x =>
      { coeff := fun a => -x.coeff a
        isPWO_support' := by
          rw [Function.support_neg]
          exact x.isPWO_support }
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
theorem support_neg {x : HahnSeries Γ R} : (-x).support = x.support := by
  ext
  simp
#align hahn_series.support_neg HahnSeries.support_neg

@[simp]
theorem sub_coeff' {x y : HahnSeries Γ R} : (x - y).coeff = x.coeff - y.coeff := by
  ext
  simp [sub_eq_add_neg]
#align hahn_series.sub_coeff' HahnSeries.sub_coeff'

theorem sub_coeff {x y : HahnSeries Γ R} {a : Γ} : (x - y).coeff a = x.coeff a - y.coeff a := by
  simp
#align hahn_series.sub_coeff HahnSeries.sub_coeff

@[simp]
theorem order_neg [Zero Γ] {f : HahnSeries Γ R} : (-f).order = f.order := by
  by_cases hf : f = 0
  · simp only [hf, neg_zero]
  simp only [order, support_neg, neg_eq_zero]
#align hahn_series.order_neg HahnSeries.order_neg

end AddGroup

instance [AddCommGroup R] : AddCommGroup (HahnSeries Γ R) :=
  { inferInstanceAs (AddCommMonoid (HahnSeries Γ R)),
    inferInstanceAs (AddGroup (HahnSeries Γ R)) with }

end Addition

section DistribMulAction

variable [PartialOrder Γ] {V : Type*} [Monoid R] [AddMonoid V] [DistribMulAction R V]

instance : SMul R (HahnSeries Γ V) :=
  ⟨fun r x =>
    { coeff := r • x.coeff
      isPWO_support' := x.isPWO_support.mono (Function.support_smul_subset_right r x.coeff) }⟩

@[simp]
theorem smul_coeff {r : R} {x : HahnSeries Γ V} {a : Γ} : (r • x).coeff a = r • x.coeff a :=
  rfl
#align hahn_series.smul_coeff HahnSeries.smul_coeff

instance : DistribMulAction R (HahnSeries Γ V) where
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

theorem smul_order_leq {Γ} [Zero Γ] [LinearOrder Γ] (r : R) (x : HahnSeries Γ V) (h : r • x ≠ 0) :
    x.order ≤ (r • x).order := by
  by_cases hx : x = 0
  · rw [hx, smul_zero r] at h
    exact (h rfl).elim
  simp_all only [order, dite_false]
  exact (Set.IsWF.min_le_min_of_subset (Function.support_smul_subset_right r x.coeff))

variable {S : Type*} [Monoid S] [DistribMulAction S V]

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

variable [PartialOrder Γ] [Semiring R] {V : Type*} [AddCommMonoid V] [Module R V]

instance : Module R (HahnSeries Γ V) :=
  { inferInstanceAs (DistribMulAction R (HahnSeries Γ V)) with
    zero_smul := fun _ => by
      ext
      simp
    add_smul := fun _ _ _ => by
      ext
      simp [add_smul] }

/-- `single` as a linear map -/
@[simps]
def single.linearMap (a : Γ) : V →ₗ[R] HahnSeries Γ V :=
  { single.addMonoidHom a with
    map_smul' := fun r s => by
      ext b
      by_cases h : b = a <;> simp [h] }
#align hahn_series.single.linear_map HahnSeries.single.linearMap

/-- `coeff g` as a linear map -/
@[simps]
def coeff.linearMap (g : Γ) : HahnSeries Γ V →ₗ[R] V :=
  { coeff.addMonoidHom g with map_smul' := fun _ _ => rfl }
#align hahn_series.coeff.linear_map HahnSeries.coeff.linearMap

section Domain

variable {Γ' : Type*} [PartialOrder Γ']

theorem embDomain_smul (f : Γ ↪o Γ') (r : R) (x : HahnSeries Γ R) :
    embDomain f (r • x) = r • embDomain f x := by
  ext g
  by_cases hg : g ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hg
    simp
  · simp [embDomain_notin_range hg]
#align hahn_series.emb_domain_smul HahnSeries.embDomain_smul

/-- Extending the domain of Hahn series is a linear map. -/
@[simps]
def embDomainLinearMap (f : Γ ↪o Γ') : HahnSeries Γ R →ₗ[R] HahnSeries Γ' R where
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
theorem order_one [MulZeroOneClass R] : order (1 : HahnSeries Γ R) = 0 := by
  cases' subsingleton_or_nontrivial R with h h <;> haveI := h
  · rw [Subsingleton.elim (1 : HahnSeries Γ R) 0, order_zero]
  · exact order_single one_ne_zero
#align hahn_series.order_one HahnSeries.order_one

instance [NonUnitalNonAssocSemiring R] : Mul (HahnSeries Γ R) where
  mul x y :=
    { coeff := fun a =>
        ∑ ij in addAntidiagonal x.isPWO_support y.isPWO_support a, x.coeff ij.fst * y.coeff ij.snd
      isPWO_support' :=
        haveI h :
          { a : Γ |
              (∑ ij : Γ × Γ in addAntidiagonal x.isPWO_support y.isPWO_support a,
                  x.coeff ij.fst * y.coeff ij.snd) ≠
                0 } ⊆
            { a : Γ | (addAntidiagonal x.isPWO_support y.isPWO_support a).Nonempty } := by
          intro a ha
          contrapose! ha
          simp [not_nonempty_iff_eq_empty.1 ha]
        isPWO_support_addAntidiagonal.mono h }

/-@[simp] Porting note: removing simp. RHS is more complicated and it makes linter
failures elsewhere-/
theorem mul_coeff [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} {a : Γ} :
    (x * y).coeff a =
      ∑ ij in addAntidiagonal x.isPWO_support y.isPWO_support a, x.coeff ij.fst * y.coeff ij.snd :=
  rfl
#align hahn_series.mul_coeff HahnSeries.mul_coeff

theorem mul_coeff_right' [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} {a : Γ} {s : Set Γ}
    (hs : s.IsPWO) (hys : y.support ⊆ s) :
    (x * y).coeff a =
      ∑ ij in addAntidiagonal x.isPWO_support hs a, x.coeff ij.fst * y.coeff ij.snd := by
  rw [mul_coeff]
  apply sum_subset_zero_on_sdiff (addAntidiagonal_mono_right hys) _ fun _ _ => rfl
  intro b hb
  simp only [not_and, mem_sdiff, mem_addAntidiagonal, mem_support, not_imp_not] at hb
  rw [hb.2 hb.1.1 hb.1.2.2, mul_zero]
#align hahn_series.mul_coeff_right' HahnSeries.mul_coeff_right'

theorem mul_coeff_left' [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} {a : Γ} {s : Set Γ}
    (hs : s.IsPWO) (hxs : x.support ⊆ s) :
    (x * y).coeff a =
      ∑ ij in addAntidiagonal hs y.isPWO_support a, x.coeff ij.fst * y.coeff ij.snd := by
  rw [mul_coeff]
  apply sum_subset_zero_on_sdiff (addAntidiagonal_mono_left hxs) _ fun _ _ => rfl
  intro b hb
  simp only [not_and', mem_sdiff, mem_addAntidiagonal, mem_support, not_ne_iff] at hb
  rw [hb.2 ⟨hb.1.2.1, hb.1.2.2⟩, zero_mul]
#align hahn_series.mul_coeff_left' HahnSeries.mul_coeff_left'

instance [NonUnitalNonAssocSemiring R] : Distrib (HahnSeries Γ R) :=
  { inferInstanceAs (Mul (HahnSeries Γ R)),
    inferInstanceAs (Add (HahnSeries Γ R)) with
    left_distrib := fun x y z => by
      ext a
      have hwf := y.isPWO_support.union z.isPWO_support
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
      have hwf := x.isPWO_support.union y.isPWO_support
      rw [mul_coeff_left' hwf, add_coeff, mul_coeff_left' hwf (Set.subset_union_right _ _),
        mul_coeff_left' hwf (Set.subset_union_left _ _)]
      · simp only [add_coeff, add_mul, sum_add_distrib]
      · intro b
        simp only [add_coeff, Ne.def, Set.mem_union, Set.mem_setOf_eq, mem_support]
        contrapose!
        intro h
        rw [h.1, h.2, add_zero] }

theorem single_mul_coeff_add [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ}
    {b : Γ} : (single b r * x).coeff (a + b) = r * x.coeff a := by
  by_cases hr : r = 0
  · simp [hr, mul_coeff]
  simp only [hr, smul_coeff, mul_coeff, support_single_of_ne, Ne.def, not_false_iff, smul_eq_mul]
  by_cases hx : x.coeff a = 0
  · simp only [hx, mul_zero]
    rw [sum_congr _ fun _ _ => rfl, sum_empty]
    ext ⟨a1, a2⟩
    simp only [not_mem_empty, not_and, Set.mem_singleton_iff, Classical.not_not,
      mem_addAntidiagonal, Set.mem_setOf_eq, iff_false_iff]
    rintro rfl h2 h1
    rw [add_comm] at h1
    rw [← add_right_cancel h1] at hx
    exact h2 hx
  trans ∑ ij : Γ × Γ in {(b, a)}, (single b r).coeff ij.fst * x.coeff ij.snd
  · apply sum_congr _ fun _ _ => rfl
    ext ⟨a1, a2⟩
    simp only [Set.mem_singleton_iff, Prod.mk.inj_iff, mem_addAntidiagonal, mem_singleton,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨rfl, _, h1⟩
      rw [add_comm] at h1
      refine' ⟨rfl, add_right_cancel h1⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, by simp [hx], add_comm _ _⟩
  · simp
#align hahn_series.single_mul_coeff_add HahnSeries.single_mul_coeff_add

theorem mul_single_coeff_add [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ}
    {b : Γ} : (x * single b r).coeff (a + b) = x.coeff a * r := by
  by_cases hr : r = 0
  · simp [hr, mul_coeff]
  simp only [hr, smul_coeff, mul_coeff, support_single_of_ne, Ne.def, not_false_iff, smul_eq_mul]
  by_cases hx : x.coeff a = 0
  · simp only [hx, zero_mul]
    rw [sum_congr _ fun _ _ => rfl, sum_empty]
    ext ⟨a1, a2⟩
    simp only [not_mem_empty, not_and, Set.mem_singleton_iff, Classical.not_not,
      mem_addAntidiagonal, Set.mem_setOf_eq, iff_false_iff]
    rintro h2 rfl h1
    rw [← add_right_cancel h1] at hx
    exact h2 hx
  trans ∑ ij : Γ × Γ in {(a, b)}, x.coeff ij.fst * (single b r).coeff ij.snd
  · apply sum_congr _ fun _ _ => rfl
    ext ⟨a1, a2⟩
    simp only [Set.mem_singleton_iff, Prod.mk.inj_iff, mem_addAntidiagonal, mem_singleton,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨_, rfl, h1⟩
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
    ((single 0 r : HahnSeries Γ R) * x).coeff a = r * x.coeff a := by
  rw [← add_zero a, single_mul_coeff_add, add_zero]
#align hahn_series.single_zero_mul_coeff HahnSeries.single_zero_mul_coeff

@[simp]
theorem single_zero_mul_eq_smul [Semiring R] {r : R} {x : HahnSeries Γ R} :
    single 0 r * x = r • x := by
  ext
  exact single_zero_mul_coeff
#align hahn_series.single_zero_mul_eq_smul HahnSeries.single_zero_mul_eq_smul

theorem support_mul_subset_add_support [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} :
    support (x * y) ⊆ support x + support y := by
  apply Set.Subset.trans (fun x hx => _) support_addAntidiagonal_subset_add
  · exact x.isPWO_support
  · exact y.isPWO_support
  intro x hx
  contrapose! hx
  simp only [not_nonempty_iff_eq_empty, Ne.def, Set.mem_setOf_eq] at hx
  simp [hx, mul_coeff]
#align hahn_series.support_mul_subset_add_support HahnSeries.support_mul_subset_add_support

theorem mul_coeff_order_add_order {Γ} [LinearOrderedCancelAddCommMonoid Γ]
    [NonUnitalNonAssocSemiring R] (x y : HahnSeries Γ R) :
    (x * y).coeff (x.order + y.order) = x.coeff x.order * y.coeff y.order := by
  by_cases hx : x = 0; · simp [hx, mul_coeff]
  by_cases hy : y = 0; · simp [hy, mul_coeff]
  rw [order_of_ne hx, order_of_ne hy, mul_coeff, Finset.addAntidiagonal_min_add_min,
    Finset.sum_singleton]
#align hahn_series.mul_coeff_order_add_order HahnSeries.mul_coeff_order_add_order

private theorem mul_assoc' [NonUnitalSemiring R] (x y z : HahnSeries Γ R) :
    x * y * z = x * (y * z) := by
  ext b
  rw [mul_coeff_left' (x.isPWO_support.add y.isPWO_support) support_mul_subset_add_support,
    mul_coeff_right' (y.isPWO_support.add z.isPWO_support) support_mul_subset_add_support]
  simp only [mul_coeff, add_coeff, sum_mul, mul_sum, sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l + j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i + k, l), (i, k)⟩) <;>
    aesop (add safe Set.add_mem_add) (add simp [add_assoc, mul_assoc])

instance [NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring (HahnSeries Γ R) :=
  { inferInstanceAs (AddCommMonoid (HahnSeries Γ R)),
    inferInstanceAs (Distrib (HahnSeries Γ R)) with
    zero_mul := fun _ => by
      ext
      simp [mul_coeff]
    mul_zero := fun _ => by
      ext
      simp [mul_coeff] }

instance [NonUnitalSemiring R] : NonUnitalSemiring (HahnSeries Γ R) :=
  { inferInstanceAs (NonUnitalNonAssocSemiring (HahnSeries Γ R)) with
    mul_assoc := mul_assoc' }

instance [NonAssocSemiring R] : NonAssocSemiring (HahnSeries Γ R) :=
  { AddMonoidWithOne.unary,
    inferInstanceAs (NonUnitalNonAssocSemiring (HahnSeries Γ R)) with
    one_mul := fun x => by
      ext
      exact single_zero_mul_coeff.trans (one_mul _)
    mul_one := fun x => by
      ext
      exact mul_single_zero_coeff.trans (mul_one _) }

instance [Semiring R] : Semiring (HahnSeries Γ R) :=
  { inferInstanceAs (NonAssocSemiring (HahnSeries Γ R)),
    inferInstanceAs (NonUnitalSemiring (HahnSeries Γ R)) with }

instance [NonUnitalCommSemiring R] : NonUnitalCommSemiring (HahnSeries Γ R) where
  __ : NonUnitalSemiring (HahnSeries Γ R) := inferInstance
  mul_comm x y := by
    ext
    simp_rw [mul_coeff, mul_comm]
    exact Finset.sum_equiv (Equiv.prodComm _ _) (fun _ ↦ swap_mem_addAntidiagonal.symm) <| by simp

instance [CommSemiring R] : CommSemiring (HahnSeries Γ R) :=
  { inferInstanceAs (NonUnitalCommSemiring (HahnSeries Γ R)),
    inferInstanceAs (Semiring (HahnSeries Γ R)) with }

instance [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing (HahnSeries Γ R) :=
  { inferInstanceAs (NonUnitalNonAssocSemiring (HahnSeries Γ R)),
    inferInstanceAs (AddGroup (HahnSeries Γ R)) with }

instance [NonUnitalRing R] : NonUnitalRing (HahnSeries Γ R) :=
  { inferInstanceAs (NonUnitalNonAssocRing (HahnSeries Γ R)),
    inferInstanceAs (NonUnitalSemiring (HahnSeries Γ R)) with }

instance [NonAssocRing R] : NonAssocRing (HahnSeries Γ R) :=
  { inferInstanceAs (NonUnitalNonAssocRing (HahnSeries Γ R)),
    inferInstanceAs (NonAssocSemiring (HahnSeries Γ R)) with }

instance [Ring R] : Ring (HahnSeries Γ R) :=
  { inferInstanceAs (Semiring (HahnSeries Γ R)),
    inferInstanceAs (AddCommGroup (HahnSeries Γ R)) with }

instance [NonUnitalCommRing R] : NonUnitalCommRing (HahnSeries Γ R) :=
  { inferInstanceAs (NonUnitalCommSemiring (HahnSeries Γ R)),
    inferInstanceAs (NonUnitalRing (HahnSeries Γ R)) with }

instance [CommRing R] : CommRing (HahnSeries Γ R) :=
  { inferInstanceAs (CommSemiring (HahnSeries Γ R)),
    inferInstanceAs (Ring (HahnSeries Γ R)) with }

instance {Γ} [LinearOrderedCancelAddCommMonoid Γ] [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] :
    NoZeroDivisors (HahnSeries Γ R) where
    eq_zero_or_eq_zero_of_mul_eq_zero {x y} xy := by
      contrapose! xy
      rw [Ne, HahnSeries.ext_iff, Function.funext_iff, not_forall]
      refine' ⟨x.order + y.order, _⟩
      rw [mul_coeff_order_add_order x y, zero_coeff, mul_eq_zero]
      simp [coeff_order_ne_zero, xy]

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
  · rw [order_of_ne hx, order_of_ne hy, order_of_ne (mul_ne_zero hx hy), ← Set.IsWF.min_add]
    exact Set.IsWF.min_le_min_of_subset support_mul_subset_add_support
#align hahn_series.order_mul HahnSeries.order_mul

@[simp]
theorem order_pow {Γ} [LinearOrderedCancelAddCommMonoid Γ] [Semiring R] [NoZeroDivisors R]
    (x : HahnSeries Γ R) (n : ℕ) : (x ^ n).order = n • x.order := by
  induction' n with h IH
  · simp
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  rw [pow_succ', order_mul (pow_ne_zero _ hx) hx, succ_nsmul', IH]
#align hahn_series.order_pow HahnSeries.order_pow

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring R]

@[simp]
theorem single_mul_single {a b : Γ} {r s : R} :
    single a r * single b s = single (a + b) (r * s) := by
  ext x
  by_cases h : x = a + b
  · rw [h, mul_single_coeff_add]
    simp
  · rw [single_coeff_of_ne h, mul_coeff, sum_eq_zero]
    simp_rw [mem_addAntidiagonal]
    rintro ⟨y, z⟩ ⟨hy, hz, rfl⟩
    rw [eq_of_mem_support_single hy, eq_of_mem_support_single hz] at h
    exact (h rfl).elim
#align hahn_series.single_mul_single HahnSeries.single_mul_single

end NonUnitalNonAssocSemiring

section NonAssocSemiring

variable [NonAssocSemiring R]

/-- `C a` is the constant Hahn Series `a`. `C` is provided as a ring homomorphism. -/
@[simps]
def C : R →+* HahnSeries Γ R where
  toFun := single 0
  map_zero' := single_eq_zero
  map_one' := rfl
  map_add' x y := by
    ext a
    by_cases h : a = 0 <;> simp [h]
  map_mul' x y := by rw [single_mul_single, zero_add]
#align hahn_series.C HahnSeries.C

--@[simp] Porting note: simp can prove it
theorem C_zero : C (0 : R) = (0 : HahnSeries Γ R) :=
  C.map_zero
#align hahn_series.C_zero HahnSeries.C_zero

--@[simp] Porting note: simp can prove it
theorem C_one : C (1 : R) = (1 : HahnSeries Γ R) :=
  C.map_one
#align hahn_series.C_one HahnSeries.C_one

theorem C_injective : Function.Injective (C : R → HahnSeries Γ R) := by
  intro r s rs
  rw [HahnSeries.ext_iff, Function.funext_iff] at rs
  have h := rs 0
  rwa [C_apply, single_coeff_same, C_apply, single_coeff_same] at h
#align hahn_series.C_injective HahnSeries.C_injective

theorem C_ne_zero {r : R} (h : r ≠ 0) : (C r : HahnSeries Γ R) ≠ 0 := by
  contrapose! h
  rw [← C_zero] at h
  exact C_injective h
#align hahn_series.C_ne_zero HahnSeries.C_ne_zero

theorem order_C {r : R} : order (C r : HahnSeries Γ R) = 0 := by
  by_cases h : r = 0
  · rw [h, C_zero, order_zero]
  · exact order_single h
#align hahn_series.order_C HahnSeries.order_C

end NonAssocSemiring

section Semiring

variable [Semiring R]

theorem C_mul_eq_smul {r : R} {x : HahnSeries Γ R} : C r * x = r • x :=
  single_zero_mul_eq_smul
#align hahn_series.C_mul_eq_smul HahnSeries.C_mul_eq_smul

end Semiring

section Domain

variable {Γ' : Type*} [OrderedCancelAddCommMonoid Γ']

theorem embDomain_mul [NonUnitalNonAssocSemiring R] (f : Γ ↪o Γ')
    (hf : ∀ x y, f (x + y) = f x + f y) (x y : HahnSeries Γ R) :
    embDomain f (x * y) = embDomain f x * embDomain f y := by
  ext g
  by_cases hg : g ∈ Set.range f
  · obtain ⟨g, rfl⟩ := hg
    simp only [mul_coeff, embDomain_coeff]
    trans
      ∑ ij in
        (addAntidiagonal x.isPWO_support y.isPWO_support g).map
          (Function.Embedding.prodMap f.toEmbedding f.toEmbedding),
        (embDomain f x).coeff ij.1 * (embDomain f y).coeff ij.2
    · simp
    apply sum_subset
    · rintro ⟨i, j⟩ hij
      simp only [exists_prop, mem_map, Prod.mk.inj_iff, mem_addAntidiagonal,
        Function.Embedding.coe_prodMap, mem_support, Prod.exists] at hij
      obtain ⟨i, j, ⟨hx, hy, rfl⟩, rfl, rfl⟩ := hij
      simp [hx, hy, hf]
    · rintro ⟨_, _⟩ h1 h2
      contrapose! h2
      obtain ⟨i, _, rfl⟩ := support_embDomain_subset (ne_zero_and_ne_zero_of_mul h2).1
      obtain ⟨j, _, rfl⟩ := support_embDomain_subset (ne_zero_and_ne_zero_of_mul h2).2
      simp only [exists_prop, mem_map, Prod.mk.inj_iff, mem_addAntidiagonal,
        Function.Embedding.coe_prodMap, mem_support, Prod.exists]
      simp only [mem_addAntidiagonal, embDomain_coeff, mem_support, ← hf,
        OrderEmbedding.eq_iff_eq] at h1
      exact ⟨i, j, h1, rfl⟩
  · rw [embDomain_notin_range hg, eq_comm]
    contrapose! hg
    obtain ⟨_, hi, _, hj, rfl⟩ := support_mul_subset_add_support ((mem_support _ _).2 hg)
    obtain ⟨i, _, rfl⟩ := support_embDomain_subset hi
    obtain ⟨j, _, rfl⟩ := support_embDomain_subset hj
    refine' ⟨i + j, hf i j⟩
#align hahn_series.emb_domain_mul HahnSeries.embDomain_mul

theorem embDomain_one [NonAssocSemiring R] (f : Γ ↪o Γ') (hf : f 0 = 0) :
    embDomain f (1 : HahnSeries Γ R) = (1 : HahnSeries Γ' R) :=
  embDomain_single.trans <| hf.symm ▸ rfl
#align hahn_series.emb_domain_one HahnSeries.embDomain_one

/-- Extending the domain of Hahn series is a ring homomorphism. -/
@[simps]
def embDomainRingHom [NonAssocSemiring R] (f : Γ →+ Γ') (hfi : Function.Injective f)
    (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') : HahnSeries Γ R →+* HahnSeries Γ' R where
  toFun := embDomain ⟨⟨f, hfi⟩, hf _ _⟩
  map_one' := embDomain_one _ f.map_zero
  map_mul' := embDomain_mul _ f.map_add
  map_zero' := embDomain_zero
  map_add' := embDomain_add _
#align hahn_series.emb_domain_ring_hom HahnSeries.embDomainRingHom

theorem embDomainRingHom_C [NonAssocSemiring R] {f : Γ →+ Γ'} {hfi : Function.Injective f}
    {hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g'} {r : R} : embDomainRingHom f hfi hf (C r) = C r :=
  embDomain_single.trans (by simp)
#align hahn_series.emb_domain_ring_hom_C HahnSeries.embDomainRingHom_C

end Domain

section Algebra

variable [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]

instance : Algebra R (HahnSeries Γ A) where
  toRingHom := C.comp (algebraMap R A)
  smul_def' r x := by
    ext
    simp
  commutes' r x := by
    ext
    simp only [smul_coeff, single_zero_mul_eq_smul, RingHom.coe_comp, RingHom.toFun_eq_coe, C_apply,
      Function.comp_apply, algebraMap_smul, mul_single_zero_coeff]
    rw [← Algebra.commutes, Algebra.smul_def]

theorem C_eq_algebraMap : C = algebraMap R (HahnSeries Γ R) :=
  rfl
#align hahn_series.C_eq_algebra_map HahnSeries.C_eq_algebraMap

theorem algebraMap_apply {r : R} : algebraMap R (HahnSeries Γ A) r = C (algebraMap R A r) :=
  rfl
#align hahn_series.algebra_map_apply HahnSeries.algebraMap_apply

instance [Nontrivial Γ] [Nontrivial R] : Nontrivial (Subalgebra R (HahnSeries Γ R)) :=
  ⟨⟨⊥, ⊤, by
      rw [Ne.def, SetLike.ext_iff, not_forall]
      obtain ⟨a, ha⟩ := exists_ne (0 : Γ)
      refine' ⟨single a 1, _⟩
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true_iff, Algebra.mem_top]
      intro x
      rw [HahnSeries.ext_iff, Function.funext_iff, not_forall]
      refine' ⟨a, _⟩
      rw [single_coeff_same, algebraMap_apply, C_apply, single_coeff_of_ne ha]
      exact zero_ne_one⟩⟩

section Domain

variable {Γ' : Type*} [OrderedCancelAddCommMonoid Γ']

/-- Extending the domain of Hahn series is an algebra homomorphism. -/
@[simps!]
def embDomainAlgHom (f : Γ →+ Γ') (hfi : Function.Injective f)
    (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') : HahnSeries Γ A →ₐ[R] HahnSeries Γ' A :=
  { embDomainRingHom f hfi hf with commutes' := fun _ => embDomainRingHom_C (hf := hf) }
#align hahn_series.emb_domain_alg_hom HahnSeries.embDomainAlgHom

end Domain

end Algebra

end Multiplication

section Semiring

variable [Semiring R]

/-- The ring `HahnSeries ℕ R` is isomorphic to `PowerSeries R`. -/
@[simps]
def toPowerSeries : HahnSeries ℕ R ≃+* PowerSeries R where
  toFun f := PowerSeries.mk f.coeff
  invFun f := ⟨fun n => PowerSeries.coeff R n f, (Nat.lt_wfRel.wf.isWF _).isPWO⟩
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
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, mul_coeff, isPWO_support]
    classical
    refine (sum_filter_ne_zero _).symm.trans <| (sum_congr ?_ fun _ _ ↦ rfl).trans <|
      sum_filter_ne_zero _
    ext m
    simp only [mem_antidiagonal, mem_addAntidiagonal, and_congr_left_iff, mem_filter,
      mem_support]
    rintro h
    rw [and_iff_right (left_ne_zero_of_mul h), and_iff_right (right_ne_zero_of_mul h)]
#align hahn_series.to_power_series HahnSeries.toPowerSeries

theorem coeff_toPowerSeries {f : HahnSeries ℕ R} {n : ℕ} :
    PowerSeries.coeff R n (toPowerSeries f) = f.coeff n :=
  PowerSeries.coeff_mk _ _
#align hahn_series.coeff_to_power_series HahnSeries.coeff_toPowerSeries

theorem coeff_toPowerSeries_symm {f : PowerSeries R} {n : ℕ} :
    (HahnSeries.toPowerSeries.symm f).coeff n = PowerSeries.coeff R n f :=
  rfl
#align hahn_series.coeff_to_power_series_symm HahnSeries.coeff_toPowerSeries_symm

variable (Γ R) [StrictOrderedSemiring Γ]

/-- Casts a power series as a Hahn series with coefficients from a `StrictOrderedSemiring`. -/
def ofPowerSeries : PowerSeries R →+* HahnSeries Γ R :=
  (HahnSeries.embDomainRingHom (Nat.castAddMonoidHom Γ) Nat.strictMono_cast.injective fun _ _ =>
        Nat.cast_le).comp
    (RingEquiv.toRingHom toPowerSeries.symm)
#align hahn_series.of_power_series HahnSeries.ofPowerSeries

variable {Γ} {R}

theorem ofPowerSeries_injective : Function.Injective (ofPowerSeries Γ R) :=
  embDomain_injective.comp toPowerSeries.symm.injective
#align hahn_series.of_power_series_injective HahnSeries.ofPowerSeries_injective

/-@[simp] Porting note: removing simp. RHS is more complicated and it makes linter
failures elsewhere-/
theorem ofPowerSeries_apply (x : PowerSeries R) :
    ofPowerSeries Γ R x =
      HahnSeries.embDomain
        ⟨⟨((↑) : ℕ → Γ), Nat.strictMono_cast.injective⟩, by
          simp only [Function.Embedding.coeFn_mk]
          exact Nat.cast_le⟩
        (toPowerSeries.symm x) :=
  rfl
#align hahn_series.of_power_series_apply HahnSeries.ofPowerSeries_apply

theorem ofPowerSeries_apply_coeff (x : PowerSeries R) (n : ℕ) :
    (ofPowerSeries Γ R x).coeff n = PowerSeries.coeff R n x := by simp [ofPowerSeries_apply]
#align hahn_series.of_power_series_apply_coeff HahnSeries.ofPowerSeries_apply_coeff

@[simp]
theorem ofPowerSeries_C (r : R) : ofPowerSeries Γ R (PowerSeries.C R r) = HahnSeries.C r := by
  ext n
  simp only [ofPowerSeries_apply, C, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, ne_eq,
    single_coeff]
  split_ifs with hn
  · subst hn
    convert @embDomain_coeff ℕ R _ _ Γ _ _ _ 0 <;> simp
  · rw [embDomain_notin_image_support]
    simp only [not_exists, Set.mem_image, toPowerSeries_symm_apply_coeff, mem_support,
      PowerSeries.coeff_C]
    intro
    simp (config := { contextual := true }) [Ne.symm hn]
#align hahn_series.of_power_series_C HahnSeries.ofPowerSeries_C

@[simp]
theorem ofPowerSeries_X : ofPowerSeries Γ R PowerSeries.X = single 1 1 := by
  ext n
  simp only [single_coeff, ofPowerSeries_apply, RingHom.coe_mk]
  split_ifs with hn
  · rw [hn]
    convert @embDomain_coeff ℕ R _ _ Γ _ _ _ 1 <;> simp
  · rw [embDomain_notin_image_support]
    simp only [not_exists, Set.mem_image, toPowerSeries_symm_apply_coeff, mem_support,
      PowerSeries.coeff_X]
    intro
    simp (config := { contextual := true }) [Ne.symm hn]
#align hahn_series.of_power_series_X HahnSeries.ofPowerSeries_X

@[simp]
theorem ofPowerSeries_X_pow {R} [CommSemiring R] (n : ℕ) :
    ofPowerSeries Γ R (PowerSeries.X ^ n) = single (n : Γ) 1 := by
  rw [RingHom.map_pow]
  induction' n with n ih
  · simp
    rfl
  · rw [pow_succ, ih, ofPowerSeries_X, mul_comm, single_mul_single, one_mul,
      Nat.cast_succ, add_comm]
#align hahn_series.of_power_series_X_pow HahnSeries.ofPowerSeries_X_pow

-- Lemmas about converting hahn_series over fintype to and from mv_power_series
/-- The ring `HahnSeries (σ →₀ ℕ) R` is isomorphic to `MvPowerSeries σ R` for a `Fintype` `σ`.
We take the index set of the hahn series to be `Finsupp` rather than `pi`,
even though we assume `Fintype σ` as this is more natural for alignment with `MvPowerSeries`.
After importing `Algebra.Order.Pi` the ring `HahnSeries (σ → ℕ) R` could be constructed instead.
 -/
@[simps]
def toMvPowerSeries {σ : Type*} [Fintype σ] : HahnSeries (σ →₀ ℕ) R ≃+* MvPowerSeries σ R where
  toFun f := f.coeff
  invFun f := ⟨(f : (σ →₀ ℕ) → R), Finsupp.isPWO _⟩
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
      refine' (sum_filter_ne_zero _).symm.trans <| (sum_congr _ fun _ _ ↦ rfl).trans <|
        sum_filter_ne_zero _
      ext m
      simp only [and_congr_left_iff, mem_addAntidiagonal, mem_filter, mem_support,
        Finset.mem_antidiagonal]
      rintro h
      rw [and_iff_right (left_ne_zero_of_mul h), and_iff_right (right_ne_zero_of_mul h)]
#align hahn_series.to_mv_power_series HahnSeries.toMvPowerSeries

variable {σ : Type*} [Fintype σ]

theorem coeff_toMvPowerSeries {f : HahnSeries (σ →₀ ℕ) R} {n : σ →₀ ℕ} :
    MvPowerSeries.coeff R n (toMvPowerSeries f) = f.coeff n :=
  rfl
#align hahn_series.coeff_to_mv_power_series HahnSeries.coeff_toMvPowerSeries

theorem coeff_toMvPowerSeries_symm {f : MvPowerSeries σ R} {n : σ →₀ ℕ} :
    (HahnSeries.toMvPowerSeries.symm f).coeff n = MvPowerSeries.coeff R n f :=
  rfl
#align hahn_series.coeff_to_mv_power_series_symm HahnSeries.coeff_toMvPowerSeries_symm

end Semiring

section Algebra

variable (R) [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]

/-- The `R`-algebra `HahnSeries ℕ A` is isomorphic to `PowerSeries A`. -/
@[simps!]
def toPowerSeriesAlg : HahnSeries ℕ A ≃ₐ[R] PowerSeries A :=
  { toPowerSeries with
    commutes' := fun r => by
      ext n
      cases n <;> simp [algebraMap_apply, PowerSeries.algebraMap_apply] }
#align hahn_series.to_power_series_alg HahnSeries.toPowerSeriesAlg

variable (Γ) [StrictOrderedSemiring Γ]

/-- Casting a power series as a Hahn series with coefficients from a `StrictOrderedSemiring`
  is an algebra homomorphism. -/
@[simps!]
def ofPowerSeriesAlg : PowerSeries A →ₐ[R] HahnSeries Γ A :=
  (HahnSeries.embDomainAlgHom (Nat.castAddMonoidHom Γ) Nat.strictMono_cast.injective fun _ _ =>
        Nat.cast_le).comp
    (AlgEquiv.toAlgHom (toPowerSeriesAlg R).symm)
#align hahn_series.of_power_series_alg HahnSeries.ofPowerSeriesAlg

instance powerSeriesAlgebra {S : Type*} [CommSemiring S] [Algebra S (PowerSeries R)] :
    Algebra S (HahnSeries Γ R) :=
  RingHom.toAlgebra <| (ofPowerSeries Γ R).comp (algebraMap S (PowerSeries R))
#align hahn_series.power_series_algebra HahnSeries.powerSeriesAlgebra

variable {R}
variable {S : Type*} [CommSemiring S] [Algebra S (PowerSeries R)]

theorem algebraMap_apply' (x : S) :
    algebraMap S (HahnSeries Γ R) x = ofPowerSeries Γ R (algebraMap S (PowerSeries R) x) :=
  rfl
#align hahn_series.algebra_map_apply' HahnSeries.algebraMap_apply'

@[simp]
theorem _root_.Polynomial.algebraMap_hahnSeries_apply (f : R[X]) :
    algebraMap R[X] (HahnSeries Γ R) f = ofPowerSeries Γ R f :=
  rfl
#align polynomial.algebra_map_hahn_series_apply Polynomial.algebraMap_hahnSeries_apply

theorem _root_.Polynomial.algebraMap_hahnSeries_injective :
    Function.Injective (algebraMap R[X] (HahnSeries Γ R)) :=
  ofPowerSeries_injective.comp (Polynomial.coe_injective R)
#align polynomial.algebra_map_hahn_series_injective Polynomial.algebraMap_hahnSeries_injective

end Algebra

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
  refine' Set.iUnion_subset fun n => _
  induction' n with n ih <;> intro g hn
  · simp only [Nat.zero_eq, pow_zero, support_one, Set.mem_singleton_iff] at hn
    rw [hn, SetLike.mem_coe]
    exact AddSubmonoid.zero_mem _
  · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset_add_support hn
    exact SetLike.mem_coe.2 (AddSubmonoid.add_mem _ (AddSubmonoid.subset_closure hi) (ih hj))
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

instance : DFunLike (SummableFamily Γ R α) α fun _ => HahnSeries Γ R where
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

instance : AddCommGroup (SummableFamily Γ R α) :=
  { inferInstanceAs (AddCommMonoid (SummableFamily Γ R α)) with
    neg := fun s =>
      { toFun := fun a => -s a
        isPWO_iUnion_support' := by
          simp_rw [support_neg]
          exact s.isPWO_iUnion_support'
        finite_co_support' := fun g => by
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

variable [OrderedCancelAddCommMonoid Γ] [Semiring R] {α : Type*}

instance : SMul (HahnSeries Γ R) (SummableFamily Γ R α) where
  smul x s :=
    { toFun := fun a => x * s a
      isPWO_iUnion_support' := by
        apply (x.isPWO_support.add s.isPWO_iUnion_support).mono
        refine' Set.Subset.trans (Set.iUnion_mono fun a => support_mul_subset_add_support) _
        intro g
        simp only [Set.mem_iUnion, exists_imp]
        exact fun a ha => (Set.add_subset_add (Set.Subset.refl _) (Set.subset_iUnion _ a)) ha
      finite_co_support' := fun g => by
        refine'
          ((addAntidiagonal x.isPWO_support s.isPWO_iUnion_support g).finite_toSet.biUnion'
                fun ij _ => _).subset
            fun a ha => _
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
  refine'
    (Eq.trans (finsum_congr fun a => _)
          (finsum_sum_comm (addAntidiagonal x.isPWO_support s.isPWO_iUnion_support g)
            (fun i ij => x.coeff (Prod.fst ij) * (s i).coeff ij.snd) _)).trans
      _
  · refine' sum_subset (addAntidiagonal_mono_right
      (Set.subset_iUnion (fun j => support (toFun s j)) a)) _
    rintro ⟨i, j⟩ hU ha
    rw [mem_addAntidiagonal] at *
    rw [Classical.not_not.1 fun con => ha ⟨hU.1, con, hU.2.2⟩, mul_zero]
  · rintro ⟨i, j⟩ _
    refine' (s.finite_co_support j).subset _
    simp_rw [Function.support_subset_iff', Function.mem_support, Classical.not_not]
    intro a ha
    rw [ha, mul_zero]
  · refine' (sum_congr rfl _).trans (sum_subset (addAntidiagonal_mono_right _) _).symm
    · rintro ⟨i, j⟩ _
      rw [mul_finsum]
      apply s.finite_co_support
    · intro x hx
      simp only [Set.mem_iUnion, Ne.def, mem_support]
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
    refine' Set.iUnion_subset_iff.2 fun a g hg => _
    have haf : a ∈ f.support := by
      rw [Finsupp.mem_support_iff, ← support_nonempty_iff]
      exact ⟨g, hg⟩
    exact Set.mem_biUnion haf hg
  finite_co_support' g := by
    refine' f.support.finite_toSet.subset fun a ha => _
    simp only [coeff.addMonoidHom_apply, mem_coe, Finsupp.mem_support_iff, Ne.def,
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
  simp only [hsum_coeff, coe_ofFinsupp, Finsupp.sum, Ne.def]
  simp_rw [← coeff.addMonoidHom_apply, id.def]
  rw [map_sum, finsum_eq_sum_of_support_subset]
  intro x h
  simp only [coeff.addMonoidHom_apply, mem_coe, Finsupp.mem_support_iff, Ne.def]
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
    refine' s.isPWO_iUnion_support.mono (Set.iUnion_subset fun b g h => _)
    by_cases hb : b ∈ Set.range f
    · dsimp only at h
      rw [dif_pos hb] at h
      exact Set.mem_iUnion.2 ⟨Classical.choose hb, h⟩
    · contrapose! h
      rw [dif_neg hb]
      simp
  finite_co_support' g :=
    ((s.finite_co_support g).image f).subset
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
    refine'
      ((((addAntidiagonal x.isPWO_support hpwo y).finite_toSet.biUnion fun ij hij =>
                    hy ij.snd _ _).image
                Nat.succ).union
            (Set.finite_singleton 0)).subset
        _
    · exact (mem_addAntidiagonal.1 (mem_coe.1 hij)).2.1
    · obtain ⟨hi, _, rfl⟩ := mem_addAntidiagonal.1 (mem_coe.1 hij)
      rw [← zero_add ij.snd, ← add_assoc, add_zero]
      exact
        add_lt_add_right (WithTop.coe_lt_coe.1 (lt_of_lt_of_le hx (addVal_le_of_coeff_ne_zero hi)))
          _
    · rintro (_ | n) hn
      · exact Set.mem_union_right _ (Set.mem_singleton 0)
      · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset_add_support hn
        refine' Set.mem_union_left _ ⟨n, Set.mem_iUnion.2 ⟨⟨i, j⟩, Set.mem_iUnion.2 ⟨_, hj⟩⟩, rfl⟩
        simp only [and_true_iff, Set.mem_iUnion, mem_addAntidiagonal, mem_coe, eq_self_iff_true,
          Ne.def, mem_support, Set.mem_setOf_eq]
        exact ⟨hi, n, hj⟩
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
  · refine' Eq.trans (embDomain_image _ ⟨Nat.succ, Nat.succ_injective⟩) _
    simp only [pow_succ, coe_powers, coe_sub, smul_apply, coe_ofFinsupp, Pi.sub_apply]
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
  refine' lt_of_le_of_ne ((addVal Γ R).map_le_sub (ge_of_eq (addVal Γ R).map_one) _) _
  · simp only [AddValuation.map_mul]
    rw [addVal_apply_of_ne x0, addVal_apply_of_ne (single_ne_zero h10), addVal_apply_of_ne _,
      order_C, order_single h10, WithTop.coe_zero, zero_add, ← WithTop.coe_add, neg_add_self,
      WithTop.coe_zero]
    · exact C_ne_zero (left_ne_zero_of_mul_eq_one hr)
  · rw [addVal_apply, ← WithTop.coe_zero]
    split_ifs with h
    · apply WithTop.coe_ne_top
    rw [Ne.def, WithTop.coe_eq_coe]
    intro con
    apply coeff_order_ne_zero h
    rw [← con, mul_assoc, sub_coeff, one_coeff, if_pos rfl, C_mul_eq_smul, smul_coeff, smul_eq_mul,
      ← add_neg_self x.order, single_mul_coeff_add, one_mul, hr, sub_self]
#align hahn_series.unit_aux HahnSeries.unit_aux

theorem isUnit_iff {x : HahnSeries Γ R} : IsUnit x ↔ IsUnit (x.coeff x.order) := by
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
    have h := SummableFamily.one_sub_self_mul_hsum_powers (unit_aux x iu)
    rw [sub_sub_cancel] at h
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_eq_one _ _ h)
#align hahn_series.is_unit_iff HahnSeries.isUnit_iff

end IsDomain

instance [Field R] : Field (HahnSeries Γ R) :=
  { inferInstanceAs (IsDomain (HahnSeries Γ R)),
    inferInstanceAs (CommRing (HahnSeries Γ R)) with
    inv := fun x =>
      if x0 : x = 0 then 0
      else
        C (x.coeff x.order)⁻¹ * (single (-x.order)) 1 *
          (SummableFamily.powers _ (unit_aux x (inv_mul_cancel (coeff_order_ne_zero x0)))).hsum
    inv_zero := dif_pos rfl
    mul_inv_cancel := fun x x0 => by
      refine' (congr rfl (dif_neg x0)).trans _
      have h :=
        SummableFamily.one_sub_self_mul_hsum_powers
          (unit_aux x (inv_mul_cancel (coeff_order_ne_zero x0)))
      rw [sub_sub_cancel] at h
      rw [← mul_assoc, mul_comm x, h] }

end Inversion

end HahnSeries
