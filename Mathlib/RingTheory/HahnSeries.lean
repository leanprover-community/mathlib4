/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Order.WellFoundedSet
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Finsupp.Pwo
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
  isPwo_support' : (Function.support coeff).IsPwo
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
theorem isPwo_support (x : HahnSeries Γ R) : x.support.IsPwo :=
  x.isPwo_support'
#align hahn_series.is_pwo_support HahnSeries.isPwo_support

@[simp]
theorem isWf_support (x : HahnSeries Γ R) : x.support.IsWf :=
  x.isPwo_support.isWf
#align hahn_series.is_wf_support HahnSeries.isWf_support

@[simp]
theorem mem_support (x : HahnSeries Γ R) (a : Γ) : a ∈ x.support ↔ x.coeff a ≠ 0 :=
  Iff.refl _
#align hahn_series.mem_support HahnSeries.mem_support

instance : Zero (HahnSeries Γ R) :=
  ⟨{  coeff := 0
      isPwo_support' := by simp }⟩
                           -- 🎉 no goals

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
  -- 🎉 no goals
#align hahn_series.support_nonempty_iff HahnSeries.support_nonempty_iff

@[simp]
theorem support_eq_empty_iff {x : HahnSeries Γ R} : x.support = ∅ ↔ x = 0 :=
  support_eq_empty_iff.trans coeff_fun_eq_zero_iff
#align hahn_series.support_eq_empty_iff HahnSeries.support_eq_empty_iff

/-- `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise. -/
def single (a : Γ) : ZeroHom R (HahnSeries Γ R) where
  toFun r :=
    { coeff := Pi.single a r
      isPwo_support' := (Set.isPwo_singleton a).mono Pi.support_single_subset }
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
  -- ⊢ coeff (↑(single a) r) b = r
                       -- 🎉 no goals
                       -- 🎉 no goals
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
                   -- 🎉 no goals
#align hahn_series.single_injective HahnSeries.single_injective

theorem single_ne_zero (h : r ≠ 0) : single a r ≠ 0 := fun con =>
  h (single_injective a (con.trans single_eq_zero.symm))
#align hahn_series.single_ne_zero HahnSeries.single_ne_zero

@[simp]
theorem single_eq_zero_iff {a : Γ} {r : R} : single a r = 0 ↔ r = 0 := by
  constructor
  -- ⊢ ↑(single a) r = 0 → r = 0
  · contrapose!
    -- ⊢ r ≠ 0 → ↑(single a) r ≠ 0
    exact single_ne_zero
    -- 🎉 no goals
  · simp (config := { contextual := true })
    -- 🎉 no goals
#align hahn_series.single_eq_zero_iff HahnSeries.single_eq_zero_iff

instance [Nonempty Γ] [Nontrivial R] : Nontrivial (HahnSeries Γ R) :=
  ⟨by
    obtain ⟨r, s, rs⟩ := exists_pair_ne R
    -- ⊢ ∃ x y, x ≠ y
    inhabit Γ
    -- ⊢ ∃ x y, x ≠ y
    refine' ⟨single default r, single default s, fun con => rs _⟩
    -- ⊢ r = s
    rw [← single_coeff_same (default : Γ) r, con, single_coeff_same]⟩
    -- 🎉 no goals

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

theorem coeff_order_ne_zero {x : HahnSeries Γ R} (hx : x ≠ 0) : x.coeff x.order ≠ 0 := by
  rw [order_of_ne hx]
  -- ⊢ coeff x (Set.IsWf.min (_ : Set.IsWf (support x)) (_ : Set.Nonempty (support  …
  exact x.isWf_support.min_mem (support_nonempty_iff.2 hx)
  -- 🎉 no goals
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

theorem coeff_eq_zero_of_lt_order {x : HahnSeries Γ R} {i : Γ} (hi : i < x.order) :
    x.coeff i = 0 := by
  rcases eq_or_ne x 0 with (rfl | hx)
  -- ⊢ coeff 0 i = 0
  · simp
    -- 🎉 no goals
  contrapose! hi
  -- ⊢ ¬i < order x
  rw [← mem_support] at hi
  -- ⊢ ¬i < order x
  rw [order_of_ne hx]
  -- ⊢ ¬i < Set.IsWf.min (_ : Set.IsWf (support x)) (_ : Set.Nonempty (support x))
  exact Set.IsWf.not_lt_min _ _ hi
  -- 🎉 no goals
#align hahn_series.coeff_eq_zero_of_lt_order HahnSeries.coeff_eq_zero_of_lt_order

end Order

section Domain

variable {Γ' : Type*} [PartialOrder Γ']

/-- Extends the domain of a `HahnSeries` by an `OrderEmbedding`. -/
def embDomain (f : Γ ↪o Γ') : HahnSeries Γ R → HahnSeries Γ' R := fun x =>
  { coeff := fun b : Γ' => if h : b ∈ f '' x.support then x.coeff (Classical.choose h) else 0
    isPwo_support' :=
      (x.isPwo_support.image_of_monotone f.monotone).mono fun b hb => by
        contrapose! hb
        -- ⊢ ¬b ∈ Function.support fun b => if h : b ∈ (fun a => ↑f a) '' support x then  …
        rw [Function.mem_support, dif_neg hb, Classical.not_not] }
        -- 🎉 no goals
#align hahn_series.emb_domain HahnSeries.embDomain

@[simp]
theorem embDomain_coeff {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {a : Γ} :
    (embDomain f x).coeff (f a) = x.coeff a := by
  rw [embDomain]
  -- ⊢ coeff { coeff := fun b => if h : b ∈ ↑f '' support x then coeff x (Classical …
  dsimp only
  -- ⊢ (if h : ↑f a ∈ ↑f '' support x then coeff x (Classical.choose h) else 0) = c …
  by_cases ha : a ∈ x.support
  -- ⊢ (if h : ↑f a ∈ ↑f '' support x then coeff x (Classical.choose h) else 0) = c …
  · rw [dif_pos (Set.mem_image_of_mem f ha)]
    -- ⊢ coeff x (Classical.choose (_ : ↑f a ∈ ↑f '' support x)) = coeff x a
    exact congr rfl (f.injective (Classical.choose_spec (Set.mem_image_of_mem f ha)).2)
    -- 🎉 no goals
  · rw [dif_neg, Classical.not_not.1 fun c => ha ((mem_support _ _).2 c)]
    -- ⊢ ¬↑f a ∈ ↑f '' support x
    contrapose! ha
    -- ⊢ a ∈ support x
    obtain ⟨b, hb1, hb2⟩ := (Set.mem_image _ _ _).1 ha
    -- ⊢ a ∈ support x
    rwa [f.injective hb2] at hb1
    -- 🎉 no goals
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
  -- ⊢ g ∈ ↑f '' support x
  contrapose! hg
  -- ⊢ ¬g ∈ support (embDomain f x)
  rw [mem_support, embDomain_notin_image_support hg, Classical.not_not]
  -- 🎉 no goals
#align hahn_series.support_emb_domain_subset HahnSeries.support_embDomain_subset

theorem embDomain_notin_range {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {b : Γ'} (hb : b ∉ Set.range f) :
    (embDomain f x).coeff b = 0 :=
  embDomain_notin_image_support fun con => hb (Set.image_subset_range _ _ con)
#align hahn_series.emb_domain_notin_range HahnSeries.embDomain_notin_range

@[simp]
theorem embDomain_zero {f : Γ ↪o Γ'} : embDomain f (0 : HahnSeries Γ R) = 0 := by
  ext
  -- ⊢ coeff (embDomain f 0) x✝ = coeff 0 x✝
  simp [embDomain_notin_image_support]
  -- 🎉 no goals
#align hahn_series.emb_domain_zero HahnSeries.embDomain_zero

@[simp]
theorem embDomain_single {f : Γ ↪o Γ'} {g : Γ} {r : R} :
    embDomain f (single g r) = single (f g) r := by
  ext g'
  -- ⊢ coeff (embDomain f (↑(single g) r)) g' = coeff (↑(single (↑f g)) r) g'
  by_cases h : g' = f g
  -- ⊢ coeff (embDomain f (↑(single g) r)) g' = coeff (↑(single (↑f g)) r) g'
  · simp [h]
    -- 🎉 no goals
  rw [embDomain_notin_image_support, single_coeff_of_ne h]
  -- ⊢ ¬g' ∈ ↑f '' support (↑(single g) r)
  by_cases hr : r = 0
  -- ⊢ ¬g' ∈ ↑f '' support (↑(single g) r)
  · simp [hr]
    -- 🎉 no goals
  rwa [support_single_of_ne hr, Set.image_singleton, Set.mem_singleton_iff]
  -- 🎉 no goals
#align hahn_series.emb_domain_single HahnSeries.embDomain_single

theorem embDomain_injective {f : Γ ↪o Γ'} :
    Function.Injective (embDomain f : HahnSeries Γ R → HahnSeries Γ' R) := fun x y xy => by
  ext g
  -- ⊢ coeff x g = coeff y g
  rw [HahnSeries.ext_iff, Function.funext_iff] at xy
  -- ⊢ coeff x g = coeff y g
  have xyg := xy (f g)
  -- ⊢ coeff x g = coeff y g
  rwa [embDomain_coeff, embDomain_coeff] at xyg
  -- 🎉 no goals
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
    -- ⊢ coeff (x + y + z) x✝ = coeff (x + (y + z)) x✝
    apply add_assoc
    -- 🎉 no goals
  zero_add x := by
    ext
    -- ⊢ coeff (0 + x) x✝ = coeff x x✝
    apply zero_add
    -- 🎉 no goals
  add_zero x := by
    ext
    -- ⊢ coeff (x + 0) x✝ = coeff x x✝
    apply add_zero
    -- 🎉 no goals

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
  -- ⊢ a ∈ support x ∪ support y
  rw [Set.mem_union, mem_support, mem_support]
  -- ⊢ coeff x a ≠ 0 ∨ coeff y a ≠ 0
  contrapose! ha
  -- ⊢ coeff x a + coeff y a = 0
  rw [ha.1, ha.2, add_zero]
  -- 🎉 no goals
#align hahn_series.support_add_subset HahnSeries.support_add_subset

theorem min_order_le_order_add {Γ} [LinearOrderedCancelAddCommMonoid Γ] {x y : HahnSeries Γ R}
    (hxy : x + y ≠ 0) : min x.order y.order ≤ (x + y).order := by
  by_cases hx : x = 0; · simp [hx]
  -- ⊢ min (order x) (order y) ≤ order (x + y)
                         -- 🎉 no goals
  by_cases hy : y = 0; · simp [hy]
  -- ⊢ min (order x) (order y) ≤ order (x + y)
                         -- 🎉 no goals
  rw [order_of_ne hx, order_of_ne hy, order_of_ne hxy]
  -- ⊢ min (Set.IsWf.min (_ : Set.IsWf (support x)) (_ : Set.Nonempty (support x))) …
  refine' le_of_eq_of_le _ (Set.IsWf.min_le_min_of_subset (support_add_subset (x := x) (y := y)))
  · exact (Set.IsWf.min_union _ _ _ _).symm
    -- 🎉 no goals
#align hahn_series.min_order_le_order_add HahnSeries.min_order_le_order_add

/-- `single` as an additive monoid/group homomorphism -/
@[simps]
def single.addMonoidHom (a : Γ) : R →+ HahnSeries Γ R :=
  { single a with
    map_add' := fun x y => by
      ext b
      -- ⊢ coeff (ZeroHom.toFun { toFun := src✝.toFun, map_zero' := (_ : ZeroHom.toFun  …
      by_cases h : b = a <;> simp [h] }
      -- ⊢ coeff (ZeroHom.toFun { toFun := src✝.toFun, map_zero' := (_ : ZeroHom.toFun  …
                             -- 🎉 no goals
                             -- 🎉 no goals
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
  -- ⊢ coeff (embDomain f (x + y)) g = coeff (embDomain f x + embDomain f y) g
  by_cases hg : g ∈ Set.range f
  -- ⊢ coeff (embDomain f (x + y)) g = coeff (embDomain f x + embDomain f y) g
  · obtain ⟨a, rfl⟩ := hg
    -- ⊢ coeff (embDomain f (x + y)) (↑f a) = coeff (embDomain f x + embDomain f y) ( …
    simp
    -- 🎉 no goals
  · simp [embDomain_notin_range hg]
    -- 🎉 no goals
#align hahn_series.emb_domain_add HahnSeries.embDomain_add

end Domain

end AddMonoid

instance [AddCommMonoid R] : AddCommMonoid (HahnSeries Γ R) :=
  { inferInstanceAs (AddMonoid (HahnSeries Γ R)) with
    add_comm := fun x y => by
      ext
      -- ⊢ coeff (x + y) x✝ = coeff (y + x) x✝
      apply add_comm }
      -- 🎉 no goals

section AddGroup

variable [AddGroup R]

instance : AddGroup (HahnSeries Γ R) :=
  { inferInstanceAs (AddMonoid (HahnSeries Γ R)) with
    neg := fun x =>
      { coeff := fun a => -x.coeff a
        isPwo_support' := by
          rw [Function.support_neg]
          -- ⊢ Set.IsPwo (Function.support fun a => coeff x a)
          exact x.isPwo_support }
          -- 🎉 no goals
    add_left_neg := fun x => by
      ext
      -- ⊢ coeff (-x + x) x✝ = coeff 0 x✝
      apply add_left_neg }
      -- 🎉 no goals

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
  -- ⊢ x✝ ∈ support (-x) ↔ x✝ ∈ support x
  simp
  -- 🎉 no goals
#align hahn_series.support_neg HahnSeries.support_neg

@[simp]
theorem sub_coeff' {x y : HahnSeries Γ R} : (x - y).coeff = x.coeff - y.coeff := by
  ext
  -- ⊢ coeff (x - y) x✝ = (x.coeff - y.coeff) x✝
  simp [sub_eq_add_neg]
  -- 🎉 no goals
#align hahn_series.sub_coeff' HahnSeries.sub_coeff'

theorem sub_coeff {x y : HahnSeries Γ R} {a : Γ} : (x - y).coeff a = x.coeff a - y.coeff a := by
  simp
  -- 🎉 no goals
#align hahn_series.sub_coeff HahnSeries.sub_coeff

@[simp]
theorem order_neg [Zero Γ] {f : HahnSeries Γ R} : (-f).order = f.order := by
  by_cases hf : f = 0
  -- ⊢ order (-f) = order f
  · simp only [hf, neg_zero]
    -- 🎉 no goals
  simp only [order, support_neg, neg_eq_zero]
  -- 🎉 no goals
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
      isPwo_support' := x.isPwo_support.mono (Function.support_smul_subset_right r x.coeff) }⟩

@[simp]
theorem smul_coeff {r : R} {x : HahnSeries Γ V} {a : Γ} : (r • x).coeff a = r • x.coeff a :=
  rfl
#align hahn_series.smul_coeff HahnSeries.smul_coeff

instance : DistribMulAction R (HahnSeries Γ V) where
  smul := (· • ·)
  one_smul _ := by
    ext
    -- ⊢ coeff (1 • x✝¹) x✝ = coeff x✝¹ x✝
    simp
    -- 🎉 no goals
  smul_zero _ := by
    ext
    -- ⊢ coeff (x✝¹ • 0) x✝ = coeff 0 x✝
    simp
    -- 🎉 no goals
  smul_add _ _ _ := by
    ext
    -- ⊢ coeff (x✝³ • (x✝² + x✝¹)) x✝ = coeff (x✝³ • x✝² + x✝³ • x✝¹) x✝
    -- ⊢ coeff ((x✝³ * x✝²) • x✝¹) x✝ = coeff (x✝³ • x✝² • x✝¹) x✝
    simp [smul_add]
    -- 🎉 no goals
    -- 🎉 no goals
  mul_smul _ _ _ := by
    ext
    simp [mul_smul]

variable {S : Type*} [Monoid S] [DistribMulAction S V]

instance [SMul R S] [IsScalarTower R S V] : IsScalarTower R S (HahnSeries Γ V) :=
  ⟨fun r s a => by
    ext
    -- ⊢ coeff ((r • s) • a) x✝ = coeff (r • s • a) x✝
    simp⟩
    -- 🎉 no goals

instance [SMulCommClass R S V] : SMulCommClass R S (HahnSeries Γ V) :=
  ⟨fun r s a => by
    ext
    -- ⊢ coeff (r • s • a) x✝ = coeff (s • r • a) x✝
    simp [smul_comm]⟩
    -- 🎉 no goals

end DistribMulAction

section Module

variable [PartialOrder Γ] [Semiring R] {V : Type*} [AddCommMonoid V] [Module R V]

instance : Module R (HahnSeries Γ V) :=
  { inferInstanceAs (DistribMulAction R (HahnSeries Γ V)) with
    zero_smul := fun _ => by
      ext
      -- ⊢ coeff (0 • x✝¹) x✝ = coeff 0 x✝
      simp
      -- 🎉 no goals
      -- ⊢ coeff ((x✝³ + x✝²) • x✝¹) x✝ = coeff (x✝³ • x✝¹ + x✝² • x✝¹) x✝
    add_smul := fun _ _ _ => by
      -- 🎉 no goals
      ext
      simp [add_smul] }

/-- `single` as a linear map -/
@[simps]
def single.linearMap (a : Γ) : R →ₗ[R] HahnSeries Γ R :=
  { single.addMonoidHom a with
    map_smul' := fun r s => by
      ext b
      -- ⊢ coeff (AddHom.toFun { toFun := src✝.toFun, map_add' := (_ : ∀ (x y : R), Zer …
      by_cases h : b = a <;> simp [h] }
      -- ⊢ coeff (AddHom.toFun { toFun := src✝.toFun, map_add' := (_ : ∀ (x y : R), Zer …
                             -- 🎉 no goals
                             -- 🎉 no goals
#align hahn_series.single.linear_map HahnSeries.single.linearMap

/-- `coeff g` as a linear map -/
@[simps]
def coeff.linearMap (g : Γ) : HahnSeries Γ R →ₗ[R] R :=
  { coeff.addMonoidHom g with map_smul' := fun _ _ => rfl }
#align hahn_series.coeff.linear_map HahnSeries.coeff.linearMap

section Domain

variable {Γ' : Type*} [PartialOrder Γ']

theorem embDomain_smul (f : Γ ↪o Γ') (r : R) (x : HahnSeries Γ R) :
    embDomain f (r • x) = r • embDomain f x := by
  ext g
  -- ⊢ coeff (embDomain f (r • x)) g = coeff (r • embDomain f x) g
  by_cases hg : g ∈ Set.range f
  -- ⊢ coeff (embDomain f (r • x)) g = coeff (r • embDomain f x) g
  · obtain ⟨a, rfl⟩ := hg
    -- ⊢ coeff (embDomain f (r • x)) (↑f a) = coeff (r • embDomain f x) (↑f a)
    simp
    -- 🎉 no goals
  · simp [embDomain_notin_range hg]
    -- 🎉 no goals
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
  -- ⊢ order 1 = 0
                                                   -- ⊢ order 1 = 0
                                                   -- ⊢ order 1 = 0
  · rw [Subsingleton.elim (1 : HahnSeries Γ R) 0, order_zero]
    -- 🎉 no goals
  · exact order_single one_ne_zero
    -- 🎉 no goals
#align hahn_series.order_one HahnSeries.order_one

instance [NonUnitalNonAssocSemiring R] : Mul (HahnSeries Γ R)
    where mul x y :=
    { coeff := fun a =>
        ∑ ij in addAntidiagonal x.isPwo_support y.isPwo_support a, x.coeff ij.fst * y.coeff ij.snd
      isPwo_support' :=
        haveI h :
          { a : Γ |
              (∑ ij : Γ × Γ in addAntidiagonal x.isPwo_support y.isPwo_support a,
                  x.coeff ij.fst * y.coeff ij.snd) ≠
                0 } ⊆
            { a : Γ | (addAntidiagonal x.isPwo_support y.isPwo_support a).Nonempty } := by
          intro a ha
          -- ⊢ a ∈ {a | Finset.Nonempty (addAntidiagonal (_ : Set.IsPwo (support x)) (_ : S …
          contrapose! ha
          -- ⊢ ¬a ∈ {a | ∑ ij in addAntidiagonal (_ : Set.IsPwo (support x)) (_ : Set.IsPwo …
          simp [not_nonempty_iff_eq_empty.1 ha]
          -- 🎉 no goals
        isPwo_support_addAntidiagonal.mono h }

/-@[simp] Porting note: removing simp. RHS is more complicated and it makes linter
failures elsewhere-/
theorem mul_coeff [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} {a : Γ} :
    (x * y).coeff a =
      ∑ ij in addAntidiagonal x.isPwo_support y.isPwo_support a, x.coeff ij.fst * y.coeff ij.snd :=
  rfl
#align hahn_series.mul_coeff HahnSeries.mul_coeff

theorem mul_coeff_right' [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} {a : Γ} {s : Set Γ}
    (hs : s.IsPwo) (hys : y.support ⊆ s) :
    (x * y).coeff a =
      ∑ ij in addAntidiagonal x.isPwo_support hs a, x.coeff ij.fst * y.coeff ij.snd := by
  rw [mul_coeff]
  -- ⊢ ∑ ij in addAntidiagonal (_ : Set.IsPwo (support x)) (_ : Set.IsPwo (support  …
  apply sum_subset_zero_on_sdiff (addAntidiagonal_mono_right hys) _ fun _ _ => rfl
  -- ⊢ ∀ (x_1 : Γ × Γ), x_1 ∈ addAntidiagonal (_ : Set.IsPwo (support x)) hs a \ ad …
  intro b hb
  -- ⊢ coeff x b.fst * coeff y b.snd = 0
  simp only [not_and, mem_sdiff, mem_addAntidiagonal, mem_support, not_imp_not] at hb
  -- ⊢ coeff x b.fst * coeff y b.snd = 0
  rw [hb.2 hb.1.1 hb.1.2.2, mul_zero]
  -- 🎉 no goals
#align hahn_series.mul_coeff_right' HahnSeries.mul_coeff_right'

theorem mul_coeff_left' [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} {a : Γ} {s : Set Γ}
    (hs : s.IsPwo) (hxs : x.support ⊆ s) :
    (x * y).coeff a =
      ∑ ij in addAntidiagonal hs y.isPwo_support a, x.coeff ij.fst * y.coeff ij.snd := by
  rw [mul_coeff]
  -- ⊢ ∑ ij in addAntidiagonal (_ : Set.IsPwo (support x)) (_ : Set.IsPwo (support  …
  apply sum_subset_zero_on_sdiff (addAntidiagonal_mono_left hxs) _ fun _ _ => rfl
  -- ⊢ ∀ (x_1 : Γ × Γ), x_1 ∈ addAntidiagonal hs (_ : Set.IsPwo (support y)) a \ ad …
  intro b hb
  -- ⊢ coeff x b.fst * coeff y b.snd = 0
  simp only [not_and', mem_sdiff, mem_addAntidiagonal, mem_support, not_ne_iff] at hb
  -- ⊢ coeff x b.fst * coeff y b.snd = 0
  rw [hb.2 ⟨hb.1.2.1, hb.1.2.2⟩, zero_mul]
  -- 🎉 no goals
#align hahn_series.mul_coeff_left' HahnSeries.mul_coeff_left'

instance [NonUnitalNonAssocSemiring R] : Distrib (HahnSeries Γ R) :=
  { inferInstanceAs (Mul (HahnSeries Γ R)),
    inferInstanceAs (Add (HahnSeries Γ R)) with
    left_distrib := fun x y z => by
      ext a
      -- ⊢ coeff (x * (y + z)) a = coeff (x * y + x * z) a
      have hwf := y.isPwo_support.union z.isPwo_support
      -- ⊢ coeff (x * (y + z)) a = coeff (x * y + x * z) a
      rw [mul_coeff_right' hwf, add_coeff, mul_coeff_right' hwf (Set.subset_union_right _ _),
        mul_coeff_right' hwf (Set.subset_union_left _ _)]
      · simp only [add_coeff, mul_add, sum_add_distrib]
        -- 🎉 no goals
      · intro b
        -- ⊢ b ∈ support (y + z) → b ∈ support y ∪ support z
        simp only [add_coeff, Ne.def, Set.mem_union, Set.mem_setOf_eq, mem_support]
        -- ⊢ ¬coeff y b + coeff z b = 0 → ¬coeff y b = 0 ∨ ¬coeff z b = 0
        contrapose!
        -- ⊢ coeff y b = 0 ∧ coeff z b = 0 → coeff y b + coeff z b = 0
        intro h
        -- ⊢ coeff y b + coeff z b = 0
        rw [h.1, h.2, add_zero]
        -- 🎉 no goals
    right_distrib := fun x y z => by
      ext a
      -- ⊢ coeff ((x + y) * z) a = coeff (x * z + y * z) a
      have hwf := x.isPwo_support.union y.isPwo_support
      -- ⊢ coeff ((x + y) * z) a = coeff (x * z + y * z) a
      rw [mul_coeff_left' hwf, add_coeff, mul_coeff_left' hwf (Set.subset_union_right _ _),
        mul_coeff_left' hwf (Set.subset_union_left _ _)]
      · simp only [add_coeff, add_mul, sum_add_distrib]
        -- 🎉 no goals
      · intro b
        -- ⊢ b ∈ support (x + y) → b ∈ support x ∪ support y
        simp only [add_coeff, Ne.def, Set.mem_union, Set.mem_setOf_eq, mem_support]
        -- ⊢ ¬coeff x b + coeff y b = 0 → ¬coeff x b = 0 ∨ ¬coeff y b = 0
        contrapose!
        -- ⊢ coeff x b = 0 ∧ coeff y b = 0 → coeff x b + coeff y b = 0
        intro h
        -- ⊢ coeff x b + coeff y b = 0
        rw [h.1, h.2, add_zero] }
        -- 🎉 no goals

theorem single_mul_coeff_add [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ}
    {b : Γ} : (single b r * x).coeff (a + b) = r * x.coeff a := by
  by_cases hr : r = 0
  -- ⊢ coeff (↑(single b) r * x) (a + b) = r * coeff x a
  · simp [hr, mul_coeff]
    -- 🎉 no goals
  simp only [hr, smul_coeff, mul_coeff, support_single_of_ne, Ne.def, not_false_iff, smul_eq_mul]
  -- ⊢ ∑ x_1 in addAntidiagonal (_ : Set.IsPwo {b}) (_ : Set.IsPwo (support x)) (a  …
  by_cases hx : x.coeff a = 0
  -- ⊢ ∑ x_1 in addAntidiagonal (_ : Set.IsPwo {b}) (_ : Set.IsPwo (support x)) (a  …
  · simp only [hx, mul_zero]
    -- ⊢ ∑ x_1 in addAntidiagonal (_ : Set.IsPwo {b}) (_ : Set.IsPwo (support x)) (a  …
    rw [sum_congr _ fun _ _ => rfl, sum_empty]
    -- ⊢ addAntidiagonal (_ : Set.IsPwo {b}) (_ : Set.IsPwo (support x)) (a + b) = ∅
    ext ⟨a1, a2⟩
    -- ⊢ (a1, a2) ∈ addAntidiagonal (_ : Set.IsPwo {b}) (_ : Set.IsPwo (support x)) ( …
    simp only [not_mem_empty, not_and, Set.mem_singleton_iff, Classical.not_not,
      mem_addAntidiagonal, Set.mem_setOf_eq, iff_false_iff]
    rintro rfl h2 h1
    -- ⊢ False
    rw [add_comm] at h1
    -- ⊢ False
    rw [← add_right_cancel h1] at hx
    -- ⊢ False
    exact h2 hx
    -- 🎉 no goals
  trans ∑ ij : Γ × Γ in {(b, a)}, (single b r).coeff ij.fst * x.coeff ij.snd
  -- ⊢ ∑ x_1 in addAntidiagonal (_ : Set.IsPwo {b}) (_ : Set.IsPwo (support x)) (a  …
  · apply sum_congr _ fun _ _ => rfl
    -- ⊢ addAntidiagonal (_ : Set.IsPwo {b}) (_ : Set.IsPwo (support x)) (a + b) = {( …
    ext ⟨a1, a2⟩
    -- ⊢ (a1, a2) ∈ addAntidiagonal (_ : Set.IsPwo {b}) (_ : Set.IsPwo (support x)) ( …
    simp only [Set.mem_singleton_iff, Prod.mk.inj_iff, mem_addAntidiagonal, mem_singleton,
      Set.mem_setOf_eq]
    constructor
    -- ⊢ a1 = b ∧ a2 ∈ support x ∧ a1 + a2 = a + b → a1 = b ∧ a2 = a
    · rintro ⟨rfl, _, h1⟩
      -- ⊢ a1 = a1 ∧ a2 = a
      rw [add_comm] at h1
      -- ⊢ a1 = a1 ∧ a2 = a
      refine' ⟨rfl, add_right_cancel h1⟩
      -- 🎉 no goals
    · rintro ⟨rfl, rfl⟩
      -- ⊢ a1 = a1 ∧ a2 ∈ support x ∧ a1 + a2 = a2 + a1
      exact ⟨rfl, by simp [hx], add_comm _ _⟩
      -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align hahn_series.single_mul_coeff_add HahnSeries.single_mul_coeff_add

theorem mul_single_coeff_add [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ}
    {b : Γ} : (x * single b r).coeff (a + b) = x.coeff a * r := by
  by_cases hr : r = 0
  -- ⊢ coeff (x * ↑(single b) r) (a + b) = coeff x a * r
  · simp [hr, mul_coeff]
    -- 🎉 no goals
  simp only [hr, smul_coeff, mul_coeff, support_single_of_ne, Ne.def, not_false_iff, smul_eq_mul]
  -- ⊢ ∑ x_1 in addAntidiagonal (_ : Set.IsPwo (support x)) (_ : Set.IsPwo {b}) (a  …
  by_cases hx : x.coeff a = 0
  -- ⊢ ∑ x_1 in addAntidiagonal (_ : Set.IsPwo (support x)) (_ : Set.IsPwo {b}) (a  …
  · simp only [hx, zero_mul]
    -- ⊢ ∑ x_1 in addAntidiagonal (_ : Set.IsPwo (support x)) (_ : Set.IsPwo {b}) (a  …
    rw [sum_congr _ fun _ _ => rfl, sum_empty]
    -- ⊢ addAntidiagonal (_ : Set.IsPwo (support x)) (_ : Set.IsPwo {b}) (a + b) = ∅
    ext ⟨a1, a2⟩
    -- ⊢ (a1, a2) ∈ addAntidiagonal (_ : Set.IsPwo (support x)) (_ : Set.IsPwo {b}) ( …
    simp only [not_mem_empty, not_and, Set.mem_singleton_iff, Classical.not_not,
      mem_addAntidiagonal, Set.mem_setOf_eq, iff_false_iff]
    rintro h2 rfl h1
    -- ⊢ False
    rw [← add_right_cancel h1] at hx
    -- ⊢ False
    exact h2 hx
    -- 🎉 no goals
  trans ∑ ij : Γ × Γ in {(a, b)}, x.coeff ij.fst * (single b r).coeff ij.snd
  -- ⊢ ∑ x_1 in addAntidiagonal (_ : Set.IsPwo (support x)) (_ : Set.IsPwo {b}) (a  …
  · apply sum_congr _ fun _ _ => rfl
    -- ⊢ addAntidiagonal (_ : Set.IsPwo (support x)) (_ : Set.IsPwo {b}) (a + b) = {( …
    ext ⟨a1, a2⟩
    -- ⊢ (a1, a2) ∈ addAntidiagonal (_ : Set.IsPwo (support x)) (_ : Set.IsPwo {b}) ( …
    simp only [Set.mem_singleton_iff, Prod.mk.inj_iff, mem_addAntidiagonal, mem_singleton,
      Set.mem_setOf_eq]
    constructor
    -- ⊢ a1 ∈ support x ∧ a2 = b ∧ a1 + a2 = a + b → a1 = a ∧ a2 = b
    · rintro ⟨_, rfl, h1⟩
      -- ⊢ a1 = a ∧ a2 = a2
      refine' ⟨add_right_cancel h1, rfl⟩
      -- 🎉 no goals
    · rintro ⟨rfl, rfl⟩
      -- ⊢ a1 ∈ support x ∧ a2 = a2 ∧ a1 + a2 = a1 + a2
      simp [hx]
      -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align hahn_series.mul_single_coeff_add HahnSeries.mul_single_coeff_add

@[simp]
theorem mul_single_zero_coeff [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ} :
    (x * single 0 r).coeff a = x.coeff a * r := by rw [← add_zero a, mul_single_coeff_add, add_zero]
                                                   -- 🎉 no goals
#align hahn_series.mul_single_zero_coeff HahnSeries.mul_single_zero_coeff

theorem single_zero_mul_coeff [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ} :
    ((single 0 r : HahnSeries Γ R) * x).coeff a = r * x.coeff a :=
  by rw [← add_zero a, single_mul_coeff_add, add_zero]
     -- 🎉 no goals
#align hahn_series.single_zero_mul_coeff HahnSeries.single_zero_mul_coeff

@[simp]
theorem single_zero_mul_eq_smul [Semiring R] {r : R} {x : HahnSeries Γ R} :
    single 0 r * x = r • x := by
  ext
  -- ⊢ coeff (↑(single 0) r * x) x✝ = coeff (r • x) x✝
  exact single_zero_mul_coeff
  -- 🎉 no goals
#align hahn_series.single_zero_mul_eq_smul HahnSeries.single_zero_mul_eq_smul

theorem support_mul_subset_add_support [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} :
    support (x * y) ⊆ support x + support y := by
  apply Set.Subset.trans (fun x hx => _) support_addAntidiagonal_subset_add
  · exact x.isPwo_support
    -- 🎉 no goals
  · exact y.isPwo_support
    -- 🎉 no goals
  intro x hx
  -- ⊢ x ∈ {a | Finset.Nonempty (addAntidiagonal (_ : Set.IsPwo (support x✝)) (_ :  …
  contrapose! hx
  -- ⊢ ¬x ∈ support (x✝ * y)
  simp only [not_nonempty_iff_eq_empty, Ne.def, Set.mem_setOf_eq] at hx
  -- ⊢ ¬x ∈ support (x✝ * y)
  simp [hx, mul_coeff]
  -- 🎉 no goals
#align hahn_series.support_mul_subset_add_support HahnSeries.support_mul_subset_add_support

theorem mul_coeff_order_add_order {Γ} [LinearOrderedCancelAddCommMonoid Γ]
    [NonUnitalNonAssocSemiring R] (x y : HahnSeries Γ R) :
    (x * y).coeff (x.order + y.order) = x.coeff x.order * y.coeff y.order := by
  by_cases hx : x = 0; · simp [hx, mul_coeff]
  -- ⊢ coeff (x * y) (order x + order y) = coeff x (order x) * coeff y (order y)
                         -- 🎉 no goals
  by_cases hy : y = 0; · simp [hy, mul_coeff]
  -- ⊢ coeff (x * y) (order x + order y) = coeff x (order x) * coeff y (order y)
                         -- 🎉 no goals
  rw [order_of_ne hx, order_of_ne hy, mul_coeff, Finset.addAntidiagonal_min_add_min,
    Finset.sum_singleton]
#align hahn_series.mul_coeff_order_add_order HahnSeries.mul_coeff_order_add_order

private theorem mul_assoc' [NonUnitalSemiring R] (x y z : HahnSeries Γ R) :
    x * y * z = x * (y * z) := by
  ext b
  -- ⊢ coeff (x * y * z) b = coeff (x * (y * z)) b
  rw [mul_coeff_left' (x.isPwo_support.add y.isPwo_support) support_mul_subset_add_support,
    mul_coeff_right' (y.isPwo_support.add z.isPwo_support) support_mul_subset_add_support]
  simp only [mul_coeff, add_coeff, sum_mul, mul_sum, sum_sigma']
  -- ⊢ ∑ x_1 in Finset.sigma (addAntidiagonal (_ : Set.IsPwo (support x + support y …
  refine' sum_bij_ne_zero (fun a _ _ => ⟨⟨a.2.1, a.2.2 + a.1.2⟩, ⟨a.2.2, a.1.2⟩⟩) _ _ _ _
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ H1 H2
    -- ⊢ (fun a x_1 x => { fst := (a.snd.fst, a.snd.snd + a.fst.snd), snd := (a.snd.s …
    simp only [and_true_iff, Set.image2_add, eq_self_iff_true, mem_addAntidiagonal, Ne.def,
      Set.image_prod, mem_sigma, Set.mem_setOf_eq] at H1 H2 ⊢
    obtain ⟨⟨H3, nz, rfl⟩, nx, ny, rfl⟩ := H1
    -- ⊢ (k ∈ support x ∧ l + j ∈ support y + support z ∧ k + (l + j) = k + l + j) ∧  …
    exact ⟨⟨nx, Set.add_mem_add ny nz, (add_assoc _ _ _).symm⟩, ny, nz⟩
    -- 🎉 no goals
  · rintro ⟨⟨i1, j1⟩, k1, l1⟩ ⟨⟨i2, j2⟩, k2, l2⟩ H1 H2 H3 H4 H5
    -- ⊢ { fst := (i1, j1), snd := (k1, l1) } = { fst := (i2, j2), snd := (k2, l2) }
    simp only [Set.image2_add, Prod.mk.inj_iff, mem_addAntidiagonal, Ne.def, Set.image_prod,
      mem_sigma, Set.mem_setOf_eq, heq_iff_eq] at H1 H3 H5
    obtain (⟨⟨rfl, _⟩, rfl, rfl⟩ : (k1 = k2 ∧ l1 + j1 = l2 + j2) ∧ l1 = l2 ∧ j1 = j2) :=
      by simpa using H5
    simp only [and_true_iff, Prod.mk.inj_iff, eq_self_iff_true, heq_iff_eq, ← H1.2.2.2, ← H3.2.2.2]
    -- 🎉 no goals
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ H1 H2
    -- ⊢ ∃ a h₁ h₂, { fst := (i, j), snd := (k, l) } = (fun a x_1 x => { fst := (a.sn …
    simp only [exists_prop, Set.image2_add, Prod.mk.inj_iff, mem_addAntidiagonal, Sigma.exists,
      Ne.def, Set.image_prod, mem_sigma, Set.mem_setOf_eq, heq_iff_eq, Prod.exists] at H1 H2 ⊢
    obtain ⟨⟨nx, H, rfl⟩, ny, nz, rfl⟩ := H1
    -- ⊢ ∃ a b a_1 b_1, ((a ∈ support x + support y ∧ b ∈ support z ∧ a + b = i + (k  …
    exact
      ⟨i + k, l, i, k, ⟨⟨Set.add_mem_add nx ny, nz, add_assoc _ _ _⟩ , nx, ny, rfl⟩,
        fun h => H2 <| by rw [←h, mul_assoc], rfl⟩
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ _ _
    -- ⊢ coeff x { fst := (i, j), snd := (k, l) }.snd.fst * coeff y { fst := (i, j),  …
    simp [mul_assoc]
    -- 🎉 no goals

instance [NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring (HahnSeries Γ R) :=
  { inferInstanceAs (AddCommMonoid (HahnSeries Γ R)),
    inferInstanceAs (Distrib (HahnSeries Γ R)) with
    zero := 0
    add := (· + ·)
    mul := (· * ·)
    zero_mul := fun _ => by
      ext
      -- ⊢ coeff (0 * x✝¹) x✝ = coeff 0 x✝
      simp [mul_coeff]
      -- 🎉 no goals
    mul_zero := fun _ => by
      ext
      -- ⊢ coeff (x✝¹ * 0) x✝ = coeff 0 x✝
      simp [mul_coeff] }
      -- 🎉 no goals

instance [NonUnitalSemiring R] : NonUnitalSemiring (HahnSeries Γ R) :=
  { inferInstanceAs (NonUnitalNonAssocSemiring (HahnSeries Γ R)) with
    zero := 0
    add := (· + ·)
    mul := (· * ·)
    mul_assoc := mul_assoc' }

instance [NonAssocSemiring R] : NonAssocSemiring (HahnSeries Γ R) :=
  { AddMonoidWithOne.unary,
    inferInstanceAs (NonUnitalNonAssocSemiring (HahnSeries Γ R)) with
    zero := 0
    one := 1
    add := (· + ·)
    mul := (· * ·)
    one_mul := fun x => by
      ext
      -- ⊢ coeff (1 * x) x✝ = coeff x x✝
      exact single_zero_mul_coeff.trans (one_mul _)
      -- 🎉 no goals
    mul_one := fun x => by
      ext
      -- ⊢ coeff (x * 1) x✝ = coeff x x✝
      exact mul_single_zero_coeff.trans (mul_one _) }
      -- 🎉 no goals

instance [Semiring R] : Semiring (HahnSeries Γ R) :=
  { inferInstanceAs (NonAssocSemiring (HahnSeries Γ R)),
    inferInstanceAs (NonUnitalSemiring (HahnSeries Γ R)) with
    zero := 0
    one := 1
    add := (· + ·)
    mul := (· * ·) }

instance [NonUnitalCommSemiring R] : NonUnitalCommSemiring (HahnSeries Γ R) :=
  { inferInstanceAs (NonUnitalSemiring (HahnSeries Γ R)) with
    mul_comm := fun x y => by
      ext
      -- ⊢ coeff (x * y) x✝ = coeff (y * x) x✝
      simp_rw [mul_coeff, mul_comm]
      -- ⊢ ∑ ij in addAntidiagonal (_ : Set.IsPwo (support x)) (_ : Set.IsPwo (support  …
      refine'
          sum_bij (fun a _ => a.swap) (fun a ha => _) (fun a _ => rfl)
            (fun _ _ _ _ => Prod.swap_inj.1) fun a ha => ⟨a.swap, _, a.swap_swap.symm⟩ <;>
        rwa [swap_mem_addAntidiagonal] }
        -- 🎉 no goals
        -- 🎉 no goals

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
    eq_zero_or_eq_zero_of_mul_eq_zero {x} {y} xy := by
      by_cases hx : x = 0
      -- ⊢ x = 0 ∨ y = 0
      · left
        -- ⊢ x = 0
        exact hx
        -- 🎉 no goals
      right
      -- ⊢ y = 0
      contrapose! xy
      -- ⊢ x * y ≠ 0
      rw [Ne, HahnSeries.ext_iff, Function.funext_iff, not_forall]
      -- ⊢ ∃ x_1, ¬coeff (x * y) x_1 = coeff 0 x_1
      refine' ⟨x.order + y.order, _⟩
      -- ⊢ ¬coeff (x * y) (order x + order y) = coeff 0 (order x + order y)
      rw [mul_coeff_order_add_order x y, zero_coeff, mul_eq_zero]
      -- ⊢ ¬(coeff x (order x) = 0 ∨ coeff y (order y) = 0)
      simp [coeff_order_ne_zero, hx, xy]
      -- 🎉 no goals

instance {Γ} [LinearOrderedCancelAddCommMonoid Γ] [Ring R] [IsDomain R] :
    IsDomain (HahnSeries Γ R) :=
  NoZeroDivisors.to_isDomain _

@[simp]
theorem order_mul {Γ} [LinearOrderedCancelAddCommMonoid Γ] [NonUnitalNonAssocSemiring R]
    [NoZeroDivisors R] {x y : HahnSeries Γ R} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * y).order = x.order + y.order := by
  apply le_antisymm
  -- ⊢ order (x * y) ≤ order x + order y
  · apply order_le_of_coeff_ne_zero
    -- ⊢ coeff (x * y) (order x + order y) ≠ 0
    rw [mul_coeff_order_add_order x y]
    -- ⊢ coeff x (order x) * coeff y (order y) ≠ 0
    exact mul_ne_zero (coeff_order_ne_zero hx) (coeff_order_ne_zero hy)
    -- 🎉 no goals
  · rw [order_of_ne hx, order_of_ne hy, order_of_ne (mul_ne_zero hx hy), ← Set.IsWf.min_add]
    -- ⊢ Set.IsWf.min (_ : Set.IsWf (support x + support y)) (_ : Set.Nonempty (suppo …
    exact Set.IsWf.min_le_min_of_subset support_mul_subset_add_support
    -- 🎉 no goals
#align hahn_series.order_mul HahnSeries.order_mul

@[simp]
theorem order_pow {Γ} [LinearOrderedCancelAddCommMonoid Γ] [Semiring R] [NoZeroDivisors R]
    (x : HahnSeries Γ R) (n : ℕ) : (x ^ n).order = n • x.order := by
  induction' n with h IH
  -- ⊢ order (x ^ Nat.zero) = Nat.zero • order x
  · simp
    -- 🎉 no goals
  rcases eq_or_ne x 0 with (rfl | hx)
  -- ⊢ order (0 ^ Nat.succ h) = Nat.succ h • order 0
  · simp
    -- 🎉 no goals
  rw [pow_succ', order_mul (pow_ne_zero _ hx) hx, succ_nsmul', IH]
  -- 🎉 no goals
#align hahn_series.order_pow HahnSeries.order_pow

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring R]

@[simp]
theorem single_mul_single {a b : Γ} {r s : R} :
    single a r * single b s = single (a + b) (r * s) := by
  ext x
  -- ⊢ coeff (↑(single a) r * ↑(single b) s) x = coeff (↑(single (a + b)) (r * s)) x
  by_cases h : x = a + b
  -- ⊢ coeff (↑(single a) r * ↑(single b) s) x = coeff (↑(single (a + b)) (r * s)) x
  · rw [h, mul_single_coeff_add]
    -- ⊢ coeff (↑(single a) r) a * s = coeff (↑(single (a + b)) (r * s)) (a + b)
    simp
    -- 🎉 no goals
  · rw [single_coeff_of_ne h, mul_coeff, sum_eq_zero]
    -- ⊢ ∀ (x_1 : Γ × Γ), x_1 ∈ addAntidiagonal (_ : Set.IsPwo (support (↑(single a)  …
    simp_rw [mem_addAntidiagonal]
    -- ⊢ ∀ (x_1 : Γ × Γ), x_1.fst ∈ support (↑(single a) r) ∧ x_1.snd ∈ support (↑(si …
    rintro ⟨y, z⟩ ⟨hy, hz, rfl⟩
    -- ⊢ coeff (↑(single a) r) (y, z).fst * coeff (↑(single b) s) (y, z).snd = 0
    rw [eq_of_mem_support_single hy, eq_of_mem_support_single hz] at h
    -- ⊢ coeff (↑(single a) r) (y, z).fst * coeff (↑(single b) s) (y, z).snd = 0
    exact (h rfl).elim
    -- 🎉 no goals
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
    -- ⊢ coeff (OneHom.toFun (↑{ toOneHom := { toFun := ↑(single 0), map_one' := (_ : …
    by_cases h : a = 0 <;> simp [h]
                     -- 🎉 no goals
    -- ⊢ coeff (OneHom.toFun (↑{ toOneHom := { toFun := ↑(single 0), map_one' := (_ : …
                           -- 🎉 no goals
                           -- 🎉 no goals
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
  -- ⊢ r = s
  rw [HahnSeries.ext_iff, Function.funext_iff] at rs
  -- ⊢ r = s
  have h := rs 0
  -- ⊢ r = s
  rwa [C_apply, single_coeff_same, C_apply, single_coeff_same] at h
  -- 🎉 no goals
#align hahn_series.C_injective HahnSeries.C_injective

theorem C_ne_zero {r : R} (h : r ≠ 0) : (C r : HahnSeries Γ R) ≠ 0 := by
  contrapose! h
  -- ⊢ r = 0
  rw [← C_zero] at h
  -- ⊢ r = 0
  exact C_injective h
  -- 🎉 no goals
#align hahn_series.C_ne_zero HahnSeries.C_ne_zero

theorem order_C {r : R} : order (C r : HahnSeries Γ R) = 0 := by
  by_cases h : r = 0
  -- ⊢ order (↑C r) = 0
  · rw [h, C_zero, order_zero]
    -- 🎉 no goals
  · exact order_single h
    -- 🎉 no goals
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
  -- ⊢ coeff (embDomain f (x * y)) g = coeff (embDomain f x * embDomain f y) g
  by_cases hg : g ∈ Set.range f
  -- ⊢ coeff (embDomain f (x * y)) g = coeff (embDomain f x * embDomain f y) g
  · obtain ⟨g, rfl⟩ := hg
    -- ⊢ coeff (embDomain f (x * y)) (↑f g) = coeff (embDomain f x * embDomain f y) ( …
    simp only [mul_coeff, embDomain_coeff]
    -- ⊢ ∑ ij in addAntidiagonal (_ : Set.IsPwo (support x)) (_ : Set.IsPwo (support  …
    trans
      ∑ ij in
        (addAntidiagonal x.isPwo_support y.isPwo_support g).map
          (Function.Embedding.prodMap f.toEmbedding f.toEmbedding),
        (embDomain f x).coeff ij.1 * (embDomain f y).coeff ij.2
    · simp
      -- 🎉 no goals
    apply sum_subset
    -- ⊢ Finset.map (Embedding.prodMap f.toEmbedding f.toEmbedding) (addAntidiagonal  …
    · rintro ⟨i, j⟩ hij
      -- ⊢ (i, j) ∈ addAntidiagonal (_ : Set.IsPwo (support (embDomain f x))) (_ : Set. …
      simp only [exists_prop, mem_map, Prod.mk.inj_iff, mem_addAntidiagonal,
        Function.Embedding.coe_prodMap, mem_support, Prod.exists] at hij
      obtain ⟨i, j, ⟨hx, hy, rfl⟩, rfl, rfl⟩ := hij
      -- ⊢ (↑f.toEmbedding i, ↑f.toEmbedding j) ∈ addAntidiagonal (_ : Set.IsPwo (suppo …
      simp [hx, hy, hf]
      -- 🎉 no goals
    · rintro ⟨_, _⟩ h1 h2
      -- ⊢ coeff (embDomain f x) (fst✝, snd✝).fst * coeff (embDomain f y) (fst✝, snd✝). …
      contrapose! h2
      -- ⊢ (fst✝, snd✝) ∈ Finset.map (Embedding.prodMap f.toEmbedding f.toEmbedding) (a …
      obtain ⟨i, _, rfl⟩ := support_embDomain_subset (ne_zero_and_ne_zero_of_mul h2).1
      -- ⊢ (↑f i, snd✝) ∈ Finset.map (Embedding.prodMap f.toEmbedding f.toEmbedding) (a …
      obtain ⟨j, _, rfl⟩ := support_embDomain_subset (ne_zero_and_ne_zero_of_mul h2).2
      -- ⊢ (↑f i, ↑f j) ∈ Finset.map (Embedding.prodMap f.toEmbedding f.toEmbedding) (a …
      simp only [exists_prop, mem_map, Prod.mk.inj_iff, mem_addAntidiagonal,
        Function.Embedding.coe_prodMap, mem_support, Prod.exists]
      simp only [mem_addAntidiagonal, embDomain_coeff, mem_support, ← hf,
        OrderEmbedding.eq_iff_eq] at h1
      exact ⟨i, j, h1, rfl⟩
      -- 🎉 no goals
  · rw [embDomain_notin_range hg, eq_comm]
    -- ⊢ coeff (embDomain f x * embDomain f y) g = 0
    contrapose! hg
    -- ⊢ g ∈ Set.range ↑f
    obtain ⟨_, _, hi, hj, rfl⟩ := support_mul_subset_add_support ((mem_support _ _).2 hg)
    -- ⊢ (fun x x_1 => x + x_1) w✝¹ w✝ ∈ Set.range ↑f
    obtain ⟨i, _, rfl⟩ := support_embDomain_subset hi
    -- ⊢ (fun x x_1 => x + x_1) (↑f i) w✝ ∈ Set.range ↑f
    obtain ⟨j, _, rfl⟩ := support_embDomain_subset hj
    -- ⊢ (fun x x_1 => x + x_1) (↑f i) (↑f j) ∈ Set.range ↑f
    refine' ⟨i + j, hf i j⟩
    -- 🎉 no goals
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
                             -- 🎉 no goals
#align hahn_series.emb_domain_ring_hom_C HahnSeries.embDomainRingHom_C

end Domain

section Algebra

variable [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]

instance : Algebra R (HahnSeries Γ A) where
  toRingHom := C.comp (algebraMap R A)
  smul_def' r x := by
    ext
    -- ⊢ coeff (r • x) x✝ = coeff (↑(RingHom.comp C (algebraMap R A)) r * x) x✝
    simp
    -- 🎉 no goals
    -- ⊢ coeff (↑(RingHom.comp C (algebraMap R A)) r * x) x✝ = coeff (x * ↑(RingHom.c …
  commutes' r x := by
    ext
    simp only [smul_coeff, single_zero_mul_eq_smul, RingHom.coe_comp, RingHom.toFun_eq_coe, C_apply,
    -- 🎉 no goals
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
      -- ⊢ ∃ x, ¬(x ∈ ⊥ ↔ x ∈ ⊤)
      obtain ⟨a, ha⟩ := exists_ne (0 : Γ)
      -- ⊢ ∃ x, ¬(x ∈ ⊥ ↔ x ∈ ⊤)
      refine' ⟨single a 1, _⟩
      -- ⊢ ¬(↑(single a) 1 ∈ ⊥ ↔ ↑(single a) 1 ∈ ⊤)
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true_iff, Algebra.mem_top]
      -- ⊢ ∀ (x : R), ¬↑(algebraMap R (HahnSeries Γ R)) x = ↑(single a) 1
      intro x
      -- ⊢ ¬↑(algebraMap R (HahnSeries Γ R)) x = ↑(single a) 1
      rw [HahnSeries.ext_iff, Function.funext_iff, not_forall]
      -- ⊢ ∃ x_1, ¬coeff (↑(algebraMap R (HahnSeries Γ R)) x) x_1 = coeff (↑(single a)  …
      refine' ⟨a, _⟩
      -- ⊢ ¬coeff (↑(algebraMap R (HahnSeries Γ R)) x) a = coeff (↑(single a) 1) a
      rw [single_coeff_same, algebraMap_apply, C_apply, single_coeff_of_ne ha]
      -- ⊢ ¬0 = 1
      exact zero_ne_one⟩⟩
      -- 🎉 no goals

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
  invFun f := ⟨fun n => PowerSeries.coeff R n f, (Nat.lt_wfRel.wf.isWf _).isPwo⟩
  left_inv f := by
    ext
    -- ⊢ coeff ((fun f => { coeff := fun n => ↑(PowerSeries.coeff R n) f, isPwo_suppo …
    simp
    -- 🎉 no goals
  right_inv f := by
    ext
    -- ⊢ ↑(PowerSeries.coeff R n✝) ((fun f => PowerSeries.mk f.coeff) ((fun f => { co …
    simp
    -- 🎉 no goals
  map_add' f g := by
    ext
    -- ⊢ ↑(PowerSeries.coeff R n✝) (Equiv.toFun { toFun := fun f => PowerSeries.mk f. …
    simp
    -- 🎉 no goals
    -- ⊢ ↑(PowerSeries.coeff R n) (Equiv.toFun { toFun := fun f => PowerSeries.mk f.c …
  map_mul' f g := by
    -- ⊢ ∑ ij in addAntidiagonal (_ : Set.IsPwo (support f)) (_ : Set.IsPwo (support  …
    ext n
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, mul_coeff, isPwo_support]
    classical
      refine' sum_filter_ne_zero.symm.trans ((sum_congr _ fun _ _ => rfl).trans sum_filter_ne_zero)
      ext m
      simp only [Nat.mem_antidiagonal, mem_addAntidiagonal, and_congr_left_iff, mem_filter,
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
          -- ⊢ ∀ {a b : ℕ}, ↑a ≤ ↑b ↔ a ≤ b
          exact Nat.cast_le⟩
          -- 🎉 no goals
        (toPowerSeries.symm x) :=
  rfl
#align hahn_series.of_power_series_apply HahnSeries.ofPowerSeries_apply

theorem ofPowerSeries_apply_coeff (x : PowerSeries R) (n : ℕ) :
    (ofPowerSeries Γ R x).coeff n = PowerSeries.coeff R n x := by simp [ofPowerSeries_apply]
                                                                  -- 🎉 no goals
#align hahn_series.of_power_series_apply_coeff HahnSeries.ofPowerSeries_apply_coeff

@[simp]
theorem ofPowerSeries_C (r : R) : ofPowerSeries Γ R (PowerSeries.C R r) = HahnSeries.C r := by
  ext n
  -- ⊢ coeff (↑(ofPowerSeries Γ R) (↑(PowerSeries.C R) r)) n = coeff (↑C r) n
  simp only [ofPowerSeries_apply, C, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, ne_eq,
    single_coeff]
  split_ifs with hn
  -- ⊢ coeff (embDomain { toEmbedding := { toFun := Nat.cast, inj' := (_ : Injectiv …
  · subst hn
    -- ⊢ coeff (embDomain { toEmbedding := { toFun := Nat.cast, inj' := (_ : Injectiv …
    convert @embDomain_coeff ℕ R _ _ Γ _ _ _ 0 <;> simp
    -- ⊢ 0 = ↑{ toEmbedding := { toFun := Nat.cast, inj' := (_ : Injective Nat.cast)  …
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
  · rw [embDomain_notin_image_support]
    -- ⊢ ¬n ∈ ↑{ toEmbedding := { toFun := Nat.cast, inj' := (_ : Injective Nat.cast) …
    simp only [not_exists, Set.mem_image, toPowerSeries_symm_apply_coeff, mem_support,
      PowerSeries.coeff_C]
    intro
    -- ⊢ ¬((if x✝ = 0 then r else 0) ≠ 0 ∧ ↑{ toEmbedding := { toFun := Nat.cast, inj …
    simp (config := { contextual := true }) [Ne.symm hn]
    -- 🎉 no goals
#align hahn_series.of_power_series_C HahnSeries.ofPowerSeries_C

@[simp]
theorem ofPowerSeries_X : ofPowerSeries Γ R PowerSeries.X = single 1 1 := by
  ext n
  -- ⊢ coeff (↑(ofPowerSeries Γ R) PowerSeries.X) n = coeff (↑(single 1) 1) n
  simp only [single_coeff, ofPowerSeries_apply, RingHom.coe_mk]
  -- ⊢ coeff (embDomain { toEmbedding := { toFun := Nat.cast, inj' := (_ : Injectiv …
  split_ifs with hn
  -- ⊢ coeff (embDomain { toEmbedding := { toFun := Nat.cast, inj' := (_ : Injectiv …
  · rw [hn]
    -- ⊢ coeff (embDomain { toEmbedding := { toFun := Nat.cast, inj' := (_ : Injectiv …
    convert @embDomain_coeff ℕ R _ _ Γ _ _ _ 1 <;> simp
    -- ⊢ 1 = ↑{ toEmbedding := { toFun := Nat.cast, inj' := (_ : Injective Nat.cast)  …
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
  · rw [embDomain_notin_image_support]
    -- ⊢ ¬n ∈ ↑{ toEmbedding := { toFun := Nat.cast, inj' := (_ : Injective Nat.cast) …
    simp only [not_exists, Set.mem_image, toPowerSeries_symm_apply_coeff, mem_support,
      PowerSeries.coeff_X]
    intro
    -- ⊢ ¬((if x✝ = 1 then 1 else 0) ≠ 0 ∧ ↑{ toEmbedding := { toFun := Nat.cast, inj …
    simp (config := { contextual := true }) [Ne.symm hn]
    -- 🎉 no goals
#align hahn_series.of_power_series_X HahnSeries.ofPowerSeries_X

@[simp]
theorem ofPowerSeries_X_pow {R} [CommSemiring R] (n : ℕ) :
    ofPowerSeries Γ R (PowerSeries.X ^ n) = single (n : Γ) 1 := by
  rw [RingHom.map_pow]
  -- ⊢ ↑(ofPowerSeries Γ R) PowerSeries.X ^ n = ↑(single ↑n) 1
  induction' n with n ih
  -- ⊢ ↑(ofPowerSeries Γ R) PowerSeries.X ^ Nat.zero = ↑(single ↑Nat.zero) 1
  · simp
    -- ⊢ 1 = ↑(single 0) 1
    rfl
    -- 🎉 no goals
  · rw [pow_succ, pow_succ, ih, ofPowerSeries_X, mul_comm, single_mul_single, one_mul,
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
  invFun f := ⟨(f : (σ →₀ ℕ) → R), Finsupp.isPwo _⟩
  left_inv f := by
    ext
    -- ⊢ coeff ((fun f => { coeff := f, isPwo_support' := (_ : Set.IsPwo (Function.su …
    simp
    -- 🎉 no goals
  right_inv f := by
    ext
    -- ⊢ ↑(MvPowerSeries.coeff R n✝) ((fun f => f.coeff) ((fun f => { coeff := f, isP …
    simp
    -- 🎉 no goals
  map_add' f g := by
    ext
    -- ⊢ ↑(MvPowerSeries.coeff R n✝) (Equiv.toFun { toFun := fun f => f.coeff, invFun …
    simp
    -- 🎉 no goals
    -- ⊢ ↑(MvPowerSeries.coeff R n) (Equiv.toFun { toFun := fun f => f.coeff, invFun  …
  map_mul' f g := by
    -- ⊢ ↑(MvPowerSeries.coeff R n) (f * g).coeff = ∑ x in Finsupp.antidiagonal n, ↑( …
    ext n
    simp only [MvPowerSeries.coeff_mul]
    classical
      change (f * g).coeff n = _
      simp_rw [mul_coeff]
      refine' sum_filter_ne_zero.symm.trans ((sum_congr _ fun _ _ => rfl).trans sum_filter_ne_zero)
      ext m
      simp only [and_congr_left_iff, mem_addAntidiagonal, mem_filter, mem_support,
        Finsupp.mem_antidiagonal]
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
      -- ⊢ ↑(PowerSeries.coeff A n) (Equiv.toFun src✝.toEquiv (↑(algebraMap R (HahnSeri …
      simp only [algebraMap_apply, PowerSeries.algebraMap_apply, C_apply,
        coeff_toPowerSeries]
      cases' n with n
      -- ⊢ ↑(PowerSeries.coeff A Nat.zero) (Equiv.toFun toPowerSeries.toEquiv (↑(single …
      · simp [PowerSeries.coeff_zero_eq_constantCoeff, single_coeff_same]
        -- 🎉 no goals
      · simp [n.succ_ne_zero, Ne.def, not_false_iff, single_coeff_of_ne]
        -- ⊢ 0 = ↑(PowerSeries.coeff A (Nat.succ n)) (↑(PowerSeries.C A) (↑(algebraMap R  …
        rw [PowerSeries.coeff_C, if_neg n.succ_ne_zero] }
        -- 🎉 no goals
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
                                                 -- 🎉 no goals
    (fun x y => by
      by_cases hx : x = 0
      -- ⊢ min ((fun x => if x = 0 then ⊤ else ↑(order x)) x) ((fun x => if x = 0 then  …
      · by_cases hy : y = 0 <;> · simp [hx, hy]
        -- ⊢ min ((fun x => if x = 0 then ⊤ else ↑(order x)) x) ((fun x => if x = 0 then  …
                                  -- 🎉 no goals
                                  -- 🎉 no goals
      · by_cases hy : y = 0
        -- ⊢ min ((fun x => if x = 0 then ⊤ else ↑(order x)) x) ((fun x => if x = 0 then  …
        · simp [hx, hy]
          -- 🎉 no goals
        · simp only [hx, hy, support_nonempty_iff, if_neg, not_false_iff, isWf_support]
          -- ⊢ min ↑(order x) ↑(order y) ≤ if x + y = 0 then ⊤ else ↑(order (x + y))
          by_cases hxy : x + y = 0
          -- ⊢ min ↑(order x) ↑(order y) ≤ if x + y = 0 then ⊤ else ↑(order (x + y))
          · simp [hxy]
            -- 🎉 no goals
          rw [if_neg hxy, ← WithTop.coe_min, WithTop.coe_le_coe]
          -- ⊢ min (order x) (order y) ≤ order (x + y)
          exact min_order_le_order_add hxy)
          -- 🎉 no goals
    fun x y => by
    by_cases hx : x = 0
    -- ⊢ (fun x => if x = 0 then ⊤ else ↑(order x)) (x * y) = (fun x => if x = 0 then …
    · simp [hx]
      -- 🎉 no goals
    by_cases hy : y = 0
    -- ⊢ (fun x => if x = 0 then ⊤ else ↑(order x)) (x * y) = (fun x => if x = 0 then …
    · simp [hy]
      -- 🎉 no goals
    dsimp only
    -- ⊢ (if x * y = 0 then ⊤ else ↑(order (x * y))) = (if x = 0 then ⊤ else ↑(order  …
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
  -- ⊢ order x ≤ g
  exact order_le_of_coeff_ne_zero h
  -- 🎉 no goals
#align hahn_series.add_val_le_of_coeff_ne_zero HahnSeries.addVal_le_of_coeff_ne_zero

end Valuation

theorem isPwo_iUnion_support_powers [LinearOrderedCancelAddCommMonoid Γ] [Ring R] [IsDomain R]
    {x : HahnSeries Γ R} (hx : 0 < addVal Γ R x) : (⋃ n : ℕ, (x ^ n).support).IsPwo := by
  apply (x.isWf_support.isPwo.addSubmonoid_closure _).mono _
  -- ⊢ ∀ (x_1 : Γ), x_1 ∈ support x → 0 ≤ x_1
  · exact fun g hg => WithTop.coe_le_coe.1 (le_trans (le_of_lt hx) (addVal_le_of_coeff_ne_zero hg))
    -- 🎉 no goals
  refine' Set.iUnion_subset fun n => _
  -- ⊢ support (x ^ n) ⊆ ↑(AddSubmonoid.closure (support x))
  induction' n with n ih <;> intro g hn
  -- ⊢ support (x ^ Nat.zero) ⊆ ↑(AddSubmonoid.closure (support x))
                             -- ⊢ g ∈ ↑(AddSubmonoid.closure (support x))
                             -- ⊢ g ∈ ↑(AddSubmonoid.closure (support x))
  · simp only [Nat.zero_eq, pow_zero, support_one, Set.mem_singleton_iff] at hn
    -- ⊢ g ∈ ↑(AddSubmonoid.closure (support x))
    rw [hn, SetLike.mem_coe]
    -- ⊢ 0 ∈ AddSubmonoid.closure (support x)
    exact AddSubmonoid.zero_mem _
    -- 🎉 no goals
  · obtain ⟨i, j, hi, hj, rfl⟩ := support_mul_subset_add_support hn
    -- ⊢ (fun x x_1 => x + x_1) i j ∈ ↑(AddSubmonoid.closure (support x))
    exact SetLike.mem_coe.2 (AddSubmonoid.add_mem _ (AddSubmonoid.subset_closure hi) (ih hj))
    -- 🎉 no goals
#align hahn_series.is_pwo_Union_support_powers HahnSeries.isPwo_iUnion_support_powers

section

variable (Γ) (R) [PartialOrder Γ] [AddCommMonoid R]

/-- An infinite family of Hahn series which has a formal coefficient-wise sum.
  The requirements for this are that the union of the supports of the series is well-founded,
  and that only finitely many series are nonzero at any given coefficient. -/
structure SummableFamily (α : Type*) where
  toFun : α → HahnSeries Γ R
  isPwo_iUnion_support' : Set.IsPwo (⋃ a : α, (toFun a).support)
  finite_co_support' : ∀ g : Γ, { a | (toFun a).coeff g ≠ 0 }.Finite
#align hahn_series.summable_family HahnSeries.SummableFamily

end

namespace SummableFamily

section AddCommMonoid

variable [PartialOrder Γ] [AddCommMonoid R] {α : Type*}

instance : FunLike (SummableFamily Γ R α) α fun _ => HahnSeries Γ R where
  coe := toFun
  coe_injective' | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

theorem isPwo_iUnion_support (s : SummableFamily Γ R α) : Set.IsPwo (⋃ a : α, (s a).support) :=
  s.isPwo_iUnion_support'
#align hahn_series.summable_family.is_pwo_Union_support HahnSeries.SummableFamily.isPwo_iUnion_support

theorem finite_co_support (s : SummableFamily Γ R α) (g : Γ) :
    (Function.support fun a => (s a).coeff g).Finite :=
  s.finite_co_support' g
#align hahn_series.summable_family.finite_co_support HahnSeries.SummableFamily.finite_co_support

theorem coe_injective : @Function.Injective (SummableFamily Γ R α) (α → HahnSeries Γ R) (⇑) :=
  FunLike.coe_injective
#align hahn_series.summable_family.coe_injective HahnSeries.SummableFamily.coe_injective

@[ext]
theorem ext {s t : SummableFamily Γ R α} (h : ∀ a : α, s a = t a) : s = t :=
  FunLike.ext s t h
#align hahn_series.summable_family.ext HahnSeries.SummableFamily.ext

instance : Add (SummableFamily Γ R α) :=
  ⟨fun x y =>
    { toFun := x + y
      isPwo_iUnion_support' :=
        (x.isPwo_iUnion_support.union y.isPwo_iUnion_support).mono
          (by
            rw [← Set.iUnion_union_distrib]
            -- ⊢ ⋃ (a : α), support ((↑x + ↑y) a) ⊆ ⋃ (i : α), support (↑x i) ∪ support (↑y i)
            exact Set.iUnion_mono fun a => support_add_subset)
            -- 🎉 no goals
      finite_co_support' := fun g =>
        ((x.finite_co_support g).union (y.finite_co_support g)).subset
          (by
            intro a ha
            -- ⊢ a ∈ (Function.support fun a => coeff (↑x a) g) ∪ Function.support fun a => c …
            change (x a).coeff g + (y a).coeff g ≠ 0 at ha
            -- ⊢ a ∈ (Function.support fun a => coeff (↑x a) g) ∪ Function.support fun a => c …
            rw [Set.mem_union, Function.mem_support, Function.mem_support]
            -- ⊢ coeff (↑x a) g ≠ 0 ∨ coeff (↑y a) g ≠ 0
            contrapose! ha
            -- ⊢ coeff (↑x a) g + coeff (↑y a) g = 0
            rw [ha.1, ha.2, add_zero]) }⟩
            -- 🎉 no goals

instance : Zero (SummableFamily Γ R α) :=
  ⟨⟨0, by simp, by simp⟩⟩
          -- 🎉 no goals
                   -- 🎉 no goals

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
    -- ⊢ coeff (↑(0 + s) a✝) x✝ = coeff (↑s a✝) x✝
    apply zero_add
    -- 🎉 no goals
  add_zero s := by
    ext
    -- ⊢ coeff (↑(s + 0) a✝) x✝ = coeff (↑s a✝) x✝
    apply add_zero
    -- 🎉 no goals
  add_comm s t := by
    -- ⊢ coeff (↑(r + s + t) a✝) x✝ = coeff (↑(r + (s + t)) a✝) x✝
    ext
    -- 🎉 no goals
    -- ⊢ coeff (↑(s + t) a✝) x✝ = coeff (↑(t + s) a✝) x✝
    apply add_comm
    -- 🎉 no goals
  add_assoc r s t := by
    ext
    apply add_assoc

/-- The infinite sum of a `SummableFamily` of Hahn series. -/
def hsum (s : SummableFamily Γ R α) : HahnSeries Γ R where
  coeff g := ∑ᶠ i, (s i).coeff g
  isPwo_support' :=
    s.isPwo_iUnion_support.mono fun g => by
      contrapose
      -- ⊢ ¬g ∈ ⋃ (a : α), support (↑s a) → ¬g ∈ Function.support fun g => ∑ᶠ (i : α),  …
      rw [Set.mem_iUnion, not_exists, Function.mem_support, Classical.not_not]
      -- ⊢ (∀ (x : α), ¬g ∈ support (↑s x)) → ∑ᶠ (i : α), coeff (↑s i) g = 0
      simp_rw [mem_support, Classical.not_not]
      -- ⊢ (∀ (x : α), coeff (↑s x) g = 0) → ∑ᶠ (i : α), coeff (↑s i) g = 0
      intro h
      -- ⊢ ∑ᶠ (i : α), coeff (↑s i) g = 0
      rw [finsum_congr h, finsum_zero]
      -- 🎉 no goals
#align hahn_series.summable_family.hsum HahnSeries.SummableFamily.hsum

@[simp]
theorem hsum_coeff {s : SummableFamily Γ R α} {g : Γ} : s.hsum.coeff g = ∑ᶠ i, (s i).coeff g :=
  rfl
#align hahn_series.summable_family.hsum_coeff HahnSeries.SummableFamily.hsum_coeff

theorem support_hsum_subset {s : SummableFamily Γ R α} : s.hsum.support ⊆ ⋃ a : α, (s a).support :=
  fun g hg => by
  rw [mem_support, hsum_coeff, finsum_eq_sum _ (s.finite_co_support _)] at hg
  -- ⊢ g ∈ ⋃ (a : α), support (↑s a)
  obtain ⟨a, _, h2⟩ := exists_ne_zero_of_sum_ne_zero hg
  -- ⊢ g ∈ ⋃ (a : α), support (↑s a)
  rw [Set.mem_iUnion]
  -- ⊢ ∃ i, g ∈ support (↑s i)
  exact ⟨a, h2⟩
  -- 🎉 no goals
#align hahn_series.summable_family.support_hsum_subset HahnSeries.SummableFamily.support_hsum_subset

@[simp]
theorem hsum_add {s t : SummableFamily Γ R α} : (s + t).hsum = s.hsum + t.hsum := by
  ext g
  -- ⊢ coeff (hsum (s + t)) g = coeff (hsum s + hsum t) g
  simp only [hsum_coeff, add_coeff, add_apply]
  -- ⊢ ∑ᶠ (i : α), (coeff (↑s i) g + coeff (↑t i) g) = ∑ᶠ (i : α), coeff (↑s i) g + …
  exact finsum_add_distrib (s.finite_co_support _) (t.finite_co_support _)
  -- 🎉 no goals
#align hahn_series.summable_family.hsum_add HahnSeries.SummableFamily.hsum_add

end AddCommMonoid

section AddCommGroup

variable [PartialOrder Γ] [AddCommGroup R] {α : Type*} {s t : SummableFamily Γ R α} {a : α}

instance : AddCommGroup (SummableFamily Γ R α) :=
  { inferInstanceAs (AddCommMonoid (SummableFamily Γ R α)) with
    neg := fun s =>
      { toFun := fun a => -s a
        isPwo_iUnion_support' := by
          simp_rw [support_neg]
          -- ⊢ Set.IsPwo (⋃ (a : α), support (↑s a))
          exact s.isPwo_iUnion_support'
          -- 🎉 no goals
        finite_co_support' := fun g => by
          simp only [neg_coeff', Pi.neg_apply, Ne.def, neg_eq_zero]
          -- ⊢ Set.Finite {a | ¬coeff (↑s a) g = 0}
          exact s.finite_co_support g }
          -- 🎉 no goals
    add_left_neg := fun a => by
      ext
      -- ⊢ coeff (↑(-a + a) a✝) x✝ = coeff (↑0 a✝) x✝
      apply add_left_neg }
      -- 🎉 no goals

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

instance : SMul (HahnSeries Γ R) (SummableFamily Γ R α)
    where smul x s :=
    { toFun := fun a => x * s a
      isPwo_iUnion_support' := by
        apply (x.isPwo_support.add s.isPwo_iUnion_support).mono
        -- ⊢ ⋃ (a : α), support ((fun a => x * ↑s a) a) ⊆ support x + ⋃ (a : α), support  …
        refine' Set.Subset.trans (Set.iUnion_mono fun a => support_mul_subset_add_support) _
        -- ⊢ ⋃ (i : α), support x + support (↑s i) ⊆ support x + ⋃ (a : α), support (↑s a)
        intro g
        -- ⊢ g ∈ ⋃ (i : α), support x + support (↑s i) → g ∈ support x + ⋃ (a : α), suppo …
        simp only [Set.mem_iUnion, exists_imp]
        -- ⊢ ∀ (x_1 : α), g ∈ support x + support (↑s x_1) → g ∈ support x + ⋃ (a : α), s …
        exact fun a ha => (Set.add_subset_add (Set.Subset.refl _) (Set.subset_iUnion _ a)) ha
        -- 🎉 no goals
      finite_co_support' := fun g => by
        refine'
          ((addAntidiagonal x.isPwo_support s.isPwo_iUnion_support g).finite_toSet.biUnion'
                fun ij _ => _).subset
            fun a ha => _
        · exact fun ij _ => Function.support fun a => (s a).coeff ij.2
          -- 🎉 no goals
        · apply s.finite_co_support
          -- 🎉 no goals
        · obtain ⟨i, j, hi, hj, rfl⟩ := support_mul_subset_add_support ha
          -- ⊢ a ∈ ⋃ (i_1 : Γ × Γ) (_ : i_1 ∈ ↑(addAntidiagonal (_ : Set.IsPwo (support x)) …
          simp only [exists_prop, Set.mem_iUnion, mem_addAntidiagonal, mul_coeff, mem_support,
            isPwo_support, Prod.exists]
          exact ⟨i, j, mem_coe.2 (mem_addAntidiagonal.2 ⟨hi, Set.mem_iUnion.2 ⟨a, hj⟩, rfl⟩), hj⟩ }
          -- 🎉 no goals

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
  -- ⊢ coeff (hsum (x • s)) g = coeff (x * hsum s) g
  simp only [mul_coeff, hsum_coeff, smul_apply]
  -- ⊢ ∑ᶠ (i : α), ∑ ij in addAntidiagonal (_ : Set.IsPwo (support x)) (_ : Set.IsP …
  refine'
    (Eq.trans (finsum_congr fun a => _)
          (finsum_sum_comm (addAntidiagonal x.isPwo_support s.isPwo_iUnion_support g)
            (fun i ij => x.coeff (Prod.fst ij) * (s i).coeff ij.snd) _)).trans
      _
  · refine' sum_subset (addAntidiagonal_mono_right
      (Set.subset_iUnion (fun j => support (toFun s j)) a)) _
    rintro ⟨i, j⟩ hU ha
    -- ⊢ coeff x (i, j).fst * coeff (↑s a) (i, j).snd = 0
    rw [mem_addAntidiagonal] at *
    -- ⊢ coeff x (i, j).fst * coeff (↑s a) (i, j).snd = 0
    rw [Classical.not_not.1 fun con => ha ⟨hU.1, con, hU.2.2⟩, mul_zero]
    -- 🎉 no goals
  · rintro ⟨i, j⟩ _
    -- ⊢ Set.Finite (Function.support fun a => (fun i ij => coeff x ij.fst * coeff (↑ …
    refine' (s.finite_co_support j).subset _
    -- ⊢ (Function.support fun a => (fun i ij => coeff x ij.fst * coeff (↑s i) ij.snd …
    simp_rw [Function.support_subset_iff', Function.mem_support, Classical.not_not]
    -- ⊢ ∀ (x_1 : α), coeff (↑s x_1) j = 0 → coeff x i * coeff (↑s x_1) j = 0
    intro a ha
    -- ⊢ coeff x i * coeff (↑s a) j = 0
    rw [ha, mul_zero]
    -- 🎉 no goals
  · refine' (sum_congr rfl _).trans (sum_subset (addAntidiagonal_mono_right _) _).symm
    · rintro ⟨i, j⟩ _
      -- ⊢ ∑ᶠ (a : α), coeff x (i, j).fst * coeff (↑s a) (i, j).snd = coeff x (i, j).fs …
      rw [mul_finsum]
      -- ⊢ Set.Finite (Function.support fun i_1 => coeff (↑s i_1) (i, j).snd)
      apply s.finite_co_support
      -- 🎉 no goals
    · intro x hx
      -- ⊢ x ∈ ⋃ (a : α), support (↑s a)
      simp only [Set.mem_iUnion, Ne.def, mem_support]
      -- ⊢ ∃ i, ¬coeff (↑s i) x = 0
      contrapose! hx
      -- ⊢ ¬x ∈ support (hsum s)
      simp [hx]
      -- 🎉 no goals
    · rintro ⟨i, j⟩ hU ha
      -- ⊢ coeff x (i, j).fst * ∑ᶠ (i_1 : α), coeff (↑s i_1) (i, j).snd = 0
      rw [mem_addAntidiagonal] at *
      -- ⊢ coeff x (i, j).fst * ∑ᶠ (i_1 : α), coeff (↑s i_1) (i, j).snd = 0
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
  -- 🎉 no goals
#align hahn_series.summable_family.hsum_sub HahnSeries.SummableFamily.hsum_sub

end Semiring

section OfFinsupp

variable [PartialOrder Γ] [AddCommMonoid R] {α : Type*}

/-- A family with only finitely many nonzero elements is summable. -/
def ofFinsupp (f : α →₀ HahnSeries Γ R) : SummableFamily Γ R α where
  toFun := f
  isPwo_iUnion_support' := by
    apply (f.support.isPwo_bUnion.2 fun a _ => (f a).isPwo_support).mono
    -- ⊢ ⋃ (a : α), support (↑f a) ⊆ ⋃ (i : α) (_ : i ∈ f.support), support (↑f i)
    refine' Set.iUnion_subset_iff.2 fun a g hg => _
    -- ⊢ g ∈ ⋃ (i : α) (_ : i ∈ f.support), support (↑f i)
    have haf : a ∈ f.support := by
      rw [Finsupp.mem_support_iff, ← support_nonempty_iff]
      exact ⟨g, hg⟩
    exact Set.mem_biUnion haf hg
    -- 🎉 no goals
  finite_co_support' g := by
    refine' f.support.finite_toSet.subset fun a ha => _
    -- ⊢ a ∈ ↑f.support
    simp only [coeff.addMonoidHom_apply, mem_coe, Finsupp.mem_support_iff, Ne.def,
      Function.mem_support]
    contrapose! ha
    -- ⊢ ¬a ∈ {a | coeff (↑f a) g ≠ 0}
    simp [ha]
    -- 🎉 no goals
#align hahn_series.summable_family.of_finsupp HahnSeries.SummableFamily.ofFinsupp

@[simp]
theorem coe_ofFinsupp {f : α →₀ HahnSeries Γ R} : ⇑(SummableFamily.ofFinsupp f) = f :=
  rfl
#align hahn_series.summable_family.coe_of_finsupp HahnSeries.SummableFamily.coe_ofFinsupp

@[simp]
theorem hsum_ofFinsupp {f : α →₀ HahnSeries Γ R} : (ofFinsupp f).hsum = f.sum fun _ => id := by
  ext g
  -- ⊢ coeff (hsum (ofFinsupp f)) g = coeff (Finsupp.sum f fun x => id) g
  simp only [hsum_coeff, coe_ofFinsupp, Finsupp.sum, Ne.def]
  -- ⊢ ∑ᶠ (i : α), coeff (↑f i) g = coeff (∑ x in f.support, id (↑f x)) g
  simp_rw [← coeff.addMonoidHom_apply, id.def]
  -- ⊢ ∑ᶠ (i : α), ↑(coeff.addMonoidHom g) (↑f i) = ↑(coeff.addMonoidHom g) (∑ x in …
  rw [map_sum, finsum_eq_sum_of_support_subset]
  -- ⊢ (Function.support fun i => ↑(coeff.addMonoidHom g) (↑f i)) ⊆ ↑f.support
  intro x h
  -- ⊢ x ∈ ↑f.support
  simp only [coeff.addMonoidHom_apply, mem_coe, Finsupp.mem_support_iff, Ne.def]
  -- ⊢ ¬↑f x = 0
  contrapose! h
  -- ⊢ ¬x ∈ Function.support fun i => ↑(coeff.addMonoidHom g) (↑f i)
  simp [h]
  -- 🎉 no goals
#align hahn_series.summable_family.hsum_of_finsupp HahnSeries.SummableFamily.hsum_ofFinsupp

end OfFinsupp

section EmbDomain

variable [PartialOrder Γ] [AddCommMonoid R] {α β : Type*}

/-- A summable family can be reindexed by an embedding without changing its sum. -/
def embDomain (s : SummableFamily Γ R α) (f : α ↪ β) : SummableFamily Γ R β where
  toFun b := if h : b ∈ Set.range f then s (Classical.choose h) else 0
  isPwo_iUnion_support' := by
    refine' s.isPwo_iUnion_support.mono (Set.iUnion_subset fun b g h => _)
    -- ⊢ g ∈ ⋃ (a : α), support (↑s a)
    by_cases hb : b ∈ Set.range f
    -- ⊢ g ∈ ⋃ (a : α), support (↑s a)
    · dsimp only at h
      -- ⊢ g ∈ ⋃ (a : α), support (↑s a)
      rw [dif_pos hb] at h
      -- ⊢ g ∈ ⋃ (a : α), support (↑s a)
      exact Set.mem_iUnion.2 ⟨Classical.choose hb, h⟩
      -- 🎉 no goals
    · contrapose! h
      -- ⊢ ¬g ∈ support (if h : b ∈ Set.range ↑f then ↑s (Classical.choose (_ : b ∈ Set …
      rw [dif_neg hb]
      -- ⊢ ¬g ∈ support 0
      simp
      -- 🎉 no goals
  finite_co_support' g :=
    ((s.finite_co_support g).image f).subset
      (by
        intro b h
        -- ⊢ b ∈ ↑f '' Function.support fun a => coeff (↑s a) g
        by_cases hb : b ∈ Set.range f
        -- ⊢ b ∈ ↑f '' Function.support fun a => coeff (↑s a) g
        · simp only [Ne.def, Set.mem_setOf_eq, dif_pos hb] at h
          -- ⊢ b ∈ ↑f '' Function.support fun a => coeff (↑s a) g
          exact ⟨Classical.choose hb, h, Classical.choose_spec hb⟩
          -- 🎉 no goals
        · contrapose! h
          -- ⊢ ¬b ∈ {a | coeff (if h : a ∈ Set.range ↑f then ↑s (Classical.choose (_ : a ∈  …
          simp only [Ne.def, Set.mem_setOf_eq, dif_neg hb, Classical.not_not, zero_coeff])
          -- 🎉 no goals
#align hahn_series.summable_family.emb_domain HahnSeries.SummableFamily.embDomain

variable (s : SummableFamily Γ R α) (f : α ↪ β) {a : α} {b : β}

theorem embDomain_apply :
    s.embDomain f b = if h : b ∈ Set.range f then s (Classical.choose h) else 0 :=
  rfl
#align hahn_series.summable_family.emb_domain_apply HahnSeries.SummableFamily.embDomain_apply

@[simp]
theorem embDomain_image : s.embDomain f (f a) = s a := by
  rw [embDomain_apply, dif_pos (Set.mem_range_self a)]
  -- ⊢ ↑s (Classical.choose (_ : ↑f a ∈ Set.range ↑f)) = ↑s a
  exact congr rfl (f.injective (Classical.choose_spec (Set.mem_range_self a)))
  -- 🎉 no goals
#align hahn_series.summable_family.emb_domain_image HahnSeries.SummableFamily.embDomain_image

@[simp]
theorem embDomain_notin_range (h : b ∉ Set.range f) : s.embDomain f b = 0 := by
  rw [embDomain_apply, dif_neg h]
  -- 🎉 no goals
#align hahn_series.summable_family.emb_domain_notin_range HahnSeries.SummableFamily.embDomain_notin_range

@[simp]
theorem hsum_embDomain : (s.embDomain f).hsum = s.hsum := by
  ext g
  -- ⊢ coeff (hsum (embDomain s f)) g = coeff (hsum s) g
  simp only [hsum_coeff, embDomain_apply, apply_dite HahnSeries.coeff, dite_apply, zero_coeff]
  -- ⊢ (∑ᶠ (i : β), if h : i ∈ Set.range ↑f then coeff (↑s (Classical.choose (_ : i …
  exact finsum_emb_domain f fun a => (s a).coeff g
  -- 🎉 no goals
#align hahn_series.summable_family.hsum_emb_domain HahnSeries.SummableFamily.hsum_embDomain

end EmbDomain

section powers

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R] [IsDomain R]

/-- The powers of an element of positive valuation form a summable family. -/
def powers (x : HahnSeries Γ R) (hx : 0 < addVal Γ R x) : SummableFamily Γ R ℕ where
  toFun n := x ^ n
  isPwo_iUnion_support' := isPwo_iUnion_support_powers hx
  finite_co_support' g := by
    have hpwo := isPwo_iUnion_support_powers hx
    -- ⊢ Set.Finite {a | coeff ((fun n => x ^ n) a) g ≠ 0}
    by_cases hg : g ∈ ⋃ n : ℕ, { g | (x ^ n).coeff g ≠ 0 }
    -- ⊢ Set.Finite {a | coeff ((fun n => x ^ n) a) g ≠ 0}
    swap; · exact Set.finite_empty.subset fun n hn => hg (Set.mem_iUnion.2 ⟨n, hn⟩)
    -- ⊢ Set.Finite {a | coeff ((fun n => x ^ n) a) g ≠ 0}
            -- 🎉 no goals
    apply hpwo.isWf.induction hg
    -- ⊢ ∀ (y : Γ), y ∈ ⋃ (n : ℕ), support (x ^ n) → (∀ (z : Γ), z ∈ ⋃ (n : ℕ), suppo …
    intro y ys hy
    -- ⊢ Set.Finite {a | coeff ((fun n => x ^ n) a) y ≠ 0}
    refine'
      ((((addAntidiagonal x.isPwo_support hpwo y).finite_toSet.biUnion fun ij hij =>
                    hy ij.snd _ _).image
                Nat.succ).union
            (Set.finite_singleton 0)).subset
        _
    · exact (mem_addAntidiagonal.1 (mem_coe.1 hij)).2.1
      -- 🎉 no goals
    · obtain ⟨hi, _, rfl⟩ := mem_addAntidiagonal.1 (mem_coe.1 hij)
      -- ⊢ ij.snd < ij.fst + ij.snd
      rw [← zero_add ij.snd, ← add_assoc, add_zero]
      -- ⊢ 0 + ij.snd < ij.fst + ij.snd
      exact
        add_lt_add_right (WithTop.coe_lt_coe.1 (lt_of_lt_of_le hx (addVal_le_of_coeff_ne_zero hi)))
          _
    · rintro (_ | n) hn
      -- ⊢ Nat.zero ∈ (Nat.succ '' ⋃ (i : Γ × Γ) (_ : i ∈ ↑(addAntidiagonal (_ : Set.Is …
      · exact Set.mem_union_right _ (Set.mem_singleton 0)
        -- 🎉 no goals
      · obtain ⟨i, j, hi, hj, rfl⟩ := support_mul_subset_add_support hn
        -- ⊢ Nat.succ n ∈ (Nat.succ '' ⋃ (i_1 : Γ × Γ) (_ : i_1 ∈ ↑(addAntidiagonal (_ :  …
        refine' Set.mem_union_left _ ⟨n, Set.mem_iUnion.2 ⟨⟨i, j⟩, Set.mem_iUnion.2 ⟨_, hj⟩⟩, rfl⟩
        -- ⊢ (i, j) ∈ ↑(addAntidiagonal (_ : Set.IsPwo (support x)) hpwo ((fun x x_1 => x …
        simp only [and_true_iff, Set.mem_iUnion, mem_addAntidiagonal, mem_coe, eq_self_iff_true,
          Ne.def, mem_support, Set.mem_setOf_eq]
        exact ⟨hi, n, hj⟩
        -- 🎉 no goals
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
  -- ⊢ ∀ (a : ℕ), ↑(embDomain (x • powers x hx) { toFun := Nat.succ, inj' := Nat.su …
  rintro (_ | n)
  -- ⊢ ↑(embDomain (x • powers x hx) { toFun := Nat.succ, inj' := Nat.succ_injectiv …
  · rw [embDomain_notin_range, sub_apply, coe_powers, pow_zero, coe_ofFinsupp,
      Finsupp.single_eq_same, sub_self]
    rw [Set.mem_range, not_exists]
    -- ⊢ ∀ (x : ℕ), ¬↑{ toFun := Nat.succ, inj' := Nat.succ_injective } x = Nat.zero
    exact Nat.succ_ne_zero
    -- 🎉 no goals
  · refine' Eq.trans (embDomain_image _ ⟨Nat.succ, Nat.succ_injective⟩) _
    -- ⊢ ↑(x • powers x hx) n = ↑(powers x hx - ofFinsupp (Finsupp.single 0 1)) (Nat. …
    simp only [pow_succ, coe_powers, coe_sub, smul_apply, coe_ofFinsupp, Pi.sub_apply]
    -- ⊢ x * x ^ n = x * x ^ n - ↑(Finsupp.single 0 1) (Nat.succ n)
    rw [Finsupp.single_eq_of_ne n.succ_ne_zero.symm, sub_zero]
    -- 🎉 no goals
#align hahn_series.summable_family.emb_domain_succ_smul_powers HahnSeries.SummableFamily.embDomain_succ_smul_powers

theorem one_sub_self_mul_hsum_powers : (1 - x) * (powers x hx).hsum = 1 := by
  rw [← hsum_smul, sub_smul 1 x (powers x hx), one_smul, hsum_sub, ←
    hsum_embDomain (x • powers x hx) ⟨Nat.succ, Nat.succ_injective⟩, embDomain_succ_smul_powers]
  simp
  -- 🎉 no goals
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
  -- ⊢ 0 < ↑(addVal Γ R) (1 - ↑C r * ↑(single (-order x)) 1 * x)
  have x0 : x ≠ 0 := ne_zero_of_coeff_ne_zero (right_ne_zero_of_mul_eq_one hr)
  -- ⊢ 0 < ↑(addVal Γ R) (1 - ↑C r * ↑(single (-order x)) 1 * x)
  refine' lt_of_le_of_ne ((addVal Γ R).map_le_sub (ge_of_eq (addVal Γ R).map_one) _) _
  -- ⊢ 0 ≤ ↑(addVal Γ R) (↑C r * ↑(single (-order x)) 1 * x)
  · simp only [AddValuation.map_mul]
    -- ⊢ 0 ≤ ↑(addVal Γ R) (↑C r) + ↑(addVal Γ R) (↑(single (-order x)) 1) + ↑(addVal …
    rw [addVal_apply_of_ne x0, addVal_apply_of_ne (single_ne_zero h10), addVal_apply_of_ne _,
      order_C, order_single h10, WithTop.coe_zero, zero_add, ← WithTop.coe_add, neg_add_self,
      WithTop.coe_zero]
    · exact C_ne_zero (left_ne_zero_of_mul_eq_one hr)
      -- 🎉 no goals
  · rw [addVal_apply, ← WithTop.coe_zero]
    -- ⊢ ↑0 ≠ if 1 - ↑C r * ↑(single (-order x)) 1 * x = 0 then ⊤ else ↑(order (1 - ↑ …
    split_ifs with h
    -- ⊢ ↑0 ≠ ⊤
    · apply WithTop.coe_ne_top
      -- 🎉 no goals
    rw [Ne.def, WithTop.coe_eq_coe]
    -- ⊢ ¬0 = order (1 - ↑C r * ↑(single (-order x)) 1 * x)
    intro con
    -- ⊢ False
    apply coeff_order_ne_zero h
    -- ⊢ coeff (1 - ↑C r * ↑(single (-order x)) 1 * x) (order (1 - ↑C r * ↑(single (- …
    rw [← con, mul_assoc, sub_coeff, one_coeff, if_pos rfl, C_mul_eq_smul, smul_coeff, smul_eq_mul,
      ← add_neg_self x.order, single_mul_coeff_add, one_mul, hr, sub_self]
#align hahn_series.unit_aux HahnSeries.unit_aux

theorem isUnit_iff {x : HahnSeries Γ R} : IsUnit x ↔ IsUnit (x.coeff x.order) := by
  constructor
  -- ⊢ IsUnit x → IsUnit (coeff x (order x))
  · rintro ⟨⟨u, i, ui, iu⟩, rfl⟩
    -- ⊢ IsUnit (coeff (↑{ val := u, inv := i, val_inv := ui, inv_val := iu }) (order …
    refine'
      isUnit_of_mul_eq_one (u.coeff u.order) (i.coeff i.order)
        ((mul_coeff_order_add_order u i).symm.trans _)
    rw [ui, one_coeff, if_pos]
    -- ⊢ order u + order i = 0
    rw [← order_mul (left_ne_zero_of_mul_eq_one ui) (right_ne_zero_of_mul_eq_one ui), ui, order_one]
    -- 🎉 no goals
  · rintro ⟨⟨u, i, ui, iu⟩, h⟩
    -- ⊢ IsUnit x
    rw [Units.val_mk] at h
    -- ⊢ IsUnit x
    rw [h] at iu
    -- ⊢ IsUnit x
    have h := SummableFamily.one_sub_self_mul_hsum_powers (unit_aux x iu)
    -- ⊢ IsUnit x
    rw [sub_sub_cancel] at h
    -- ⊢ IsUnit x
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_eq_one _ _ h)
    -- 🎉 no goals
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
      -- ⊢ x * (↑C (coeff x (order x))⁻¹ * ↑(single (-order x)) 1 * SummableFamily.hsum …
      have h :=
        SummableFamily.one_sub_self_mul_hsum_powers
          (unit_aux x (inv_mul_cancel (coeff_order_ne_zero x0)))
      rw [sub_sub_cancel] at h
      -- ⊢ x * (↑C (coeff x (order x))⁻¹ * ↑(single (-order x)) 1 * SummableFamily.hsum …
      rw [← mul_assoc, mul_comm x, h] }
      -- 🎉 no goals

end Inversion

end HahnSeries
