/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Group.Subsemigroup.Operations
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Order.Filter.Extr

/-!
# Lemmas about the `sup` and `inf` of the support of `AddMonoidAlgebra`

## TODO
The current plan is to state and prove lemmas about `Finset.sup (Finsupp.support f) D` with a
"generic" degree/weight function `D` from the grading Type `A` to a somewhat ordered Type `B`.

Next, the general lemmas get specialized for some yet-to-be-defined `degree`s.
-/


variable {R R' A T B ι : Type*}

namespace AddMonoidAlgebra

/-!

# sup-degree and inf-degree of an `AddMonoidAlgebra`

Let `R` be a semiring and let `A` be a `SemilatticeSup`.
For an element `f : R[A]`, this file defines
* `AddMonoidAlgebra.supDegree`: the sup-degree taking values in `WithBot A`,
* `AddMonoidAlgebra.infDegree`: the inf-degree taking values in `WithTop A`.

If the grading type `A` is a linearly ordered additive monoid, then these two notions of degree
coincide with the standard one:
* the sup-degree is the maximum of the exponents of the monomials that appear with non-zero
  coefficient in `f`, or `⊥`, if `f = 0`;
* the inf-degree is the minimum of the exponents of the monomials that appear with non-zero
  coefficient in `f`, or `⊤`, if `f = 0`.

The main results are
* `AddMonoidAlgebra.supDegree_mul_le`:
  the sup-degree of a product is at most the sum of the sup-degrees,
* `AddMonoidAlgebra.le_infDegree_mul`:
  the inf-degree of a product is at least the sum of the inf-degrees,
* `AddMonoidAlgebra.supDegree_add_le`:
  the sup-degree of a sum is at most the sup of the sup-degrees,
* `AddMonoidAlgebra.le_infDegree_add`:
  the inf-degree of a sum is at least the inf of the inf-degrees.

## Implementation notes

The current plan is to state and prove lemmas about `Finset.sup (Finsupp.support f) D` with a
"generic" degree/weight function `D` from the grading Type `A` to a somewhat ordered Type `B`.
Next, the general lemmas get specialized twice:
* once for `supDegree` (essentially a simple application) and
* once for `infDegree` (a simple application, via `OrderDual`).

These final lemmas are the ones that likely get used the most.  The generic lemmas about
`Finset.support.sup` may not be used directly much outside of this file.
To see this in action, you can look at the triple
`(sup_support_mul_le, maxDegree_mul_le, le_minDegree_mul)`.
-/


section GeneralResultsAssumingSemilatticeSup

variable [SemilatticeSup B] [OrderBot B] [SemilatticeInf T] [OrderTop T]

section Semiring

variable [Semiring R]

section ExplicitDegrees

/-!

In this section, we use `degb` and `degt` to denote "degree functions" on `A` with values in
a type with *b*ot or *t*op respectively.
-/


variable (degb : A → B) (degt : A → T) (f g : R[A])

theorem sup_support_add_le :
    (f + g).support.sup degb ≤ f.support.sup degb ⊔ g.support.sup degb := by
  classical
  exact (Finset.sup_mono Finsupp.support_add).trans_eq Finset.sup_union

theorem le_inf_support_add : f.support.inf degt ⊓ g.support.inf degt ≤ (f + g).support.inf degt :=
  sup_support_add_le (fun a : A => OrderDual.toDual (degt a)) f g

end ExplicitDegrees

section AddOnly

variable [Add A] [Add B] [Add T] [AddLeftMono B] [AddRightMono B]
  [AddLeftMono T] [AddRightMono T]

theorem sup_support_mul_le {degb : A → B} (degbm : ∀ {a b}, degb (a + b) ≤ degb a + degb b)
    (f g : R[A]) :
    (f * g).support.sup degb ≤ f.support.sup degb + g.support.sup degb := by
  classical
  exact (Finset.sup_mono <| support_mul _ _).trans <| Finset.sup_add_le.2 fun _fd fds _gd gds ↦
    degbm.trans <| add_le_add (Finset.le_sup fds) (Finset.le_sup gds)

theorem le_inf_support_mul {degt : A → T} (degtm : ∀ {a b}, degt a + degt b ≤ degt (a + b))
    (f g : R[A]) :
    f.support.inf degt + g.support.inf degt ≤ (f * g).support.inf degt :=
  sup_support_mul_le (B := Tᵒᵈ) degtm f g

end AddOnly

section AddMonoids

variable [AddMonoid A] [AddMonoid B] [AddLeftMono B] [AddRightMono B]
  [AddMonoid T] [AddLeftMono T] [AddRightMono T]
  {degb : A → B} {degt : A → T}

theorem sup_support_list_prod_le (degb0 : degb 0 ≤ 0)
    (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b) :
    ∀ l : List R[A],
      l.prod.support.sup degb ≤ (l.map fun f : R[A] => f.support.sup degb).sum
  | [] => by
    rw [List.map_nil, Finset.sup_le_iff, List.prod_nil, List.sum_nil]
    exact fun a ha => by rwa [Finset.mem_singleton.mp (Finsupp.support_single_subset ha)]
  | f::fs => by
    rw [List.prod_cons, List.map_cons, List.sum_cons]
    exact (sup_support_mul_le (@fun a b => degbm a b) _ _).trans
        (add_le_add_left (sup_support_list_prod_le degb0 degbm fs) _)

theorem le_inf_support_list_prod (degt0 : 0 ≤ degt 0)
    (degtm : ∀ a b, degt a + degt b ≤ degt (a + b)) (l : List R[A]) :
    (l.map fun f : R[A] => f.support.inf degt).sum ≤ l.prod.support.inf degt := by
  refine OrderDual.ofDual_le_ofDual.mpr ?_
  refine sup_support_list_prod_le ?_ ?_ l
  · refine (OrderDual.ofDual_le_ofDual.mp ?_)
    exact degt0
  · refine (fun a b => OrderDual.ofDual_le_ofDual.mp ?_)
    exact degtm a b

theorem sup_support_pow_le (degb0 : degb 0 ≤ 0) (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b)
    (n : ℕ) (f : R[A]) : (f ^ n).support.sup degb ≤ n • f.support.sup degb := by
  rw [← List.prod_replicate, ← List.sum_replicate]
  refine (sup_support_list_prod_le degb0 degbm _).trans_eq ?_
  rw [List.map_replicate]

theorem le_inf_support_pow (degt0 : 0 ≤ degt 0) (degtm : ∀ a b, degt a + degt b ≤ degt (a + b))
    (n : ℕ) (f : R[A]) : n • f.support.inf degt ≤ (f ^ n).support.inf degt := by
  refine OrderDual.ofDual_le_ofDual.mpr <| sup_support_pow_le (OrderDual.ofDual_le_ofDual.mp ?_)
      (fun a b => OrderDual.ofDual_le_ofDual.mp ?_) n f
  · exact degt0
  · exact degtm _ _

end AddMonoids

end Semiring

section CommutativeLemmas

variable [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [AddLeftMono B] [AddRightMono B]
  [AddCommMonoid T] [AddLeftMono T] [AddRightMono T]
  {degb : A → B} {degt : A → T}

theorem sup_support_multiset_prod_le (degb0 : degb 0 ≤ 0)
    (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b) (m : Multiset R[A]) :
    m.prod.support.sup degb ≤ (m.map fun f : R[A] => f.support.sup degb).sum := by
  induction m using Quot.inductionOn
  rw [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.sum_coe, Multiset.prod_coe]
  exact sup_support_list_prod_le degb0 degbm _

theorem le_inf_support_multiset_prod (degt0 : 0 ≤ degt 0)
    (degtm : ∀ a b, degt a + degt b ≤ degt (a + b)) (m : Multiset R[A]) :
    (m.map fun f : R[A] => f.support.inf degt).sum ≤ m.prod.support.inf degt := by
  refine OrderDual.ofDual_le_ofDual.mpr <|
    sup_support_multiset_prod_le (OrderDual.ofDual_le_ofDual.mp ?_)
      (fun a b => OrderDual.ofDual_le_ofDual.mp ?_) m
  · exact degt0
  · exact degtm _ _

theorem sup_support_finset_prod_le (degb0 : degb 0 ≤ 0)
    (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b) (s : Finset ι) (f : ι → R[A]) :
    (∏ i ∈ s, f i).support.sup degb ≤ ∑ i ∈ s, (f i).support.sup degb :=
  (sup_support_multiset_prod_le degb0 degbm _).trans_eq <| congr_arg _ <| Multiset.map_map _ _ _

theorem le_inf_support_finset_prod (degt0 : 0 ≤ degt 0)
    (degtm : ∀ a b, degt a + degt b ≤ degt (a + b)) (s : Finset ι) (f : ι → R[A]) :
    (∑ i ∈ s, (f i).support.inf degt) ≤ (∏ i ∈ s, f i).support.inf degt :=
  le_of_eq_of_le (by rw [Multiset.map_map]; rfl) (le_inf_support_multiset_prod degt0 degtm _)

end CommutativeLemmas

end GeneralResultsAssumingSemilatticeSup


/-! ### Shorthands for special cases
Note that these definitions are reducible, in order to make it easier to apply the more generic
lemmas above. -/


section Degrees

variable [Semiring R] [Ring R']

section SupDegree

variable [SemilatticeSup B] [OrderBot B] (D : A → B)

/-- Let `R` be a semiring, let `A` be an `AddZeroClass`, let `B` be an `OrderBot`,
and let `D : A → B` be a "degree" function.
For an element `f : R[A]`, the element `supDegree f : B` is the supremum of all the elements in the
support of `f`, or `⊥` if `f` is zero.
Often, the Type `B` is `WithBot A`,
If, further, `A` has a linear order, then this notion coincides with the usual one,
using the maximum of the exponents.

If `A := σ →₀ ℕ` then `R[A] = MvPolynomial σ R`, and if we equip `σ` with a linear order then
the induced linear order on `Lex A` equips `MvPolynomial` ring with a
[monomial order](https://en.wikipedia.org/wiki/Monomial_order) (i.e. a linear order on `A`, the
type of (monic) monomials in `R[A]`, that respects addition). We make use of this monomial order
by taking `D := toLex`, and different monomial orders could be accessed via different type
synonyms once they are added. -/
abbrev supDegree (f : R[A]) : B :=
  f.support.sup D

variable {D}

theorem supDegree_add_le {f g : R[A]} :
    (f + g).supDegree D ≤ (f.supDegree D) ⊔ (g.supDegree D) :=
  sup_support_add_le D f g

@[simp]
theorem supDegree_neg {f : R'[A]} :
    (-f).supDegree D = f.supDegree D := by
  rw [supDegree, supDegree, Finsupp.support_neg]

theorem supDegree_sub_le {f g : R'[A]} :
    (f - g).supDegree D ≤ f.supDegree D ⊔ g.supDegree D := by
  rw [sub_eq_add_neg, ← supDegree_neg (f := g)]; apply supDegree_add_le

theorem supDegree_sum_le {ι} {s : Finset ι} {f : ι → R[A]} :
    (∑ i ∈ s, f i).supDegree D ≤ s.sup (fun i => (f i).supDegree D) := by
  classical
  exact (Finset.sup_mono Finsupp.support_finset_sum).trans_eq (Finset.sup_biUnion _ _)

theorem supDegree_single_ne_zero (a : A) {r : R} (hr : r ≠ 0) :
    (single a r).supDegree D = D a := by
  rw [supDegree, Finsupp.support_single_ne_zero a hr, Finset.sup_singleton]

open Classical in
theorem supDegree_single (a : A) (r : R) :
    (single a r).supDegree D = if r = 0 then ⊥ else D a := by
  split_ifs with hr <;> simp [supDegree_single_ne_zero, hr]

theorem apply_eq_zero_of_not_le_supDegree {p : R[A]} {a : A} (hlt : ¬ D a ≤ p.supDegree D) :
    p a = 0 := by
  contrapose! hlt
  exact Finset.le_sup (Finsupp.mem_support_iff.2 hlt)

theorem supDegree_withBot_some_comp {s : AddMonoidAlgebra R A} (hs : s.support.Nonempty) :
    supDegree (WithBot.some ∘ D) s = supDegree D s := by
  unfold AddMonoidAlgebra.supDegree
  rw [← Finset.coe_sup' hs, Finset.sup'_eq_sup]

theorem supDegree_eq_of_isMaxOn {p : R[A]} {a : A} (hmem : a ∈ p.support)
    (hmax : IsMaxOn D p.support a) : p.supDegree D = D a :=
  sup_eq_of_isMaxOn hmem hmax

variable [AddZeroClass A] {p q : R[A]}

@[simp]
theorem supDegree_zero : (0 : R[A]).supDegree D = ⊥ := by simp [supDegree]

theorem ne_zero_of_supDegree_ne_bot : p.supDegree D ≠ ⊥ → p ≠ 0 := mt (fun h => h ▸ supDegree_zero)

theorem ne_zero_of_not_supDegree_le {b : B} (h : ¬ p.supDegree D ≤ b) : p ≠ 0 :=
  ne_zero_of_supDegree_ne_bot (fun he => h <| he ▸ bot_le)

theorem supDegree_eq_of_max {b : B} (hb : b ∈ Set.range D) (hmem : D.invFun b ∈ p.support)
    (hmax : ∀ a ∈ p.support, D a ≤ b) : p.supDegree D = b :=
  sup_eq_of_max hb hmem hmax

variable [Add B]

theorem supDegree_mul_le (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    [AddLeftMono B] [AddRightMono B] :
    (p * q).supDegree D ≤ p.supDegree D + q.supDegree D :=
  sup_support_mul_le (fun {_ _} => (hadd _ _).le) p q

theorem supDegree_prod_le {R A B : Type*} [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B]
    [SemilatticeSup B] [OrderBot B]
    [AddLeftMono B] [AddRightMono B]
    {D : A → B} (hzero : D 0 = 0) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    {ι} {s : Finset ι} {f : ι → R[A]} :
    (∏ i ∈ s, f i).supDegree D ≤ ∑ i ∈ s, (f i).supDegree D := by
  classical
  refine s.induction ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty, one_def, supDegree_single]
    split_ifs; exacts [bot_le, hzero.le]
  · intro i s his ih
    rw [Finset.prod_insert his, Finset.sum_insert his]
    exact (supDegree_mul_le hadd).trans (by gcongr)

theorem apply_add_of_supDegree_le (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    [AddLeftStrictMono B] [AddRightStrictMono B]
    (hD : D.Injective) {ap aq : A} (hp : p.supDegree D ≤ D ap) (hq : q.supDegree D ≤ D aq) :
    (p * q) (ap + aq) = p ap * q aq := by
  classical
  simp_rw [mul_apply, Finsupp.sum]
  rw [Finset.sum_eq_single ap, Finset.sum_eq_single aq, if_pos rfl]
  · refine fun a ha hne => if_neg (fun he => ?_)
    apply_fun D at he; simp_rw [hadd] at he
    exact (add_lt_add_left (((Finset.le_sup ha).trans hq).lt_of_ne <| hD.ne_iff.2 hne) _).ne he
  · intro h; rw [if_pos rfl, Finsupp.notMem_support_iff.1 h, mul_zero]
  · refine fun a ha hne => Finset.sum_eq_zero (fun a' ha' => if_neg <| fun he => ?_)
    apply_fun D at he
    simp_rw [hadd] at he
    have := addLeftMono_of_addLeftStrictMono B
    exact (add_lt_add_of_lt_of_le (((Finset.le_sup ha).trans hp).lt_of_ne <| hD.ne_iff.2 hne)
      <| (Finset.le_sup ha').trans hq).ne he
  · refine fun h => Finset.sum_eq_zero (fun a _ => ite_eq_right_iff.mpr <| fun _ => ?_)
    rw [Finsupp.notMem_support_iff.mp h, zero_mul]

end SupDegree

section LinearOrder

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

/-- If `D` is an injection into a linear order `B`, the leading coefficient of `f : R[A]` is the
  nonzero coefficient of highest degree according to `D`, or 0 if `f = 0`. In general, it is defined
  to be the coefficient at an inverse image of `supDegree f` (if such exists). -/
noncomputable def leadingCoeff [Nonempty A] (f : R[A]) : R :=
  f (D.invFun <| f.supDegree D)

/-- An element `f : R[A]` is monic if its leading coefficient is one. -/
@[reducible] def Monic [Nonempty A] (f : R[A]) : Prop :=
  f.leadingCoeff D = 1

variable {D}

@[simp]
theorem leadingCoeff_single [Nonempty A] (hD : D.Injective) (a : A) (r : R) :
    (single a r).leadingCoeff D = r := by
  classical
  rw [leadingCoeff, supDegree_single]
  split_ifs with hr
  · simp [hr]
  · rw [Function.leftInverse_invFun hD, single_apply, if_pos rfl]

@[simp]
theorem leadingCoeff_zero [Nonempty A] : (0 : R[A]).leadingCoeff D = 0 := rfl

lemma Monic.ne_zero [Nonempty A] [Nontrivial R] (hp : p.Monic D) : p ≠ 0 := fun h => by
  simp_rw [Monic, h, leadingCoeff_zero, zero_ne_one] at hp

@[simp]
theorem monic_one [AddZeroClass A] (hD : D.Injective) : (1 : R[A]).Monic D := by
  rw [Monic, one_def, leadingCoeff_single hD]

variable (D) in
lemma exists_supDegree_mem_support (hp : p ≠ 0) : ∃ a ∈ p.support, p.supDegree D = D a :=
  Finset.exists_mem_eq_sup _ (Finsupp.support_nonempty_iff.mpr hp) D

variable (D) in
lemma supDegree_mem_range (hp : p ≠ 0) : p.supDegree D ∈ Set.range D := by
  obtain ⟨a, -, he⟩ := exists_supDegree_mem_support D hp; exact ⟨a, he.symm⟩

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}

lemma supDegree_sum_lt (hs : s.Nonempty) {b : B}
    (h : ∀ i ∈ s, (f i).supDegree D < b) : (∑ i ∈ s, f i).supDegree D < b := by
  refine supDegree_sum_le.trans_lt ((Finset.sup_lt_iff ?_).mpr h)
  obtain ⟨i, hi⟩ := hs; exact bot_le.trans_lt (h i hi)

variable [AddZeroClass A]

open Finsupp in
lemma supDegree_add_eq_left (h : q.supDegree D < p.supDegree D) :
    (p + q).supDegree D = p.supDegree D := by
  apply (supDegree_add_le.trans <| sup_le le_rfl h.le).antisymm
  obtain ⟨a, ha, he⟩ := exists_supDegree_mem_support D (ne_zero_of_not_supDegree_le h.not_ge)
  rw [he] at h ⊢
  apply Finset.le_sup
  rw [mem_support_iff, add_apply, apply_eq_zero_of_not_le_supDegree h.not_ge, add_zero]
  exact mem_support_iff.mp ha

lemma supDegree_add_eq_right (h : p.supDegree D < q.supDegree D) :
    (p + q).supDegree D = q.supDegree D := by
  rw [add_comm, supDegree_add_eq_left h]

lemma leadingCoeff_add_eq_left (h : q.supDegree D < p.supDegree D) :
    (p + q).leadingCoeff D = p.leadingCoeff D := by
  obtain ⟨a, he⟩ := supDegree_mem_range D (ne_zero_of_not_supDegree_le h.not_ge)
  rw [leadingCoeff, supDegree_add_eq_left h, Finsupp.add_apply, ← leadingCoeff,
    apply_eq_zero_of_not_le_supDegree (D := D), add_zero]
  rw [← he, Function.apply_invFun_apply (f := D), he]; exact h.not_ge

lemma leadingCoeff_add_eq_right (h : p.supDegree D < q.supDegree D) :
    (p + q).leadingCoeff D = q.leadingCoeff D := by
  rw [add_comm, leadingCoeff_add_eq_left h]

lemma supDegree_mem_support (hD : D.Injective) (hp : p ≠ 0) :
    D.invFun (p.supDegree D) ∈ p.support := by
  obtain ⟨a, ha, he⟩ := exists_supDegree_mem_support D hp
  rwa [he, Function.leftInverse_invFun hD]

@[simp]
lemma leadingCoeff_eq_zero (hD : D.Injective) : p.leadingCoeff D = 0 ↔ p = 0 := by
  refine ⟨(fun h => ?_).mtr, fun h => h ▸ leadingCoeff_zero⟩
  rw [leadingCoeff, ← Ne, ← Finsupp.mem_support_iff]
  exact supDegree_mem_support hD h

lemma leadingCoeff_ne_zero (hD : D.Injective) : p.leadingCoeff D ≠ 0 ↔ p ≠ 0 :=
  (leadingCoeff_eq_zero hD).ne

lemma supDegree_sub_lt_of_leadingCoeff_eq (hD : D.Injective) {R} [Ring R] {p q : R[A]}
    (hd : p.supDegree D = q.supDegree D) (hc : p.leadingCoeff D = q.leadingCoeff D) :
    (p - q).supDegree D < p.supDegree D ∨ p = q := by
  rw [or_iff_not_imp_right]
  refine fun he => (supDegree_sub_le.trans ?_).lt_of_ne ?_
  · rw [hd, sup_idem]
  · rw [← sub_eq_zero, ← leadingCoeff_eq_zero hD, leadingCoeff] at he
    refine fun h => he ?_
    rwa [h, Finsupp.sub_apply, ← leadingCoeff, hd, ← leadingCoeff, sub_eq_zero]

lemma supDegree_leadingCoeff_sum_eq
    (hi : i ∈ s) (hmax : ∀ j ∈ s, j ≠ i → (f j).supDegree D < (f i).supDegree D) :
    (∑ j ∈ s, f j).supDegree D = (f i).supDegree D ∧
    (∑ j ∈ s, f j).leadingCoeff D = (f i).leadingCoeff D := by
  classical
  rw [← s.add_sum_erase _ hi]
  by_cases hs : s.erase i = ∅
  · rw [hs, Finset.sum_empty, add_zero]; exact ⟨rfl, rfl⟩
  suffices _ from ⟨supDegree_add_eq_left this, leadingCoeff_add_eq_left this⟩
  refine supDegree_sum_lt ?_ (fun j hj => ?_)
  · rw [Finset.nonempty_iff_ne_empty]; exact hs
  · rw [Finset.mem_erase] at hj; exact hmax j hj.2 hj.1

open Finset in
lemma sum_ne_zero_of_injOn_supDegree' (hs : ∃ i ∈ s, f i ≠ 0)
    (hd : (s : Set ι).InjOn (supDegree D ∘ f)) :
    ∑ i ∈ s, f i ≠ 0 := by
  obtain ⟨j, hj, hne⟩ := hs
  obtain ⟨i, hi, he⟩ := exists_mem_eq_sup _ ⟨j, hj⟩ (supDegree D ∘ f)
  by_cases h : ∀ k ∈ s, k = i
  · refine (sum_eq_single_of_mem j hj (fun k hk hne => ?_)).trans_ne hne
    rw [h k hk, h j hj] at hne; exact hne.irrefl.elim
  push_neg at h; obtain ⟨j, hj, hne⟩ := h
  apply ne_zero_of_supDegree_ne_bot (D := D)
  have (k) (hk : k ∈ s) (hne : k ≠ i) : supDegree D (f k) < supDegree D (f i) :=
    ((le_sup hk).trans_eq he).lt_of_ne (hd.ne hk hi hne)
  rw [(supDegree_leadingCoeff_sum_eq hi this).1]
  exact (this j hj hne).ne_bot

lemma sum_ne_zero_of_injOn_supDegree (hs : s ≠ ∅)
    (hf : ∀ i ∈ s, f i ≠ 0) (hd : (s : Set ι).InjOn (supDegree D ∘ f)) :
    ∑ i ∈ s, f i ≠ 0 :=
  let ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hs
  sum_ne_zero_of_injOn_supDegree' ⟨i, hi, hf i hi⟩ hd

variable [Add B]
variable [AddLeftStrictMono B] [AddRightStrictMono B]

lemma apply_supDegree_add_supDegree (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) :
    (p * q) (D.invFun (p.supDegree D + q.supDegree D)) = p.leadingCoeff D * q.leadingCoeff D := by
  obtain rfl | hp := eq_or_ne p 0
  · simp_rw [leadingCoeff_zero, zero_mul, Finsupp.coe_zero, Pi.zero_apply]
  obtain rfl | hq := eq_or_ne q 0
  · simp_rw [leadingCoeff_zero, mul_zero, Finsupp.coe_zero, Pi.zero_apply]
  obtain ⟨ap, -, hp⟩ := exists_supDegree_mem_support D hp
  obtain ⟨aq, -, hq⟩ := exists_supDegree_mem_support D hq
  simp_rw [leadingCoeff, hp, hq, ← hadd, Function.leftInverse_invFun hD _]
  exact apply_add_of_supDegree_le hadd hD hp.le hq.le

lemma supDegree_mul
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    (hpq : leadingCoeff D p * leadingCoeff D q ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D := by
  apply supDegree_eq_of_max
  · rw [← AddSubsemigroup.coe_set_mk (Set.range D), ← AddHom.srange_mk _ hadd, SetLike.mem_coe]
    · exact add_mem (supDegree_mem_range D hp) (supDegree_mem_range D hq)
    · exact (AddHom.srange ⟨D, hadd⟩).add_mem
  · simp_rw [Finsupp.mem_support_iff, apply_supDegree_add_supDegree hD hadd]
    exact hpq
  · have := addLeftMono_of_addLeftStrictMono B
    have := addRightMono_of_addRightStrictMono B
    exact fun a ha => (Finset.le_sup ha).trans (supDegree_mul_le hadd)

lemma Monic.supDegree_mul_of_ne_zero_left
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    (hq : q.Monic D) (hp : p ≠ 0) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D := by
  cases subsingleton_or_nontrivial R; · exact (hp (Subsingleton.elim _ _)).elim
  apply supDegree_mul hD hadd ?_ hp hq.ne_zero
  simp_rw [hq, mul_one, Ne, leadingCoeff_eq_zero hD, hp, not_false_eq_true]

lemma Monic.supDegree_mul_of_ne_zero_right
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    (hp : p.Monic D) (hq : q ≠ 0) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D := by
  cases subsingleton_or_nontrivial R; · exact (hq (Subsingleton.elim _ _)).elim
  apply supDegree_mul hD hadd ?_ hp.ne_zero hq
  simp_rw [hp, one_mul, Ne, leadingCoeff_eq_zero hD, hq, not_false_eq_true]

lemma Monic.supDegree_mul
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    (hbot : (⊥ : B) + ⊥ = ⊥) (hp : p.Monic D) (hq : q.Monic D) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D := by
  cases subsingleton_or_nontrivial R
  · simp_rw [Subsingleton.eq_zero p, Subsingleton.eq_zero q, mul_zero, supDegree_zero, hbot]
  exact hq.supDegree_mul_of_ne_zero_left hD hadd hp.ne_zero

lemma leadingCoeff_mul [NoZeroDivisors R]
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) :
    (p * q).leadingCoeff D = p.leadingCoeff D * q.leadingCoeff D := by
  obtain rfl | hp := eq_or_ne p 0
  · simp_rw [leadingCoeff_zero, zero_mul, leadingCoeff_zero]
  obtain rfl | hq := eq_or_ne q 0
  · simp_rw [leadingCoeff_zero, mul_zero, leadingCoeff_zero]
  rw [← apply_supDegree_add_supDegree hD hadd, ← supDegree_mul hD hadd ?_ hp hq, leadingCoeff]
  apply mul_ne_zero <;> rwa [Ne, leadingCoeff_eq_zero hD]

lemma Monic.leadingCoeff_mul_eq_left
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) (hq : q.Monic D) :
    (p * q).leadingCoeff D = p.leadingCoeff D := by
  obtain rfl | hp := eq_or_ne p 0
  · rw [zero_mul]
  rw [leadingCoeff, hq.supDegree_mul_of_ne_zero_left hD hadd hp,
    apply_supDegree_add_supDegree hD hadd, hq, mul_one]

lemma Monic.leadingCoeff_mul_eq_right
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) (hp : p.Monic D) :
    (p * q).leadingCoeff D = q.leadingCoeff D := by
  obtain rfl | hq := eq_or_ne q 0
  · rw [mul_zero]
  rw [leadingCoeff, hp.supDegree_mul_of_ne_zero_right hD hadd hq,
    apply_supDegree_add_supDegree hD hadd, hp, one_mul]

lemma Monic.mul
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    (hp : p.Monic D) (hq : q.Monic D) : (p * q).Monic D := by
  rw [Monic, hq.leadingCoeff_mul_eq_left hD hadd]; exact hp

section AddMonoid

variable {A B : Type*} [AddMonoid A] [AddMonoid B] [LinearOrder B] [OrderBot B]
  [AddLeftStrictMono B] [AddRightStrictMono B]
  {D : A → B} {p : R[A]} {n : ℕ}

lemma Monic.pow
    (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) (hD : D.Injective)
    (hp : p.Monic D) : (p ^ n).Monic D := by
  induction n with
  | zero => rw [pow_zero]; exact monic_one hD
  | succ n ih => rw [pow_succ']; exact hp.mul hD hadd ih

lemma Monic.supDegree_pow
    (hzero : D 0 = 0) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) (hD : D.Injective)
    [Nontrivial R] (hp : p.Monic D) :
    (p ^ n).supDegree D = n • p.supDegree D := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul, one_def, supDegree_single 0 1, if_neg one_ne_zero, hzero]
  | succ n ih => rw [pow_succ', (hp.pow hadd hD).supDegree_mul_of_ne_zero_left hD hadd hp.ne_zero,
      ih, succ_nsmul']

end AddMonoid

end LinearOrder

section InfDegree

variable [SemilatticeInf T] [OrderTop T] (D : A → T)

/-- Let `R` be a semiring, let `A` be an `AddZeroClass`, let `T` be an `OrderTop`,
and let `D : A → T` be a "degree" function.
For an element `f : R[A]`, the element `infDegree f : T` is the infimum of all the elements in the
support of `f`, or `⊤` if `f` is zero.
Often, the Type `T` is `WithTop A`,
If, further, `A` has a linear order, then this notion coincides with the usual one,
using the minimum of the exponents. -/
abbrev infDegree (f : R[A]) : T :=
  f.support.inf D

theorem le_infDegree_add (f g : R[A]) :
    (f.infDegree D) ⊓ (g.infDegree D) ≤ (f + g).infDegree D :=
  le_inf_support_add D f g

variable {D} in
theorem infDegree_withTop_some_comp {s : AddMonoidAlgebra R A} (hs : s.support.Nonempty) :
    infDegree (WithTop.some ∘ D) s = infDegree D s := by
  unfold AddMonoidAlgebra.infDegree
  rw [← Finset.coe_inf' hs, Finset.inf'_eq_inf]

theorem le_infDegree_mul [AddZeroClass A] [Add T] [AddLeftMono T] [AddRightMono T]
    (D : AddHom A T) (f g : R[A]) :
    f.infDegree D + g.infDegree D ≤ (f * g).infDegree D :=
  le_inf_support_mul (fun {a b : A} => (map_add D a b).ge) _ _

end InfDegree

end Degrees

end AddMonoidAlgebra
