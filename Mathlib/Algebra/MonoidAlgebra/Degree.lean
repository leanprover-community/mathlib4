/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Order.Filter.Extr

#align_import algebra.monoid_algebra.degree from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"

/-!
# Lemmas about the `sup` and `inf` of the support of `AddMonoidAlgebra`

## TODO
The current plan is to state and prove lemmas about `Finset.sup (Finsupp.support f) D` with a
"generic" degree/weight function `D` from the grading Type `A` to a somewhat ordered Type `B`.

Next, the general lemmas get specialized for some yet-to-be-defined `degree`s.
-/


variable {R A T B ι : Type*}

namespace AddMonoidAlgebra

open Classical BigOperators

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

theorem sup_support_add_le : (f + g).support.sup degb ≤ f.support.sup degb ⊔ g.support.sup degb :=
  (Finset.sup_mono Finsupp.support_add).trans_eq Finset.sup_union
#align add_monoid_algebra.sup_support_add_le AddMonoidAlgebra.sup_support_add_le

theorem le_inf_support_add : f.support.inf degt ⊓ g.support.inf degt ≤ (f + g).support.inf degt :=
  sup_support_add_le (fun a : A => OrderDual.toDual (degt a)) f g
#align add_monoid_algebra.le_inf_support_add AddMonoidAlgebra.le_inf_support_add

end ExplicitDegrees

section AddOnly

variable [Add A] [Add B] [Add T] [CovariantClass B B (· + ·) (· ≤ ·)]
  [CovariantClass B B (Function.swap (· + ·)) (· ≤ ·)] [CovariantClass T T (· + ·) (· ≤ ·)]
  [CovariantClass T T (Function.swap (· + ·)) (· ≤ ·)]

theorem sup_support_mul_le {degb : A → B} (degbm : ∀ {a b}, degb (a + b) ≤ degb a + degb b)
    (f g : R[A]) :
    (f * g).support.sup degb ≤ f.support.sup degb + g.support.sup degb :=
  (Finset.sup_mono <| support_mul _ _).trans <| Finset.sup_add_le.2 fun _fd fds _gd gds ↦
    degbm.trans <| add_le_add (Finset.le_sup fds) (Finset.le_sup gds)
#align add_monoid_algebra.sup_support_mul_le AddMonoidAlgebra.sup_support_mul_le

theorem le_inf_support_mul {degt : A → T} (degtm : ∀ {a b}, degt a + degt b ≤ degt (a + b))
    (f g : R[A]) :
    f.support.inf degt + g.support.inf degt ≤ (f * g).support.inf degt :=
  sup_support_mul_le (B := Tᵒᵈ) degtm f g
#align add_monoid_algebra.le_inf_support_mul AddMonoidAlgebra.le_inf_support_mul

end AddOnly

section AddMonoids

variable [AddMonoid A] [AddMonoid B] [CovariantClass B B (· + ·) (· ≤ ·)]
  [CovariantClass B B (Function.swap (· + ·)) (· ≤ ·)] [AddMonoid T]
  [CovariantClass T T (· + ·) (· ≤ ·)] [CovariantClass T T (Function.swap (· + ·)) (· ≤ ·)]
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
#align add_monoid_algebra.sup_support_list_prod_le AddMonoidAlgebra.sup_support_list_prod_le

theorem le_inf_support_list_prod (degt0 : 0 ≤ degt 0)
    (degtm : ∀ a b, degt a + degt b ≤ degt (a + b)) (l : List R[A]) :
    (l.map fun f : R[A] => f.support.inf degt).sum ≤ l.prod.support.inf degt := by
  refine' OrderDual.ofDual_le_ofDual.mpr _
  refine' sup_support_list_prod_le _ _ l
  · refine' (OrderDual.ofDual_le_ofDual.mp _)
    exact degt0
  · refine' (fun a b => OrderDual.ofDual_le_ofDual.mp _)
    exact degtm a b
#align add_monoid_algebra.le_inf_support_list_prod AddMonoidAlgebra.le_inf_support_list_prod

theorem sup_support_pow_le (degb0 : degb 0 ≤ 0) (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b)
    (n : ℕ) (f : R[A]) : (f ^ n).support.sup degb ≤ n • f.support.sup degb := by
  rw [← List.prod_replicate, ← List.sum_replicate]
  refine' (sup_support_list_prod_le degb0 degbm _).trans_eq _
  rw [List.map_replicate]
#align add_monoid_algebra.sup_support_pow_le AddMonoidAlgebra.sup_support_pow_le

theorem le_inf_support_pow (degt0 : 0 ≤ degt 0) (degtm : ∀ a b, degt a + degt b ≤ degt (a + b))
    (n : ℕ) (f : R[A]) : n • f.support.inf degt ≤ (f ^ n).support.inf degt := by
  refine' OrderDual.ofDual_le_ofDual.mpr <| sup_support_pow_le (OrderDual.ofDual_le_ofDual.mp _)
      (fun a b => OrderDual.ofDual_le_ofDual.mp _) n f
  · exact degt0
  · exact degtm _ _
#align add_monoid_algebra.le_inf_support_pow AddMonoidAlgebra.le_inf_support_pow

end AddMonoids

end Semiring

section CommutativeLemmas

variable [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [CovariantClass B B (· + ·) (· ≤ ·)]
  [CovariantClass B B (Function.swap (· + ·)) (· ≤ ·)] [AddCommMonoid T]
  [CovariantClass T T (· + ·) (· ≤ ·)] [CovariantClass T T (Function.swap (· + ·)) (· ≤ ·)]
  {degb : A → B} {degt : A → T}

theorem sup_support_multiset_prod_le (degb0 : degb 0 ≤ 0)
    (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b) (m : Multiset R[A]) :
    m.prod.support.sup degb ≤ (m.map fun f : R[A] => f.support.sup degb).sum := by
  induction m using Quot.inductionOn
  rw [Multiset.quot_mk_to_coe'', Multiset.coe_map, Multiset.coe_sum, Multiset.coe_prod]
  exact sup_support_list_prod_le degb0 degbm _
#align add_monoid_algebra.sup_support_multiset_prod_le AddMonoidAlgebra.sup_support_multiset_prod_le

theorem le_inf_support_multiset_prod (degt0 : 0 ≤ degt 0)
    (degtm : ∀ a b, degt a + degt b ≤ degt (a + b)) (m : Multiset R[A]) :
    (m.map fun f : R[A] => f.support.inf degt).sum ≤ m.prod.support.inf degt := by
  refine' OrderDual.ofDual_le_ofDual.mpr <|
    sup_support_multiset_prod_le (OrderDual.ofDual_le_ofDual.mp _)
      (fun a b => OrderDual.ofDual_le_ofDual.mp _) m
  exact degt0
  exact degtm _ _
#align add_monoid_algebra.le_inf_support_multiset_prod AddMonoidAlgebra.le_inf_support_multiset_prod

theorem sup_support_finset_prod_le (degb0 : degb 0 ≤ 0)
    (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b) (s : Finset ι) (f : ι → R[A]) :
    (∏ i in s, f i).support.sup degb ≤ ∑ i in s, (f i).support.sup degb :=
  (sup_support_multiset_prod_le degb0 degbm _).trans_eq <| congr_arg _ <| Multiset.map_map _ _ _
#align add_monoid_algebra.sup_support_finset_prod_le AddMonoidAlgebra.sup_support_finset_prod_le

theorem le_inf_support_finset_prod (degt0 : 0 ≤ degt 0)
    (degtm : ∀ a b, degt a + degt b ≤ degt (a + b)) (s : Finset ι) (f : ι → R[A]) :
    (∑ i in s, (f i).support.inf degt) ≤ (∏ i in s, f i).support.inf degt :=
  le_of_eq_of_le (by rw [Multiset.map_map]; rfl) (le_inf_support_multiset_prod degt0 degtm _)
#align add_monoid_algebra.le_inf_support_finset_prod AddMonoidAlgebra.le_inf_support_finset_prod

end CommutativeLemmas

end GeneralResultsAssumingSemilatticeSup


/-! ### Shorthands for special cases
Note that these definitions are reducible, in order to make it easier to apply the more generic
lemmas above. -/


section Degrees

variable [Semiring R]

section SupDegree

variable [AddZeroClass A] [Add B] (D : A → B)

section SemilatticeSup

variable [SemilatticeSup B] [OrderBot B]

/-- Let `R` be a semiring, let `A, B` be two `AddZeroClass`es, let `B` be an `OrderBot`,
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
@[reducible] def supDegree (f : R[A]) : B := f.support.sup D

/-- If `D` is an injection into a linear order `B`, the leading coefficient of `f : R[A]` is the
  nonzero coefficient of highest degree according to `D`, or 0 if `f = 0`. In general, it is defined
  to be the coefficient at an inverse image of `supDegree f` (if such exists). -/
noncomputable def leadingCoeff (f : R[A]) : R := f (D.invFun <| f.supDegree D)

/-- An element `f : R[A]` is monic if its leading coefficient is one. -/
@[reducible] def Monic (f : R[A]) : Prop := f.leadingCoeff D = 1

variable {D}

theorem supDegree_add_le {f g : R[A]} :
    (f + g).supDegree D ≤ (f.supDegree D) ⊔ (g.supDegree D) :=
  sup_support_add_le D f g

lemma supDegree_neg {R} [CommRing R] {f : R[A]} :
    (-f).supDegree D = f.supDegree D := by
  rw [supDegree, supDegree, Finsupp.support_neg]

lemma supDegree_sub_le {R} [CommRing R] {f g : R[A]} :
    (f - g).supDegree D ≤ f.supDegree D ⊔ g.supDegree D := by
  rw [sub_eq_add_neg, ← supDegree_neg (f := g)]; apply supDegree_add_le

lemma supDegree_sum_le {ι} {s : Finset ι} {f : ι → R[A]} :
    (∑ i in s, f i).supDegree D ≤ s.sup (fun i => (f i).supDegree D) :=
(Finset.sup_mono Finsupp.support_finset_sum).trans_eq (Finset.sup_biUnion _ _)

theorem supDegree_single_ne_zero (a : A) {r : R} (hr : r ≠ 0) :
    (single a r).supDegree D = D a := by
  rw [supDegree, Finsupp.support_single_ne_zero a hr, Finset.sup_singleton]

theorem supDegree_single (a : A) (r : R) :
    (single a r).supDegree D = if r = 0 then ⊥ else D a := by
  split_ifs with hr <;> simp [supDegree_single_ne_zero, hr]

theorem leadingCoeff_single (hD : D.Injective) (a : A) (r : R) :
    (single a r).leadingCoeff D = r := by
  rw [leadingCoeff, supDegree_single]
  split_ifs with hr
  · simp [hr]
  · rw [Function.leftInverse_invFun hD, single_apply, if_pos rfl]

variable {p q : R[A]}

theorem supDegree_zero : (0 : R[A]).supDegree D = ⊥ := by simp [supDegree]

theorem leadingCoeff_zero : (0 : R[A]).leadingCoeff D = 0 := rfl

theorem ne_zero_of_supDegree_ne_bot : p.supDegree D ≠ ⊥ → p ≠ 0 := mt (fun h => h ▸ supDegree_zero)

theorem ne_zero_of_not_supDegree_le {b : B} (h : ¬ p.supDegree D ≤ b) : p ≠ 0 :=
  ne_zero_of_supDegree_ne_bot (fun he => h <| he ▸ bot_le)

lemma Monic.ne_zero [Nontrivial R] (hp : p.Monic D) : p ≠ 0 := fun h => by
  simp_rw [Monic, h, leadingCoeff_zero, zero_ne_one] at hp

theorem monic_one (hD : D.Injective) : (1 : R[A]).Monic D := by
  rw [Monic, one_def, leadingCoeff_single hD]

theorem supDegree_eq_of_isMaxOn {a : A} (hmem : a ∈ p.support)
    (hmax : IsMaxOn D p.support a) : p.supDegree D = D a :=
  (Finset.sup_le hmax).antisymm (Finset.le_sup hmem)

theorem supDegree_eq_of_max {b : B} (hb : b ∈ Set.range D) (hmem : D.invFun b ∈ p.support)
    (hmax : ∀ a ∈ p.support, D a ≤ b) : p.supDegree D = b := by
  obtain ⟨a, rfl⟩ := hb
  rw [← Function.apply_invFun_apply (f := D)]
  apply supDegree_eq_of_isMaxOn hmem; intro
  rw [Function.apply_invFun_apply (f := D)]; apply hmax

lemma apply_eq_zero_of_not_le_supDegree {a : A} (hlt : ¬ D a ≤ p.supDegree D) : p a = 0 := by
  contrapose! hlt; exact Finset.le_sup (Finsupp.mem_support_iff.2 hlt)

variable (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)

theorem supDegree_mul_le [CovariantClass B B (· + ·) (· ≤ ·)]
    [CovariantClass B B (Function.swap (· + ·)) (· ≤ ·)] :
    (p * q).supDegree D ≤ p.supDegree D + q.supDegree D :=
  sup_support_mul_le (fun {_ _} => (hadd _ _).le) p q

theorem supDegree_prod_le {R A B} [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B]
    [SemilatticeSup B] [OrderBot B]
    [CovariantClass B B (· + ·) (· ≤ ·)] [CovariantClass B B (Function.swap (· + ·)) (· ≤ ·)]
    {D : A → B} (hzero : D 0 = 0) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    {ι} {s : Finset ι} {f : ι → R[A]} :
    (∏ i in s, f i).supDegree D ≤ ∑ i in s, (f i).supDegree D := by
  refine' s.induction _ _
  · rw [Finset.prod_empty, Finset.sum_empty, one_def, supDegree_single]
    split_ifs; exacts [bot_le, hzero.le]
  · intro i s his ih
    rw [Finset.prod_insert his, Finset.sum_insert his]
    exact (supDegree_mul_le hadd).trans (add_le_add_left ih _)

variable [CovariantClass B B (· + ·) (· < ·)] [CovariantClass B B (Function.swap (· + ·)) (· < ·)]

lemma apply_add_of_supDegree_eq (hD : D.Injective) {ap aq : A}
    (hp : p.supDegree D = D ap) (hq : q.supDegree D = D aq) :
    (p * q) (ap + aq) = p ap * q aq := by
  simp_rw [mul_apply, Finsupp.sum]
  rw [Finset.sum_eq_single ap, Finset.sum_eq_single aq, if_pos rfl]
  · refine fun a ha hne => if_neg (fun he => ?_)
    apply_fun D at he; simp_rw [hadd] at he
    exact (add_lt_add_left (((Finset.le_sup ha).trans_eq hq).lt_of_ne <| hD.ne_iff.2 hne) _).ne he
  · intro h; rw [if_pos rfl, Finsupp.not_mem_support_iff.1 h, mul_zero]
  · refine fun a ha hne => Finset.sum_eq_zero (fun a' ha' => if_neg <| fun he => ?_)
    apply_fun D at he; simp_rw [hadd] at he
    have := covariantClass_le_of_lt B B (· + ·)
    exact (add_lt_add_of_lt_of_le (((Finset.le_sup ha).trans_eq hp).lt_of_ne <| hD.ne_iff.2 hne)
      <| (Finset.le_sup ha').trans_eq hq).ne he
  · refine fun h => Finset.sum_eq_zero (fun a _ => ite_eq_right_iff.mpr <| fun _ => ?_)
    rw [Finsupp.not_mem_support_iff.mp h, zero_mul]

end SemilatticeSup

section LinearOrder

variable [LinearOrder B] [OrderBot B] {p q : R[A]}

lemma exists_supDegree_mem_support (hp : p ≠ 0) : ∃ a ∈ p.support, p.supDegree D = D a :=
  Finset.exists_mem_eq_sup _ (Finsupp.support_nonempty_iff.mpr hp) D

lemma supDegree_mem_range (hp : p ≠ 0) : p.supDegree D ∈ Set.range D := by
  obtain ⟨a, -, he⟩ := exists_supDegree_mem_support D hp; exact ⟨a, he.symm⟩

variable {D}

open Finsupp in
lemma supDegree_add_eq (h : q.supDegree D < p.supDegree D) :
    (p + q).supDegree D = p.supDegree D := by
  apply (supDegree_add_le.trans <| sup_le le_rfl h.le).antisymm
  obtain ⟨a, ha, he⟩ := exists_supDegree_mem_support D (ne_zero_of_not_supDegree_le h.not_le)
  rw [he] at h ⊢; apply Finset.le_sup
  rw [mem_support_iff, add_apply, apply_eq_zero_of_not_le_supDegree h.not_le, add_zero]
  exact mem_support_iff.mp ha

lemma leadingCoeff_add_eq (h : q.supDegree D < p.supDegree D) :
    (p + q).leadingCoeff D = p.leadingCoeff D := by
  obtain ⟨a, he⟩ := supDegree_mem_range D (ne_zero_of_not_supDegree_le h.not_le)
  rw [leadingCoeff, supDegree_add_eq h, Finsupp.add_apply, ← leadingCoeff,
      apply_eq_zero_of_not_le_supDegree (D := D), add_zero]
  rw [← he, Function.apply_invFun_apply (f := D), he]; exact h.not_le

variable (hD : D.Injective)

lemma supDegree_mem_support (hp : p ≠ 0) : D.invFun (p.supDegree D) ∈ p.support := by
  obtain ⟨a, ha, he⟩ := exists_supDegree_mem_support D hp
  rw [he, Function.leftInverse_invFun hD]; exact ha

lemma leadingCoeff_eq_zero : p.leadingCoeff D = 0 ↔ p = 0 := by
  refine ⟨(fun h => ?_).mtr, fun h => h ▸ leadingCoeff_zero⟩
  rw [leadingCoeff, ← Ne, ← Finsupp.mem_support_iff]
  exact supDegree_mem_support hD h

lemma supDegree_sub_lt_of_leadingCoeff_eq {R} [CommRing R] {p q : R[A]}
    (hd : p.supDegree D = q.supDegree D) (hc : p.leadingCoeff D = q.leadingCoeff D) :
    (p - q).supDegree D < p.supDegree D ∨ p = q := by
  by_cases he : p = q; · exact Or.inr he
  refine Or.inl ((supDegree_sub_le.trans ?_).lt_of_ne ?_)
  · rw [hd, sup_idem]
  · rw [← sub_eq_zero, ← leadingCoeff_eq_zero hD, leadingCoeff] at he
    refine fun h => he ?_
    rwa [h, Finsupp.sub_apply, ← leadingCoeff, hd, ← leadingCoeff, sub_eq_zero]

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}
  (hmax : ∀ j ∈ s, j ≠ i → (f j).supDegree D < (f i).supDegree D)

lemma supDegree_sum_lt (hs : s.Nonempty) {b : B}
    (h : ∀ i ∈ s, (f i).supDegree D < b) : (∑ i in s, f i).supDegree D < b := by
  refine supDegree_sum_le.trans_lt ((Finset.sup_lt_iff ?_).mpr h)
  obtain ⟨i, hi⟩ := hs; exact bot_le.trans_lt (h i hi)

lemma supDegree_leadingCoeff_sum_eq :
    (∑ j in s, f j).supDegree D = (f i).supDegree D ∧
    (∑ j in s, f j).leadingCoeff D = (f i).leadingCoeff D := by
  rw [← s.add_sum_erase _ hi]
  by_cases hs : s.erase i = ∅
  · rw [hs, Finset.sum_empty, add_zero]; exact ⟨rfl, rfl⟩
  suffices _ from ⟨supDegree_add_eq this, leadingCoeff_add_eq this⟩
  refine supDegree_sum_lt ?_ (fun j hj => ?_)
  · rw [Finset.nonempty_iff_ne_empty]; exact hs
  · rw [Finset.mem_erase] at hj; exact hmax j hj.2 hj.1

open Finset in
lemma sum_ne_zero_of_injOn_supDegree' (hs : ∃ i ∈ s, f i ≠ 0)
    (hd : (s : Set ι).InjOn (supDegree D ∘ f)) :
    ∑ i in s, f i ≠ 0 := by
  obtain ⟨j, hj, hne⟩ := hs
  obtain ⟨i, hi, he⟩ := exists_mem_eq_sup _ ⟨j, hj⟩ (supDegree D ∘ f)
  by_cases h : ∀ k ∈ s, k = i
  · refine (sum_eq_single_of_mem j hj (fun k hk hne => ?_)).trans_ne hne
    rw [h k hk, h j hj] at hne; exact (hne rfl).elim
  push_neg at h; obtain ⟨j, hj, hne⟩ := h
  apply ne_zero_of_supDegree_ne_bot (D := D)
  have : _; swap; rw [(supDegree_leadingCoeff_sum_eq hi this).1]
  · exact (this j hj hne).ne_bot
  exact fun k hk hne => ((le_sup hk).trans_eq he).lt_of_ne (hd.ne hk hi hne)

lemma sum_ne_zero_of_injOn_supDegree (hs : s ≠ ∅)
    (hf : ∀ i ∈ s, f i ≠ 0) (hd : (s : Set ι).InjOn (supDegree D ∘ f)) :
    ∑ i in s, f i ≠ 0 :=
  let ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hs
  sum_ne_zero_of_injOn_supDegree' ⟨i, hi, hf i hi⟩ hd

variable (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)

variable [CovariantClass B B (· + ·) (· < ·)] [CovariantClass B B (Function.swap (· + ·)) (· < ·)]

lemma apply_supDegree_add_supDegree :
    (p * q) (D.invFun (p.supDegree D + q.supDegree D)) = p.leadingCoeff D * q.leadingCoeff D := by
  obtain rfl | hp := eq_or_ne p 0
  · simp_rw [leadingCoeff_zero, zero_mul]; rfl
  obtain rfl | hq := eq_or_ne q 0
  · simp_rw [leadingCoeff_zero, mul_zero]; rfl
  obtain ⟨ap, -, hp⟩ := exists_supDegree_mem_support D hp
  obtain ⟨aq, -, hq⟩ := exists_supDegree_mem_support D hq
  simp_rw [leadingCoeff, hp, hq, ← hadd, Function.leftInverse_invFun hD _]
  exact apply_add_of_supDegree_eq hadd hD hp hq

lemma Monic.supDegree_mul_of_ne_zero (hq : q.Monic D) (hp : p ≠ 0) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D := by
  cases subsingleton_or_nontrivial R; · exact (hp (Subsingleton.elim _ _)).elim
  apply supDegree_eq_of_max
  · rw [← AddHom.mem_srange_mk hadd]
    exact add_mem (supDegree_mem_range D hp) (supDegree_mem_range D hq.ne_zero)
  · simp_rw [Finsupp.mem_support_iff, apply_supDegree_add_supDegree hD hadd, hq, mul_one,
             Ne, leadingCoeff_eq_zero hD, hp, not_false_eq_true]
  · have := covariantClass_le_of_lt B B (· + ·)
    have := covariantClass_le_of_lt B B (Function.swap (· + ·))
    exact fun a ha => (Finset.le_sup ha).trans (supDegree_mul_le hadd)

lemma Monic.supDegree_mul (hbot : (⊥ : B) + ⊥ = ⊥) (hp : p.Monic D) (hq : q.Monic D) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D := by
  cases subsingleton_or_nontrivial R
  · simp_rw [Subsingleton.eq_zero p, Subsingleton.eq_zero q, mul_zero, supDegree_zero, hbot]
  exact hq.supDegree_mul_of_ne_zero hD hadd hp.ne_zero

lemma Monic.leadingCoeff_mul (hq : q.Monic D) :
    (p * q).leadingCoeff D = p.leadingCoeff D := by
  obtain rfl | hp := eq_or_ne p 0; rw [zero_mul]
  rw [leadingCoeff, hq.supDegree_mul_of_ne_zero hD hadd hp,
      apply_supDegree_add_supDegree hD hadd, hq, mul_one]

lemma Monic.mul (hp : p.Monic D) (hq : q.Monic D) : (p * q).Monic D := by
  rw [Monic, hq.leadingCoeff_mul hD hadd]; exact hp

section AddMonoid

variable {A B : Type*} [AddMonoid A] [AddMonoid B] [LinearOrder B] [OrderBot B]
  [CovariantClass B B (· + ·) (· < ·)] [CovariantClass B B (Function.swap (· + ·)) (· < ·)]
  {D : A → B} (hzero : D 0 = 0) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
  (hD : Function.Injective D) {p : R[A]} {n : ℕ}

lemma Monic.pow (hp : p.Monic D) : (p ^ n).Monic D := by
  induction' n with n ih
  · rw [pow_zero]; exact monic_one hD
  · rw [pow_succ]; exact hp.mul hD hadd ih

lemma Monic.supDegree_pow [Nontrivial R] (hp : p.Monic D) :
    (p ^ n).supDegree D = n • p.supDegree D := by
  induction' n with n ih
  · rw [pow_zero, zero_nsmul, one_def, supDegree_single 0 1, if_neg one_ne_zero, hzero]
  · rw [pow_succ, (hp.pow hadd hD).supDegree_mul_of_ne_zero hD hadd hp.ne_zero, ih, succ_nsmul]

end AddMonoid

end LinearOrder

end SupDegree

section InfDegree

variable [AddZeroClass A] [SemilatticeInf T] [Add T] [OrderTop T]

/-- Let `R` be a semiring, let `A, B` be two `AddZeroClass`es, let `T` be an `OrderTop`,
and let `D : A → T` be a "degree" function.
For an element `f : R[A]`, the element `infDegree f : T` is the infimum of all the elements in the
support of `f`, or `⊤` if `f` is zero.
Often, the Type `T` is `WithTop A`,
If, further, `A` has a linear order, then this notion coincides with the usual one,
using the minimum of the exponents. -/
@[reducible]
def infDegree (D : A → T) (f : R[A]) : T :=
  f.support.inf D

theorem le_infDegree_add {D : A → T} (f g : R[A]) :
    (f.infDegree D) ⊓ (g.infDegree D) ≤ (f + g).infDegree D :=
  le_inf_support_add D f g

variable [CovariantClass T T (· + ·) (· ≤ ·)] [CovariantClass T T (Function.swap (· + ·)) (· ≤ ·)]
  {D : AddHom A T} in
theorem le_infDegree_mul (f g : R[A]) :
    f.infDegree D + g.infDegree D ≤ (f * g).infDegree D :=
  --  Porting note: added `a b` in `AddMonoidHom.map_add D a b`, was `AddMonoidHom.map_add D _ _`
  le_inf_support_mul (fun {a b : A} => (map_add D a b).ge) _ _

end InfDegree

end Degrees

end AddMonoidAlgebra
