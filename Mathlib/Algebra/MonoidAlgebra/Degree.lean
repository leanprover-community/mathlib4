/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.MonoidAlgebra.Support

#align_import algebra.monoid_algebra.degree from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"

/-!
# Lemmas about the `sup` and `inf` of the support of `AddMonoidAlgebra`

## TODO
The current plan is to state and prove lemmas about `Finset.sup (Finsupp.support f) D` with a
"generic" degree/weight function `D` from the grading Type `A` to a somewhat ordered Type `B`.

Next, the general lemmas get specialized for some yet-to-be-defined `degree`s.
-/


variable {R R' A T B ι : Type*}

namespace AddMonoidAlgebra

open scoped Classical

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
  refine OrderDual.ofDual_le_ofDual.mpr ?_
  refine sup_support_list_prod_le ?_ ?_ l
  · refine (OrderDual.ofDual_le_ofDual.mp ?_)
    exact degt0
  · refine (fun a b => OrderDual.ofDual_le_ofDual.mp ?_)
    exact degtm a b
#align add_monoid_algebra.le_inf_support_list_prod AddMonoidAlgebra.le_inf_support_list_prod

theorem sup_support_pow_le (degb0 : degb 0 ≤ 0) (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b)
    (n : ℕ) (f : R[A]) : (f ^ n).support.sup degb ≤ n • f.support.sup degb := by
  rw [← List.prod_replicate, ← List.sum_replicate]
  refine (sup_support_list_prod_le degb0 degbm _).trans_eq ?_
  rw [List.map_replicate]
#align add_monoid_algebra.sup_support_pow_le AddMonoidAlgebra.sup_support_pow_le

theorem le_inf_support_pow (degt0 : 0 ≤ degt 0) (degtm : ∀ a b, degt a + degt b ≤ degt (a + b))
    (n : ℕ) (f : R[A]) : n • f.support.inf degt ≤ (f ^ n).support.inf degt := by
  refine OrderDual.ofDual_le_ofDual.mpr <| sup_support_pow_le (OrderDual.ofDual_le_ofDual.mp ?_)
      (fun a b => OrderDual.ofDual_le_ofDual.mp ?_) n f
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
  rw [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.sum_coe, Multiset.prod_coe]
  exact sup_support_list_prod_le degb0 degbm _
#align add_monoid_algebra.sup_support_multiset_prod_le AddMonoidAlgebra.sup_support_multiset_prod_le

theorem le_inf_support_multiset_prod (degt0 : 0 ≤ degt 0)
    (degtm : ∀ a b, degt a + degt b ≤ degt (a + b)) (m : Multiset R[A]) :
    (m.map fun f : R[A] => f.support.inf degt).sum ≤ m.prod.support.inf degt := by
  refine OrderDual.ofDual_le_ofDual.mpr <|
    sup_support_multiset_prod_le (OrderDual.ofDual_le_ofDual.mp ?_)
      (fun a b => OrderDual.ofDual_le_ofDual.mp ?_) m
  · exact degt0
  · exact degtm _ _
#align add_monoid_algebra.le_inf_support_multiset_prod AddMonoidAlgebra.le_inf_support_multiset_prod

theorem sup_support_finset_prod_le (degb0 : degb 0 ≤ 0)
    (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b) (s : Finset ι) (f : ι → R[A]) :
    (∏ i ∈ s, f i).support.sup degb ≤ ∑ i ∈ s, (f i).support.sup degb :=
  (sup_support_multiset_prod_le degb0 degbm _).trans_eq <| congr_arg _ <| Multiset.map_map _ _ _
#align add_monoid_algebra.sup_support_finset_prod_le AddMonoidAlgebra.sup_support_finset_prod_le

theorem le_inf_support_finset_prod (degt0 : 0 ≤ degt 0)
    (degtm : ∀ a b, degt a + degt b ≤ degt (a + b)) (s : Finset ι) (f : ι → R[A]) :
    (∑ i ∈ s, (f i).support.inf degt) ≤ (∏ i ∈ s, f i).support.inf degt :=
  le_of_eq_of_le (by rw [Multiset.map_map]; rfl) (le_inf_support_multiset_prod degt0 degtm _)
#align add_monoid_algebra.le_inf_support_finset_prod AddMonoidAlgebra.le_inf_support_finset_prod

end CommutativeLemmas

end GeneralResultsAssumingSemilatticeSup


/-! ### Shorthands for special cases
Note that these definitions are reducible, in order to make it easier to apply the more generic
lemmas above. -/


section Degrees

variable [Semiring R] [Ring R']

section SupDegree

variable [AddZeroClass A] [SemilatticeSup B] [Add B] [OrderBot B] (D : A → B)

/-- Let `R` be a semiring, let `A` be an `AddZeroClass`, let `B` be an `OrderBot`,
and let `D : A → B` be a "degree" function.
For an element `f : R[A]`, the element `supDegree f : B` is the supremum of all the elements in the
support of `f`, or `⊥` if `f` is zero.
Often, the Type `B` is `WithBot A`,
If, further, `A` has a linear order, then this notion coincides with the usual one,
using the maximum of the exponents. -/
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
    (∑ i ∈ s, f i).supDegree D ≤ s.sup (fun i => (f i).supDegree D) :=
  (Finset.sup_mono Finsupp.support_finset_sum).trans_eq (Finset.sup_biUnion _ _)

theorem supDegree_single_ne_zero (a : A) {r : R} (hr : r ≠ 0) :
    (single a r).supDegree D = D a := by
  rw [supDegree, Finsupp.support_single_ne_zero a hr, Finset.sup_singleton]

theorem supDegree_single (a : A) (r : R) :
    (single a r).supDegree D = if r = 0 then ⊥ else D a := by
  split_ifs with hr <;> simp [supDegree_single_ne_zero, hr]

variable {p q : R[A]}

@[simp]
theorem supDegree_zero : (0 : R[A]).supDegree D = ⊥ := by simp [supDegree]

theorem ne_zero_of_supDegree_ne_bot : p.supDegree D ≠ ⊥ → p ≠ 0 := mt (fun h => h ▸ supDegree_zero)

theorem ne_zero_of_not_supDegree_le {b : B} (h : ¬ p.supDegree D ≤ b) : p ≠ 0 :=
  ne_zero_of_supDegree_ne_bot (fun he => h <| he ▸ bot_le)

theorem apply_eq_zero_of_not_le_supDegree {a : A} (hlt : ¬ D a ≤ p.supDegree D) : p a = 0 := by
  contrapose! hlt
  exact Finset.le_sup (Finsupp.mem_support_iff.2 hlt)

variable (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)

theorem supDegree_mul_le [CovariantClass B B (· + ·) (· ≤ ·)]
    [CovariantClass B B (Function.swap (· + ·)) (· ≤ ·)] :
    (p * q).supDegree D ≤ p.supDegree D + q.supDegree D :=
  sup_support_mul_le (fun {_ _} => (hadd _ _).le) p q

theorem supDegree_prod_le {R A B : Type*} [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B]
    [SemilatticeSup B] [OrderBot B]
    [CovariantClass B B (· + ·) (· ≤ ·)] [CovariantClass B B (Function.swap (· + ·)) (· ≤ ·)]
    {D : A → B} (hzero : D 0 = 0) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    {ι} {s : Finset ι} {f : ι → R[A]} :
    (∏ i ∈ s, f i).supDegree D ≤ ∑ i ∈ s, (f i).supDegree D := by
  refine s.induction ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty, one_def, supDegree_single]
    split_ifs; exacts [bot_le, hzero.le]
  · intro i s his ih
    rw [Finset.prod_insert his, Finset.sum_insert his]
    exact (supDegree_mul_le hadd).trans (add_le_add_left ih _)

variable [CovariantClass B B (· + ·) (· < ·)] [CovariantClass B B (Function.swap (· + ·)) (· < ·)]

theorem apply_add_of_supDegree_le (hD : D.Injective) {ap aq : A}
    (hp : p.supDegree D ≤ D ap) (hq : q.supDegree D ≤ D aq) :
    (p * q) (ap + aq) = p ap * q aq := by
  simp_rw [mul_apply, Finsupp.sum]
  rw [Finset.sum_eq_single ap, Finset.sum_eq_single aq, if_pos rfl]
  · refine fun a ha hne => if_neg (fun he => ?_)
    apply_fun D at he; simp_rw [hadd] at he
    exact (add_lt_add_left (((Finset.le_sup ha).trans hq).lt_of_ne <| hD.ne_iff.2 hne) _).ne he
  · intro h; rw [if_pos rfl, Finsupp.not_mem_support_iff.1 h, mul_zero]
  · refine fun a ha hne => Finset.sum_eq_zero (fun a' ha' => if_neg <| fun he => ?_)
    apply_fun D at he
    simp_rw [hadd] at he
    have := covariantClass_le_of_lt B B (· + ·)
    exact (add_lt_add_of_lt_of_le (((Finset.le_sup ha).trans hp).lt_of_ne <| hD.ne_iff.2 hne)
      <| (Finset.le_sup ha').trans hq).ne he
  · refine fun h => Finset.sum_eq_zero (fun a _ => ite_eq_right_iff.mpr <| fun _ => ?_)
    rw [Finsupp.not_mem_support_iff.mp h, zero_mul]

theorem supDegree_withBot_some_comp {s : AddMonoidAlgebra R A} (hs : s.support.Nonempty) :
    supDegree (WithBot.some ∘ D) s = supDegree D s := by
  unfold AddMonoidAlgebra.supDegree
  rw [← Finset.coe_sup' hs, Finset.sup'_eq_sup]

end SupDegree

section InfDegree

variable [AddZeroClass A] [SemilatticeInf T] [Add T] [OrderTop T] (D : A → T)

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

variable [CovariantClass T T (· + ·) (· ≤ ·)] [CovariantClass T T (Function.swap (· + ·)) (· ≤ ·)]
  (D : AddHom A T) in
theorem le_infDegree_mul (f g : R[A]) :
    f.infDegree D + g.infDegree D ≤ (f * g).infDegree D :=
  le_inf_support_mul (fun {a b : A} => (map_add D a b).ge) _ _

variable {D}

theorem infDegree_withTop_some_comp {s : AddMonoidAlgebra R A} (hs : s.support.Nonempty) :
    infDegree (WithTop.some ∘ D) s = infDegree D s := by
  unfold AddMonoidAlgebra.infDegree
  rw [← Finset.coe_inf' hs, Finset.inf'_eq_inf]

end InfDegree

end Degrees

end AddMonoidAlgebra
