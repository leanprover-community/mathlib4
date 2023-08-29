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


variable {R A T B ι : Type*}

namespace AddMonoidAlgebra

open Classical BigOperators

/-!

# sup-degree and inf-degree of an `AddMonoidAlgebra`

Let `R` be a semiring and let `A` be a `SemilatticeSup`.
For an element `f : AddMonoidAlgebra R A`, this file defines
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


variable (degb : A → B) (degt : A → T) (f g : AddMonoidAlgebra R A)

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
    (f g : AddMonoidAlgebra R A) :
    (f * g).support.sup degb ≤ f.support.sup degb + g.support.sup degb := by
  refine' (Finset.sup_mono <| support_mul _ _).trans _
  -- ⊢ Finset.sup (Finset.biUnion f.support fun a₁ => Finset.biUnion g.support fun  …
  simp_rw [Finset.sup_biUnion, Finset.sup_singleton]
  -- ⊢ (Finset.sup f.support fun x => Finset.sup g.support fun x_1 => degb (x + x_1 …
  refine' Finset.sup_le fun fd fds => Finset.sup_le fun gd gds => degbm.trans <| add_le_add _ _ <;>
  -- ⊢ degb fd ≤ Finset.sup f.support degb
    exact Finset.le_sup ‹_›
    -- 🎉 no goals
    -- 🎉 no goals
#align add_monoid_algebra.sup_support_mul_le AddMonoidAlgebra.sup_support_mul_le

theorem le_inf_support_mul {degt : A → T} (degtm : ∀ {a b}, degt a + degt b ≤ degt (a + b))
    (f g : AddMonoidAlgebra R A) :
    f.support.inf degt + g.support.inf degt ≤ (f * g).support.inf degt := by
    refine' OrderDual.ofDual_le_ofDual.mpr <| sup_support_mul_le (_) f g
    -- ⊢ ∀ {a b : A}, degt (a + b) ≤ degt a + degt b
    intros a b
    -- ⊢ degt (a + b) ≤ degt a + degt b
    exact OrderDual.ofDual_le_ofDual.mp degtm
    -- 🎉 no goals
#align add_monoid_algebra.le_inf_support_mul AddMonoidAlgebra.le_inf_support_mul

end AddOnly

section AddMonoids

variable [AddMonoid A] [AddMonoid B] [CovariantClass B B (· + ·) (· ≤ ·)]
  [CovariantClass B B (Function.swap (· + ·)) (· ≤ ·)] [AddMonoid T]
  [CovariantClass T T (· + ·) (· ≤ ·)] [CovariantClass T T (Function.swap (· + ·)) (· ≤ ·)]
  {degb : A → B} {degt : A → T}

theorem sup_support_list_prod_le (degb0 : degb 0 ≤ 0)
    (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b) :
    ∀ l : List (AddMonoidAlgebra R A),
      l.prod.support.sup degb ≤ (l.map fun f : AddMonoidAlgebra R A => f.support.sup degb).sum
  | [] => by
    rw [List.map_nil, Finset.sup_le_iff, List.prod_nil, List.sum_nil]
    -- ⊢ ∀ (b : A), b ∈ 1.support → degb b ≤ 0
    exact fun a ha => by rwa [Finset.mem_singleton.mp (Finsupp.support_single_subset ha)]
    -- 🎉 no goals
  | f::fs => by
    rw [List.prod_cons, List.map_cons, List.sum_cons]
    -- ⊢ Finset.sup (f * List.prod fs).support degb ≤ Finset.sup f.support degb + Lis …
    exact (sup_support_mul_le (@fun a b => degbm a b) _ _).trans
        (add_le_add_left (sup_support_list_prod_le degb0 degbm fs) _)
#align add_monoid_algebra.sup_support_list_prod_le AddMonoidAlgebra.sup_support_list_prod_le

theorem le_inf_support_list_prod (degt0 : 0 ≤ degt 0)
    (degtm : ∀ a b, degt a + degt b ≤ degt (a + b)) (l : List (AddMonoidAlgebra R A)) :
    (l.map fun f : AddMonoidAlgebra R A => f.support.inf degt).sum ≤ l.prod.support.inf degt := by
  refine' OrderDual.ofDual_le_ofDual.mpr _
  -- ⊢ Quot.lift (fun l => List.foldr (fun x x_1 => x ⊓ x_1) ⊤ l) (_ : ∀ (_l₁ _l₂ : …
  refine' sup_support_list_prod_le _ _ l
  -- ⊢ degt 0 ≤ 0
  · refine' (OrderDual.ofDual_le_ofDual.mp _)
    -- ⊢ ↑OrderDual.ofDual 0 ≤ ↑OrderDual.ofDual (degt 0)
    exact degt0
    -- 🎉 no goals
  · refine' (fun a b => OrderDual.ofDual_le_ofDual.mp _)
    -- ⊢ ↑OrderDual.ofDual (degt a + degt b) ≤ ↑OrderDual.ofDual (degt (a + b))
    exact degtm a b
    -- 🎉 no goals
#align add_monoid_algebra.le_inf_support_list_prod AddMonoidAlgebra.le_inf_support_list_prod

theorem sup_support_pow_le (degb0 : degb 0 ≤ 0) (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b)
    (n : ℕ) (f : AddMonoidAlgebra R A) : (f ^ n).support.sup degb ≤ n • f.support.sup degb := by
  rw [← List.prod_replicate, ← List.sum_replicate]
  -- ⊢ Finset.sup (List.prod (List.replicate n f)).support degb ≤ List.sum (List.re …
  refine' (sup_support_list_prod_le degb0 degbm _).trans_eq _
  -- ⊢ List.sum (List.map (fun f => Finset.sup f.support degb) (List.replicate n f) …
  rw [List.map_replicate]
  -- 🎉 no goals
#align add_monoid_algebra.sup_support_pow_le AddMonoidAlgebra.sup_support_pow_le

theorem le_inf_support_pow (degt0 : 0 ≤ degt 0) (degtm : ∀ a b, degt a + degt b ≤ degt (a + b))
    (n : ℕ) (f : AddMonoidAlgebra R A) : n • f.support.inf degt ≤ (f ^ n).support.inf degt := by
  refine' OrderDual.ofDual_le_ofDual.mpr <| sup_support_pow_le (OrderDual.ofDual_le_ofDual.mp _)
      (fun a b => OrderDual.ofDual_le_ofDual.mp _) n f
  exact degt0
  -- ⊢ ↑OrderDual.ofDual (degt (a + b)) ≤ ↑OrderDual.ofDual (degt a + degt b)
  exact degtm _ _
  -- 🎉 no goals
#align add_monoid_algebra.le_inf_support_pow AddMonoidAlgebra.le_inf_support_pow

end AddMonoids

end Semiring

section CommutativeLemmas

variable [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [CovariantClass B B (· + ·) (· ≤ ·)]
  [CovariantClass B B (Function.swap (· + ·)) (· ≤ ·)] [AddCommMonoid T]
  [CovariantClass T T (· + ·) (· ≤ ·)] [CovariantClass T T (Function.swap (· + ·)) (· ≤ ·)]
  {degb : A → B} {degt : A → T}

theorem sup_support_multiset_prod_le (degb0 : degb 0 ≤ 0)
    (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b) (m : Multiset (AddMonoidAlgebra R A)) :
    m.prod.support.sup degb ≤ (m.map fun f : AddMonoidAlgebra R A => f.support.sup degb).sum := by
  induction m using Quot.inductionOn
  -- ⊢ Finset.sup (Multiset.prod (Quot.mk Setoid.r a✝)).support degb ≤ Multiset.sum …
  rw [Multiset.quot_mk_to_coe'', Multiset.coe_map, Multiset.coe_sum, Multiset.coe_prod]
  -- ⊢ Finset.sup (List.prod a✝).support degb ≤ List.sum (List.map (fun f => Finset …
  exact sup_support_list_prod_le degb0 degbm _
  -- 🎉 no goals
#align add_monoid_algebra.sup_support_multiset_prod_le AddMonoidAlgebra.sup_support_multiset_prod_le

theorem le_inf_support_multiset_prod (degt0 : 0 ≤ degt 0)
    (degtm : ∀ a b, degt a + degt b ≤ degt (a + b)) (m : Multiset (AddMonoidAlgebra R A)) :
    (m.map fun f : AddMonoidAlgebra R A => f.support.inf degt).sum ≤ m.prod.support.inf degt := by
  refine' OrderDual.ofDual_le_ofDual.mpr <|
    sup_support_multiset_prod_le (OrderDual.ofDual_le_ofDual.mp _)
      (fun a b => OrderDual.ofDual_le_ofDual.mp (_)) m
  exact degt0
  -- ⊢ ↑OrderDual.ofDual (degt (a + b)) ≤ ↑OrderDual.ofDual (degt a + degt b)
  exact degtm _ _
  -- 🎉 no goals
#align add_monoid_algebra.le_inf_support_multiset_prod AddMonoidAlgebra.le_inf_support_multiset_prod

theorem sup_support_finset_prod_le (degb0 : degb 0 ≤ 0)
    (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b) (s : Finset ι) (f : ι → AddMonoidAlgebra R A) :
    (∏ i in s, f i).support.sup degb ≤ ∑ i in s, (f i).support.sup degb :=
  (sup_support_multiset_prod_le degb0 degbm _).trans_eq <| congr_arg _ <| Multiset.map_map _ _ _
#align add_monoid_algebra.sup_support_finset_prod_le AddMonoidAlgebra.sup_support_finset_prod_le

theorem le_inf_support_finset_prod (degt0 : 0 ≤ degt 0)
    (degtm : ∀ a b, degt a + degt b ≤ degt (a + b)) (s : Finset ι) (f : ι → AddMonoidAlgebra R A) :
    (∑ i in s, (f i).support.inf degt) ≤ (∏ i in s, f i).support.inf degt :=
  le_of_eq_of_le (by rw [Multiset.map_map]; rfl) (le_inf_support_multiset_prod degt0 degtm _)
                     -- ⊢ ∑ i in s, Finset.inf (f i).support degt = Multiset.sum (Multiset.map ((fun f …
                                            -- 🎉 no goals
#align add_monoid_algebra.le_inf_support_finset_prod AddMonoidAlgebra.le_inf_support_finset_prod

end CommutativeLemmas

end GeneralResultsAssumingSemilatticeSup


/-! ### Shorthands for special cases
Note that these definitions are reducible, in order to make it easier to apply the more generic
lemmas above. -/


section Degrees

variable [Semiring R]

section SupDegree

variable [AddZeroClass A] [SemilatticeSup B] [AddZeroClass B] [OrderBot B]
  (D : A → B)

/-- Let `R` be a semiring, let `A, B` be two `AddZeroClass`es, let `B` be an `OrderBot`,
and let `D : A → B` be a "degree" function.
For an element `f : R[A]`, the `AddMonoidAlgebra R A`, the element `supDegree f : B` is the
supremum of all the elements in the support of `f`, or `⊥` if `f` is zero.
Often, the Type `B` is `WithBot A`,
If, further, `A` has a linear order, then this notion coincides with the usual one,
using the maximum of the exponents. -/
@[reducible]
def supDegree (f : AddMonoidAlgebra R A) : B :=
  f.support.sup D

theorem supDegree_add_le (f g : AddMonoidAlgebra R A) :
    (f + g).supDegree D ≤ (f.supDegree D) ⊔ (g.supDegree D) :=
  sup_support_add_le D f g

variable [CovariantClass B B (· + ·) (· ≤ ·)] [CovariantClass B B (Function.swap (· + ·)) (· ≤ ·)]
  (D : A →+ B) in
theorem supDegree_mul_le (f g : AddMonoidAlgebra R A) :
    (f * g).supDegree D ≤ f.supDegree D + g.supDegree D :=
  sup_support_mul_le (fun {_ _} => (AddMonoidHom.map_add D _ _).le) f g

end SupDegree

section InfDegree

variable [AddZeroClass A] [SemilatticeInf T] [AddZeroClass T] [OrderTop T]

/-- Let `R` be a semiring, let `A, B` be two `AddZeroClass`es, let `T` be an `OrderTop`,
and let `D : A → T` be a "degree" function.
For an element `f : R[A]`, the `AddMonoidAlgebra R A`, the element `infDegree f : T` is the
infimum of all the elements in the support of `f`, or `⊤` if `f` is zero.
Often, the Type `T` is `WithTop A`,
If, further, `A` has a linear order, then this notion coincides with the usual one,
using the minimum of the exponents. -/
@[reducible]
def infDegree (D : A → T) (f : AddMonoidAlgebra R A) : T :=
  f.support.inf D

theorem le_infDegree_add (D : A → T) (f g : AddMonoidAlgebra R A) :
    (f.infDegree D) ⊓ (g.infDegree D) ≤ (f + g).infDegree D :=
  le_inf_support_add D f g

variable [CovariantClass T T (· + ·) (· ≤ ·)] [CovariantClass T T (Function.swap (· + ·)) (· ≤ ·)]
  (D : A →+ T) in
theorem le_infDegree_mul (f g : AddMonoidAlgebra R A) :
    f.infDegree D + g.infDegree D ≤ (f * g).infDegree D :=
  --  Porting note: added `a b` in `AddMonoidHom.map_add D a b`, was `AddMonoidHom.map_add D _ _`
  le_inf_support_mul (fun {a b : A} => (AddMonoidHom.map_add D a b).ge) _ _

end InfDegree

end Degrees

end AddMonoidAlgebra
