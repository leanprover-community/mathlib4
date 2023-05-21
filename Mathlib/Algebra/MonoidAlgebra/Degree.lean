/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

! This file was ported from Lean 3 source module algebra.monoid_algebra.degree
! leanprover-community/mathlib commit f694c7dead66f5d4c80f446c796a5aad14707f0e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.MonoidAlgebra.Support

/-!
# Lemmas about the `sup` and `inf` of the support of `AddMonoidAlgebra`

## TODO
The current plan is to state and prove lemmas about `Finset.sup (Finsupp.support f) D` with a
"generic" degree/weight function `D` from the grading Type `A` to a somewhat ordered Type `B`.

Next, the general lemmas get specialized for some yet-to-be-defined `degree`s.
-/


variable {R A T B ι : Type _}

namespace AddMonoidAlgebra

open Classical BigOperators

/-! ### Results about the `Finset.sup` and `Finset.inf` of `Finsupp.support` -/


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
  simp_rw [Finset.sup_biUnion, Finset.sup_singleton]
  refine' Finset.sup_le fun fd fds => Finset.sup_le fun gd gds => degbm.trans <| add_le_add _ _ <;>
    exact Finset.le_sup ‹_›
#align add_monoid_algebra.sup_support_mul_le AddMonoidAlgebra.sup_support_mul_le

theorem le_inf_support_mul {degt : A → T} (degtm : ∀ {a b}, degt a + degt b ≤ degt (a + b))
    (f g : AddMonoidAlgebra R A) :
    f.support.inf degt + g.support.inf degt ≤ (f * g).support.inf degt := by
    refine' OrderDual.ofDual_le_ofDual.mpr <| sup_support_mul_le (_) f g
    intros a b
    exact OrderDual.ofDual_le_ofDual.mp degtm
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
    exact fun a ha => by rwa [Finset.mem_singleton.mp (Finsupp.support_single_subset ha)]
  | f::fs => by
    rw [List.prod_cons, List.map_cons, List.sum_cons]
    exact (sup_support_mul_le (@fun a b => degbm a b) _ _).trans
        (add_le_add_left (sup_support_list_prod_le degb0 degbm fs) _)
#align add_monoid_algebra.sup_support_list_prod_le AddMonoidAlgebra.sup_support_list_prod_le

theorem le_inf_support_list_prod (degt0 : 0 ≤ degt 0)
    (degtm : ∀ a b, degt a + degt b ≤ degt (a + b)) (l : List (AddMonoidAlgebra R A)) :
    (l.map fun f : AddMonoidAlgebra R A => f.support.inf degt).sum ≤ l.prod.support.inf degt := by
  refine' OrderDual.ofDual_le_ofDual.mpr _
  refine' sup_support_list_prod_le _ _ l
  · refine' (OrderDual.ofDual_le_ofDual.mp _)
    exact degt0
  · refine' (fun a b => OrderDual.ofDual_le_ofDual.mp _)
    exact degtm a b
#align add_monoid_algebra.le_inf_support_list_prod AddMonoidAlgebra.le_inf_support_list_prod

theorem sup_support_pow_le (degb0 : degb 0 ≤ 0) (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b)
    (n : ℕ) (f : AddMonoidAlgebra R A) : (f ^ n).support.sup degb ≤ n • f.support.sup degb := by
  rw [← List.prod_replicate, ← List.sum_replicate]
  refine' (sup_support_list_prod_le degb0 degbm _).trans_eq _
  rw [List.map_replicate]
#align add_monoid_algebra.sup_support_pow_le AddMonoidAlgebra.sup_support_pow_le

theorem le_inf_support_pow (degt0 : 0 ≤ degt 0) (degtm : ∀ a b, degt a + degt b ≤ degt (a + b))
    (n : ℕ) (f : AddMonoidAlgebra R A) : n • f.support.inf degt ≤ (f ^ n).support.inf degt := by
  refine' OrderDual.ofDual_le_ofDual.mpr <| sup_support_pow_le (OrderDual.ofDual_le_ofDual.mp _)
      (fun a b => OrderDual.ofDual_le_ofDual.mp _) n f
  exact degt0
  exact degtm _ _
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
  rw [Multiset.quot_mk_to_coe'', Multiset.coe_map, Multiset.coe_sum, Multiset.coe_prod]
  exact sup_support_list_prod_le degb0 degbm _
#align add_monoid_algebra.sup_support_multiset_prod_le AddMonoidAlgebra.sup_support_multiset_prod_le

theorem le_inf_support_multiset_prod (degt0 : 0 ≤ degt 0)
    (degtm : ∀ a b, degt a + degt b ≤ degt (a + b)) (m : Multiset (AddMonoidAlgebra R A)) :
    (m.map fun f : AddMonoidAlgebra R A => f.support.inf degt).sum ≤ m.prod.support.inf degt := by
  refine' OrderDual.ofDual_le_ofDual.mpr <|
    sup_support_multiset_prod_le (OrderDual.ofDual_le_ofDual.mp _)
      (fun a b => OrderDual.ofDual_le_ofDual.mp (_)) m
  exact degt0
  exact degtm _ _
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
#align add_monoid_algebra.le_inf_support_finset_prod AddMonoidAlgebra.le_inf_support_finset_prod

end CommutativeLemmas

end GeneralResultsAssumingSemilatticeSup

end AddMonoidAlgebra
