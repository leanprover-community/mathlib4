/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.Group.UniqueProds
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Finsupp.Lex
import Mathlib.Data.ZMod.Basic

#align_import zero_divisors_in_add_monoid_algebras from "leanprover-community/mathlib"@"328375597f2c0dd00522d9c2e5a33b6a6128feeb"

/-!
# Examples of zero-divisors in `AddMonoidAlgebra`s

This file contains an easy source of zero-divisors in an `AddMonoidAlgebra`.
If `k` is a field and `G` is an additive group containing a non-zero torsion element, then
`k[G]` contains non-zero zero-divisors: this is lemma `zero_divisors_of_torsion`.

There is also a version for periodic elements of an additive monoid: `zero_divisors_of_periodic`.

The converse of this statement is
[Kaplansky's zero divisor conjecture](https://en.wikipedia.org/wiki/Kaplansky%27s_conjectures).

The formalized example generalizes in trivial ways the assumptions: the field `k` can be any
nontrivial ring `R` and the additive group `G` with a torsion element can be any additive monoid
`A` with a non-zero periodic element.

Besides this example, we also address a comment in `Data.Finsupp.Lex` to the effect that the proof
that addition is monotone on `α →₀ N` uses that it is *strictly* monotone on `N`.

The specific statement is about `Finsupp.Lex.covariantClass_lt_left` and its analogue
`Finsupp.Lex.covariantClass_le_right`.  We do not need two separate counterexamples, since the
operation is commutative.

The example is very simple.  Let `F = {0, 1}` with order determined by `0 < 1` and absorbing
addition (which is the same as `max` in this case).  We denote a function `f : F → F` (which is
automatically finitely supported!) by `[f 0, f 1]`, listing its values.  Recall that the order on
finitely supported function is lexicographic, matching the list notation.  The inequality
`[0, 1] ≤ [1, 0]` holds.  However, adding `[1, 0]` to both sides yields the *reversed* inequality
`[1, 1] > [1, 0]`.
-/


set_option linter.uppercaseLean3 false

open Finsupp hiding single
open AddMonoidAlgebra

namespace Counterexample

/-- This is a simple example showing that if `R` is a non-trivial ring and `A` is an additive
monoid with an element `a` satisfying `n • a = a` and `(n - 1) • a ≠ a`, for some `2 ≤ n`,
then `R[A]` contains non-zero zero-divisors.  The elements are easy to write down:
`[a]` and `[a] ^ (n - 1) - 1` are non-zero elements of `R[A]` whose product
is zero.

Observe that such an element `a` *cannot* be invertible.  In particular, this lemma never applies
if `A` is a group. -/
theorem zero_divisors_of_periodic {R A} [Nontrivial R] [Ring R] [AddMonoid A] {n : ℕ} (a : A)
    (n2 : 2 ≤ n) (na : n • a = a) (na1 : (n - 1) • a ≠ 0) :
    ∃ f g : R[A], f ≠ 0 ∧ g ≠ 0 ∧ f * g = 0 := by
  refine' ⟨single a 1, single ((n - 1) • a) 1 - single 0 1, by simp, _, _⟩
  · exact sub_ne_zero.mpr (by simpa [single, AddMonoidAlgebra, single_eq_single_iff])
  · rw [mul_sub, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single,
      sub_eq_zero, add_zero, ← succ_nsmul, Nat.sub_add_cancel (one_le_two.trans n2), na]
#align counterexample.zero_divisors_of_periodic Counterexample.zero_divisors_of_periodic

theorem single_zero_one {R A} [Semiring R] [Zero A] :
    single (0 : A) (1 : R) = (1 : R[A]) :=
  rfl
#align counterexample.single_zero_one Counterexample.single_zero_one

/-- This is a simple example showing that if `R` is a non-trivial ring and `A` is an additive
monoid with a non-zero element `a` of finite order `oa`, then `R[A]` contains
non-zero zero-divisors.  The elements are easy to write down:
`∑ i in Finset.range oa, [a] ^ i` and `[a] - 1` are non-zero elements of `R[A]`
whose product is zero.

In particular, this applies whenever the additive monoid `A` is an additive group with a non-zero
torsion element. -/
theorem zero_divisors_of_torsion {R A} [Nontrivial R] [Ring R] [AddMonoid A] (a : A)
    (o2 : 2 ≤ addOrderOf a) : ∃ f g : R[A], f ≠ 0 ∧ g ≠ 0 ∧ f * g = 0 := by
  refine'
    ⟨(Finset.range (addOrderOf a)).sum fun i : ℕ => single a 1 ^ i, single a 1 - single 0 1, _, _,
      _⟩
  · apply_fun fun x : R[A] => x 0
    refine' ne_of_eq_of_ne (_ : (_ : R) = 1) one_ne_zero
    dsimp only; rw [Finset.sum_apply']
    refine (Finset.sum_eq_single 0 ?_ ?_).trans ?_
    · intro b hb b0
      rw [single_pow, one_pow, single_eq_of_ne]
      exact nsmul_ne_zero_of_lt_addOrderOf' b0 (Finset.mem_range.mp hb)
    · simp only [(zero_lt_two.trans_le o2).ne', Finset.mem_range, not_lt, le_zero_iff,
        false_imp_iff]
    · rw [single_pow, one_pow, zero_smul, single_eq_same]
  · apply_fun fun x : R[A] => x 0
    refine' sub_ne_zero.mpr (ne_of_eq_of_ne (_ : (_ : R) = 0) _)
    · have a0 : a ≠ 0 :=
        ne_of_eq_of_ne (one_nsmul a).symm
          (nsmul_ne_zero_of_lt_addOrderOf' one_ne_zero (Nat.succ_le_iff.mp o2))
      simp only [a0, single_eq_of_ne, Ne.def, not_false_iff]
    · simpa only [single_eq_same] using zero_ne_one
  · convert Commute.geom_sum₂_mul (α := AddMonoidAlgebra R A) _ (addOrderOf a) using 3
    · rw [single_zero_one, one_pow, mul_one]
    · rw [single_pow, one_pow, addOrderOf_nsmul_eq_zero, single_zero_one, one_pow, sub_self]
    · simp only [single_zero_one, Commute.one_right]
#align counterexample.zero_divisors_of_torsion Counterexample.zero_divisors_of_torsion

example {R} [Ring R] [Nontrivial R] (n : ℕ) (n0 : 2 ≤ n) :
    ∃ f g : AddMonoidAlgebra R (ZMod n), f ≠ 0 ∧ g ≠ 0 ∧ f * g = 0 :=
  zero_divisors_of_torsion (1 : ZMod n) (n0.trans_eq (ZMod.addOrderOf_one _).symm)

/-- `F` is the type with two elements `zero` and `one`.  We define the "obvious" linear order and
absorbing addition on it to generate our counterexample. -/
inductive F
  | zero
  | one
  deriving DecidableEq, Inhabited
#align counterexample.F Counterexample.F

/-- The same as `List.getRest`, except that we take the "rest" from the first match, rather than
from the beginning, returning `[]` if there is no match.  For instance,
```lean
#eval dropUntil [1,2] [3,1,2,4,1,2]  -- [4, 1, 2]
```
-/
def List.dropUntil {α} [DecidableEq α] : List α → List α → List α
  | _, [] => []
  | l, a :: as => ((a::as).getRest l).getD (dropUntil l as)
#align counterexample.list.drop_until Counterexample.List.dropUntil

open Lean Elab in
/-- `guard_decl na mod` makes sure that the declaration with name `na` is in the module `mod`.
```lean
guard_decl Nat.nontrivial Mathlib.Data.Nat.Basic -- does nothing

guard_decl Nat.nontrivial Not.In.Here
-- the module Not.In.Here is not imported!
```

This test makes sure that the comment referring to this example is in the file claimed in the
doc-module to this counterexample. -/
elab "guard_decl" na:ident mod:ident : command => do
  let dcl ← resolveGlobalConstNoOverloadWithInfo na
  let mdn := mod.getId
  let env ← getEnv
  let .some dcli := env.getModuleIdxFor? dcl | unreachable!
  let .some mdni := env.getModuleIdx? mdn | throwError "the module {mod} is not imported!"
  unless dcli = mdni do throwError "instance {na} is no longer in {mod}."

guard_decl Finsupp.Lex.covariantClass_le_left Mathlib.Data.Finsupp.Lex

guard_decl Finsupp.Lex.covariantClass_le_right Mathlib.Data.Finsupp.Lex

namespace F

instance : Zero F :=
  ⟨F.zero⟩

/-- `1` is not really needed, but it is nice to use the notation. -/
instance : One F :=
  ⟨F.one⟩

/-- A tactic to prove trivial goals by enumeration. -/
macro "boom" : tactic => `(tactic| (repeat' rintro ⟨⟩) <;> decide)

/-- `val` maps `0 1 : F` to their counterparts in `ℕ`.
We use it to lift the linear order on `ℕ`. -/
def val : F → ℕ
  | 0 => 0
  | 1 => 1
#align counterexample.F.val Counterexample.F.val

instance : LinearOrder F :=
  LinearOrder.lift' val (by boom)

@[simp]
theorem z01 : (0 : F) < 1 := by decide
#align counterexample.F.z01 Counterexample.F.z01

/-- `F` would be a `CommSemiring`, using `min` as multiplication.  Again, we do not need this. -/
instance : AddCommMonoid F where
  add := max
  add_assoc := by boom
  zero := 0
  zero_add := by boom
  add_zero := by boom
  add_comm := by boom

/-- The `CovariantClass`es asserting monotonicity of addition hold for `F`. -/
instance covariantClass_add_le : CovariantClass F F (· + ·) (· ≤ ·) :=
  ⟨by boom⟩
#align counterexample.F.covariant_class_add_le Counterexample.F.covariantClass_add_le

example : CovariantClass F F (Function.swap (· + ·)) (· ≤ ·) := by infer_instance

/-- The following examples show that `F` has all the typeclasses used by
`Finsupp.Lex.covariantClass_le_left`... -/
example : LinearOrder F := by infer_instance

example : AddMonoid F := by infer_instance

/-- ... except for the strict monotonicity of addition, the crux of the matter. -/
example : ¬CovariantClass F F (· + ·) (· < ·) := fun h =>
  lt_irrefl 1 <| (h.elim : Covariant F F (· + ·) (· < ·)) 1 z01

/-- A few `simp`-lemmas to take care of trivialities in the proof of the example below. -/
@[simp]
theorem f1 : ∀ a : F, 1 + a = 1 := by boom
#align counterexample.F.f1 Counterexample.F.f1

@[simp]
theorem f011 : ofLex (Finsupp.single (0 : F) (1 : F)) 1 = 0 :=
  single_apply_eq_zero.mpr fun h => h
#align counterexample.F.f011 Counterexample.F.f011

@[simp]
theorem f010 : ofLex (Finsupp.single (0 : F) (1 : F)) 0 = 1 :=
  single_eq_same
#align counterexample.F.f010 Counterexample.F.f010

@[simp]
theorem f111 : ofLex (Finsupp.single (1 : F) (1 : F)) 1 = 1 :=
  single_eq_same
#align counterexample.F.f111 Counterexample.F.f111

@[simp]
theorem f110 : ofLex (Finsupp.single (1 : F) (1 : F)) 0 = 0 :=
  single_apply_eq_zero.mpr fun h => h.symm
#align counterexample.F.f110 Counterexample.F.f110

/-- Here we see that (not-necessarily strict) monotonicity of addition on `Lex (F →₀ F)` is not
a consequence of monotonicity of addition on `F`.  Strict monotonicity of addition on `F` is
enough and is the content of `Finsupp.Lex.covariantClass_le_left`. -/
example : ¬CovariantClass (Lex (F →₀ F)) (Lex (F →₀ F)) (· + ·) (· ≤ ·) := by
  rintro ⟨h⟩
  refine (not_lt (α := Lex (F →₀ F))).mpr (@h (Finsupp.single (0 : F) (1 : F))
    (Finsupp.single 1 1) (Finsupp.single 0 1) ?_) ⟨1, ?_⟩
  · exact Or.inr ⟨0, by simp [(by boom : ∀ j : F, j < 0 ↔ False)]⟩
  · simp only [(by boom : ∀ j : F, j < 1 ↔ j = 0), ofLex_add, coe_add, Pi.add_apply, forall_eq,
      f010, f1, f110, add_zero, f011, f111, zero_add, and_self]

example {α} [Ring α] [Nontrivial α] : ∃ f g : AddMonoidAlgebra α F, f ≠ 0 ∧ g ≠ 0 ∧ f * g = 0 :=
  zero_divisors_of_periodic (1 : F) le_rfl (by simp [two_smul]) z01.ne'

example {α} [Zero α] :
    2 • (Finsupp.single 0 1 : α →₀ F) = Finsupp.single 0 1 ∧ (Finsupp.single 0 1 : α →₀ F) ≠ 0 :=
  ⟨smul_single _ _ _, by simp [Ne.def, Finsupp.single_eq_zero, z01.ne]⟩

end F

/-- A Type that does not have `UniqueProds`. -/
example : ¬UniqueProds ℕ := by
  rintro ⟨h⟩
  refine' not_not.mpr (h (Finset.singleton_nonempty 0) (Finset.insert_nonempty 0 {1})) _
  simp [UniqueMul, not_or]
  exact ⟨⟨0, 1, by simp⟩, ⟨0, 0, by simp⟩⟩

/-- Some Types that do not have `UniqueSums`. -/
example (n : ℕ) (n2 : 2 ≤ n) : ¬UniqueSums (ZMod n) := by
  haveI : Fintype (ZMod n) := @ZMod.fintype n ⟨(zero_lt_two.trans_le n2).ne'⟩
  haveI : Nontrivial (ZMod n) := CharP.nontrivial_of_char_ne_one (one_lt_two.trans_le n2).ne'
  rintro ⟨h⟩
  refine' not_not.mpr (h Finset.univ_nonempty Finset.univ_nonempty) _
  suffices ∀ x y : ZMod n, ∃ x' y' : ZMod n, x' + y' = x + y ∧ (x' = x → ¬y' = y) by
    simpa [UniqueAdd]
  exact fun x y => ⟨x - 1, y + 1, sub_add_add_cancel _ _ _, by simp⟩

end Counterexample
