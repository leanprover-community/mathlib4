/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov, Yaël Dillies

! This file was ported from Lean 3 source module algebra.module.big_operators
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.GroupTheory.GroupAction.BigOperators

/-!
# Finite sums over modules over a ring
-/


open BigOperators

variable {α β R M ι : Type _}

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x y : M)

theorem List.sum_smul {l : List R} {x : M} : l.Sum • x = (l.map fun r => r • x).Sum :=
  ((smulAddHom R M).flip x).map_list_sum l
#align list.sum_smul List.sum_smul

theorem Multiset.sum_smul {l : Multiset R} {x : M} : l.Sum • x = (l.map fun r => r • x).Sum :=
  ((smulAddHom R M).flip x).map_multiset_sum l
#align multiset.sum_smul Multiset.sum_smul

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Multiset.sum_smul_sum {s : Multiset R} {t : Multiset M} :
    s.Sum • t.Sum = ((s ×ˢ t).map fun p : R × M => p.fst • p.snd).Sum :=
  by
  induction' s using Multiset.induction with a s ih
  · simp
  · simp [add_smul, ih, ← Multiset.smul_sum]
#align multiset.sum_smul_sum Multiset.sum_smul_sum

/- warning: finset.sum_smul -> Finset.sum_smul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u_3}} {M : Type.{u_4}} {ι : Type.{u_5}} [_inst_1 : Semiring.{u_3} R] [_inst_2 : AddCommMonoid.{u_4} M] [_inst_3 : Module.{u_3, u_4} R M _inst_1 _inst_2] {f : ι -> R} {s : Finset.{u_5} ι} {x : M}, Eq.{succ u_4} M (SMul.smul.{u_3, u_4} R M (SMulZeroClass.toHasSmul.{u_3, u_4} R M (AddZeroClass.toHasZero.{u_4} M (AddMonoid.toAddZeroClass.{u_4} M (AddCommMonoid.toAddMonoid.{u_4} M _inst_2))) (SMulWithZero.toSmulZeroClass.{u_3, u_4} R M (MulZeroClass.toHasZero.{u_3} R (MulZeroOneClass.toMulZeroClass.{u_3} R (MonoidWithZero.toMulZeroOneClass.{u_3} R (Semiring.toMonoidWithZero.{u_3} R _inst_1)))) (AddZeroClass.toHasZero.{u_4} M (AddMonoid.toAddZeroClass.{u_4} M (AddCommMonoid.toAddMonoid.{u_4} M _inst_2))) (MulActionWithZero.toSMulWithZero.{u_3, u_4} R M (Semiring.toMonoidWithZero.{u_3} R _inst_1) (AddZeroClass.toHasZero.{u_4} M (AddMonoid.toAddZeroClass.{u_4} M (AddCommMonoid.toAddMonoid.{u_4} M _inst_2))) (Module.toMulActionWithZero.{u_3, u_4} R M _inst_1 _inst_2 _inst_3)))) (Finset.sum.{u_3, u_5} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u_3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_3} R (Semiring.toNonAssocSemiring.{u_3} R _inst_1))) s (fun (i : ι) => f i)) x) (Finset.sum.{u_4, u_5} M ι _inst_2 s (fun (i : ι) => SMul.smul.{u_3, u_4} R M (SMulZeroClass.toHasSmul.{u_3, u_4} R M (AddZeroClass.toHasZero.{u_4} M (AddMonoid.toAddZeroClass.{u_4} M (AddCommMonoid.toAddMonoid.{u_4} M _inst_2))) (SMulWithZero.toSmulZeroClass.{u_3, u_4} R M (MulZeroClass.toHasZero.{u_3} R (MulZeroOneClass.toMulZeroClass.{u_3} R (MonoidWithZero.toMulZeroOneClass.{u_3} R (Semiring.toMonoidWithZero.{u_3} R _inst_1)))) (AddZeroClass.toHasZero.{u_4} M (AddMonoid.toAddZeroClass.{u_4} M (AddCommMonoid.toAddMonoid.{u_4} M _inst_2))) (MulActionWithZero.toSMulWithZero.{u_3, u_4} R M (Semiring.toMonoidWithZero.{u_3} R _inst_1) (AddZeroClass.toHasZero.{u_4} M (AddMonoid.toAddZeroClass.{u_4} M (AddCommMonoid.toAddMonoid.{u_4} M _inst_2))) (Module.toMulActionWithZero.{u_3, u_4} R M _inst_1 _inst_2 _inst_3)))) (f i) x))
but is expected to have type
  forall {R : Type.{u}} {M : Type.{v}} [ι : AddCommMonoid.{u} R] (_inst_1 : Finset.{v} M) (_inst_2 : Nat) (_inst_3 : M -> R), Eq.{succ u} R (Finset.sum.{u, v} R M ι _inst_1 (fun (x : M) => HSMul.hSMul.{0, u, u} Nat R R (instHSMul.{0, u} Nat R (AddMonoid.SMul.{u} R (AddCommMonoid.toAddMonoid.{u} R ι))) _inst_2 (_inst_3 x))) (HSMul.hSMul.{0, u, u} Nat R R (instHSMul.{0, u} Nat R (AddMonoid.SMul.{u} R (AddCommMonoid.toAddMonoid.{u} R ι))) _inst_2 (Finset.sum.{u, v} R M ι _inst_1 (fun (x : M) => _inst_3 x)))
Case conversion may be inaccurate. Consider using '#align finset.sum_smul Finset.sum_smulₓ'. -/
theorem Finset.sum_smul {f : ι → R} {s : Finset ι} {x : M} :
    (∑ i in s, f i) • x = ∑ i in s, f i • x :=
  ((smulAddHom R M).flip x).map_sum f s
#align finset.sum_smul Finset.sum_smul

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Finset.sum_smul_sum {f : α → R} {g : β → M} {s : Finset α} {t : Finset β} :
    ((∑ i in s, f i) • ∑ i in t, g i) = ∑ p in s ×ˢ t, f p.fst • g p.snd :=
  by
  rw [Finset.sum_product, Finset.sum_smul, Finset.sum_congr rfl]
  intros
  rw [Finset.smul_sum]
#align finset.sum_smul_sum Finset.sum_smul_sum

end AddCommMonoid

theorem Finset.cast_card [CommSemiring R] (s : Finset α) : (s.card : R) = ∑ a in s, 1 := by
  rw [Finset.sum_const, Nat.smul_one_eq_coe]
#align finset.cast_card Finset.cast_card

