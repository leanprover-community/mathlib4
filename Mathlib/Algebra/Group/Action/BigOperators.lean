/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Action.Defs

/-!
# Lemmas about group actions on big operators
-/

assert_not_exists MonoidWithZero

variable {ι M N : Type*}

namespace List

@[to_additive]
theorem smul_prod [Monoid M] [MulOneClass N] [MulAction M N] [IsScalarTower M N N]
    [SMulCommClass M N N] (l : List N) (m : M) :
    m ^ l.length • l.prod = (l.map (m • ·)).prod := by
  induction l with
  | nil => simp
  | cons head tail ih => simp [← ih, smul_mul_smul_comm, pow_succ']

end List

namespace Multiset

@[to_additive]
theorem smul_prod [Monoid M] [CommMonoid N] [MulAction M N] [IsScalarTower M N N]
    [SMulCommClass M N N] (s : Multiset N) (b : M) :
    b ^ card s • s.prod = (s.map (b • ·)).prod :=
  Quot.induction_on s <| by simp [List.smul_prod]

end Multiset

namespace Finset

@[to_additive]
theorem smul_prod
    [CommMonoid N] [Monoid M] [MulAction M N] [IsScalarTower M N N] [SMulCommClass M N N]
    (s : Finset ι) (b : M) (f : ι → N) :
    b ^ #s • ∏ i ∈ s, f i = ∏ i ∈ s, b • f i := by
  have : Multiset.map (b • f ·) s.val = .map (b • ·) (.map f s.val) := by
    simp only [Multiset.map_map, Function.comp_apply]
  simp_rw [prod_eq_multiset_prod, card_def, this, ← Multiset.smul_prod _ b, Multiset.card_map]

@[to_additive]
lemma prod_smul
    [CommMonoid N] [CommMonoid M] [MulAction M N] [IsScalarTower M N N] [SMulCommClass M N N]
    (s : Finset ι) (b : ι → M) (f : ι → N) :
    ∏ i ∈ s, b i • f i = (∏ i ∈ s, b i) • ∏ i ∈ s, f i := by
  induction s using Finset.cons_induction_on <;> simp [smul_mul_smul_comm, *]

end Finset
