/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Group.Action.Basic

/-!
# Lemmas about group actions on big operators

This file contains results about two kinds of actions:

* sums over `DistribSMul`: `r • ∑ x ∈ s, f x = ∑ x ∈ s, r • f x`
* products over `MulDistribMulAction` (with primed name): `r • ∏ x ∈ s, f x = ∏ x ∈ s, r • f x`
* products over `SMulCommClass` (with unprimed name):
  `b ^ s.card • ∏ x ∈ s, f x = ∏ x ∈ s, b • f x`

Note that analogous lemmas for `Module`s like `Finset.sum_smul` appear in other files.
-/


variable {M N γ : Type*}

section

variable [AddMonoid N] [DistribSMul M N]

theorem List.smul_sum {r : M} {l : List N} : r • l.sum = (l.map (r • ·)).sum :=
  map_list_sum (DistribSMul.toAddMonoidHom N r) l

end

section

variable [Monoid M] [Monoid N] [MulDistribMulAction M N]

theorem List.smul_prod' {r : M} {l : List N} : r • l.prod = (l.map (r • ·)).prod :=
  map_list_prod (MulDistribMulAction.toMonoidHom N r) l

end

section

variable [AddCommMonoid N] [DistribSMul M N] {r : M}

theorem Multiset.smul_sum {s : Multiset N} : r • s.sum = (s.map (r • ·)).sum :=
  (DistribSMul.toAddMonoidHom N r).map_multiset_sum s

theorem Finset.smul_sum {f : γ → N} {s : Finset γ} :
    (r • ∑ x ∈ s, f x) = ∑ x ∈ s, r • f x :=
  map_sum (DistribSMul.toAddMonoidHom N r) f s

theorem smul_finsum_mem {f : γ → N} {s : Set γ} (hs : s.Finite) :
    r • ∑ᶠ x ∈ s, f x = ∑ᶠ x ∈ s, r • f x :=
  (DistribSMul.toAddMonoidHom N r).map_finsum_mem f hs

end

section

variable [Monoid M] [CommMonoid N] [MulDistribMulAction M N]

theorem Multiset.smul_prod' {r : M} {s : Multiset N} : r • s.prod = (s.map (r • ·)).prod :=
  (MulDistribMulAction.toMonoidHom N r).map_multiset_prod s

theorem Finset.smul_prod' {r : M} {f : γ → N} {s : Finset γ} :
    (r • ∏ x ∈ s, f x) = ∏ x ∈ s, r • f x :=
  map_prod (MulDistribMulAction.toMonoidHom N r) f s

theorem smul_finprod' {ι : Sort*} [Finite ι] {f : ι → N} (r : M) :
    r • ∏ᶠ x : ι, f x = ∏ᶠ x : ι, r • (f x) := by
  cases nonempty_fintype (PLift ι)
  simp only [finprod_eq_prod_plift_of_mulSupport_subset (s := Finset.univ) (by simp),
    Finset.smul_prod']

variable {G : Type*} [Group G] [MulDistribMulAction G N]

theorem Finset.smul_prod_perm [Fintype G] (b : N) (g : G) :
    (g • ∏ h : G, h • b) = ∏ h : G, h • b := by
  simp only [smul_prod', smul_smul]
  exact Finset.prod_bijective (g * ·) (Group.mulLeft_bijective g) (by simp) (fun _ _ ↦ rfl)

theorem smul_finprod_perm [Finite G] (b : N) (g : G) :
    (g • ∏ᶠ h : G, h • b) = ∏ᶠ h : G, h • b := by
  cases nonempty_fintype G
  simp only [finprod_eq_prod_of_fintype, Finset.smul_prod_perm]

end

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

theorem smul_prod
    [CommMonoid N] [Monoid M] [MulAction M N] [IsScalarTower M N N] [SMulCommClass M N N]
    (s : Finset N) (b : M) (f : N → N) :
    b ^ s.card • ∏ x ∈ s, f x = ∏ x ∈ s, b • f x := by
  have : Multiset.map (fun (x : N) ↦ b • f x) s.val =
      Multiset.map (fun x ↦ b • x) (Multiset.map f s.val) := by
    simp only [Multiset.map_map, Function.comp_apply]
  simp_rw [prod_eq_multiset_prod, card_def, this, ← Multiset.smul_prod _ b, Multiset.card_map]

theorem prod_smul
    [CommMonoid N] [CommMonoid M] [MulAction M N] [IsScalarTower M N N] [SMulCommClass M N N]
    (s : Finset N) (b : N → M) (f : N → N) :
    ∏ i ∈ s, b i • f i = (∏ i ∈ s, b i) • ∏ i ∈ s, f i := by
  induction s using Finset.cons_induction_on with
  | empty =>  simp
  | cons _ _ hj ih => rw [prod_cons, ih, smul_mul_smul_comm, ← prod_cons hj, ← prod_cons hj]

end Finset
