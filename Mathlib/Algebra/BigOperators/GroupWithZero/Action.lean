/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Data.Finset.Basic
public import Mathlib.Algebra.Group.Action.Basic

/-!
# Lemmas about group with zero actions on big operators

This file contains results about two kinds of actions:

* sums over `DistribSMul`: `r • ∑ x ∈ s, f x = ∑ x ∈ s, r • f x`
* products over `MulDistribMulAction` (with primed name): `r • ∏ x ∈ s, f x = ∏ x ∈ s, r • f x`

Note that analogous lemmas for `Module`s like `Finset.sum_smul` appear in other files.
-/

@[expose] public section


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
