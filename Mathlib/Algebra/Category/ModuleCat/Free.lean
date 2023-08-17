/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Homology.ShortExact.Preadditive
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Rank
import Mathlib.LinearAlgebra.Dimension
import Mathlib.LinearAlgebra.Finrank

/-!
# Exact sequences with free modules

This file proves results about linear independence and span in exact sequences of modules.

## Main theorems

* `linearIndependent_shortExact`: Given a short exact sequence `0 ⟶ N ⟶ M ⟶ P ⟶ 0` of
  `R`-modules and linearly independent families `v : ι → N` and `w : ι' → M`, we get a linearly
  independent family `ι ⊕ ι' → M`
* `span_rightExact`: Given an exact sequence `N ⟶ M ⟶ P ⟶ 0` of `R`-modules and spanning
  families `v : ι → N` and `w : ι' → M`, we get a spanning family `ι ⊕ ι' → M`
* Using `linearIndependent_shortExact` and `span_rightExact`, we prove `free_shortExact`: In a
  short exact sequence `0 ⟶ N ⟶ M ⟶ P ⟶ 0` where `N` and `P` are free, `M` is free as well.

## Tags
linear algebra, module, free

-/

set_option autoImplicit true

namespace ModuleCat

variable {ι ι' R : Type*}[Ring R] {N P : ModuleCat R} {v : ι → N}

open CategoryTheory Submodule Set

section LinearIndependent

variable (hv : LinearIndependent R v) {M : ModuleCat R}
  {u : ι ⊕ ι' → M} {f : N ⟶ M} {g : M ⟶ P}
  (hw : LinearIndependent R (g ∘ u ∘ Sum.inr))
  (hm : Mono f) (he : Exact f g) (huv : u ∘ Sum.inl = f ∘ v)

theorem disjoint_span_sum : Disjoint (span R (range (u ∘ Sum.inl)))
    (span R (range (u ∘ Sum.inr))) := by
  rw [huv, disjoint_comm]
  refine' Disjoint.mono_right (span_mono (range_comp_subset_range _ _)) _
  rw [← LinearMap.range_coe, (span_eq (LinearMap.range f)), (exact_iff _ _).mp he]
  exact range_ker_disjoint hw

/-- In the commutative diagram
```
             f     g
    0 --→ N --→ M --→  P
          ↑     ↑      ↑
         v|    u|     w|
          ι → ι ⊕ ι' ← ι'
```
where the top row is an exact sequence of modules and the maps on the bottom are `Sum.inl` and
`Sum.inr`. If `u` is injective and `v` and `w` are linearly independent, then `u` is linearly
independent. -/
theorem linearIndependent_leftExact : LinearIndependent R u :=
  linearIndependent_sum.mpr
  ⟨(congr_arg (fun f ↦ LinearIndependent R f) huv).mpr
    ((LinearMap.linearIndependent_iff (f : N →ₗ[R] M)
    (LinearMap.ker_eq_bot.mpr ((mono_iff_injective _).mp hm))).mpr hv),
    LinearIndependent.of_comp g hw, disjoint_span_sum hw he huv⟩

/-- Given a short exact sequence `0 ⟶ N ⟶ M ⟶ P ⟶ 0` of `R`-modules and linearly independent
    families `v : ι → N` and `w : ι' → P`, we get a linearly independent family `ι ⊕ ι' → M` -/
theorem linearIndependent_shortExact {w : ι' → P}
    (hw : LinearIndependent R w) (hse : ShortExact f g) :
    LinearIndependent R (Sum.elim (f ∘ v) (g.toFun.invFun ∘ w)) := by
  refine' linearIndependent_leftExact hv _ hse.mono hse.exact _
  · simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Sum.elim_comp_inr]
    rwa [← Function.comp.assoc, Function.RightInverse.comp_eq_id (Function.rightInverse_invFun
      ((epi_iff_surjective _).mp hse.epi)),
      Function.comp.left_id]
  · simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Sum.elim_comp_inl]

end LinearIndependent

section Span

variable {M : ModuleCat R} {u : ι⊕ ι' → M} {f : N ⟶ M} {g : M ⟶ P}

/-- In the commutative diagram
```
    f     g
 N --→ M --→  P
 ↑     ↑      ↑
v|    u|     w|
 ι → ι ⊕ ι' ← ι'
```
where the top row is an exact sequence of modules and the maps on the bottom are `Sum.inl` and
`Sum.inr`. If `v` spans `N` and `w` spans `P`, then `u` spans `M`. -/
theorem span_exact (he : Exact f g) (huv : u ∘ Sum.inl = f ∘ v)
    (hv : ⊤ ≤ span R (range v))
    (hw : ⊤ ≤ span R (range (g ∘ u ∘ Sum.inr))) :
    ⊤ ≤ span R (range u) := by
  intro m _
  have hgm : g m ∈ span R (range (g ∘ u ∘ Sum.inr)) := hw mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hgm
  obtain ⟨cm, hm⟩ := hgm
  let m' : M := Finsupp.sum cm fun j a ↦ a • (u (Sum.inr j))
  have hsub : m - m' ∈ LinearMap.range f
  · rw [(exact_iff _ _).mp he]
    simp only [LinearMap.mem_ker, map_sub, sub_eq_zero]
    rw [← hm, map_finsupp_sum]
    simp only [Function.comp_apply, SMulHomClass.map_smul]
  obtain ⟨n, hnm⟩ := hsub
  have hn : n ∈ span R (range v) := hv mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hn
  obtain ⟨cn, hn⟩ := hn
  rw [← hn, map_finsupp_sum] at hnm
  rw [← sub_add_cancel m m', ← hnm,]
  simp only [SMulHomClass.map_smul]
  have hn' : (Finsupp.sum cn fun a b ↦ b • f (v a)) =
      (Finsupp.sum cn fun a b ↦ b • u (Sum.inl a)) :=
    by congr; ext a b; change b • (f ∘ v) a = _; rw [← huv]; rfl
  rw [hn']
  apply add_mem
  · rw [Finsupp.mem_span_range_iff_exists_finsupp]
    use cn.mapDomain (Sum.inl)
    rw [Finsupp.sum_mapDomain_index_inj Sum.inl_injective]
  · rw [Finsupp.mem_span_range_iff_exists_finsupp]
    use cm.mapDomain (Sum.inr)
    rw [Finsupp.sum_mapDomain_index_inj Sum.inr_injective]

/-- Given an exact sequence `N ⟶ M ⟶ P ⟶ 0` of `R`-modules and spanning
    families `v : ι → N` and `w : ι' → P`, we get a spanning family `ι ⊕ ι' → M` -/
theorem span_rightExact {w : ι' → P} (hv : ⊤ ≤ span R (range v))
    (hw : ⊤ ≤ span R (range w)) (hE : Epi g) (he : Exact f g) :
    ⊤ ≤ span R (range (Sum.elim (f ∘ v) (g.toFun.invFun ∘ w))) := by
  refine' span_exact he _ hv _
  · simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Sum.elim_comp_inl]
  · convert hw
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Sum.elim_comp_inr]
    rw [ModuleCat.epi_iff_surjective] at hE
    rw [← Function.comp.assoc, Function.RightInverse.comp_eq_id (Function.rightInverse_invFun hE),
      Function.comp.left_id]

end Span

/-- In a short exact sequence `0 ⟶ N ⟶ M ⟶ P ⟶ 0`, given bases for `N` and `P` indexed by `ι` and
    `ι'` respectively, we get a basis for `M` indexed by `ι ⊕ ι'`. -/
noncomputable
def Basis.ofShortExact {M : ModuleCat R} {f : N ⟶ M} {g : M ⟶ P} (h : ShortExact f g)
    (bN : Basis ι R N) (bP : Basis ι' R P) : Basis (ι ⊕ ι') R M :=
  Basis.mk (linearIndependent_shortExact bN.linearIndependent bP.linearIndependent h)
    (span_rightExact (le_of_eq (bN.span_eq.symm)) (le_of_eq (bP.span_eq.symm)) h.epi h.exact)

/-- In a short exact sequence `0 ⟶ N ⟶ M ⟶ P ⟶ 0`, if `N` and `P` are free, then `M` is free.-/
theorem free_shortExact {M : ModuleCat R} {f : N ⟶ M}
    {g : M ⟶ P} (h : ShortExact f g) [Module.Free R N] [Module.Free R P] :
    Module.Free R M :=
  Module.Free.of_basis (Basis.ofShortExact h (Module.Free.chooseBasis R N)
    (Module.Free.chooseBasis R P))

theorem free_shortExact_rank_add {M : ModuleCat R} {f : N ⟶ M}
    {g : M ⟶ P} (h : ShortExact f g) [Module.Free R N] [Module.Free R P] [StrongRankCondition R] :
    Module.rank R M = Module.rank R N + Module.rank R P := by
  haveI := free_shortExact h
  rw [Module.Free.rank_eq_card_chooseBasisIndex, Module.Free.rank_eq_card_chooseBasisIndex R N,
    Module.Free.rank_eq_card_chooseBasisIndex R P, Cardinal.add_def, Cardinal.eq]
  exact ⟨Basis.indexEquiv (Module.Free.chooseBasis R M) (Basis.ofShortExact h
    (Module.Free.chooseBasis R N) (Module.Free.chooseBasis R P))⟩

theorem free_shortExact_finrank_add {M : ModuleCat R} {f : N ⟶ M}
    {g : M ⟶ P} (h : ShortExact f g) [Module.Free R N] [Module.Finite R N]
    [Module.Free R P] [Module.Finite R P]
    (hN : FiniteDimensional.finrank R N = n)
    (hP : FiniteDimensional.finrank R P = p)
    [StrongRankCondition R]:
    FiniteDimensional.finrank R M = n + p := by
  apply FiniteDimensional.finrank_eq_of_rank_eq
  rw [free_shortExact_rank_add h, ← hN, ← hP]
  simp only [Nat.cast_add, FiniteDimensional.finrank_eq_rank]

end ModuleCat
