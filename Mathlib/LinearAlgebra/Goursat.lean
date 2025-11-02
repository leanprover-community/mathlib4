/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.GroupTheory.Goursat
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Goursat's lemma for submodules

Let `M, N` be modules over a ring `R`. If `L` is a submodule of `M × N` which projects fully on
to both factors, then there exist submodules `M' ≤ M` and `N' ≤ N` such that `M' × N' ≤ L` and the
image of `L` in `(M ⧸ M') × (N ⧸ N')` is the graph of an isomorphism `M ⧸ M' ≃ₗ[R] N ⧸ N'`.
Equivalently, `L` is equal to the preimage in `M × N` of the graph of this isomorphism
`M ⧸ M' ≃ₗ[R] N ⧸ N'`.

`M'` and `N'` can be explicitly constructed as `Submodule.goursatFst L` and `Submodule.goursatSnd L`
respectively.
-/

open Function Set LinearMap

namespace Submodule
variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {L : Submodule R (M × N)}
  (hL₁ : Surjective (Prod.fst ∘ L.subtype)) (hL₂ : Surjective (Prod.snd ∘ L.subtype))

variable (L) in
/-- For `L` a submodule of `M × N`, `L.goursatFst` is the kernel of the projection map `L → N`,
considered as a submodule of `M`.

This is the first submodule appearing in Goursat's lemma. See `Subgroup.goursat`. -/
def goursatFst : Submodule R M :=
  (LinearMap.ker <| (LinearMap.snd R M N).comp L.subtype).map ((LinearMap.fst R M N).comp L.subtype)


variable (L) in
/-- For `L` a subgroup of `M × N`, `L.goursatSnd` is the kernel of the projection map `L → M`,
considered as a subgroup of `N`.

This is the second subgroup appearing in Goursat's lemma. See `Subgroup.goursat`. -/
def goursatSnd : Submodule R N :=
  (LinearMap.ker <| (LinearMap.fst R M N).comp L.subtype).map ((LinearMap.snd R M N).comp L.subtype)

lemma goursatFst_toAddSubgroup :
    (goursatFst L).toAddSubgroup = L.toAddSubgroup.goursatFst := by
  ext x
  simp [mem_toAddSubgroup, goursatFst, AddSubgroup.mem_goursatFst]

lemma goursatSnd_toAddSubgroup :
    (goursatSnd L).toAddSubgroup = L.toAddSubgroup.goursatSnd := by
  ext x
  simp [mem_toAddSubgroup, goursatSnd, AddSubgroup.mem_goursatSnd]

variable (L) in
lemma goursatFst_prod_goursatSnd_le : L.goursatFst.prod L.goursatSnd ≤ L := by
  simpa only [← toAddSubgroup_le, goursatFst_toAddSubgroup, goursatSnd_toAddSubgroup]
    using L.toAddSubgroup.goursatFst_prod_goursatSnd_le

include hL₁ hL₂ in
/-- **Goursat's lemma** for a submodule of a product with surjective projections.

If `L` is a submodule of `M × N` which projects fully on both factors, then there exist submodules
`M' ≤ M` and `N' ≤ N` such that `M' × N' ≤ L` and the image of `L` in `(M ⧸ M') × (N ⧸ N')` is the
graph of an isomorphism of `R`-modules `(M ⧸ M') ≃ (N ⧸ N')`.

`M` and `N` can be explicitly constructed as `L.goursatFst` and `L.goursatSnd` respectively. -/
lemma goursat_surjective : ∃ e : (M ⧸ L.goursatFst) ≃ₗ[R] N ⧸ L.goursatSnd,
    LinearMap.range ((L.goursatFst.mkQ.prodMap L.goursatSnd.mkQ).comp L.subtype) = e.graph := by
  -- apply add-group result
  obtain ⟨(e : M ⧸ L.goursatFst ≃+ N ⧸ L.goursatSnd), he⟩ :=
    L.toAddSubgroup.goursat_surjective hL₁ hL₂
  -- check R-linearity of the map
  have (r : R) (x : M ⧸ L.goursatFst) : e (r • x) = r • e x := by
    change (r • x, r • e x) ∈ e.toAddMonoidHom.graph
    rw [← he, ← Prod.smul_mk]
    have : (x, e x) ∈ e.toAddMonoidHom.graph := rfl
    rw [← he, AddMonoidHom.mem_range] at this
    rcases this with ⟨⟨l, hl⟩, hl'⟩
    use ⟨r • l, L.smul_mem r hl⟩
    rw [← hl']
    rfl
  -- define the map as an R-linear equiv
  use { e with map_smul' := this }
  rw [← toAddSubgroup_injective.eq_iff]
  convert he using 1
  ext v
  rw [mem_toAddSubgroup, mem_graph_iff, Eq.comm]
  rfl

/-- **Goursat's lemma** for an arbitrary submodule of a product.

If `L` is a submodule of `M × N`, then there exist submodules `M'' ≤ M' ≤ M` and `N'' ≤ N' ≤ N` such
that `L ≤ M' × N'`, and `L` is (the image in `M × N` of) the preimage of the graph of an `R`-linear
isomorphism `M' ⧸ M'' ≃ N' ⧸ N''`. -/
lemma goursat : ∃ (M' : Submodule R M) (N' : Submodule R N) (M'' : Submodule R M')
    (N'' : Submodule R N') (e : (M' ⧸ M'') ≃ₗ[R] N' ⧸ N''),
    L = (e.graph.comap <| M''.mkQ.prodMap N''.mkQ).map (M'.subtype.prodMap N'.subtype) := by
  let M' := L.map (LinearMap.fst ..)
  let N' := L.map (LinearMap.snd ..)
  let P : L →ₗ[R] M' := (LinearMap.fst ..).submoduleMap L
  let Q : L →ₗ[R] N' := (LinearMap.snd ..).submoduleMap L
  let L' : Submodule R (M' × N') := LinearMap.range (P.prod Q)
  have hL₁' : Surjective (Prod.fst ∘ L'.subtype) := by
    simp only [← coe_fst (R := R), ← coe_comp, ← range_eq_top, LinearMap.range_comp, range_subtype]
    simpa only [L', ← LinearMap.range_comp, fst_prod, range_eq_top] using
      (LinearMap.fst ..).submoduleMap_surjective L
  have hL₂' : Surjective (Prod.snd ∘ L'.subtype) := by
    simp only [← coe_snd (R := R), ← coe_comp, ← range_eq_top, LinearMap.range_comp, range_subtype]
    simpa only [L', ← LinearMap.range_comp, snd_prod, range_eq_top] using
      (LinearMap.snd ..).submoduleMap_surjective L
  obtain ⟨e, he⟩ := goursat_surjective hL₁' hL₂'
  use M', N', L'.goursatFst, L'.goursatSnd, e
  rw [← he]
  simp only [LinearMap.range_comp, Submodule.range_subtype, L']
  rw [comap_map_eq_self]
  · ext ⟨m, n⟩
    constructor
    · intro hmn
      simp only [mem_map, LinearMap.mem_range, prod_apply, Subtype.exists, Prod.exists, coe_prodMap,
        coe_subtype, Prod.map_apply, Prod.mk.injEq, exists_and_right, exists_eq_right_right,
        exists_eq_right, M', N', fst_apply, snd_apply]
      exact ⟨⟨n, hmn⟩, ⟨m, hmn⟩, ⟨m, n, hmn, rfl⟩⟩
    · simp only [mem_map, LinearMap.mem_range, prod_apply, Subtype.exists, Prod.exists,
        coe_prodMap, coe_subtype, Prod.map_apply, Prod.mk.injEq, exists_and_right,
        exists_eq_right_right, exists_eq_right, forall_exists_index, Pi.prod]
      rintro hm hn m₁ n₁ hm₁n₁ ⟨hP, hQ⟩
      simp only [Subtype.ext_iff] at hP hQ
      rwa [← hP, ← hQ]
  · convert goursatFst_prod_goursatSnd_le (range <| P.prod Q)
    ext ⟨m, n⟩
    simp_rw [mem_ker, coe_prodMap, Prod.map_apply, Submodule.mem_prod, Prod.zero_eq_mk,
      Prod.ext_iff, ← mem_ker, ker_mkQ]

end Submodule
