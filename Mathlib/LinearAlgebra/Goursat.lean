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

Let `G, H` be modules over a ring `R`. If `I` is a submodule of `G × H` which projects fully on
to both factors, then there exist submodules `G' ≤ G` and `H' ≤ H` such that `G' × H' ≤ I` and the
image of `I` in `(G ⧸ G') × (H ⧸ H')` is the graph of an isomorphism `G ⧸ G' ≃ₗ[R] H ⧸ H'`.

`G'` and `H'` can be explicitly constructed as `Submodule.goursatFst I` and `Submodule.goursatSnd I`
respectively.
-/

open Function Set LinearMap

namespace Submodule
variable {R G H : Type*} [Ring R] [AddCommGroup G] [Module R G] [AddCommGroup H] [Module R H]
  {I : Submodule R (G × H)}
  (hI₁ : Surjective (Prod.fst ∘ I.subtype)) (hI₂ : Surjective (Prod.snd ∘ I.subtype))

variable (I) in
/-- For `I` a submodule of `G × H`, `I.goursatFst` is the kernel of the projection map `I → H`,
considered as a submodule of `G`.

This is the first subgroup appearing in Goursat's lemma. See `Subgroup.goursat`. -/
def goursatFst : Submodule R G :=
  ((LinearMap.snd R G H).comp I.subtype).ker.map ((LinearMap.fst R G H).comp I.subtype)

variable (I) in
/-- For `I` a subgroup of `G × H`, `I.goursatSnd` is the kernel of the projection map `I → G`,
considered as a subgroup of `H`.

This is the second subgroup appearing in Goursat's lemma. See `Subgroup.goursat`. -/
def goursatSnd : Submodule R H :=
  ((LinearMap.fst R G H).comp I.subtype).ker.map ((LinearMap.snd R G H).comp I.subtype)

lemma goursatFst_toAddSubgroup :
    (goursatFst I).toAddSubgroup = I.toAddSubgroup.goursatFst := by
  ext x
  simp [mem_toAddSubgroup, goursatFst, AddSubgroup.mem_goursatFst]

lemma goursatSnd_toAddSubgroup :
    (goursatSnd I).toAddSubgroup = I.toAddSubgroup.goursatSnd := by
  ext x
  simp [mem_toAddSubgroup, goursatSnd, AddSubgroup.mem_goursatSnd]

variable (I) in
lemma goursatFst_prod_goursatSnd_le : I.goursatFst.prod I.goursatSnd ≤ I := by
  simpa only [← toAddSubgroup_le, goursatFst_toAddSubgroup, goursatSnd_toAddSubgroup]
    using I.toAddSubgroup.goursatFst_prod_goursatSnd_le

include hI₁ hI₂ in
/-- **Goursat's lemma** for a submodule of a product with surjective projections.

If `I` is a submodule of `G × H` which projects fully on both factors, then there exist submodules
`M ≤ G` and `N ≤ H` such that `M × N ≤ I` and the image of `I` in `G ⧸ M × H ⧸ N` is the
graph of an isomorphism of `R`-modules `G ⧸ M ≃ H ⧸ N`.

`M` and `N` can be explicitly constructed as `I.goursatFst` and `I.goursatSnd` respectively. -/
lemma goursat_surjective : ∃ e : (G ⧸ I.goursatFst) ≃ₗ[R] H ⧸ I.goursatSnd,
    LinearMap.range ((I.goursatFst.mkQ.prodMap I.goursatSnd.mkQ).comp I.subtype) = e.graph := by
  -- apply add-group result
  obtain ⟨(e : G ⧸ I.goursatFst ≃+ H ⧸ I.goursatSnd), he⟩ :=
    I.toAddSubgroup.goursat_surjective hI₁ hI₂
  -- check R-linearity of the map
  have (r : R) (x : G ⧸ I.goursatFst) : e (r • x) = r • e x := by
    show (r • x, r • e x) ∈ e.toAddMonoidHom.graph
    rw [← he, ← Prod.smul_mk]
    have : (x, e x) ∈ e.toAddMonoidHom.graph := rfl
    rw [← he, AddMonoidHom.mem_range] at this
    rcases this with ⟨⟨i, hi⟩, hi'⟩
    use ⟨r • i, I.smul_mem r hi⟩
    rw [← hi']
    rfl
  -- define the map as an R-linear equiv
  use { e with map_smul' := this }
  rw [← toAddSubgroup_injective.eq_iff]
  convert he using 1
  ext v
  rw [mem_toAddSubgroup, mem_graph_iff, Eq.comm]
  rfl

/-- **Goursat's lemma** for an arbitrary submodule of a product.

If `I` is a submodule of `G × H`, then there exist submodules `M ≤ G' ≤ G` and `N ≤ H' ≤ H` such
that `I ≤ G' × H'`, and `I` is (the image in `G × H` of) the preimage of the graph of an `R`-linear
isomorphism `G' ⧸ M ≃ H' ⧸ N`. -/
lemma goursat : ∃ (G' : Submodule R G) (H' : Submodule R H) (M : Submodule R G')
    (N : Submodule R H') (e : (G' ⧸ M) ≃ₗ[R] H' ⧸ N),
    I = (e.graph.comap <| M.mkQ.prodMap N.mkQ).map (G'.subtype.prodMap H'.subtype) := by
  let G' := I.map (LinearMap.fst ..)
  let H' := I.map (LinearMap.snd ..)
  let P : I →ₗ[R] G' := (LinearMap.fst ..).submoduleMap I
  let Q : I →ₗ[R] H' := (LinearMap.snd ..).submoduleMap I
  let I' : Submodule R (G' × H') := LinearMap.range (P.prod Q)
  have hI₁' : Surjective (Prod.fst ∘ I'.subtype) := by
    simp only [← coe_fst (R := R), ← coe_comp, ← range_eq_top, LinearMap.range_comp, range_subtype]
    simpa only [I', ← LinearMap.range_comp, fst_prod, range_eq_top] using
      (LinearMap.fst ..).submoduleMap_surjective I
  have hI₂' : Surjective (Prod.snd ∘ I'.subtype) := by
    simp only [← coe_snd (R := R), ← coe_comp, ← range_eq_top, LinearMap.range_comp, range_subtype]
    simpa only [I', ← LinearMap.range_comp, snd_prod, range_eq_top] using
      (LinearMap.snd ..).submoduleMap_surjective I
  obtain ⟨e, he⟩ := goursat_surjective hI₁' hI₂'
  use G', H', I'.goursatFst, I'.goursatSnd, e
  rw [← he]
  simp only [LinearMap.range_comp, Submodule.range_subtype, I']
  rw [comap_map_eq_self]
  · ext ⟨g, h⟩
    constructor
    · intro hgh
      simp only [mem_map, LinearMap.mem_range, prod_apply, Subtype.exists, Prod.exists, coe_prodMap,
        coe_subtype, Prod.map_apply, Prod.mk.injEq, exists_and_right, exists_eq_right_right,
        exists_eq_right, G', H', fst_apply, snd_apply]
      exact ⟨⟨h, hgh⟩, ⟨g, hgh⟩, ⟨g, h, hgh, rfl⟩⟩
    · simp only [mem_map, LinearMap.mem_range, prod_apply, Subtype.exists, Prod.exists,
        coe_prodMap, coe_subtype, Prod.map_apply, Prod.mk.injEq, exists_and_right,
        exists_eq_right_right, exists_eq_right, forall_exists_index, Pi.prod]
      rintro hg hh g₁ h₁ hg₁h₁ ⟨hP, hQ⟩
      simp only [Subtype.ext_iff] at hP hQ
      rwa [← hP, ← hQ]
  · convert goursatFst_prod_goursatSnd_le (range <| P.prod Q)
    ext ⟨g, h⟩
    simp_rw [mem_ker, coe_prodMap, Prod.map_apply, Submodule.mem_prod, Prod.zero_eq_mk,
      Prod.ext_iff, ← mem_ker, ker_mkQ]

end Submodule
