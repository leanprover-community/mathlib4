/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.GroupTheory.Goursat

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
  rw [mem_toAddSubgroup, LinearMap.mem_graph_iff, Eq.comm]
  rfl

end Submodule
