/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!

# Topological monoids with open units

We say that a topological monoid `M` has open units (`IsOpenUnits`) if `Mˣ` is open in `M` and
has the subspace topology (i.e. inverse is continuous).

Typical examples include monoids with discrete topology, topological groups (or fields),
and rings `R` equipped with the `I`-adic topology where `I ≤ J(R)` (`IsOpenUnits.of_isAdic`).

A non-example is `𝔸ₖ`, because the topology on ideles is not the induced topology from adeles.

This condition is necessary and sufficient for `U(R)` to be an open subspace of `X(R)`
for all affine scheme `X` over `R` and all affine open subscheme `U ⊆ X`.
-/

open Topology

/--
We say that a topological monoid `M` has open units if `Mˣ` is open in `M` and
has the subspace topology (i.e. inverse is continuous).

Typical examples include monoids with discrete topology, topological groups (or fields),
and rings `R` equipped with the `I`-adic topology where `I ≤ J(R)`.
-/
@[mk_iff]
class IsOpenUnits (M : Type*) [Monoid M] [TopologicalSpace M] : Prop where
  isOpenEmbedding_unitsVal : IsOpenEmbedding (Units.val : Mˣ → M)

instance (priority := 900) (M : Type*) [Monoid M] [TopologicalSpace M] [DiscreteTopology M] :
    IsOpenUnits M where
  isOpenEmbedding_unitsVal :=
    .of_continuous_injective_isOpenMap Units.continuous_val Units.val_injective
      fun _ _ ↦ isOpen_discrete _

instance (priority := 900) {M : Type*} [Group M] [TopologicalSpace M] [ContinuousInv M] :
    IsOpenUnits M where
  isOpenEmbedding_unitsVal := toUnits_homeomorph.symm.isOpenEmbedding

instance (priority := 900) {M : Type*} [GroupWithZero M]
    [TopologicalSpace M] [HasContinuousInv₀ M] [T1Space M] : IsOpenUnits M where
  isOpenEmbedding_unitsVal := by
    refine ⟨Units.isEmbedding_val₀, ?_⟩
    convert (isClosed_singleton (X := M) (x := 0)).isOpen_compl
    ext
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact isUnit_iff_ne_zero

/-- If `R` has the `I`-adic topology where `I` is contained in the jacobson radical
(e.g. when `R` is complete or local), then `Rˣ` is an open subspace of `R`. -/
lemma IsOpenUnits.of_isAdic {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {I : Ideal R}
    (hR : IsAdic I) (hI : I ≤ Ideal.jacobson ⊥) :
    IsOpenUnits R := by
  refine ⟨.of_continuous_injective_isOpenMap Units.continuous_val Units.val_injective ?_⟩
  refine (TopologicalGroup.isOpenMap_iff_nhds_one (f := Units.coeHom R)).mpr ?_
  rw [nhds_induced, nhds_prod_eq]
  simp only [Units.embedProduct_apply, Units.val_one, inv_one, MulOpposite.op_one]
  intro s hs
  have H := hR ▸ Ideal.hasBasis_nhds_adic I 1
  have := (H.prod (H.comap MulOpposite.opHomeomorph.symm))
  simp only [Homeomorph.comap_nhds_eq, Homeomorph.symm_symm, MulOpposite.opHomeomorph_apply,
    MulOpposite.op_one, and_self, Set.image_add_left] at this
  have : ∃ n₁ n₂, ∀ (u : Rˣ), (-1 + u : R) ∈ I ^ n₁ → (-1 + u⁻¹ : R) ∈ I ^ n₂ → ↑u ∈ s := by
    simpa [Set.subset_def, forall_comm (β := Rˣ), forall_comm (β := _ = _)] using
      (((this.comap (Units.embedProduct R)).map (Units.coeHom R)).1 _).mp hs
  obtain ⟨n, hn, hn'⟩ : ∃ n ≠ 0, ∀ (u : Rˣ), (-1 + u : R) ∈ I ^ n →
      (-1 + u⁻¹ : R) ∈ I ^ n → ↑u ∈ s := by
    obtain ⟨n₁, n₂, H⟩ := this
    exact ⟨n₁ ⊔ n₂ ⊔ 1, by simp, fun u h₁ h₂ ↦ H u
      (Ideal.pow_le_pow_right (by simp) h₁)
      (Ideal.pow_le_pow_right (by simp) h₂)⟩
  rw [H.1]
  refine ⟨n, trivial, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have := Ideal.mem_jacobson_bot.mp (hI (Ideal.pow_le_self hn hx)) 1
  rw [mul_one, add_comm] at this
  refine hn' this.unit (by simpa using hx) ?_
  have : -1 + ↑this.unit⁻¹ = -this.unit⁻¹ * x := by
    trans this.unit⁻¹ * (-(1 + x) + 1)
    · rw [mul_add, mul_neg, IsUnit.val_inv_mul, mul_one]
    · simp
  rw [this]
  exact Ideal.mul_mem_left _ _ hx
