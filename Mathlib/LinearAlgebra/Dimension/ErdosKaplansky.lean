/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen,
Kim Morrison, Chris Hughes, Anne Baanen, Junyan Xu
-/
import Mathlib.Algebra.Field.Opposite
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.SetTheory.Cardinal.Subfield

/-!
# Erdős-Kaplansky theorem

For modules over a division ring, we have

* `rank_dual_eq_card_dual_of_aleph0_le_rank`: The **Erdős-Kaplansky Theorem** which says that
  the dimension of an infinite-dimensional dual space over a division ring has dimension
  equal to its cardinality.

-/

noncomputable section

universe u v

variable {K : Type u}

open Cardinal

section Cardinal

variable (K)
variable [DivisionRing K]

/-- Key lemma towards the Erdős-Kaplansky theorem from https://mathoverflow.net/a/168624 -/
theorem max_aleph0_card_le_rank_fun_nat : max ℵ₀ #K ≤ Module.rank K (ℕ → K) := by
  have aleph0_le : ℵ₀ ≤ Module.rank K (ℕ → K) := (rank_finsupp_self K ℕ).symm.trans_le
    (Finsupp.lcoeFun.rank_le_of_injective <| by exact DFunLike.coe_injective)
  refine max_le aleph0_le ?_
  obtain card_K | card_K := le_or_gt #K ℵ₀
  · exact card_K.trans aleph0_le
  by_contra!
  obtain ⟨⟨ιK, bK⟩⟩ := Module.Free.exists_basis (R := K) (M := ℕ → K)
  let L := Subfield.closure (Set.range (fun i : ιK × ℕ ↦ bK i.1 i.2))
  have hLK : #L < #K := by
    refine (Subfield.cardinalMk_closure_le_max _).trans_lt
      (max_lt_iff.mpr ⟨mk_range_le.trans_lt ?_, card_K⟩)
    rwa [mk_prod, ← aleph0, lift_uzero, bK.mk_eq_rank'', mul_aleph0_eq aleph0_le]
  letI := Module.compHom K (RingHom.op L.subtype)
  obtain ⟨⟨ιL, bL⟩⟩ := Module.Free.exists_basis (R := Lᵐᵒᵖ) (M := K)
  have card_ιL : ℵ₀ ≤ #ιL := by
    contrapose! hLK
    haveI := @Fintype.ofFinite _ (lt_aleph0_iff_finite.mp hLK)
    rw [bL.repr.toEquiv.cardinal_eq, mk_finsupp_of_fintype,
        ← MulOpposite.opEquiv.cardinal_eq] at card_K ⊢
    apply power_nat_le
    contrapose! card_K
    exact (power_lt_aleph0 card_K <| nat_lt_aleph0 _).le
  obtain ⟨e⟩ := lift_mk_le'.mp (card_ιL.trans_eq (lift_uzero #ιL).symm)
  have rep_e := bK.linearCombination_repr (bL ∘ e)
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at rep_e
  set c := bK.repr (bL ∘ e)
  set s := c.support
  let f i (j : s) : L := ⟨bK j i, Subfield.subset_closure ⟨(j, i), rfl⟩⟩
  have : ¬LinearIndependent Lᵐᵒᵖ f := fun h ↦ by
    have := h.cardinal_lift_le_rank
    rw [lift_uzero, (LinearEquiv.piCongrRight fun _ ↦ MulOpposite.opLinearEquiv Lᵐᵒᵖ).rank_eq,
        rank_fun'] at this
    exact (nat_lt_aleph0 _).not_ge this
  obtain ⟨t, g, eq0, i, hi, hgi⟩ := not_linearIndependent_iff.mp this
  refine hgi (linearIndependent_iff'.mp (bL.linearIndependent.comp e e.injective) t g ?_ i hi)
  clear_value c s
  simp_rw [← rep_e, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  replace eq0 := congr_arg L.subtype (congr_fun eq0 ⟨i, hi⟩)
  rw [Finset.sum_apply, map_sum] at eq0
  have : SMulCommClass Lᵐᵒᵖ K K := ⟨fun _ _ _ ↦ mul_assoc _ _ _⟩
  simp_rw [smul_comm _ (c i), ← Finset.smul_sum]
  erw [eq0, smul_zero]

variable {K}

open Function in
theorem rank_fun_infinite {ι : Type v} [hι : Infinite ι] : Module.rank K (ι → K) = #(ι → K) := by
  obtain ⟨⟨ιK, bK⟩⟩ := Module.Free.exists_basis (R := K) (M := ι → K)
  obtain ⟨e⟩ := lift_mk_le'.mp ((aleph0_le_mk_iff.mpr hι).trans_eq (lift_uzero #ι).symm)
  have := LinearMap.lift_rank_le_of_injective _ <|
    LinearMap.funLeft_injective_of_surjective K K _ (invFun_surjective e.injective)
  rw [lift_umax.{u,v}, lift_id'.{u,v}] at this
  have key := (lift_le.{v}.mpr <| max_aleph0_card_le_rank_fun_nat K).trans this
  rw [lift_max, lift_aleph0, max_le_iff] at key
  haveI : Infinite ιK := by
    rw [← aleph0_le_mk_iff, bK.mk_eq_rank'']; exact key.1
  rw [bK.repr.toEquiv.cardinal_eq, mk_finsupp_lift_of_infinite,
      lift_umax.{u,v}, lift_id'.{u,v}, bK.mk_eq_rank'', eq_comm, max_eq_left]
  exact key.2

/-- The **Erdős-Kaplansky Theorem**: the dual of an infinite-dimensional vector space
  over a division ring has dimension equal to its cardinality. -/
theorem rank_dual_eq_card_dual_of_aleph0_le_rank' {V : Type*} [AddCommGroup V] [Module K V]
    (h : ℵ₀ ≤ Module.rank K V) : Module.rank Kᵐᵒᵖ (V →ₗ[K] K) = #(V →ₗ[K] K) := by
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  rw [← b.mk_eq_rank'', aleph0_le_mk_iff] at h
  have e := (b.constr Kᵐᵒᵖ (M' := K)).symm.trans
    (LinearEquiv.piCongrRight fun _ ↦ MulOpposite.opLinearEquiv Kᵐᵒᵖ)
  rw [e.rank_eq, e.toEquiv.cardinal_eq]
  apply rank_fun_infinite

/-- The **Erdős-Kaplansky Theorem** over a field. -/
theorem rank_dual_eq_card_dual_of_aleph0_le_rank {K V} [Field K] [AddCommGroup V] [Module K V]
    (h : ℵ₀ ≤ Module.rank K V) : Module.rank K (V →ₗ[K] K) = #(V →ₗ[K] K) := by
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  rw [← b.mk_eq_rank'', aleph0_le_mk_iff] at h
  have e := (b.constr K (M' := K)).symm
  rw [e.rank_eq, e.toEquiv.cardinal_eq]
  apply rank_fun_infinite

theorem lift_rank_lt_rank_dual' {V : Type v} [AddCommGroup V] [Module K V]
    (h : ℵ₀ ≤ Module.rank K V) :
    Cardinal.lift.{u} (Module.rank K V) < Module.rank Kᵐᵒᵖ (V →ₗ[K] K) := by
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  rw [← b.mk_eq_rank'', rank_dual_eq_card_dual_of_aleph0_le_rank' h,
      ← (b.constr ℕ (M' := K)).toEquiv.cardinal_eq, mk_arrow]
  apply cantor'
  erw [nat_lt_lift_iff, one_lt_iff_nontrivial]
  infer_instance

theorem lift_rank_lt_rank_dual {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (h : ℵ₀ ≤ Module.rank K V) :
    Cardinal.lift.{u} (Module.rank K V) < Module.rank K (V →ₗ[K] K) := by
  rw [rank_dual_eq_card_dual_of_aleph0_le_rank h, ← rank_dual_eq_card_dual_of_aleph0_le_rank' h]
  exact lift_rank_lt_rank_dual' h

theorem rank_lt_rank_dual' {V : Type u} [AddCommGroup V] [Module K V] (h : ℵ₀ ≤ Module.rank K V) :
    Module.rank K V < Module.rank Kᵐᵒᵖ (V →ₗ[K] K) := by
  convert lift_rank_lt_rank_dual' h; rw [lift_id]

theorem rank_lt_rank_dual {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    (h : ℵ₀ ≤ Module.rank K V) : Module.rank K V < Module.rank K (V →ₗ[K] K) := by
  convert lift_rank_lt_rank_dual h; rw [lift_id]

end Cardinal
