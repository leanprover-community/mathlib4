/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Fabian Glöckle, Kyle Miller
-/
module

public import Mathlib.Algebra.Module.LinearMap.DivisionRing
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.ErdosKaplansky
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Dual vector spaces

The dual space of an $R$-module $M$ is the $R$-module of $R$-linear maps $M \to R$.
This file contains basic results on dual vector spaces.

## Main definitions

* Submodules:
  * `Submodule.dualRestrict_comap W'` is the dual annihilator of `W' : Submodule R (Dual R M)`,
    pulled back along `Module.Dual.eval R M`.
  * `Submodule.dualCopairing W` is the canonical pairing between `W.dualAnnihilator` and `M ⧸ W`.
    It is nondegenerate for vector spaces (`subspace.dualCopairing_nondegenerate`).
* Vector spaces:
  * `Subspace.dualLift W` is an arbitrary section (using choice) of `Submodule.dualRestrict W`.

## Main results

* Annihilators:
  * `LinearMap.ker_dual_map_eq_dualAnnihilator_range` says that
    `f.dual_map.ker = f.range.dualAnnihilator`
  * `LinearMap.range_dual_map_eq_dualAnnihilator_ker_of_subtype_range_surjective` says that
    `f.dual_map.range = f.ker.dualAnnihilator`; this is specialized to vector spaces in
    `LinearMap.range_dual_map_eq_dualAnnihilator_ker`.
  * `Submodule.dualQuotEquivDualAnnihilator` is the equivalence
    `Dual R (M ⧸ W) ≃ₗ[R] W.dualAnnihilator`
  * `Submodule.quotDualCoannihilatorToDual` is the nondegenerate pairing
    `M ⧸ W.dualCoannihilator →ₗ[R] Dual R W`.
    It is a perfect pairing when `R` is a field and `W` is finite-dimensional.
* Vector spaces:
  * `Subspace.dualAnnihilator_dualCoannihilator_eq` says that the double dual annihilator,
    pulled back ground `Module.Dual.eval`, is the original submodule.
  * `Subspace.dualAnnihilator_gci` says that `module.dualAnnihilator_gc R M` is an
    antitone Galois coinsertion.
  * `Subspace.quotAnnihilatorEquiv` is the equivalence
    `Dual K V ⧸ W.dualAnnihilator ≃ₗ[K] Dual K W`.
  * `LinearMap.dualPairing_nondegenerate` says that `Module.dualPairing` is nondegenerate.
  * `Subspace.is_compl_dualAnnihilator` says that the dual annihilator carries complementary
    subspaces to complementary subspaces.
* Finite-dimensional vector spaces:
  * `Subspace.orderIsoFiniteCodimDim` is the antitone order isomorphism between
    finite-codimensional subspaces of `V` and finite-dimensional subspaces of `Dual K V`.
  * `Subspace.orderIsoFiniteDimensional` is the antitone order isomorphism between
    subspaces of a finite-dimensional vector space `V` and subspaces of its dual.
  * `Subspace.quotDualEquivAnnihilator W` is the equivalence
    `(Dual K V ⧸ W.dualLift.range) ≃ₗ[K] W.dualAnnihilator`, where `W.dualLift.range` is a copy
    of `Dual K W` inside `Dual K V`.
  * `Subspace.quotEquivAnnihilator W` is the equivalence `(V ⧸ W) ≃ₗ[K] W.dualAnnihilator`
  * `Subspace.dualQuotDistrib W` is an equivalence
    `Dual K (V₁ ⧸ W) ≃ₗ[K] Dual K V₁ ⧸ W.dualLift.range` from an arbitrary choice of
    splitting of `V₁`.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open Module Submodule

noncomputable section

namespace Module

variable (R A M : Type*)
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

section Prod

variable (M' : Type*) [AddCommMonoid M'] [Module R M']

/-- Taking duals distributes over products. -/
@[simps!]
def dualProdDualEquivDual : (Module.Dual R M × Module.Dual R M') ≃ₗ[R] Module.Dual R (M × M') :=
  LinearMap.coprodEquiv R

@[simp]
theorem dualProdDualEquivDual_apply (φ : Module.Dual R M) (ψ : Module.Dual R M') :
    dualProdDualEquivDual R M M' (φ, ψ) = φ.coprod ψ :=
  rfl

end Prod

end Module

section

open Module Module.Dual Submodule LinearMap Cardinal Function

universe uR uM uK uV uι
variable {R : Type uR} {M : Type uM} {K : Type uK} {V : Type uV} {ι : Type uι}

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

section Finite

variable [Finite ι]

-- Not sure whether this is true for free modules over a commutative ring
/-- A vector space over a field is isomorphic to its dual if and only if it is finite-dimensional:
  a consequence of the Erdős-Kaplansky theorem. -/
theorem Basis.linearEquiv_dual_iff_finiteDimensional [Field K] [AddCommGroup V] [Module K V] :
    Nonempty (V ≃ₗ[K] Dual K V) ↔ FiniteDimensional K V := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun h ↦ ⟨(Module.Free.chooseBasis K V).toDualEquiv⟩⟩
  rw [FiniteDimensional, ← Module.rank_lt_aleph0_iff]
  by_contra!
  apply (lift_rank_lt_rank_dual this).ne
  have := e.lift_rank_eq
  rwa [lift_umax, lift_id'.{uV}] at this

theorem Module.Basis.dual_rank_eq (b : Basis ι R M) :
    Module.rank R (Dual R M) = Cardinal.lift.{uR, uM} (Module.rank R M) := by
  classical rw [← lift_umax.{uM, uR}, b.toDualEquiv.lift_rank_eq, lift_id'.{uM, uR}]

end Finite

namespace Module

variable [Module.Finite R M]

instance dual_free [Free R M] : Free R (Dual R M) :=
  Free.of_basis (Free.chooseBasis R M).dualBasis

instance dual_projective [Projective R M] : Projective R (Dual R M) :=
  have ⟨_, f, g, _, _, hfg⟩ := Finite.exists_comp_eq_id_of_projective R M
  .of_split f.dualMap g.dualMap (congr_arg dualMap hfg)

instance dual_finite [Projective R M] : Module.Finite R (Dual R M) :=
  have ⟨n, f, g, _, _, hfg⟩ := Finite.exists_comp_eq_id_of_projective R M
  have := Finite.of_basis (Free.chooseBasis R <| Fin n → R).dualBasis
  .of_surjective _ (surjective_of_comp_eq_id f.dualMap g.dualMap <| congr_arg dualMap hfg)

end Module

end CommSemiring

end

namespace Module

universe uK uV
variable {K : Type uK} {V : Type uV}
variable [CommSemiring K] [AddCommMonoid V] [Module K V] [Projective K V]

open Module Module.Dual Submodule LinearMap Cardinal Basis Module

section

variable (K)

theorem eval_apply_injective : Function.Injective (eval K V) :=
  have ⟨s, hs⟩ := Module.projective_def'.mp ‹Projective K V›
  .of_comp (f := s.dualMap.dualMap)
    (Finsupp.basisSingleOne.eval_injective.comp <| injective_of_comp_eq_id s _ hs)

variable (V)

theorem eval_ker : LinearMap.ker (eval K V) = ⊥ := ker_eq_bot_of_injective (eval_apply_injective K)

theorem map_eval_injective : (Submodule.map (eval K V)).Injective :=
  Submodule.map_injective_of_injective (eval_apply_injective K)

theorem comap_eval_surjective : (Submodule.comap (eval K V)).Surjective :=
  Submodule.comap_surjective_of_injective (eval_apply_injective K)

end

section

variable (K)

theorem eval_apply_eq_zero_iff (v : V) : (eval K V) v = 0 ↔ v = 0 :=
  SetLike.ext_iff.mp (eval_ker K V) v

/-- This is a linear map version of `SeparatingDual.exists_ne_zero` in a projective module. -/
theorem Projective.exists_dual_ne_zero (R : Type*) [Semiring R] [Module R V]
    [Projective R V] {x : V} (hx : x ≠ 0) : ∃ f : Dual R V, f x ≠ 0 :=
  have ⟨M, _, _, _, ⟨i, s, his⟩⟩ := Projective.iff_split.mp ‹Projective R V›
  let b := Free.chooseBasis R M
  have : i x ≠ 0 := i.map_eq_zero_iff (injective_of_comp_eq_id i s his) |>.not.mpr hx
  have ⟨j, hj⟩ := not_forall.mp fun h ↦ b.repr.map_ne_zero_iff.mpr this <| Finsupp.ext h
  ⟨b.coord j ∘ₗ i, hj⟩

theorem forall_dual_apply_eq_zero_iff
    (R : Type*) [Semiring R] [Module R V] [Projective R V] (v : V) :
    (∀ φ : Module.Dual R V, φ v = 0) ↔ v = 0 := by
  refine ⟨fun h ↦ ?_, fun hv ↦ by simp [hv]⟩
  contrapose! h
  exact Projective.exists_dual_ne_zero R h

/-- This is a linear map version of `SeparatingDual.exists_eq_one` in a projective module. -/
theorem Projective.exists_dual_eq_one (K : Type*) [Semifield K] [Module K V] [Projective K V]
    {x : V} (hx : x ≠ 0) : ∃ f : Dual K V, f x = 1 :=
  have ⟨f, hf⟩ := exists_dual_ne_zero K hx
  ⟨(f x)⁻¹ • f, inv_mul_cancel₀ hf⟩

@[simp]
theorem subsingleton_dual_iff : Subsingleton (Dual K V) ↔ Subsingleton V :=
  ⟨fun _ ↦ ⟨fun _ _ ↦ eval_apply_injective K (Subsingleton.elim ..)⟩, fun _ ↦ inferInstance⟩

@[simp]
theorem nontrivial_dual_iff : Nontrivial (Dual K V) ↔ Nontrivial V := by
  contrapose!; exact subsingleton_dual_iff K

instance instNontrivialDual [Nontrivial V] : Nontrivial (Dual K V) :=
  (nontrivial_dual_iff K).mpr inferInstance

omit [Projective K V] in
/-- For an example of a non-free projective `K`-module `V` for which the forward implication
fails, see https://stacks.math.columbia.edu/tag/05WG#comment-9913. -/
theorem finite_dual_iff [Free K V] : Module.Finite K (Dual K V) ↔ Module.Finite K V := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  have ⟨⟨ι, b⟩⟩ := Free.exists_basis (R := K) (M := V)
  cases finite_or_infinite ι
  · exact .of_basis b
  nontriviality K
  have ⟨n, hn⟩ := Module.Finite.exists_nat_not_surjective K (Dual K V)
  let g := Finsupp.llift K K K ι ≪≫ₗ b.repr.dualMap
  exact hn (LinearMap.funLeft K K (Fin.valEmbedding.trans (Infinite.natEmbedding ι)) ∘ₗ _)
    ((Function.Embedding.injective _).surjective_comp_right.comp g.symm.surjective) |>.elim

end

omit [Projective K V]

theorem dual_rank_eq [Free K V] [Module.Finite K V] :
    Module.rank K (Dual K V) = Cardinal.lift.{uK, uV} (Module.rank K V) :=
  (Free.chooseBasis K V).dual_rank_eq

section IsReflexive

open Function

variable (R M N : Type*)
variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- See also `Module.instFiniteDimensionalOfIsReflexive` for the converse over a field. -/
instance (priority := 900) IsReflexive.of_finite_of_free [Module.Finite R M] [Free R M] :
    IsReflexive R M where
  bijective_dual_eval'.left := (Free.chooseBasis R M).eval_injective
  bijective_dual_eval'.right := range_eq_top.mp (Free.chooseBasis R M).eval_range

variable [IsReflexive R M]

instance (priority := 900) [Module.Finite R N] [Projective R N] : IsReflexive R N :=
  have ⟨_, f, hf⟩ := Finite.exists_fin' R N
  have ⟨g, H⟩ := projective_lifting_property f .id hf
  .of_split g f H

instance _root_.Prod.instModuleIsReflexive [IsReflexive R N] :
    IsReflexive R (M × N) where
  bijective_dual_eval' := by
    let e : Dual R (Dual R (M × N)) ≃ₗ[R] Dual R (Dual R M) × Dual R (Dual R N) :=
      (dualProdDualEquivDual R M N).dualMap.trans
        (dualProdDualEquivDual R (Dual R M) (Dual R N)).symm
    have : Dual.eval R (M × N) = e.symm.comp ((Dual.eval R M).prodMap (Dual.eval R N)) := by
      ext m f <;> simp [e]
    simp only [this,
      coe_comp, LinearEquiv.coe_coe, EquivLike.comp_bijective]
    exact (bijective_dual_eval R M).prodMap (bijective_dual_eval R N)

instance _root_.ULift.instModuleIsReflexive.{w} : IsReflexive R (ULift.{w} M) :=
  equiv ULift.moduleEquiv.symm

instance instFiniteDimensionalOfIsReflexive (K V : Type*)
    [Field K] [AddCommGroup V] [Module K V] [IsReflexive K V] :
    FiniteDimensional K V := by
  rw [FiniteDimensional, ← rank_lt_aleph0_iff]
  by_contra! contra
  suffices lift (Module.rank K V) < Module.rank K (Dual K (Dual K V)) by
    have heq := lift_rank_eq_of_equiv_equiv (R := K) (R' := K) (M := V) (M' := Dual K (Dual K V))
      (ZeroHom.id K) (evalEquiv K V) bijective_id (fun r v ↦ (evalEquiv K V).map_smul _ _)
    rw [← lift_umax, heq, lift_id'] at this
    exact lt_irrefl _ this
  have h₁ : lift (Module.rank K V) < Module.rank K (Dual K V) := lift_rank_lt_rank_dual contra
  have h₂ : Module.rank K (Dual K V) < Module.rank K (Dual K (Dual K V)) := by
    convert lift_rank_lt_rank_dual <| le_trans (by simpa) h₁.le
    rw [lift_id']
  exact lt_trans h₁ h₂

end IsReflexive

end Module

namespace Submodule

open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {p : Submodule R M}

@[simp]
theorem dualCoannihilator_top [Projective R M] :
    (⊤ : Submodule R (Module.Dual R M)).dualCoannihilator = ⊥ := by
  rw [dualCoannihilator, dualAnnihilator_top, comap_bot, Module.eval_ker]

theorem exists_dual_map_eq_bot_of_notMem
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {p : Submodule R M}
    {x : M} (hx : x ∉ p) (hp' : Projective R (M ⧸ p)) :
    ∃ f : Dual R M, f x ≠ 0 ∧ p.map f = ⊥ := by
  suffices ∃ f : Dual R (M ⧸ p), f (p.mkQ x) ≠ 0 by
    obtain ⟨f, hf⟩ := this; exact ⟨f.comp p.mkQ, hf, by simp [Submodule.map_comp]⟩
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply] at hx
  exact Projective.exists_dual_ne_zero R hx

theorem exists_dual_map_eq_bot_of_lt_top
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {p : Submodule R M}
    (hp : p < ⊤) (hp' : Projective R (M ⧸ p)) :
    ∃ f : Dual R M, f ≠ 0 ∧ p.map f = ⊥ := by
  obtain ⟨x, hx⟩ : ∃ x : M, x ∉ p := by rw [lt_top_iff_ne_top] at hp; contrapose! hp; ext; simp [hp]
  obtain ⟨f, hf, hf'⟩ := p.exists_dual_map_eq_bot_of_notMem hx hp'
  exact ⟨f, by aesop, hf'⟩

/-- Consider a reflexive module and a set `s` of linear forms. If for any `z ≠ 0` there exists
`f ∈ s` such that `f z ≠ 0`, then `s` spans the whole dual space. -/
theorem span_eq_top_of_ne_zero [IsReflexive R M]
    {s : Set (M →ₗ[R] R)} [Projective R ((M →ₗ[R] R) ⧸ (span R s))]
    (h : ∀ z ≠ 0, ∃ f ∈ s, f z ≠ 0) : span R s = ⊤ := by
  by_contra! hn
  obtain ⟨φ, φne, hφ⟩ := exists_dual_map_eq_bot_of_lt_top hn.lt_top inferInstance
  let φs := (evalEquiv R M).symm φ
  have this f (hf : f ∈ s) : f φs = 0 := by
    rw [← mem_bot R, ← hφ, mem_map]
    exact ⟨f, subset_span hf, (apply_evalEquiv_symm_apply R M f φ).symm⟩
  obtain ⟨x, xs, hx⟩ := h φs (by simp [φne, φs])
  exact hx <| this x xs

variable {ι 𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

open LinearMap Set FiniteDimensional

theorem _root_.FiniteDimensional.mem_span_of_iInf_ker_le_ker [FiniteDimensional 𝕜 E]
    {L : ι → E →ₗ[𝕜] 𝕜} {K : E →ₗ[𝕜] 𝕜}
    (h : ⨅ i, LinearMap.ker (L i) ≤ ker K) : K ∈ span 𝕜 (range L) := by
  by_contra hK
  rcases exists_dual_map_eq_bot_of_notMem hK inferInstance with ⟨φ, φne, hφ⟩
  let φs := (Module.evalEquiv 𝕜 E).symm φ
  have : K φs = 0 := by
    refine h <| (Submodule.mem_iInf _).2 fun i ↦ (mem_bot 𝕜).1 ?_
    rw [← hφ, Submodule.mem_map]
    exact ⟨L i, Submodule.subset_span ⟨i, rfl⟩, (apply_evalEquiv_symm_apply 𝕜 E _ φ).symm⟩
  simp only [apply_evalEquiv_symm_apply, φs, φne] at this

/-- Given some linear forms $L_1, ..., L_n, K$ over a vector space $E$, if
$\bigcap_{i=1}^n \mathrm{ker}(L_i) \subseteq \mathrm{ker}(K)$, then $K$ is in the space generated
by $L_1, ..., L_n$. -/
theorem _root_.mem_span_of_iInf_ker_le_ker [Finite ι] {L : ι → E →ₗ[𝕜] 𝕜} {K : E →ₗ[𝕜] 𝕜}
    (h : ⨅ i, ker (L i) ≤ ker K) : K ∈ span 𝕜 (range L) := by
  have _ := Fintype.ofFinite ι
  let φ : E →ₗ[𝕜] ι → 𝕜 := LinearMap.pi L
  let p := ⨅ i, ker (L i)
  have p_eq : p = ker φ := (ker_pi L).symm
  let ψ : (E ⧸ p) →ₗ[𝕜] ι → 𝕜 := p.liftQ φ p_eq.le
  have _ : FiniteDimensional 𝕜 (E ⧸ p) := of_injective ψ (ker_eq_bot.1 (ker_liftQ_eq_bot' p φ p_eq))
  let L' i : (E ⧸ p) →ₗ[𝕜] 𝕜 := p.liftQ (L i) (iInf_le _ i)
  let K' : (E ⧸ p) →ₗ[𝕜] 𝕜 := p.liftQ K h
  have : ⨅ i, ker (L' i) ≤ ker K' := by
    simp_rw +zetaDelta [← ker_pi, pi_liftQ_eq_liftQ_pi, ker_liftQ_eq_bot' p φ p_eq]
    exact bot_le
  obtain ⟨c, hK'⟩ :=
    (mem_span_range_iff_exists_fun 𝕜).1 (FiniteDimensional.mem_span_of_iInf_ker_le_ker this)
  refine (mem_span_range_iff_exists_fun 𝕜).2 ⟨c, ?_⟩
  conv_lhs => enter [2]; intro i; rw [← p.liftQ_mkQ (L i) (iInf_le _ i)]
  rw [← p.liftQ_mkQ K h]
  ext x
  convert LinearMap.congr_fun hK' (p.mkQ x)
  simp only [L', LinearMap.coe_sum, Finset.sum_apply, smul_apply, coe_comp, Function.comp_apply,
    smul_eq_mul]

end Submodule

namespace Subspace

open Submodule LinearMap

-- We work in vector spaces because `exists_isCompl` only hold for vector spaces
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[simp]
theorem dualAnnihilator_dualCoannihilator_eq {W : Subspace K V} :
    W.dualAnnihilator.dualCoannihilator = W := by
  refine le_antisymm (fun v ↦ Function.mtr ?_) (le_dualAnnihilator_dualCoannihilator _)
  simp only [mem_dualAnnihilator, mem_dualCoannihilator]
  rw [← Quotient.mk_eq_zero W, ← Module.forall_dual_apply_eq_zero_iff K]
  push Not
  refine fun ⟨φ, hφ⟩ ↦ ⟨φ.comp W.mkQ, fun w hw ↦ ?_, hφ⟩
  rw [comp_apply, mkQ_apply, (Quotient.mk_eq_zero W).mpr hw, φ.map_zero]

-- exact elaborates slowly
theorem forall_mem_dualAnnihilator_apply_eq_zero_iff (W : Subspace K V) (v : V) :
    (∀ φ : Module.Dual K V, φ ∈ W.dualAnnihilator → φ v = 0) ↔ v ∈ W := by
  rw [← SetLike.ext_iff.mp dualAnnihilator_dualCoannihilator_eq v, mem_dualCoannihilator]

theorem comap_dualAnnihilator_dualAnnihilator (W : Subspace K V) :
    W.dualAnnihilator.dualAnnihilator.comap (Module.Dual.eval K V) = W := by
  ext; rw [Iff.comm, ← forall_mem_dualAnnihilator_apply_eq_zero_iff]; simp

theorem map_le_dualAnnihilator_dualAnnihilator (W : Subspace K V) :
    W.map (Module.Dual.eval K V) ≤ W.dualAnnihilator.dualAnnihilator :=
  map_le_iff_le_comap.mpr (comap_dualAnnihilator_dualAnnihilator W).ge

/-- `Submodule.dualAnnihilator` and `Submodule.dualCoannihilator` form a Galois coinsertion. -/
def dualAnnihilatorGci (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    GaloisCoinsertion
      (OrderDual.toDual ∘ (dualAnnihilator : Subspace K V → Subspace K (Module.Dual K V)))
      (dualCoannihilator ∘ OrderDual.ofDual) where
  choice W _ := dualCoannihilator W
  gc := dualAnnihilator_gc K V
  u_l_le _ := dualAnnihilator_dualCoannihilator_eq.le
  choice_eq _ _ := rfl

theorem dualAnnihilator_le_dualAnnihilator_iff {W W' : Subspace K V} :
    W.dualAnnihilator ≤ W'.dualAnnihilator ↔ W' ≤ W :=
  (dualAnnihilatorGci K V).l_le_l_iff

theorem dualAnnihilator_inj {W W' : Subspace K V} :
    W.dualAnnihilator = W'.dualAnnihilator ↔ W = W' :=
  ⟨fun h ↦ (dualAnnihilatorGci K V).l_injective h, congr_arg _⟩

/-- Given a subspace `W` of `V` and an element of its dual `φ`, `dualLift W φ` is
an arbitrary extension of `φ` to an element of the dual of `V`.
That is, `dualLift W φ` sends `w ∈ W` to `φ x` and `x` in a chosen complement of `W` to `0`. -/
noncomputable def dualLift (W : Subspace K V) : Module.Dual K W →ₗ[K] Module.Dual K V :=
  W.subtype.leftInverse.dualMap

variable {W : Subspace K V}

@[simp]
theorem dualLift_of_subtype {φ : Module.Dual K W} (w : W) : W.dualLift φ (w : V) = φ w :=
  congr_arg φ <| LinearMap.leftInverse_apply_of_inj W.ker_subtype _

theorem dualLift_of_mem {φ : Module.Dual K W} {w : V} (hw : w ∈ W) : W.dualLift φ w = φ ⟨w, hw⟩ :=
  dualLift_of_subtype ⟨w, hw⟩

@[simp]
theorem dualRestrict_comp_dualLift (W : Subspace K V) : W.dualRestrict.comp W.dualLift = 1 := by
  ext φ x
  simp

theorem dualRestrict_leftInverse (W : Subspace K V) :
    Function.LeftInverse W.dualRestrict W.dualLift := fun x => by
  rw [← LinearMap.comp_apply, dualRestrict_comp_dualLift, End.one_apply]

theorem dualLift_rightInverse (W : Subspace K V) :
    Function.RightInverse W.dualLift W.dualRestrict :=
  W.dualRestrict_leftInverse

theorem dualRestrict_surjective : Function.Surjective W.dualRestrict :=
  W.dualLift_rightInverse.surjective

theorem dualLift_injective : Function.Injective W.dualLift :=
  W.dualRestrict_leftInverse.injective

/-- The quotient by the `dualAnnihilator` of a subspace is isomorphic to the
  dual of that subspace. -/
noncomputable def quotAnnihilatorEquiv (W : Subspace K V) :
    (Module.Dual K V ⧸ W.dualAnnihilator) ≃ₗ[K] Module.Dual K W :=
  (quotEquivOfEq _ _ W.dualRestrict_ker_eq_dualAnnihilator).symm.trans <|
    W.dualRestrict.quotKerEquivOfSurjective dualRestrict_surjective

@[simp]
theorem quotAnnihilatorEquiv_apply (W : Subspace K V) (φ : Module.Dual K V) :
    W.quotAnnihilatorEquiv (Submodule.Quotient.mk φ) = W.dualRestrict φ := by
  ext
  rfl

/-- The natural isomorphism from the dual of a subspace `W` to `W.dualLift.range`. -/
noncomputable def dualEquivDual (W : Subspace K V) :
    Module.Dual K W ≃ₗ[K] LinearMap.range W.dualLift :=
  LinearEquiv.ofInjective _ dualLift_injective

theorem dualEquivDual_def (W : Subspace K V) :
    W.dualEquivDual.toLinearMap = W.dualLift.rangeRestrict :=
  rfl

@[simp]
theorem dualEquivDual_apply (φ : Module.Dual K W) :
    W.dualEquivDual φ = ⟨W.dualLift φ, mem_range.2 ⟨φ, rfl⟩⟩ :=
  rfl

section

open FiniteDimensional Module

instance instModuleDualFiniteDimensional [FiniteDimensional K V] :
    FiniteDimensional K (Module.Dual K V) := by
  infer_instance

@[simp]
theorem dual_finrank_eq : finrank K (Module.Dual K V) = finrank K V := by
  by_cases h : FiniteDimensional K V
  · classical exact LinearEquiv.finrank_eq (Basis.ofVectorSpace K V).toDualEquiv.symm
  rw [finrank_eq_zero_of_basis_imp_false, finrank_eq_zero_of_basis_imp_false]
  · exact fun _ b ↦ h (Module.Finite.of_basis b)
  · exact fun _ b ↦ h ((Module.finite_dual_iff K).mp <| Module.Finite.of_basis b)

variable [FiniteDimensional K V]

theorem dualAnnihilator_dualAnnihilator_eq (W : Subspace K V) :
    W.dualAnnihilator.dualAnnihilator = Module.mapEvalEquiv K V W := by
  have : _ = W := Subspace.dualAnnihilator_dualCoannihilator_eq
  rw [dualCoannihilator, ← Module.mapEvalEquiv_symm_apply] at this
  rwa [← OrderIso.symm_apply_eq]

/-- The quotient by the dual is isomorphic to its dual annihilator. -/
noncomputable def quotDualEquivAnnihilator (W : Subspace K V) :
    (Module.Dual K V ⧸ LinearMap.range W.dualLift) ≃ₗ[K] W.dualAnnihilator :=
  LinearEquiv.quotEquivOfQuotEquiv <| LinearEquiv.trans W.quotAnnihilatorEquiv W.dualEquivDual

open scoped Classical in
/-- The quotient by a subspace is isomorphic to its dual annihilator. -/
noncomputable def quotEquivAnnihilator (W : Subspace K V) : (V ⧸ W) ≃ₗ[K] W.dualAnnihilator :=
  let φ := (Basis.ofVectorSpace K W).toDualEquiv.trans W.dualEquivDual
  let ψ := LinearEquiv.quotEquivOfEquiv φ (Basis.ofVectorSpace K V).toDualEquiv
  ψ ≪≫ₗ W.quotDualEquivAnnihilator

open Module

theorem finrank_add_finrank_dualAnnihilator_eq (W : Subspace K V) :
    finrank K W + finrank K W.dualAnnihilator = finrank K V := by
  rw [← W.quotEquivAnnihilator.finrank_eq, add_comm, Submodule.finrank_quotient_add_finrank]

@[simp]
theorem finrank_dualCoannihilator_eq {Φ : Subspace K (Module.Dual K V)} :
    finrank K Φ.dualCoannihilator = finrank K Φ.dualAnnihilator := by
  rw [Submodule.dualCoannihilator, ← Module.evalEquiv_toLinearMap]
  exact LinearEquiv.finrank_eq (LinearEquiv.ofSubmodule' _ _)

theorem finrank_add_finrank_dualCoannihilator_eq (W : Subspace K (Module.Dual K V)) :
    finrank K W + finrank K W.dualCoannihilator = finrank K V := by
  rw [finrank_dualCoannihilator_eq, finrank_add_finrank_dualAnnihilator_eq, dual_finrank_eq]

end

end Subspace

open Module

section CommRing

variable {R M M' : Type*}
variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

namespace Submodule

/-- Given a submodule, corestrict to the pairing on `M ⧸ W` by
simultaneously restricting to `W.dualAnnihilator`.

See `Subspace.dualCopairing_nondegenerate`. -/
def dualCopairing (W : Submodule R M) : W.dualAnnihilator →ₗ[R] M ⧸ W →ₗ[R] R :=
  LinearMap.flip <|
    W.liftQ ((Module.dualPairing R M).domRestrict W.dualAnnihilator).flip
      (by
        intro w hw
        ext ⟨φ, hφ⟩
        exact (mem_dualAnnihilator φ).mp hφ w hw)

instance (W : Submodule R M) : FunLike (W.dualAnnihilator) M R where
  coe φ := φ.val
  coe_injective' φ ψ h := by
    ext
    simp only [funext_iff] at h
    exact h _

@[simp]
theorem dualCopairing_apply {W : Submodule R M} (φ : W.dualAnnihilator) (x : M) :
    W.dualCopairing φ (Quotient.mk x) = φ x :=
  rfl

/-- Given a submodule, restrict to the pairing on `W` by
simultaneously corestricting to `Module.Dual R M ⧸ W.dualAnnihilator`.
This is `Submodule.dualRestrict` factored through the quotient by its kernel (which
is `W.dualAnnihilator` by definition).

See `Subspace.dualPairing_nondegenerate`. -/
def dualPairing (W : Submodule R M) : Module.Dual R M ⧸ W.dualAnnihilator →ₗ[R] W →ₗ[R] R :=
  W.dualAnnihilator.liftQ W.dualRestrict le_rfl

@[simp]
theorem dualPairing_apply {W : Submodule R M} (φ : Module.Dual R M) (x : W) :
    W.dualPairing (Quotient.mk φ) x = φ x :=
  rfl

/-- That $\operatorname{im}(q^* : (V/W)^* \to V^*) = \operatorname{ann}(W)$. -/
theorem range_dualMap_mkQ_eq (W : Submodule R M) :
    LinearMap.range W.mkQ.dualMap = W.dualAnnihilator := by
  ext φ
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨ψ, rfl⟩
    have := LinearMap.mem_range_self W.mkQ.dualMap ψ
    simpa only [ker_mkQ] using W.mkQ.range_dualMap_le_dualAnnihilator_ker this
  · intro hφ
    exists W.dualCopairing ⟨φ, hφ⟩

/-- Equivalence $(M/W)^* \cong \operatorname{ann}(W)$. That is, there is a one-to-one
correspondence between the dual of `M ⧸ W` and those elements of the dual of `M` that
vanish on `W`.

The inverse of this is `Submodule.dualCopairing`. -/
def dualQuotEquivDualAnnihilator (W : Submodule R M) :
    Module.Dual R (M ⧸ W) ≃ₗ[R] W.dualAnnihilator :=
  LinearEquiv.ofLinear
    (W.mkQ.dualMap.codRestrict W.dualAnnihilator fun φ =>
      W.range_dualMap_mkQ_eq ▸ LinearMap.mem_range_self W.mkQ.dualMap φ)
    W.dualCopairing (by ext; rfl) (by ext; rfl)

@[simp]
theorem dualQuotEquivDualAnnihilator_apply (W : Submodule R M) (φ : Module.Dual R (M ⧸ W)) (x : M) :
    dualQuotEquivDualAnnihilator W φ x = φ (Quotient.mk x) :=
  rfl

theorem dualCopairing_eq (W : Submodule R M) :
    W.dualCopairing = (dualQuotEquivDualAnnihilator W).symm.toLinearMap :=
  rfl

@[simp]
theorem dualQuotEquivDualAnnihilator_symm_apply_mk (W : Submodule R M) (φ : W.dualAnnihilator)
    (x : M) : (dualQuotEquivDualAnnihilator W).symm φ (Quotient.mk x) = φ x :=
  rfl

theorem finite_dualAnnihilator_iff {W : Submodule R M} [Free R (M ⧸ W)] :
    Module.Finite R W.dualAnnihilator ↔ Module.Finite R (M ⧸ W) :=
  (Finite.equiv_iff W.dualQuotEquivDualAnnihilator.symm).trans (finite_dual_iff R)

lemma dualAnnihilator_eq_bot_iff' {W : Submodule R M} :
    W.dualAnnihilator = ⊥ ↔ Subsingleton (Dual R (M ⧸ W)) := by
  rw [W.dualQuotEquivDualAnnihilator.toEquiv.subsingleton_congr, subsingleton_iff_eq_bot]

@[simp] lemma dualAnnihilator_eq_bot_iff {W : Submodule R M} [Projective R (M ⧸ W)] :
    W.dualAnnihilator = ⊥ ↔ W = ⊤ := by
  rw [dualAnnihilator_eq_bot_iff', subsingleton_dual_iff, Quotient.subsingleton_iff]

@[simp] lemma dualAnnihilator_eq_top_iff {W : Submodule R M} [Projective R M] :
    W.dualAnnihilator = ⊤ ↔ W = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ dualAnnihilator_bot⟩
  refine W.eq_bot_iff.mpr fun v hv ↦ (forall_dual_apply_eq_zero_iff R v).mp fun f ↦ ?_
  refine (mem_dualAnnihilator f).mp ?_ v hv
  simp [h]

open LinearMap in
/-- The pairing between a submodule `W` of a dual module `Dual R M` and the quotient of
`M` by the coannihilator of `W`, which is always nondegenerate. -/
def quotDualCoannihilatorToDual (W : Submodule R (Dual R M)) :
    M ⧸ W.dualCoannihilator →ₗ[R] Dual R W :=
  liftQ _ (flip <| Submodule.subtype _) le_rfl

@[simp]
theorem quotDualCoannihilatorToDual_apply (W : Submodule R (Dual R M)) (m : M) (w : W) :
    W.quotDualCoannihilatorToDual (Quotient.mk m) w = w.1 m := rfl

theorem quotDualCoannihilatorToDual_injective (W : Submodule R (Dual R M)) :
    Function.Injective W.quotDualCoannihilatorToDual :=
  LinearMap.ker_eq_bot.mp (ker_liftQ_eq_bot _ _ _ le_rfl)

theorem flip_quotDualCoannihilatorToDual_injective (W : Submodule R (Dual R M)) :
    Function.Injective W.quotDualCoannihilatorToDual.flip :=
  fun _ _ he ↦ Subtype.ext <| LinearMap.ext fun m ↦ DFunLike.congr_fun he ⟦m⟧

open LinearMap in
theorem quotDualCoannihilatorToDual_nondegenerate (W : Submodule R (Dual R M)) :
    W.quotDualCoannihilatorToDual.Nondegenerate := by
  rw [Nondegenerate, separatingLeft_iff_ker_eq_bot, separatingRight_iff_flip_ker_eq_bot]
  simp_rw [ker_eq_bot]
  exact ⟨W.quotDualCoannihilatorToDual_injective, W.flip_quotDualCoannihilatorToDual_injective⟩

end Submodule

namespace LinearMap

open Submodule

theorem range_dualMap_eq_dualAnnihilator_ker_of_surjective (f : M →ₗ[R] M')
    (hf : Function.Surjective f) : LinearMap.range f.dualMap = (LinearMap.ker f).dualAnnihilator :=
  ((f.quotKerEquivOfSurjective hf).dualMap.range_comp _).trans
    (LinearMap.ker f).range_dualMap_mkQ_eq

-- Note, this can be specialized to the case where `R` is an injective `R`-module, or when
-- `f.coker` is a projective `R`-module.
theorem range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective (f : M →ₗ[R] M')
    (hf : Function.Surjective (range f).subtype.dualMap) :
    LinearMap.range f.dualMap = (ker f).dualAnnihilator := by
  have rr_surj : Function.Surjective f.rangeRestrict := by
    rw [← range_eq_top, range_rangeRestrict]
  have := range_dualMap_eq_dualAnnihilator_ker_of_surjective f.rangeRestrict rr_surj
  convert this using 1
  · calc
      _ = range ((range f).subtype.comp f.rangeRestrict).dualMap := by simp
      _ = _ := ?_
    rw [← dualMap_comp_dualMap, range_comp_of_range_eq_top]
    rwa [range_eq_top]
  · apply congr_arg
    exact (ker_rangeRestrict f).symm

end LinearMap

end CommRing

section VectorSpace

section

variable {K V₁ V₂ : Type*} [DivisionRing K]
variable [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]

namespace Module.Dual

variable {f : Module.Dual K V₁}

section
variable (hf : f ≠ 0)

lemma range_eq_top_of_ne_zero {K V₁ : Type*} [DivisionSemiring K] [AddCommMonoid V₁] [Module K V₁]
    {f : Module.Dual K V₁} (hf : f ≠ 0) : LinearMap.range f = ⊤ :=
  LinearMap.range_eq_top.mpr (LinearMap.surjective hf)

variable [FiniteDimensional K V₁]
include hf

lemma finrank_ker_add_one_of_ne_zero :
    finrank K (LinearMap.ker f) + 1 = finrank K V₁ := by
  suffices finrank K (LinearMap.range f) = 1 by
    rw [← (LinearMap.ker f).finrank_quotient_add_finrank, add_comm, add_left_inj,
    f.quotKerEquivRange.finrank_eq, this]
  rw [range_eq_top_of_ne_zero hf, finrank_top, finrank_self]

lemma isCompl_ker_of_disjoint_of_ne_bot {p : Submodule K V₁}
    (hpf : Disjoint (LinearMap.ker f) p) (hp : p ≠ ⊥) :
    IsCompl (LinearMap.ker f) p := by
  refine ⟨hpf, codisjoint_iff.mpr <| eq_of_le_of_finrank_le le_top ?_⟩
  have : finrank K ↑(LinearMap.ker f ⊔ p) = finrank K (LinearMap.ker f) + finrank K p := by
    simp [← Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker f) p, hpf.eq_bot]
  rwa [finrank_top, this, ← finrank_ker_add_one_of_ne_zero hf, add_le_add_iff_left,
    Submodule.one_le_finrank_iff]

end

lemma eq_of_ker_eq_of_apply_eq [FiniteDimensional K V₁] {f g : Module.Dual K V₁} (x : V₁)
    (h : LinearMap.ker f = LinearMap.ker g) (h' : f x = g x) (hx : f x ≠ 0) :
    f = g := by
  let p := K ∙ x
  have hp : p ≠ ⊥ := by aesop
  have hpf : Disjoint (LinearMap.ker f) p := by
    rw [disjoint_iff, Submodule.eq_bot_iff]
    rintro y ⟨hfy : f y = 0, hpy : y ∈ p⟩
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hpy
    have ht : t = 0 := by simpa [hx] using hfy
    simp [ht]
  have hf : f ≠ 0 := by aesop
  ext v
  obtain ⟨y, hy, z, hz, rfl⟩ : ∃ᵉ (y ∈ LinearMap.ker f) (z ∈ p), y + z = v := by
    have : v ∈ (⊤ : Submodule K V₁) := Submodule.mem_top
    rwa [← (isCompl_ker_of_disjoint_of_ne_bot hf hpf hp).sup_eq_top, Submodule.mem_sup] at this
  have hy' : g y = 0 := by rwa [← LinearMap.mem_ker, ← h]
  replace hy : f y = 0 := by rwa [LinearMap.mem_ker] at hy
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
  simp [h', hy, hy']

end Module.Dual

end

variable {K V₁ V₂ : Type*} [Field K]
variable [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]

namespace LinearMap

theorem dualPairing_nondegenerate : (dualPairing K V₁).Nondegenerate :=
  ⟨separatingLeft_iff_ker_eq_bot.mpr ker_id, fun x => (forall_dual_apply_eq_zero_iff K x).mp⟩

theorem dualMap_surjective_of_injective {f : V₁ →ₗ[K] V₂} (hf : Function.Injective f) :
    Function.Surjective f.dualMap := fun φ ↦
  have ⟨f', hf'⟩ := f.exists_leftInverse_of_injective (ker_eq_bot.mpr hf)
  ⟨φ.comp f', ext fun x ↦ congr(φ <| $hf' x)⟩

theorem range_dualMap_eq_dualAnnihilator_ker (f : V₁ →ₗ[K] V₂) :
    LinearMap.range f.dualMap = (LinearMap.ker f).dualAnnihilator :=
  range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective f <|
    dualMap_surjective_of_injective (range f).injective_subtype

/-- For vector spaces, `f.dualMap` is surjective if and only if `f` is injective -/
@[simp]
theorem dualMap_surjective_iff {f : V₁ →ₗ[K] V₂} :
    Function.Surjective f.dualMap ↔ Function.Injective f := by
  rw [← LinearMap.range_eq_top, range_dualMap_eq_dualAnnihilator_ker,
      ← Submodule.dualAnnihilator_bot, Subspace.dualAnnihilator_inj, LinearMap.ker_eq_bot]

end LinearMap

namespace Subspace

open Submodule

theorem dualPairing_eq (W : Subspace K V₁) :
    W.dualPairing = W.quotAnnihilatorEquiv.toLinearMap := by
  ext
  rfl

theorem dualPairing_nondegenerate (W : Subspace K V₁) : W.dualPairing.Nondegenerate := by
  constructor
  · rw [LinearMap.separatingLeft_iff_ker_eq_bot, dualPairing_eq]
    apply LinearEquiv.ker
  · intro x h
    rw [← forall_dual_apply_eq_zero_iff K x]
    intro φ
    simpa only [Submodule.dualPairing_apply, dualLift_of_subtype] using
      h (Submodule.Quotient.mk (W.dualLift φ))

theorem dualCopairing_nondegenerate (W : Subspace K V₁) : W.dualCopairing.Nondegenerate := by
  constructor
  · rw [LinearMap.separatingLeft_iff_ker_eq_bot, dualCopairing_eq]
    apply LinearEquiv.ker
  · rintro ⟨x⟩
    simp only [Quotient.quot_mk_eq_mk, dualCopairing_apply, Quotient.mk_eq_zero]
    rw [← forall_mem_dualAnnihilator_apply_eq_zero_iff, SetLike.forall]
    exact id

-- Argument from https://math.stackexchange.com/a/2423263/172988
theorem dualAnnihilator_inf_eq (W W' : Subspace K V₁) :
    (W ⊓ W').dualAnnihilator = W.dualAnnihilator ⊔ W'.dualAnnihilator := by
  refine le_antisymm ?_ (sup_dualAnnihilator_le_inf W W')
  let F : V₁ →ₗ[K] (V₁ ⧸ W) × V₁ ⧸ W' := (Submodule.mkQ W).prod (Submodule.mkQ W')
  have : LinearMap.ker F = W ⊓ W' := by simp only [F, LinearMap.ker_prod, ker_mkQ]
  rw [← this, ← LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  intro φ
  rw [LinearMap.mem_range]
  rintro ⟨x, rfl⟩
  rw [Submodule.mem_sup]
  obtain ⟨⟨a, b⟩, rfl⟩ := (dualProdDualEquivDual K (V₁ ⧸ W) (V₁ ⧸ W')).surjective x
  obtain ⟨a', rfl⟩ := (dualQuotEquivDualAnnihilator W).symm.surjective a
  obtain ⟨b', rfl⟩ := (dualQuotEquivDualAnnihilator W').symm.surjective b
  use a', a'.property, b', b'.property
  rfl

-- This is also true if `V₁` is finite dimensional since one can restrict `ι` to some subtype
-- for which the infimum and supremum are the same.
-- The obstruction to the `dualAnnihilator_inf_eq` argument carrying through is that we need
-- for `Module.Dual R (Π (i : ι), V ⧸ W i) ≃ₗ[K] Π (i : ι), Module.Dual R (V ⧸ W i)`, which is not
-- true for infinite `ι`. One would need to add additional hypothesis on `W` (for example, it might
-- be true when the family is inf-closed).
-- TODO: generalize to `Sort`
theorem dualAnnihilator_iInf_eq {ι : Type*} [Finite ι] (W : ι → Subspace K V₁) :
    (⨅ i : ι, W i).dualAnnihilator = ⨆ i : ι, (W i).dualAnnihilator := by
  revert ι
  apply Finite.induction_empty_option
  · intro α β h hyp W
    rw [← h.iInf_comp, hyp _, ← h.iSup_comp]
  · intro W
    rw [iSup_of_empty', iInf_of_isEmpty, sInf_empty, sSup_empty, dualAnnihilator_top]
  · intro α _ h W
    rw [iInf_option, iSup_option, dualAnnihilator_inf_eq, h]

/-- For vector spaces, dual annihilators carry direct sum decompositions
to direct sum decompositions. -/
theorem isCompl_dualAnnihilator {W W' : Subspace K V₁} (h : IsCompl W W') :
    IsCompl W.dualAnnihilator W'.dualAnnihilator := by
  rw [isCompl_iff, disjoint_iff, codisjoint_iff] at h ⊢
  rw [← dualAnnihilator_inf_eq, ← dualAnnihilator_sup_eq, h.1, h.2, dualAnnihilator_top,
    dualAnnihilator_bot]
  exact ⟨rfl, rfl⟩

/-- For finite-dimensional vector spaces, one can distribute duals over quotients by identifying
`W.dualLift.range` with `W`. Note that this depends on a choice of splitting of `V₁`. -/
def dualQuotDistrib [FiniteDimensional K V₁] (W : Subspace K V₁) :
    Module.Dual K (V₁ ⧸ W) ≃ₗ[K] Module.Dual K V₁ ⧸ LinearMap.range W.dualLift :=
  W.dualQuotEquivDualAnnihilator.trans W.quotDualEquivAnnihilator.symm

end Subspace

section FiniteDimensional

open Module LinearMap

namespace LinearMap

@[simp]
theorem finrank_range_dualMap_eq_finrank_range (f : V₁ →ₗ[K] V₂) :
    finrank K (LinearMap.range f.dualMap) = finrank K (LinearMap.range f) := by
  rw [congr_arg dualMap (show f = (range f).subtype.comp f.rangeRestrict by rfl),
    ← dualMap_comp_dualMap, range_comp,
    range_eq_top.mpr (dualMap_surjective_of_injective (range f).injective_subtype),
    Submodule.map_top, finrank_range_of_inj, Subspace.dual_finrank_eq]
  exact dualMap_injective_of_surjective (range_eq_top.mp f.range_rangeRestrict)

/-- `f.dualMap` is injective if and only if `f` is surjective -/
@[simp]
theorem dualMap_injective_iff {f : V₁ →ₗ[K] V₂} :
    Function.Injective f.dualMap ↔ Function.Surjective f := by
  refine ⟨Function.mtr fun not_surj inj ↦ ?_, dualMap_injective_of_surjective⟩
  rw [← range_eq_top, ← Ne, ← lt_top_iff_ne_top] at not_surj
  obtain ⟨φ, φ0, range_le_ker⟩ := (range f).exists_le_ker_of_lt_top not_surj
  exact φ0 (inj <| ext fun x ↦ range_le_ker ⟨x, rfl⟩)

/-- `f.dualMap` is bijective if and only if `f` is -/
@[simp]
theorem dualMap_bijective_iff {f : V₁ →ₗ[K] V₂} :
    Function.Bijective f.dualMap ↔ Function.Bijective f := by
  simp_rw [Function.Bijective, dualMap_surjective_iff, dualMap_injective_iff, and_comm]

variable {B : V₁ →ₗ[K] V₂ →ₗ[K] K}

@[simp]
lemma dualAnnihilator_ker_eq_range_flip [IsReflexive K V₂] :
    (ker B).dualAnnihilator = range B.flip := by
  change _ = range (B.dualMap.comp (Module.evalEquiv K V₂).toLinearMap)
  rw [← range_dualMap_eq_dualAnnihilator_ker, range_comp_of_range_eq_top _ (LinearEquiv.range _)]

open Function

theorem flip_injective_iff₁ [FiniteDimensional K V₁] : Injective B.flip ↔ Surjective B := by
  rw [← dualMap_surjective_iff, ← (evalEquiv K V₁).toEquiv.surjective_comp]; rfl

theorem flip_injective_iff₂ [FiniteDimensional K V₂] : Injective B.flip ↔ Surjective B := by
  rw [← dualMap_injective_iff]; exact (evalEquiv K V₂).toEquiv.injective_comp B.dualMap

theorem flip_surjective_iff₁ [FiniteDimensional K V₁] : Surjective B.flip ↔ Injective B :=
  flip_injective_iff₂.symm

theorem flip_surjective_iff₂ [FiniteDimensional K V₂] : Surjective B.flip ↔ Injective B :=
  flip_injective_iff₁.symm

theorem flip_bijective_iff₁ [FiniteDimensional K V₁] : Bijective B.flip ↔ Bijective B := by
  simp_rw [Bijective, flip_injective_iff₁, flip_surjective_iff₁, and_comm]

theorem flip_bijective_iff₂ [FiniteDimensional K V₂] : Bijective B.flip ↔ Bijective B :=
  flip_bijective_iff₁.symm

end LinearMap

namespace Subspace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem quotDualCoannihilatorToDual_bijective (W : Subspace K (Dual K V)) [FiniteDimensional K W] :
    Function.Bijective W.quotDualCoannihilatorToDual :=
  ⟨W.quotDualCoannihilatorToDual_injective, letI : AddCommGroup W := inferInstance
    flip_injective_iff₂.mp W.flip_quotDualCoannihilatorToDual_injective⟩

theorem flip_quotDualCoannihilatorToDual_bijective (W : Subspace K (Dual K V))
    [FiniteDimensional K W] : Function.Bijective W.quotDualCoannihilatorToDual.flip :=
  letI : AddCommGroup W := inferInstance
  flip_bijective_iff₂.mpr W.quotDualCoannihilatorToDual_bijective

theorem dualCoannihilator_dualAnnihilator_eq {W : Subspace K (Dual K V)} [FiniteDimensional K W] :
    W.dualCoannihilator.dualAnnihilator = W :=
  let e := (LinearEquiv.ofBijective _ W.flip_quotDualCoannihilatorToDual_bijective).trans
    (Submodule.dualQuotEquivDualAnnihilator _)
  letI : AddCommGroup W := inferInstance
  haveI : FiniteDimensional K W.dualCoannihilator.dualAnnihilator := LinearEquiv.finiteDimensional e
  (eq_of_le_of_finrank_eq W.le_dualCoannihilator_dualAnnihilator e.finrank_eq).symm

theorem finiteDimensional_quot_dualCoannihilator_iff {W : Submodule K (Dual K V)} :
    FiniteDimensional K (V ⧸ W.dualCoannihilator) ↔ FiniteDimensional K W :=
  ⟨fun _ ↦ FiniteDimensional.of_injective _ W.flip_quotDualCoannihilatorToDual_injective,
    fun _ ↦ FiniteDimensional.of_injective _ W.quotDualCoannihilatorToDual_injective⟩

open OrderDual in
/-- For any vector space, `dualAnnihilator` and `dualCoannihilator` gives an antitone order
  isomorphism between the finite-codimensional subspaces in the vector space and the
  finite-dimensional subspaces in its dual. -/
def orderIsoFiniteCodimDim :
    {W : Subspace K V // FiniteDimensional K (V ⧸ W)} ≃o
    {W : Subspace K (Dual K V) // FiniteDimensional K W}ᵒᵈ where
  toFun W := toDual ⟨W.1.dualAnnihilator, Submodule.finite_dualAnnihilator_iff.mpr W.2⟩
  invFun W := ⟨(ofDual W).1.dualCoannihilator,
    finiteDimensional_quot_dualCoannihilator_iff.mpr (ofDual W).2⟩
  left_inv _ := Subtype.ext dualAnnihilator_dualCoannihilator_eq
  right_inv W := have := (ofDual W).2; Subtype.ext dualCoannihilator_dualAnnihilator_eq
  map_rel_iff' := dualAnnihilator_le_dualAnnihilator_iff

open OrderDual in
/-- For any finite-dimensional vector space, `dualAnnihilator` and `dualCoannihilator` give
  an antitone order isomorphism between the subspaces in the vector space and the subspaces
  in its dual. -/
def orderIsoFiniteDimensional [FiniteDimensional K V] :
    Subspace K V ≃o (Subspace K (Dual K V))ᵒᵈ where
  toFun W := toDual W.dualAnnihilator
  invFun W := (ofDual W).dualCoannihilator
  left_inv _ := dualAnnihilator_dualCoannihilator_eq
  right_inv _ := dualCoannihilator_dualAnnihilator_eq
  map_rel_iff' := dualAnnihilator_le_dualAnnihilator_iff

open Submodule in
theorem dualAnnihilator_dualAnnihilator_eq_map (W : Subspace K V) [FiniteDimensional K W] :
    W.dualAnnihilator.dualAnnihilator = W.map (Dual.eval K V) := by
  let e1 := (Free.chooseBasis K W).toDualEquiv ≪≫ₗ W.quotAnnihilatorEquiv.symm
  haveI := e1.finiteDimensional
  let e2 := (Free.chooseBasis K _).toDualEquiv ≪≫ₗ W.dualAnnihilator.dualQuotEquivDualAnnihilator
  haveI := LinearEquiv.finiteDimensional (V₂ := W.dualAnnihilator.dualAnnihilator) e2
  rw [eq_of_le_of_finrank_eq (map_le_dualAnnihilator_dualAnnihilator W)]
  rw [← (equivMapOfInjective _ (eval_apply_injective K (V := V)) W).finrank_eq, e1.finrank_eq]
  exact e2.finrank_eq

theorem map_dualCoannihilator (W : Subspace K (Dual K V)) [FiniteDimensional K V] :
    W.dualCoannihilator.map (Dual.eval K V) = W.dualAnnihilator := by
  rw [← dualAnnihilator_dualAnnihilator_eq_map, dualCoannihilator_dualAnnihilator_eq]

end Subspace

end FiniteDimensional

end VectorSpace

theorem span_flip_eq_top_iff_linearIndependent {ι α F} [Finite ι] [Field F] {f : ι → α → F} :
    span F (Set.range <| flip f) = ⊤ ↔ LinearIndependent F f := by
  rw [linearIndependent_iff_ker, ← Submodule.map_eq_top_iff (e := Finsupp.llift F F F ι),
    ← Subspace.dualCoannihilator_dualAnnihilator_eq (W := map ..), dualAnnihilator_eq_top_iff]
  congr!
  rw [SetLike.ext'_iff, map_span, Submodule.coe_dualCoannihilator_span, ← Set.range_comp]
  ext
  simp [funext_iff, Finsupp.linearCombination, Finsupp.sum, Finset.sum_apply, flip]

lemma Module.exists_dual_forall_apply_eq_one {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {s : Set ι} {v : ι → V} (hli : LinearIndepOn K v s) :
    ∃ f : Dual K V, ∀ i ∈ s, f (v i) = 1 := by
  replace hli : LinearIndepOn K id (v '' s) := LinearIndepOn.id_image hli
  let b : Basis _ K V := .mk (hli.linearIndepOn_extend (Set.subset_univ _)) <| by
    simpa using hli.span_extend_eq_span <| Set.subset_univ _
  refine ⟨b.constr K 1, fun i hi ↦ ?_⟩
  replace hi : v i ∈ hli.extend (Set.subset_univ _) :=
    hli.subset_extend _ <| Set.mem_image_of_mem v hi
  let ri : hli.extend (Set.subset_univ _) := ⟨v i, hi⟩
  have : b ri = v i := by simp [b, ri]
  simp [← this]

namespace TensorProduct

variable (R A : Type*) (M : Type*) (N : Type*)
variable {ι κ : Type*}
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι] [Fintype κ]

open TensorProduct

attribute [local ext] TensorProduct.ext

open TensorProduct

open LinearMap

section

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N]

/-- The canonical linear map from `Dual M ⊗ Dual N` to `Dual (M ⊗ N)`,
sending `f ⊗ g` to the composition of `TensorProduct.map f g` with
the natural isomorphism `R ⊗ R ≃ R`.
-/
def dualDistrib : Dual R M ⊗[R] Dual R N →ₗ[R] Dual R (M ⊗[R] N) :=
  compRight _ (TensorProduct.lid R R) ∘ₗ homTensorHomMap (.id R) M N R R

variable {R M N}

@[simp]
theorem dualDistrib_apply (f : Dual R M) (g : Dual R N) (m : M) (n : N) :
    dualDistrib R M N (f ⊗ₜ g) (m ⊗ₜ n) = f m * g n :=
  rfl

/-- Simultaneously swapping both the ordering of the applied duals and the ordering of the
tensor product argument preserves evaluation. -/
lemma dualDistrib_apply_comm (w : Dual R N ⊗[R] Dual R M) (z : M ⊗[R] N) :
    dualDistrib R N M w (TensorProduct.comm R M N z) =
      dualDistrib R M N (TensorProduct.comm R _ _ w) z := by
  induction w <;> induction z <;> simp_all [mul_comm]

end

namespace AlgebraTensorModule
variable [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module A M] [Module R N] [IsScalarTower R A M]

/-- Heterobasic version of `TensorProduct.dualDistrib` -/
def dualDistrib : Dual A M ⊗[R] Dual R N →ₗ[A] Dual A (M ⊗[R] N) :=
  compRight _ (Algebra.TensorProduct.rid R A A).toLinearMap ∘ₗ homTensorHomMap R A A M N A R

variable {R M N}

@[simp]
theorem dualDistrib_apply (f : Dual A M) (g : Dual R N) (m : M) (n : N) :
    dualDistrib R A M N (f ⊗ₜ g) (m ⊗ₜ n) = g n • f m :=
  rfl

end AlgebraTensorModule

variable {R M N}
variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N]

/-- An inverse to `TensorProduct.dualDistrib` given bases.
-/
noncomputable def dualDistribInvOfBasis (b : Basis ι R M) (c : Basis κ R N) :
    Dual R (M ⊗[R] N) →ₗ[R] Dual R M ⊗[R] Dual R N :=
  ∑ i, ∑ j,
    (ringLmapEquivSelf R ℕ _).symm (b.dualBasis i ⊗ₜ c.dualBasis j) ∘ₗ
      applyₗ (c j) ∘ₗ applyₗ (b i) ∘ₗ lcurry (.id R) M N R

@[simp]
theorem dualDistribInvOfBasis_apply (b : Basis ι R M) (c : Basis κ R N) (f : Dual R (M ⊗[R] N)) :
    dualDistribInvOfBasis b c f = ∑ i, ∑ j, f (b i ⊗ₜ c j) • b.dualBasis i ⊗ₜ c.dualBasis j := by
  simp [dualDistribInvOfBasis]

theorem dualDistrib_dualDistribInvOfBasis_left_inverse (b : Basis ι R M) (c : Basis κ R N) :
    comp (dualDistrib R M N) (dualDistribInvOfBasis b c) = LinearMap.id := by
  apply (b.tensorProduct c).dualBasis.ext
  rintro ⟨i, j⟩
  apply (b.tensorProduct c).ext
  rintro ⟨i', j'⟩
  simp only [dualDistrib, Basis.coe_dualBasis, coe_comp, Function.comp_apply,
    dualDistribInvOfBasis_apply, Basis.coord_apply, Basis.tensorProduct_repr_tmul_apply,
    Basis.repr_self, _root_.map_sum, map_smul, homTensorHomMap_apply, compRight_apply,
    Basis.tensorProduct_apply, LinearMap.coe_sum, Finset.sum_apply, smul_apply, LinearEquiv.coe_coe,
    map_tmul, lid_tmul, smul_eq_mul, id_coe, id_eq]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simpa using mul_comm _ _
  all_goals { intros; simp [*] at * }

theorem dualDistrib_dualDistribInvOfBasis_right_inverse (b : Basis ι R M) (c : Basis κ R N) :
    comp (dualDistribInvOfBasis b c) (dualDistrib R M N) = LinearMap.id := by
  apply (b.dualBasis.tensorProduct c.dualBasis).ext
  rintro ⟨i, j⟩
  simp only [Basis.tensorProduct_apply, Basis.coe_dualBasis, coe_comp, Function.comp_apply,
    dualDistribInvOfBasis_apply, dualDistrib_apply, Basis.coord_apply, Basis.repr_self,
    id_coe, id_eq]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  all_goals { intros; simp [*] at * }

/-- A linear equivalence between `Dual M ⊗ Dual N` and `Dual (M ⊗ N)` given bases for `M` and `N`.
It sends `f ⊗ g` to the composition of `TensorProduct.map f g` with the natural
isomorphism `R ⊗ R ≃ R`.
-/
@[simps!]
noncomputable def dualDistribEquivOfBasis (b : Basis ι R M) (c : Basis κ R N) :
    Dual R M ⊗[R] Dual R N ≃ₗ[R] Dual R (M ⊗[R] N) := by
  refine LinearEquiv.ofLinear (dualDistrib R M N) (dualDistribInvOfBasis b c) ?_ ?_
  · exact dualDistrib_dualDistribInvOfBasis_left_inverse _ _
  · exact dualDistrib_dualDistribInvOfBasis_right_inverse _ _

variable (R M N)
variable [Module.Finite R M] [Module.Finite R N] [Module.Free R M] [Module.Free R N]

/--
A linear equivalence between `Dual M ⊗ Dual N` and `Dual (M ⊗ N)` when `M` and `N` are finite free
modules. It sends `f ⊗ g` to the composition of `TensorProduct.map f g` with the natural
isomorphism `R ⊗ R ≃ R`.
-/
@[simp]
noncomputable def dualDistribEquiv : Dual R M ⊗[R] Dual R N ≃ₗ[R] Dual R (M ⊗[R] N) :=
  dualDistribEquivOfBasis (Module.Free.chooseBasis R M) (Module.Free.chooseBasis R N)

end TensorProduct
