/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth

! This file was ported from Lean 3 source module topology.algebra.module.basic
! leanprover-community/mathlib commit 9a59dcb7a2d06bf55da57b9030169219980660cd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Ring.Basic
import Mathbin.Topology.Algebra.MulAction
import Mathbin.Topology.Algebra.UniformGroup
import Mathbin.Topology.ContinuousFunction.Basic
import Mathbin.Topology.UniformSpace.UniformEmbedding
import Mathbin.Algebra.Algebra.Basic
import Mathbin.LinearAlgebra.Projection
import Mathbin.LinearAlgebra.Pi
import Mathbin.RingTheory.SimpleModule

/-!
# Theory of topological modules and continuous linear maps.

We use the class `has_continuous_smul` for topological (semi) modules and topological vector spaces.

In this file we define continuous (semi-)linear maps, as semilinear maps between topological
modules which are continuous. The set of continuous semilinear maps between the topological
`R₁`-module `M` and `R₂`-module `M₂` with respect to the `ring_hom` `σ` is denoted by `M →SL[σ] M₂`.
Plain linear maps are denoted by `M →L[R] M₂` and star-linear maps by `M →L⋆[R] M₂`.

The corresponding notation for equivalences is `M ≃SL[σ] M₂`, `M ≃L[R] M₂` and `M ≃L⋆[R] M₂`.
-/


open Filter

open LinearMap (ker range)

open Topology BigOperators Filter

universe u v w u'

section

variable {R : Type _} {M : Type _} [Ring R] [TopologicalSpace R] [TopologicalSpace M]
  [AddCommGroup M] [Module R M]

theorem ContinuousSMul.of_nhds_zero [TopologicalRing R] [TopologicalAddGroup M]
    (hmul : Tendsto (fun p : R × M => p.1 • p.2) (𝓝 0 ×ᶠ 𝓝 0) (𝓝 0))
    (hmulleft : ∀ m : M, Tendsto (fun a : R => a • m) (𝓝 0) (𝓝 0))
    (hmulright : ∀ a : R, Tendsto (fun m : M => a • m) (𝓝 0) (𝓝 0)) : ContinuousSMul R M :=
  ⟨by
    rw [continuous_iff_continuousAt]
    rintro ⟨a₀, m₀⟩
    have key :
      ∀ p : R × M,
        p.1 • p.2 = a₀ • m₀ + ((p.1 - a₀) • m₀ + a₀ • (p.2 - m₀) + (p.1 - a₀) • (p.2 - m₀)) :=
      by
      rintro ⟨a, m⟩
      simp [sub_smul, smul_sub]
      abel
    rw [funext key]
    clear key
    refine' tendsto_const_nhds.add (tendsto.add (tendsto.add _ _) _)
    · rw [sub_self, zero_smul]
      apply (hmulleft m₀).comp
      rw [show (fun p : R × M => p.1 - a₀) = (fun a => a - a₀) ∘ Prod.fst
          by
          ext
          rfl,
        nhds_prod_eq]
      have : tendsto (fun a => a - a₀) (𝓝 a₀) (𝓝 0) :=
        by
        rw [← sub_self a₀]
        exact tendsto_id.sub tendsto_const_nhds
      exact this.comp tendsto_fst
    · rw [sub_self, smul_zero]
      apply (hmulright a₀).comp
      rw [show (fun p : R × M => p.2 - m₀) = (fun m => m - m₀) ∘ Prod.snd
          by
          ext
          rfl,
        nhds_prod_eq]
      have : tendsto (fun m => m - m₀) (𝓝 m₀) (𝓝 0) :=
        by
        rw [← sub_self m₀]
        exact tendsto_id.sub tendsto_const_nhds
      exact this.comp tendsto_snd
    · rw [sub_self, zero_smul, nhds_prod_eq,
        show
          (fun p : R × M => (p.fst - a₀) • (p.snd - m₀)) =
            (fun p : R × M => p.1 • p.2) ∘ Prod.map (fun a => a - a₀) fun m => m - m₀
          by
          ext
          rfl]
      apply hmul.comp (tendsto.prod_map _ _) <;>
        · rw [← sub_self]
          exact tendsto_id.sub tendsto_const_nhds⟩
#align has_continuous_smul.of_nhds_zero ContinuousSMul.of_nhds_zero

end

section

variable {R : Type _} {M : Type _} [Ring R] [TopologicalSpace R] [TopologicalSpace M]
  [AddCommGroup M] [ContinuousAdd M] [Module R M] [ContinuousSMul R M]

/-- If `M` is a topological module over `R` and `0` is a limit of invertible elements of `R`, then
`⊤` is the only submodule of `M` with a nonempty interior.
This is the case, e.g., if `R` is a nontrivially normed field. -/
theorem Submodule.eq_top_of_nonempty_interior' [NeBot (𝓝[{ x : R | IsUnit x }] 0)]
    (s : Submodule R M) (hs : (interior (s : Set M)).Nonempty) : s = ⊤ :=
  by
  rcases hs with ⟨y, hy⟩
  refine' Submodule.eq_top_iff'.2 fun x => _
  rw [mem_interior_iff_mem_nhds] at hy
  have : tendsto (fun c : R => y + c • x) (𝓝[{ x : R | IsUnit x }] 0) (𝓝 (y + (0 : R) • x)) :=
    tendsto_const_nhds.add ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul tendsto_const_nhds)
  rw [zero_smul, add_zero] at this
  obtain ⟨_, hu : y + _ • _ ∈ s, u, rfl⟩ :=
    nonempty_of_mem (inter_mem (mem_map.1 (this hy)) self_mem_nhdsWithin)
  have hy' : y ∈ ↑s := mem_of_mem_nhds hy
  rwa [s.add_mem_iff_right hy', ← Units.smul_def, s.smul_mem_iff' u] at hu
#align submodule.eq_top_of_nonempty_interior' Submodule.eq_top_of_nonempty_interior'

variable (R M)

/-- Let `R` be a topological ring such that zero is not an isolated point (e.g., a nontrivially
normed field, see `normed_field.punctured_nhds_ne_bot`). Let `M` be a nontrivial module over `R`
such that `c • x = 0` implies `c = 0 ∨ x = 0`. Then `M` has no isolated points. We formulate this
using `ne_bot (𝓝[≠] x)`.

This lemma is not an instance because Lean would need to find `[has_continuous_smul ?m_1 M]` with
unknown `?m_1`. We register this as an instance for `R = ℝ` in `real.punctured_nhds_module_ne_bot`.
One can also use `haveI := module.punctured_nhds_ne_bot R M` in a proof.
-/
theorem Module.punctured_nhds_neBot [Nontrivial M] [NeBot (𝓝[≠] (0 : R))] [NoZeroSMulDivisors R M]
    (x : M) : NeBot (𝓝[≠] x) :=
  by
  rcases exists_ne (0 : M) with ⟨y, hy⟩
  suffices : tendsto (fun c : R => x + c • y) (𝓝[≠] 0) (𝓝[≠] x); exact this.ne_bot
  refine' tendsto.inf _ (tendsto_principal_principal.2 <| _)
  · convert tendsto_const_nhds.add ((@tendsto_id R _).smul_const y)
    rw [zero_smul, add_zero]
  · intro c hc
    simpa [hy] using hc
#align module.punctured_nhds_ne_bot Module.punctured_nhds_neBot

end

section LatticeOps

variable {ι R M₁ M₂ : Type _} [Semiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁]
  [Module R M₂] [u : TopologicalSpace R] {t : TopologicalSpace M₂} [ContinuousSMul R M₂]
  (f : M₁ →ₗ[R] M₂)

theorem continuousSMul_induced : @ContinuousSMul R M₁ _ u (t.induced f) :=
  {
    continuous_smul := by
      letI : TopologicalSpace M₁ := t.induced f
      refine' continuous_induced_rng.2 _
      simp_rw [Function.comp, f.map_smul]
      refine' continuous_fst.smul (continuous_induced_dom.comp continuous_snd) }
#align has_continuous_smul_induced continuousSMul_induced

end LatticeOps

namespace Submodule

variable {α β : Type _} [TopologicalSpace β]

instance [TopologicalSpace α] [Semiring α] [AddCommMonoid β] [Module α β] [ContinuousSMul α β]
    (S : Submodule α β) : ContinuousSMul α S
    where continuous_smul :=
    by
    rw [embedding_subtype_coe.to_inducing.continuous_iff]
    exact continuous_fst.smul (continuous_subtype_coe.comp continuous_snd)

instance [Ring α] [AddCommGroup β] [Module α β] [TopologicalAddGroup β] (S : Submodule α β) :
    TopologicalAddGroup S :=
  S.toAddSubgroup.TopologicalAddGroup

end Submodule

section closure

variable {R R' : Type u} {M M' : Type v} [Semiring R] [TopologicalSpace R] [Ring R']
  [TopologicalSpace R'] [TopologicalSpace M] [AddCommMonoid M] [TopologicalSpace M']
  [AddCommGroup M'] [Module R M] [ContinuousSMul R M] [Module R' M'] [ContinuousSMul R' M']

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Submodule.closure_smul_self_subset (s : Submodule R M) :
    (fun p : R × M => p.1 • p.2) '' Set.univ ×ˢ closure s ⊆ closure s :=
  calc
    (fun p : R × M => p.1 • p.2) '' Set.univ ×ˢ closure s =
        (fun p : R × M => p.1 • p.2) '' closure (Set.univ ×ˢ s) :=
      by simp [closure_prod_eq]
    _ ⊆ closure ((fun p : R × M => p.1 • p.2) '' Set.univ ×ˢ s) :=
      (image_closure_subset_closure_image continuous_smul)
    _ = closure s := by
      congr
      ext x
      refine' ⟨_, fun hx => ⟨⟨1, x⟩, ⟨Set.mem_univ _, hx⟩, one_smul R _⟩⟩
      rintro ⟨⟨c, y⟩, ⟨hc, hy⟩, rfl⟩
      simp [s.smul_mem c hy]
    
#align submodule.closure_smul_self_subset Submodule.closure_smul_self_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Submodule.closure_smul_self_eq (s : Submodule R M) :
    (fun p : R × M => p.1 • p.2) '' Set.univ ×ˢ closure s = closure s :=
  s.closure_smul_self_subset.antisymm fun x hx => ⟨⟨1, x⟩, ⟨Set.mem_univ _, hx⟩, one_smul R _⟩
#align submodule.closure_smul_self_eq Submodule.closure_smul_self_eq

variable [ContinuousAdd M]

/-- The (topological-space) closure of a submodule of a topological `R`-module `M` is itself
a submodule. -/
def Submodule.topologicalClosure (s : Submodule R M) : Submodule R M :=
  {
    s.toAddSubmonoid.topologicalClosure with
    carrier := closure (s : Set M)
    smul_mem' := fun c x hx => s.closure_smul_self_subset ⟨⟨c, x⟩, ⟨Set.mem_univ _, hx⟩, rfl⟩ }
#align submodule.topological_closure Submodule.topologicalClosure

@[simp]
theorem Submodule.topologicalClosure_coe (s : Submodule R M) :
    (s.topologicalClosure : Set M) = closure (s : Set M) :=
  rfl
#align submodule.topological_closure_coe Submodule.topologicalClosure_coe

theorem Submodule.le_topologicalClosure (s : Submodule R M) : s ≤ s.topologicalClosure :=
  subset_closure
#align submodule.le_topological_closure Submodule.le_topologicalClosure

theorem Submodule.isClosed_topologicalClosure (s : Submodule R M) :
    IsClosed (s.topologicalClosure : Set M) := by convert isClosed_closure
#align submodule.is_closed_topological_closure Submodule.isClosed_topologicalClosure

theorem Submodule.topologicalClosure_minimal (s : Submodule R M) {t : Submodule R M} (h : s ≤ t)
    (ht : IsClosed (t : Set M)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht
#align submodule.topological_closure_minimal Submodule.topologicalClosure_minimal

theorem Submodule.topologicalClosure_mono {s : Submodule R M} {t : Submodule R M} (h : s ≤ t) :
    s.topologicalClosure ≤ t.topologicalClosure :=
  s.topologicalClosure_minimal (h.trans t.le_topologicalClosure) t.isClosed_topologicalClosure
#align submodule.topological_closure_mono Submodule.topologicalClosure_mono

/-- The topological closure of a closed submodule `s` is equal to `s`. -/
theorem IsClosed.submodule_topologicalClosure_eq {s : Submodule R M} (hs : IsClosed (s : Set M)) :
    s.topologicalClosure = s :=
  le_antisymm (s.topologicalClosure_minimal rfl.le hs) s.le_topologicalClosure
#align is_closed.submodule_topological_closure_eq IsClosed.submodule_topologicalClosure_eq

/-- A subspace is dense iff its topological closure is the entire space. -/
theorem Submodule.dense_iff_topologicalClosure_eq_top {s : Submodule R M} :
    Dense (s : Set M) ↔ s.topologicalClosure = ⊤ :=
  by
  rw [← SetLike.coe_set_eq, dense_iff_closure_eq]
  simp
#align submodule.dense_iff_topological_closure_eq_top Submodule.dense_iff_topologicalClosure_eq_top

instance {M' : Type _} [AddCommMonoid M'] [Module R M'] [UniformSpace M'] [ContinuousAdd M']
    [ContinuousSMul R M'] [CompleteSpace M'] (U : Submodule R M') :
    CompleteSpace U.topologicalClosure :=
  isClosed_closure.completeSpace_coe

/-- A maximal proper subspace of a topological module (i.e a `submodule` satisfying `is_coatom`)
is either closed or dense. -/
theorem Submodule.isClosed_or_dense_of_isCoatom (s : Submodule R M) (hs : IsCoatom s) :
    IsClosed (s : Set M) ∨ Dense (s : Set M) :=
  (hs.le_iff.mp s.le_topologicalClosure).symm.imp (isClosed_of_closure_subset ∘ Eq.le)
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
#align submodule.is_closed_or_dense_of_is_coatom Submodule.isClosed_or_dense_of_isCoatom

theorem LinearMap.isClosed_or_dense_ker [ContinuousAdd M'] [IsSimpleModule R' R']
    (l : M' →ₗ[R'] R') : IsClosed (l.ker : Set M') ∨ Dense (l.ker : Set M') :=
  by
  rcases l.surjective_or_eq_zero with (hl | rfl)
  · refine' l.ker.is_closed_or_dense_of_is_coatom (LinearMap.isCoatom_ker_of_surjective hl)
  · rw [LinearMap.ker_zero]
    left
    exact isClosed_univ
#align linear_map.is_closed_or_dense_ker LinearMap.isClosed_or_dense_ker

end closure

section Pi

theorem LinearMap.continuous_on_pi {ι : Type _} {R : Type _} {M : Type _} [Finite ι] [Semiring R]
    [TopologicalSpace R] [AddCommMonoid M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] (f : (ι → R) →ₗ[R] M) : Continuous f :=
  by
  cases nonempty_fintype ι
  classical
    -- for the proof, write `f` in the standard basis, and use that each coordinate is a continuous
    -- function.
    have : (f : (ι → R) → M) = fun x => ∑ i : ι, x i • f fun j => if i = j then 1 else 0 :=
      by
      ext x
      exact f.pi_apply_eq_sum_univ x
    rw [this]
    refine' continuous_finset_sum _ fun i hi => _
    exact (continuous_apply i).smul continuous_const
#align linear_map.continuous_on_pi LinearMap.continuous_on_pi

end Pi

/-- Continuous linear maps between modules. We only put the type classes that are necessary for the
definition, although in applications `M` and `M₂` will be topological modules over the topological
ring `R`. -/
structure ContinuousLinearMap {R : Type _} {S : Type _} [Semiring R] [Semiring S] (σ : R →+* S)
  (M : Type _) [TopologicalSpace M] [AddCommMonoid M] (M₂ : Type _) [TopologicalSpace M₂]
  [AddCommMonoid M₂] [Module R M] [Module S M₂] extends M →ₛₗ[σ] M₂ where
  cont : Continuous to_fun := by continuity
#align continuous_linear_map ContinuousLinearMap

-- mathport name: «expr →SL[ ] »
notation:25 M " →SL[" σ "] " M₂ => ContinuousLinearMap σ M M₂

-- mathport name: «expr →L[ ] »
notation:25 M " →L[" R "] " M₂ => ContinuousLinearMap (RingHom.id R) M M₂

-- mathport name: «expr →L⋆[ ] »
notation:25 M " →L⋆[" R "] " M₂ => ContinuousLinearMap (starRingEnd R) M M₂

/-- `continuous_semilinear_map_class F σ M M₂` asserts `F` is a type of bundled continuous
`σ`-semilinear maps `M → M₂`.  See also `continuous_linear_map_class F R M M₂` for the case where
`σ` is the identity map on `R`.  A map `f` between an `R`-module and an `S`-module over a ring
homomorphism `σ : R →+* S` is semilinear if it satisfies the two properties `f (x + y) = f x + f y`
and `f (c • x) = (σ c) • f x`. -/
class ContinuousSemilinearMapClass (F : Type _) {R S : outParam (Type _)} [Semiring R] [Semiring S]
  (σ : outParam <| R →+* S) (M : outParam (Type _)) [TopologicalSpace M] [AddCommMonoid M]
  (M₂ : outParam (Type _)) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
  [Module S M₂] extends SemilinearMapClass F σ M M₂, ContinuousMapClass F M M₂
#align continuous_semilinear_map_class ContinuousSemilinearMapClass

-- `σ`, `R` and `S` become metavariables, but they are all outparams so it's OK
attribute [nolint dangerous_instance] ContinuousSemilinearMapClass.toContinuousMapClass

/-- `continuous_linear_map_class F R M M₂` asserts `F` is a type of bundled continuous
`R`-linear maps `M → M₂`.  This is an abbreviation for
`continuous_semilinear_map_class F (ring_hom.id R) M M₂`.  -/
abbrev ContinuousLinearMapClass (F : Type _) (R : outParam (Type _)) [Semiring R]
    (M : outParam (Type _)) [TopologicalSpace M] [AddCommMonoid M] (M₂ : outParam (Type _))
    [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M] [Module R M₂] :=
  ContinuousSemilinearMapClass F (RingHom.id R) M M₂
#align continuous_linear_map_class ContinuousLinearMapClass

/-- Continuous linear equivalences between modules. We only put the type classes that are necessary
for the definition, although in applications `M` and `M₂` will be topological modules over the
topological semiring `R`. -/
@[nolint has_nonempty_instance]
structure ContinuousLinearEquiv {R : Type _} {S : Type _} [Semiring R] [Semiring S] (σ : R →+* S)
  {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type _) [TopologicalSpace M]
  [AddCommMonoid M] (M₂ : Type _) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
  [Module S M₂] extends M ≃ₛₗ[σ] M₂ where
  continuous_toFun : Continuous to_fun := by continuity
  continuous_invFun : Continuous inv_fun := by continuity
#align continuous_linear_equiv ContinuousLinearEquiv

-- mathport name: «expr ≃SL[ ] »
notation:50 M " ≃SL[" σ "] " M₂ => ContinuousLinearEquiv σ M M₂

-- mathport name: «expr ≃L[ ] »
notation:50 M " ≃L[" R "] " M₂ => ContinuousLinearEquiv (RingHom.id R) M M₂

-- mathport name: «expr ≃L⋆[ ] »
notation:50 M " ≃L⋆[" R "] " M₂ => ContinuousLinearEquiv (starRingEnd R) M M₂

/-- `continuous_semilinear_equiv_class F σ M M₂` asserts `F` is a type of bundled continuous
`σ`-semilinear equivs `M → M₂`.  See also `continuous_linear_equiv_class F R M M₂` for the case
where `σ` is the identity map on `R`.  A map `f` between an `R`-module and an `S`-module over a ring
homomorphism `σ : R →+* S` is semilinear if it satisfies the two properties `f (x + y) = f x + f y`
and `f (c • x) = (σ c) • f x`. -/
class ContinuousSemilinearEquivClass (F : Type _) {R : outParam (Type _)} {S : outParam (Type _)}
  [Semiring R] [Semiring S] (σ : outParam <| R →+* S) {σ' : outParam <| S →+* R}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : outParam (Type _)) [TopologicalSpace M]
  [AddCommMonoid M] (M₂ : outParam (Type _)) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
  [Module S M₂] extends SemilinearEquivClass F σ M M₂ where
  map_continuous : ∀ f : F, Continuous f := by continuity
  inv_continuous : ∀ f : F, Continuous (inv f) := by continuity
#align continuous_semilinear_equiv_class ContinuousSemilinearEquivClass

/-- `continuous_linear_equiv_class F σ M M₂` asserts `F` is a type of bundled continuous
`R`-linear equivs `M → M₂`. This is an abbreviation for
`continuous_semilinear_equiv_class F (ring_hom.id) M M₂`. -/
abbrev ContinuousLinearEquivClass (F : Type _) (R : outParam (Type _)) [Semiring R]
    (M : outParam (Type _)) [TopologicalSpace M] [AddCommMonoid M] (M₂ : outParam (Type _))
    [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M] [Module R M₂] :=
  ContinuousSemilinearEquivClass F (RingHom.id R) M M₂
#align continuous_linear_equiv_class ContinuousLinearEquivClass

namespace ContinuousSemilinearEquivClass

variable (F : Type _) {R : Type _} {S : Type _} [Semiring R] [Semiring S] (σ : R →+* S)
  {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type _) [TopologicalSpace M]
  [AddCommMonoid M] (M₂ : Type _) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
  [Module S M₂]

include σ'

-- `σ'` becomes a metavariable, but it's OK since it's an outparam
@[nolint dangerous_instance]
instance (priority := 100) [s : ContinuousSemilinearEquivClass F σ M M₂] :
    ContinuousSemilinearMapClass F σ M M₂ :=
  { s with
    coe := (coe : F → M → M₂)
    coe_injective' := @FunLike.coe_injective F _ _ _ }

omit σ'

end ContinuousSemilinearEquivClass

section PointwiseLimits

variable {M₁ M₂ α R S : Type _} [TopologicalSpace M₂] [T2Space M₂] [Semiring R] [Semiring S]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module S M₂] [ContinuousConstSMul S M₂]

section

variable (M₁ M₂) (σ : R →+* S)

theorem isClosed_setOf_map_smul : IsClosed { f : M₁ → M₂ | ∀ c x, f (c • x) = σ c • f x } :=
  by
  simp only [Set.setOf_forall]
  exact
    isClosed_interᵢ fun c =>
      isClosed_interᵢ fun x => isClosed_eq (continuous_apply _) ((continuous_apply _).const_smul _)
#align is_closed_set_of_map_smul isClosed_setOf_map_smul

end

variable [ContinuousAdd M₂] {σ : R →+* S} {l : Filter α}

/-- Constructs a bundled linear map from a function and a proof that this function belongs to the
closure of the set of linear maps. -/
@[simps (config := { fullyApplied := false })]
def linearMapOfMemClosureRangeCoe (f : M₁ → M₂)
    (hf : f ∈ closure (Set.range (coeFn : (M₁ →ₛₗ[σ] M₂) → M₁ → M₂))) : M₁ →ₛₗ[σ] M₂ :=
  { addMonoidHomOfMemClosureRangeCoe f hf with
    toFun := f
    map_smul' :=
      (isClosed_setOf_map_smul M₁ M₂ σ).closure_subset_iff.2
        (Set.range_subset_iff.2 LinearMap.map_smulₛₗ) hf }
#align linear_map_of_mem_closure_range_coe linearMapOfMemClosureRangeCoe

/-- Construct a bundled linear map from a pointwise limit of linear maps -/
@[simps (config := { fullyApplied := false })]
def linearMapOfTendsto (f : M₁ → M₂) (g : α → M₁ →ₛₗ[σ] M₂) [l.ne_bot]
    (h : Tendsto (fun a x => g a x) l (𝓝 f)) : M₁ →ₛₗ[σ] M₂ :=
  linearMapOfMemClosureRangeCoe f <|
    mem_closure_of_tendsto h <| eventually_of_forall fun a => Set.mem_range_self _
#align linear_map_of_tendsto linearMapOfTendsto

variable (M₁ M₂ σ)

theorem LinearMap.isClosed_range_coe : IsClosed (Set.range (coeFn : (M₁ →ₛₗ[σ] M₂) → M₁ → M₂)) :=
  isClosed_of_closure_subset fun f hf => ⟨linearMapOfMemClosureRangeCoe f hf, rfl⟩
#align linear_map.is_closed_range_coe LinearMap.isClosed_range_coe

end PointwiseLimits

namespace ContinuousLinearMap

section Semiring

/-!
### Properties that hold for non-necessarily commutative semirings.
-/


variable {R₁ : Type _} {R₂ : Type _} {R₃ : Type _} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃} {M₁ : Type _} [TopologicalSpace M₁]
  [AddCommMonoid M₁] {M'₁ : Type _} [TopologicalSpace M'₁] [AddCommMonoid M'₁] {M₂ : Type _}
  [TopologicalSpace M₂] [AddCommMonoid M₂] {M₃ : Type _} [TopologicalSpace M₃] [AddCommMonoid M₃]
  {M₄ : Type _} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R₁ M₁] [Module R₁ M'₁]
  [Module R₂ M₂] [Module R₃ M₃]

/-- Coerce continuous linear maps to linear maps. -/
instance : Coe (M₁ →SL[σ₁₂] M₂) (M₁ →ₛₗ[σ₁₂] M₂) :=
  ⟨toLinearMap⟩

-- make the coercion the preferred form
@[simp]
theorem toLinearMap_eq_coe (f : M₁ →SL[σ₁₂] M₂) : f.toLinearMap = f :=
  rfl
#align continuous_linear_map.to_linear_map_eq_coe ContinuousLinearMap.toLinearMap_eq_coe

theorem coe_injective : Function.Injective (coe : (M₁ →SL[σ₁₂] M₂) → M₁ →ₛₗ[σ₁₂] M₂) :=
  by
  intro f g H
  cases f
  cases g
  congr
#align continuous_linear_map.coe_injective ContinuousLinearMap.coe_injective

instance : ContinuousSemilinearMapClass (M₁ →SL[σ₁₂] M₂) σ₁₂ M₁ M₂
    where
  coe f := f.toFun
  coe_injective' f g h := coe_injective (FunLike.coe_injective h)
  map_add f := map_add f.toLinearMap
  map_continuous f := f.2
  map_smulₛₗ f := f.toLinearMap.map_smul'

-- see Note [function coercion]
/-- Coerce continuous linear maps to functions. -/
instance toFun : CoeFun (M₁ →SL[σ₁₂] M₂) fun _ => M₁ → M₂ :=
  ⟨fun f => f.toFun⟩
#align continuous_linear_map.to_fun ContinuousLinearMap.toFun

@[simp]
theorem coe_mk (f : M₁ →ₛₗ[σ₁₂] M₂) (h) : (mk f h : M₁ →ₛₗ[σ₁₂] M₂) = f :=
  rfl
#align continuous_linear_map.coe_mk ContinuousLinearMap.coe_mk

@[simp]
theorem coe_mk' (f : M₁ →ₛₗ[σ₁₂] M₂) (h) : (mk f h : M₁ → M₂) = f :=
  rfl
#align continuous_linear_map.coe_mk' ContinuousLinearMap.coe_mk'

@[continuity]
protected theorem continuous (f : M₁ →SL[σ₁₂] M₂) : Continuous f :=
  f.2
#align continuous_linear_map.continuous ContinuousLinearMap.continuous

protected theorem uniformContinuous {E₁ E₂ : Type _} [UniformSpace E₁] [UniformSpace E₂]
    [AddCommGroup E₁] [AddCommGroup E₂] [Module R₁ E₁] [Module R₂ E₂] [UniformAddGroup E₁]
    [UniformAddGroup E₂] (f : E₁ →SL[σ₁₂] E₂) : UniformContinuous f :=
  uniformContinuous_addMonoidHom_of_continuous f.Continuous
#align continuous_linear_map.uniform_continuous ContinuousLinearMap.uniformContinuous

@[simp, norm_cast]
theorem coe_inj {f g : M₁ →SL[σ₁₂] M₂} : (f : M₁ →ₛₗ[σ₁₂] M₂) = g ↔ f = g :=
  coe_injective.eq_iff
#align continuous_linear_map.coe_inj ContinuousLinearMap.coe_inj

theorem coeFn_injective : @Function.Injective (M₁ →SL[σ₁₂] M₂) (M₁ → M₂) coeFn :=
  FunLike.coe_injective
#align continuous_linear_map.coe_fn_injective ContinuousLinearMap.coeFn_injective

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : M₁ →SL[σ₁₂] M₂) : M₁ → M₂ :=
  h
#align continuous_linear_map.simps.apply ContinuousLinearMap.Simps.apply

/-- See Note [custom simps projection]. -/
def Simps.coe (h : M₁ →SL[σ₁₂] M₂) : M₁ →ₛₗ[σ₁₂] M₂ :=
  h
#align continuous_linear_map.simps.coe ContinuousLinearMap.Simps.coe

initialize_simps_projections ContinuousLinearMap (to_linear_map_to_fun → apply, toLinearMap → coe)

@[ext]
theorem ext {f g : M₁ →SL[σ₁₂] M₂} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h
#align continuous_linear_map.ext ContinuousLinearMap.ext

theorem ext_iff {f g : M₁ →SL[σ₁₂] M₂} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align continuous_linear_map.ext_iff ContinuousLinearMap.ext_iff

/-- Copy of a `continuous_linear_map` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : M₁ →SL[σ₁₂] M₂) (f' : M₁ → M₂) (h : f' = ⇑f) : M₁ →SL[σ₁₂] M₂
    where
  toLinearMap := f.toLinearMap.copy f' h
  cont := show Continuous f' from h.symm ▸ f.Continuous
#align continuous_linear_map.copy ContinuousLinearMap.copy

@[simp]
theorem coe_copy (f : M₁ →SL[σ₁₂] M₂) (f' : M₁ → M₂) (h : f' = ⇑f) : ⇑(f.copy f' h) = f' :=
  rfl
#align continuous_linear_map.coe_copy ContinuousLinearMap.coe_copy

theorem copy_eq (f : M₁ →SL[σ₁₂] M₂) (f' : M₁ → M₂) (h : f' = ⇑f) : f.copy f' h = f :=
  FunLike.ext' h
#align continuous_linear_map.copy_eq ContinuousLinearMap.copy_eq

-- make some straightforward lemmas available to `simp`.
protected theorem map_zero (f : M₁ →SL[σ₁₂] M₂) : f (0 : M₁) = 0 :=
  map_zero f
#align continuous_linear_map.map_zero ContinuousLinearMap.map_zero

protected theorem map_add (f : M₁ →SL[σ₁₂] M₂) (x y : M₁) : f (x + y) = f x + f y :=
  map_add f x y
#align continuous_linear_map.map_add ContinuousLinearMap.map_add

@[simp]
protected theorem map_smulₛₗ (f : M₁ →SL[σ₁₂] M₂) (c : R₁) (x : M₁) : f (c • x) = σ₁₂ c • f x :=
  (toLinearMap _).map_smulₛₗ _ _
#align continuous_linear_map.map_smulₛₗ ContinuousLinearMap.map_smulₛₗ

@[simp]
protected theorem map_smul [Module R₁ M₂] (f : M₁ →L[R₁] M₂) (c : R₁) (x : M₁) :
    f (c • x) = c • f x := by simp only [RingHom.id_apply, ContinuousLinearMap.map_smulₛₗ]
#align continuous_linear_map.map_smul ContinuousLinearMap.map_smul

@[simp]
theorem map_smul_of_tower {R S : Type _} [Semiring S] [SMul R M₁] [Module S M₁] [SMul R M₂]
    [Module S M₂] [LinearMap.CompatibleSMul M₁ M₂ R S] (f : M₁ →L[S] M₂) (c : R) (x : M₁) :
    f (c • x) = c • f x :=
  LinearMap.CompatibleSMul.map_smul f c x
#align continuous_linear_map.map_smul_of_tower ContinuousLinearMap.map_smul_of_tower

protected theorem map_sum {ι : Type _} (f : M₁ →SL[σ₁₂] M₂) (s : Finset ι) (g : ι → M₁) :
    f (∑ i in s, g i) = ∑ i in s, f (g i) :=
  f.toLinearMap.map_sum
#align continuous_linear_map.map_sum ContinuousLinearMap.map_sum

@[simp, norm_cast]
theorem coe_coe (f : M₁ →SL[σ₁₂] M₂) : ⇑(f : M₁ →ₛₗ[σ₁₂] M₂) = f :=
  rfl
#align continuous_linear_map.coe_coe ContinuousLinearMap.coe_coe

@[ext]
theorem ext_ring [TopologicalSpace R₁] {f g : R₁ →L[R₁] M₁} (h : f 1 = g 1) : f = g :=
  coe_inj.1 <| LinearMap.ext_ring h
#align continuous_linear_map.ext_ring ContinuousLinearMap.ext_ring

theorem ext_ring_iff [TopologicalSpace R₁] {f g : R₁ →L[R₁] M₁} : f = g ↔ f 1 = g 1 :=
  ⟨fun h => h ▸ rfl, ext_ring⟩
#align continuous_linear_map.ext_ring_iff ContinuousLinearMap.ext_ring_iff

/-- If two continuous linear maps are equal on a set `s`, then they are equal on the closure
of the `submodule.span` of this set. -/
theorem eqOn_closure_span [T2Space M₂] {s : Set M₁} {f g : M₁ →SL[σ₁₂] M₂} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure (Submodule.span R₁ s : Set M₁)) :=
  (LinearMap.eqOn_span' h).closure f.Continuous g.Continuous
#align continuous_linear_map.eq_on_closure_span ContinuousLinearMap.eqOn_closure_span

/-- If the submodule generated by a set `s` is dense in the ambient module, then two continuous
linear maps equal on `s` are equal. -/
theorem ext_on [T2Space M₂] {s : Set M₁} (hs : Dense (Submodule.span R₁ s : Set M₁))
    {f g : M₁ →SL[σ₁₂] M₂} (h : Set.EqOn f g s) : f = g :=
  ext fun x => eqOn_closure_span h (hs x)
#align continuous_linear_map.ext_on ContinuousLinearMap.ext_on

/-- Under a continuous linear map, the image of the `topological_closure` of a submodule is
contained in the `topological_closure` of its image. -/
theorem Submodule.topologicalClosure_map [RingHomSurjective σ₁₂] [TopologicalSpace R₁]
    [TopologicalSpace R₂] [ContinuousSMul R₁ M₁] [ContinuousAdd M₁] [ContinuousSMul R₂ M₂]
    [ContinuousAdd M₂] (f : M₁ →SL[σ₁₂] M₂) (s : Submodule R₁ M₁) :
    s.topologicalClosure.map (f : M₁ →ₛₗ[σ₁₂] M₂) ≤
      (s.map (f : M₁ →ₛₗ[σ₁₂] M₂)).topologicalClosure :=
  image_closure_subset_closure_image f.Continuous
#align submodule.topological_closure_map Submodule.topologicalClosure_map

/-- Under a dense continuous linear map, a submodule whose `topological_closure` is `⊤` is sent to
another such submodule.  That is, the image of a dense set under a map with dense range is dense.
-/
theorem DenseRange.topologicalClosure_map_submodule [RingHomSurjective σ₁₂] [TopologicalSpace R₁]
    [TopologicalSpace R₂] [ContinuousSMul R₁ M₁] [ContinuousAdd M₁] [ContinuousSMul R₂ M₂]
    [ContinuousAdd M₂] {f : M₁ →SL[σ₁₂] M₂} (hf' : DenseRange f) {s : Submodule R₁ M₁}
    (hs : s.topologicalClosure = ⊤) : (s.map (f : M₁ →ₛₗ[σ₁₂] M₂)).topologicalClosure = ⊤ :=
  by
  rw [SetLike.ext'_iff] at hs⊢
  simp only [Submodule.topologicalClosure_coe, Submodule.top_coe, ← dense_iff_closure_eq] at hs⊢
  exact hf'.dense_image f.continuous hs
#align dense_range.topological_closure_map_submodule DenseRange.topologicalClosure_map_submodule

section SmulMonoid

variable {S₂ T₂ : Type _} [Monoid S₂] [Monoid T₂]

variable [DistribMulAction S₂ M₂] [SMulCommClass R₂ S₂ M₂] [ContinuousConstSMul S₂ M₂]

variable [DistribMulAction T₂ M₂] [SMulCommClass R₂ T₂ M₂] [ContinuousConstSMul T₂ M₂]

instance : MulAction S₂ (M₁ →SL[σ₁₂] M₂)
    where
  smul c f := ⟨c • f, (f.2.const_smul _ : Continuous fun x => c • f x)⟩
  one_smul f := ext fun x => one_smul _ _
  mul_smul a b f := ext fun x => mul_smul _ _ _

theorem smul_apply (c : S₂) (f : M₁ →SL[σ₁₂] M₂) (x : M₁) : (c • f) x = c • f x :=
  rfl
#align continuous_linear_map.smul_apply ContinuousLinearMap.smul_apply

@[simp, norm_cast]
theorem coe_smul (c : S₂) (f : M₁ →SL[σ₁₂] M₂) : (↑(c • f) : M₁ →ₛₗ[σ₁₂] M₂) = c • f :=
  rfl
#align continuous_linear_map.coe_smul ContinuousLinearMap.coe_smul

@[simp, norm_cast]
theorem coe_smul' (c : S₂) (f : M₁ →SL[σ₁₂] M₂) : ⇑(c • f) = c • f :=
  rfl
#align continuous_linear_map.coe_smul' ContinuousLinearMap.coe_smul'

instance [SMul S₂ T₂] [IsScalarTower S₂ T₂ M₂] : IsScalarTower S₂ T₂ (M₁ →SL[σ₁₂] M₂) :=
  ⟨fun a b f => ext fun x => smul_assoc a b (f x)⟩

instance [SMulCommClass S₂ T₂ M₂] : SMulCommClass S₂ T₂ (M₁ →SL[σ₁₂] M₂) :=
  ⟨fun a b f => ext fun x => smul_comm a b (f x)⟩

end SmulMonoid

/-- The continuous map that is constantly zero. -/
instance : Zero (M₁ →SL[σ₁₂] M₂) :=
  ⟨⟨0, continuous_zero⟩⟩

instance : Inhabited (M₁ →SL[σ₁₂] M₂) :=
  ⟨0⟩

@[simp]
theorem default_def : (default : M₁ →SL[σ₁₂] M₂) = 0 :=
  rfl
#align continuous_linear_map.default_def ContinuousLinearMap.default_def

@[simp]
theorem zero_apply (x : M₁) : (0 : M₁ →SL[σ₁₂] M₂) x = 0 :=
  rfl
#align continuous_linear_map.zero_apply ContinuousLinearMap.zero_apply

@[simp, norm_cast]
theorem coe_zero : ((0 : M₁ →SL[σ₁₂] M₂) : M₁ →ₛₗ[σ₁₂] M₂) = 0 :=
  rfl
#align continuous_linear_map.coe_zero ContinuousLinearMap.coe_zero

/- no simp attribute on the next line as simp does not always simplify `0 x` to `0`
when `0` is the zero function, while it does for the zero continuous linear map,
and this is the most important property we care about. -/
@[norm_cast]
theorem coe_zero' : ⇑(0 : M₁ →SL[σ₁₂] M₂) = 0 :=
  rfl
#align continuous_linear_map.coe_zero' ContinuousLinearMap.coe_zero'

instance uniqueOfLeft [Subsingleton M₁] : Unique (M₁ →SL[σ₁₂] M₂) :=
  coe_injective.unique
#align continuous_linear_map.unique_of_left ContinuousLinearMap.uniqueOfLeft

instance uniqueOfRight [Subsingleton M₂] : Unique (M₁ →SL[σ₁₂] M₂) :=
  coe_injective.unique
#align continuous_linear_map.unique_of_right ContinuousLinearMap.uniqueOfRight

theorem exists_ne_zero {f : M₁ →SL[σ₁₂] M₂} (hf : f ≠ 0) : ∃ x, f x ≠ 0 :=
  by
  by_contra' h
  exact hf (ContinuousLinearMap.ext h)
#align continuous_linear_map.exists_ne_zero ContinuousLinearMap.exists_ne_zero

section

variable (R₁ M₁)

/-- the identity map as a continuous linear map. -/
def id : M₁ →L[R₁] M₁ :=
  ⟨LinearMap.id, continuous_id⟩
#align continuous_linear_map.id ContinuousLinearMap.id

end

instance : One (M₁ →L[R₁] M₁) :=
  ⟨id R₁ M₁⟩

theorem one_def : (1 : M₁ →L[R₁] M₁) = id R₁ M₁ :=
  rfl
#align continuous_linear_map.one_def ContinuousLinearMap.one_def

theorem id_apply (x : M₁) : id R₁ M₁ x = x :=
  rfl
#align continuous_linear_map.id_apply ContinuousLinearMap.id_apply

@[simp, norm_cast]
theorem coe_id : (id R₁ M₁ : M₁ →ₗ[R₁] M₁) = LinearMap.id :=
  rfl
#align continuous_linear_map.coe_id ContinuousLinearMap.coe_id

@[simp, norm_cast]
theorem coe_id' : ⇑(id R₁ M₁) = id :=
  rfl
#align continuous_linear_map.coe_id' ContinuousLinearMap.coe_id'

@[simp, norm_cast]
theorem coe_eq_id {f : M₁ →L[R₁] M₁} : (f : M₁ →ₗ[R₁] M₁) = LinearMap.id ↔ f = id _ _ := by
  rw [← coe_id, coe_inj]
#align continuous_linear_map.coe_eq_id ContinuousLinearMap.coe_eq_id

@[simp]
theorem one_apply (x : M₁) : (1 : M₁ →L[R₁] M₁) x = x :=
  rfl
#align continuous_linear_map.one_apply ContinuousLinearMap.one_apply

section Add

variable [ContinuousAdd M₂]

instance : Add (M₁ →SL[σ₁₂] M₂) :=
  ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩

@[simp]
theorem add_apply (f g : M₁ →SL[σ₁₂] M₂) (x : M₁) : (f + g) x = f x + g x :=
  rfl
#align continuous_linear_map.add_apply ContinuousLinearMap.add_apply

@[simp, norm_cast]
theorem coe_add (f g : M₁ →SL[σ₁₂] M₂) : (↑(f + g) : M₁ →ₛₗ[σ₁₂] M₂) = f + g :=
  rfl
#align continuous_linear_map.coe_add ContinuousLinearMap.coe_add

@[norm_cast]
theorem coe_add' (f g : M₁ →SL[σ₁₂] M₂) : ⇑(f + g) = f + g :=
  rfl
#align continuous_linear_map.coe_add' ContinuousLinearMap.coe_add'

instance : AddCommMonoid (M₁ →SL[σ₁₂] M₂)
    where
  zero := (0 : M₁ →SL[σ₁₂] M₂)
  add := (· + ·)
  zero_add := by
    intros <;> ext <;> apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm]
  add_zero := by
    intros <;> ext <;> apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm]
  add_comm := by
    intros <;> ext <;> apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm]
  add_assoc := by
    intros <;> ext <;> apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm]
  nsmul := (· • ·)
  nsmul_zero f := by
    ext
    simp
  nsmul_succ n f := by
    ext
    simp [Nat.succ_eq_one_add, add_smul]

@[simp, norm_cast]
theorem coe_sum {ι : Type _} (t : Finset ι) (f : ι → M₁ →SL[σ₁₂] M₂) :
    ↑(∑ d in t, f d) = (∑ d in t, f d : M₁ →ₛₗ[σ₁₂] M₂) :=
  (AddMonoidHom.mk (coe : (M₁ →SL[σ₁₂] M₂) → M₁ →ₛₗ[σ₁₂] M₂) rfl fun _ _ => rfl).map_sum _ _
#align continuous_linear_map.coe_sum ContinuousLinearMap.coe_sum

@[simp, norm_cast]
theorem coe_sum' {ι : Type _} (t : Finset ι) (f : ι → M₁ →SL[σ₁₂] M₂) :
    ⇑(∑ d in t, f d) = ∑ d in t, f d := by simp only [← coe_coe, coe_sum, LinearMap.coeFn_sum]
#align continuous_linear_map.coe_sum' ContinuousLinearMap.coe_sum'

theorem sum_apply {ι : Type _} (t : Finset ι) (f : ι → M₁ →SL[σ₁₂] M₂) (b : M₁) :
    (∑ d in t, f d) b = ∑ d in t, f d b := by simp only [coe_sum', Finset.sum_apply]
#align continuous_linear_map.sum_apply ContinuousLinearMap.sum_apply

end Add

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/-- Composition of bounded linear maps. -/
def comp (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) : M₁ →SL[σ₁₃] M₃ :=
  ⟨(g : M₂ →ₛₗ[σ₂₃] M₃).comp ↑f, g.2.comp f.2⟩
#align continuous_linear_map.comp ContinuousLinearMap.comp

-- mathport name: «expr ∘L »
infixr:80 " ∘L " =>
  @ContinuousLinearMap.comp _ _ _ _ _ _ (RingHom.id _) (RingHom.id _) (RingHom.id _) _ _ _ _ _ _ _ _
    _ _ _ _ RingHomCompTriple.ids

@[simp, norm_cast]
theorem coe_comp (h : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) :
    (h.comp f : M₁ →ₛₗ[σ₁₃] M₃) = (h : M₂ →ₛₗ[σ₂₃] M₃).comp (f : M₁ →ₛₗ[σ₁₂] M₂) :=
  rfl
#align continuous_linear_map.coe_comp ContinuousLinearMap.coe_comp

include σ₁₃

@[simp, norm_cast]
theorem coe_comp' (h : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) : ⇑(h.comp f) = h ∘ f :=
  rfl
#align continuous_linear_map.coe_comp' ContinuousLinearMap.coe_comp'

theorem comp_apply (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) (x : M₁) : (g.comp f) x = g (f x) :=
  rfl
#align continuous_linear_map.comp_apply ContinuousLinearMap.comp_apply

omit σ₁₃

@[simp]
theorem comp_id (f : M₁ →SL[σ₁₂] M₂) : f.comp (id R₁ M₁) = f :=
  ext fun x => rfl
#align continuous_linear_map.comp_id ContinuousLinearMap.comp_id

@[simp]
theorem id_comp (f : M₁ →SL[σ₁₂] M₂) : (id R₂ M₂).comp f = f :=
  ext fun x => rfl
#align continuous_linear_map.id_comp ContinuousLinearMap.id_comp

include σ₁₃

@[simp]
theorem comp_zero (g : M₂ →SL[σ₂₃] M₃) : g.comp (0 : M₁ →SL[σ₁₂] M₂) = 0 :=
  by
  ext
  simp
#align continuous_linear_map.comp_zero ContinuousLinearMap.comp_zero

@[simp]
theorem zero_comp (f : M₁ →SL[σ₁₂] M₂) : (0 : M₂ →SL[σ₂₃] M₃).comp f = 0 :=
  by
  ext
  simp
#align continuous_linear_map.zero_comp ContinuousLinearMap.zero_comp

@[simp]
theorem comp_add [ContinuousAdd M₂] [ContinuousAdd M₃] (g : M₂ →SL[σ₂₃] M₃)
    (f₁ f₂ : M₁ →SL[σ₁₂] M₂) : g.comp (f₁ + f₂) = g.comp f₁ + g.comp f₂ :=
  by
  ext
  simp
#align continuous_linear_map.comp_add ContinuousLinearMap.comp_add

@[simp]
theorem add_comp [ContinuousAdd M₃] (g₁ g₂ : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) :
    (g₁ + g₂).comp f = g₁.comp f + g₂.comp f := by
  ext
  simp
#align continuous_linear_map.add_comp ContinuousLinearMap.add_comp

omit σ₁₃

theorem comp_assoc {R₄ : Type _} [Semiring R₄] [Module R₄ M₄] {σ₁₄ : R₁ →+* R₄} {σ₂₄ : R₂ →+* R₄}
    {σ₃₄ : R₃ →+* R₄} [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄]
    [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] (h : M₃ →SL[σ₃₄] M₄) (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl
#align continuous_linear_map.comp_assoc ContinuousLinearMap.comp_assoc

instance : Mul (M₁ →L[R₁] M₁) :=
  ⟨comp⟩

theorem mul_def (f g : M₁ →L[R₁] M₁) : f * g = f.comp g :=
  rfl
#align continuous_linear_map.mul_def ContinuousLinearMap.mul_def

@[simp]
theorem coe_mul (f g : M₁ →L[R₁] M₁) : ⇑(f * g) = f ∘ g :=
  rfl
#align continuous_linear_map.coe_mul ContinuousLinearMap.coe_mul

theorem mul_apply (f g : M₁ →L[R₁] M₁) (x : M₁) : (f * g) x = f (g x) :=
  rfl
#align continuous_linear_map.mul_apply ContinuousLinearMap.mul_apply

instance : MonoidWithZero (M₁ →L[R₁] M₁)
    where
  mul := (· * ·)
  one := 1
  zero := 0
  mul_zero f := ext fun _ => map_zero f
  zero_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  one_mul _ := ext fun _ => rfl
  mul_assoc _ _ _ := ext fun _ => rfl

instance [ContinuousAdd M₁] : Semiring (M₁ →L[R₁] M₁) :=
  { ContinuousLinearMap.monoidWithZero,
    ContinuousLinearMap.addCommMonoid with
    mul := (· * ·)
    one := 1
    left_distrib := fun f g h => ext fun x => map_add f (g x) (h x)
    right_distrib := fun _ _ _ => ext fun _ => LinearMap.add_apply _ _ _ }

/-- `continuous_linear_map.to_linear_map` as a `ring_hom`.-/
@[simps]
def toLinearMapRingHom [ContinuousAdd M₁] : (M₁ →L[R₁] M₁) →+* M₁ →ₗ[R₁] M₁
    where
  toFun := toLinearMap
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
#align continuous_linear_map.to_linear_map_ring_hom ContinuousLinearMap.toLinearMapRingHom

section ApplyAction

variable [ContinuousAdd M₁]

/-- The tautological action by `M₁ →L[R₁] M₁` on `M`.

This generalizes `function.End.apply_mul_action`. -/
instance applyModule : Module (M₁ →L[R₁] M₁) M₁ :=
  Module.compHom _ toLinearMapRingHom
#align continuous_linear_map.apply_module ContinuousLinearMap.applyModule

@[simp]
protected theorem smul_def (f : M₁ →L[R₁] M₁) (a : M₁) : f • a = f a :=
  rfl
#align continuous_linear_map.smul_def ContinuousLinearMap.smul_def

/-- `continuous_linear_map.apply_module` is faithful. -/
instance apply_faithfulSMul : FaithfulSMul (M₁ →L[R₁] M₁) M₁ :=
  ⟨fun _ _ => ContinuousLinearMap.ext⟩
#align continuous_linear_map.apply_has_faithful_smul ContinuousLinearMap.apply_faithfulSMul

instance apply_sMulCommClass : SMulCommClass R₁ (M₁ →L[R₁] M₁) M₁
    where smul_comm r e m := (e.map_smul r m).symm
#align continuous_linear_map.apply_smul_comm_class ContinuousLinearMap.apply_sMulCommClass

instance apply_smul_comm_class' : SMulCommClass (M₁ →L[R₁] M₁) R₁ M₁
    where smul_comm := ContinuousLinearMap.map_smul
#align continuous_linear_map.apply_smul_comm_class' ContinuousLinearMap.apply_smul_comm_class'

instance : ContinuousConstSMul (M₁ →L[R₁] M₁) M₁ :=
  ⟨ContinuousLinearMap.continuous⟩

end ApplyAction

/-- The cartesian product of two bounded linear maps, as a bounded linear map. -/
protected def prod [Module R₁ M₂] [Module R₁ M₃] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₁ →L[R₁] M₃) :
    M₁ →L[R₁] M₂ × M₃ :=
  ⟨(f₁ : M₁ →ₗ[R₁] M₂).Prod f₂, f₁.2.prod_mk f₂.2⟩
#align continuous_linear_map.prod ContinuousLinearMap.prod

@[simp, norm_cast]
theorem coe_prod [Module R₁ M₂] [Module R₁ M₃] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₁ →L[R₁] M₃) :
    (f₁.Prod f₂ : M₁ →ₗ[R₁] M₂ × M₃) = LinearMap.prod f₁ f₂ :=
  rfl
#align continuous_linear_map.coe_prod ContinuousLinearMap.coe_prod

@[simp, norm_cast]
theorem prod_apply [Module R₁ M₂] [Module R₁ M₃] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₁ →L[R₁] M₃) (x : M₁) :
    f₁.Prod f₂ x = (f₁ x, f₂ x) :=
  rfl
#align continuous_linear_map.prod_apply ContinuousLinearMap.prod_apply

section

variable (R₁ M₁ M₂)

/-- The left injection into a product is a continuous linear map. -/
def inl [Module R₁ M₂] : M₁ →L[R₁] M₁ × M₂ :=
  (id R₁ M₁).Prod 0
#align continuous_linear_map.inl ContinuousLinearMap.inl

/-- The right injection into a product is a continuous linear map. -/
def inr [Module R₁ M₂] : M₂ →L[R₁] M₁ × M₂ :=
  (0 : M₂ →L[R₁] M₁).Prod (id R₁ M₂)
#align continuous_linear_map.inr ContinuousLinearMap.inr

end

variable {F : Type _}

@[simp]
theorem inl_apply [Module R₁ M₂] (x : M₁) : inl R₁ M₁ M₂ x = (x, 0) :=
  rfl
#align continuous_linear_map.inl_apply ContinuousLinearMap.inl_apply

@[simp]
theorem inr_apply [Module R₁ M₂] (x : M₂) : inr R₁ M₁ M₂ x = (0, x) :=
  rfl
#align continuous_linear_map.inr_apply ContinuousLinearMap.inr_apply

@[simp, norm_cast]
theorem coe_inl [Module R₁ M₂] : (inl R₁ M₁ M₂ : M₁ →ₗ[R₁] M₁ × M₂) = LinearMap.inl R₁ M₁ M₂ :=
  rfl
#align continuous_linear_map.coe_inl ContinuousLinearMap.coe_inl

@[simp, norm_cast]
theorem coe_inr [Module R₁ M₂] : (inr R₁ M₁ M₂ : M₂ →ₗ[R₁] M₁ × M₂) = LinearMap.inr R₁ M₁ M₂ :=
  rfl
#align continuous_linear_map.coe_inr ContinuousLinearMap.coe_inr

theorem isClosed_ker [T1Space M₂] [ContinuousSemilinearMapClass F σ₁₂ M₁ M₂] (f : F) :
    IsClosed (ker f : Set M₁) :=
  continuous_iff_isClosed.1 (map_continuous f) _ isClosed_singleton
#align continuous_linear_map.is_closed_ker ContinuousLinearMap.isClosed_ker

theorem isComplete_ker {M' : Type _} [UniformSpace M'] [CompleteSpace M'] [AddCommMonoid M']
    [Module R₁ M'] [T1Space M₂] [ContinuousSemilinearMapClass F σ₁₂ M' M₂] (f : F) :
    IsComplete (ker f : Set M') :=
  (isClosed_ker f).IsComplete
#align continuous_linear_map.is_complete_ker ContinuousLinearMap.isComplete_ker

instance (priority := 100) completeSpace_ker {M' : Type _} [UniformSpace M'] [CompleteSpace M']
    [AddCommMonoid M'] [Module R₁ M'] [T1Space M₂] [ContinuousSemilinearMapClass F σ₁₂ M' M₂]
    (f : F) : CompleteSpace (ker f) :=
  (isClosed_ker f).completeSpace_coe
#align continuous_linear_map.complete_space_ker ContinuousLinearMap.completeSpace_ker

@[simp]
theorem ker_prod [Module R₁ M₂] [Module R₁ M₃] (f : M₁ →L[R₁] M₂) (g : M₁ →L[R₁] M₃) :
    ker (f.Prod g) = ker f ⊓ ker g :=
  LinearMap.ker_prod f g
#align continuous_linear_map.ker_prod ContinuousLinearMap.ker_prod

/-- Restrict codomain of a continuous linear map. -/
def codRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) : M₁ →SL[σ₁₂] p
    where
  cont := f.Continuous.subtype_mk _
  toLinearMap := (f : M₁ →ₛₗ[σ₁₂] M₂).codRestrict p h
#align continuous_linear_map.cod_restrict ContinuousLinearMap.codRestrict

@[norm_cast]
theorem coe_codRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    (f.codRestrict p h : M₁ →ₛₗ[σ₁₂] p) = (f : M₁ →ₛₗ[σ₁₂] M₂).codRestrict p h :=
  rfl
#align continuous_linear_map.coe_cod_restrict ContinuousLinearMap.coe_codRestrict

@[simp]
theorem coe_codRestrict_apply (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) (x) :
    (f.codRestrict p h x : M₂) = f x :=
  rfl
#align continuous_linear_map.coe_cod_restrict_apply ContinuousLinearMap.coe_codRestrict_apply

@[simp]
theorem ker_codRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    ker (f.codRestrict p h) = ker f :=
  (f : M₁ →ₛₗ[σ₁₂] M₂).ker_codRestrict p h
#align continuous_linear_map.ker_cod_restrict ContinuousLinearMap.ker_codRestrict

/-- `submodule.subtype` as a `continuous_linear_map`. -/
def Submodule.subtypeL (p : Submodule R₁ M₁) : p →L[R₁] M₁
    where
  cont := continuous_subtype_val
  toLinearMap := p.Subtype
#align submodule.subtypeL Submodule.subtypeL

@[simp, norm_cast]
theorem Submodule.coe_subtypeL (p : Submodule R₁ M₁) : (p.subtypeL : p →ₗ[R₁] M₁) = p.Subtype :=
  rfl
#align submodule.coe_subtypeL Submodule.coe_subtypeL

@[simp]
theorem Submodule.coe_subtypeL' (p : Submodule R₁ M₁) : ⇑p.subtypeL = p.Subtype :=
  rfl
#align submodule.coe_subtypeL' Submodule.coe_subtypeL'

@[simp, norm_cast]
theorem Submodule.subtypeL_apply (p : Submodule R₁ M₁) (x : p) : p.subtypeL x = x :=
  rfl
#align submodule.subtypeL_apply Submodule.subtypeL_apply

@[simp]
theorem Submodule.range_subtypeL (p : Submodule R₁ M₁) : range p.subtypeL = p :=
  Submodule.range_subtype _
#align submodule.range_subtypeL Submodule.range_subtypeL

@[simp]
theorem Submodule.ker_subtypeL (p : Submodule R₁ M₁) : ker p.subtypeL = ⊥ :=
  Submodule.ker_subtype _
#align submodule.ker_subtypeL Submodule.ker_subtypeL

variable (R₁ M₁ M₂)

/-- `prod.fst` as a `continuous_linear_map`. -/
def fst [Module R₁ M₂] : M₁ × M₂ →L[R₁] M₁
    where
  cont := continuous_fst
  toLinearMap := LinearMap.fst R₁ M₁ M₂
#align continuous_linear_map.fst ContinuousLinearMap.fst

/-- `prod.snd` as a `continuous_linear_map`. -/
def snd [Module R₁ M₂] : M₁ × M₂ →L[R₁] M₂
    where
  cont := continuous_snd
  toLinearMap := LinearMap.snd R₁ M₁ M₂
#align continuous_linear_map.snd ContinuousLinearMap.snd

variable {R₁ M₁ M₂}

@[simp, norm_cast]
theorem coe_fst [Module R₁ M₂] : ↑(fst R₁ M₁ M₂) = LinearMap.fst R₁ M₁ M₂ :=
  rfl
#align continuous_linear_map.coe_fst ContinuousLinearMap.coe_fst

@[simp, norm_cast]
theorem coe_fst' [Module R₁ M₂] : ⇑(fst R₁ M₁ M₂) = Prod.fst :=
  rfl
#align continuous_linear_map.coe_fst' ContinuousLinearMap.coe_fst'

@[simp, norm_cast]
theorem coe_snd [Module R₁ M₂] : ↑(snd R₁ M₁ M₂) = LinearMap.snd R₁ M₁ M₂ :=
  rfl
#align continuous_linear_map.coe_snd ContinuousLinearMap.coe_snd

@[simp, norm_cast]
theorem coe_snd' [Module R₁ M₂] : ⇑(snd R₁ M₁ M₂) = Prod.snd :=
  rfl
#align continuous_linear_map.coe_snd' ContinuousLinearMap.coe_snd'

@[simp]
theorem fst_prod_snd [Module R₁ M₂] : (fst R₁ M₁ M₂).Prod (snd R₁ M₁ M₂) = id R₁ (M₁ × M₂) :=
  ext fun ⟨x, y⟩ => rfl
#align continuous_linear_map.fst_prod_snd ContinuousLinearMap.fst_prod_snd

@[simp]
theorem fst_comp_prod [Module R₁ M₂] [Module R₁ M₃] (f : M₁ →L[R₁] M₂) (g : M₁ →L[R₁] M₃) :
    (fst R₁ M₂ M₃).comp (f.Prod g) = f :=
  ext fun x => rfl
#align continuous_linear_map.fst_comp_prod ContinuousLinearMap.fst_comp_prod

@[simp]
theorem snd_comp_prod [Module R₁ M₂] [Module R₁ M₃] (f : M₁ →L[R₁] M₂) (g : M₁ →L[R₁] M₃) :
    (snd R₁ M₂ M₃).comp (f.Prod g) = g :=
  ext fun x => rfl
#align continuous_linear_map.snd_comp_prod ContinuousLinearMap.snd_comp_prod

/-- `prod.map` of two continuous linear maps. -/
def prodMap [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₃ →L[R₁] M₄) :
    M₁ × M₃ →L[R₁] M₂ × M₄ :=
  (f₁.comp (fst R₁ M₁ M₃)).Prod (f₂.comp (snd R₁ M₁ M₃))
#align continuous_linear_map.prod_map ContinuousLinearMap.prodMap

@[simp, norm_cast]
theorem coe_prodMap [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (f₁ : M₁ →L[R₁] M₂)
    (f₂ : M₃ →L[R₁] M₄) : ↑(f₁.Prod_map f₂) = (f₁ : M₁ →ₗ[R₁] M₂).Prod_map (f₂ : M₃ →ₗ[R₁] M₄) :=
  rfl
#align continuous_linear_map.coe_prod_map ContinuousLinearMap.coe_prodMap

@[simp, norm_cast]
theorem coe_prod_map' [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (f₁ : M₁ →L[R₁] M₂)
    (f₂ : M₃ →L[R₁] M₄) : ⇑(f₁.Prod_map f₂) = Prod.map f₁ f₂ :=
  rfl
#align continuous_linear_map.coe_prod_map' ContinuousLinearMap.coe_prod_map'

/-- The continuous linear map given by `(x, y) ↦ f₁ x + f₂ y`. -/
def coprod [Module R₁ M₂] [Module R₁ M₃] [ContinuousAdd M₃] (f₁ : M₁ →L[R₁] M₃)
    (f₂ : M₂ →L[R₁] M₃) : M₁ × M₂ →L[R₁] M₃ :=
  ⟨LinearMap.coprod f₁ f₂, (f₁.cont.comp continuous_fst).add (f₂.cont.comp continuous_snd)⟩
#align continuous_linear_map.coprod ContinuousLinearMap.coprod

@[norm_cast, simp]
theorem coe_coprod [Module R₁ M₂] [Module R₁ M₃] [ContinuousAdd M₃] (f₁ : M₁ →L[R₁] M₃)
    (f₂ : M₂ →L[R₁] M₃) : (f₁.coprod f₂ : M₁ × M₂ →ₗ[R₁] M₃) = LinearMap.coprod f₁ f₂ :=
  rfl
#align continuous_linear_map.coe_coprod ContinuousLinearMap.coe_coprod

@[simp]
theorem coprod_apply [Module R₁ M₂] [Module R₁ M₃] [ContinuousAdd M₃] (f₁ : M₁ →L[R₁] M₃)
    (f₂ : M₂ →L[R₁] M₃) (x) : f₁.coprod f₂ x = f₁ x.1 + f₂ x.2 :=
  rfl
#align continuous_linear_map.coprod_apply ContinuousLinearMap.coprod_apply

theorem range_coprod [Module R₁ M₂] [Module R₁ M₃] [ContinuousAdd M₃] (f₁ : M₁ →L[R₁] M₃)
    (f₂ : M₂ →L[R₁] M₃) : range (f₁.coprod f₂) = range f₁ ⊔ range f₂ :=
  LinearMap.range_coprod _ _
#align continuous_linear_map.range_coprod ContinuousLinearMap.range_coprod

section

variable {R S : Type _} [Semiring R] [Semiring S] [Module R M₁] [Module R M₂] [Module R S]
  [Module S M₂] [IsScalarTower R S M₂] [TopologicalSpace S] [ContinuousSMul S M₂]

/-- The linear map `λ x, c x • f`.  Associates to a scalar-valued linear map and an element of
`M₂` the `M₂`-valued linear map obtained by multiplying the two (a.k.a. tensoring by `M₂`).
See also `continuous_linear_map.smul_rightₗ` and `continuous_linear_map.smul_rightL`. -/
def smulRight (c : M₁ →L[R] S) (f : M₂) : M₁ →L[R] M₂ :=
  { c.toLinearMap.smul_right f with cont := c.2.smul continuous_const }
#align continuous_linear_map.smul_right ContinuousLinearMap.smulRight

@[simp]
theorem smulRight_apply {c : M₁ →L[R] S} {f : M₂} {x : M₁} :
    (smulRight c f : M₁ → M₂) x = c x • f :=
  rfl
#align continuous_linear_map.smul_right_apply ContinuousLinearMap.smulRight_apply

end

variable [Module R₁ M₂] [TopologicalSpace R₁] [ContinuousSMul R₁ M₂]

@[simp]
theorem smulRight_one_one (c : R₁ →L[R₁] M₂) : smulRight (1 : R₁ →L[R₁] R₁) (c 1) = c := by
  ext <;> simp [← ContinuousLinearMap.map_smul_of_tower]
#align continuous_linear_map.smul_right_one_one ContinuousLinearMap.smulRight_one_one

@[simp]
theorem smulRight_one_eq_iff {f f' : M₂} :
    smulRight (1 : R₁ →L[R₁] R₁) f = smulRight (1 : R₁ →L[R₁] R₁) f' ↔ f = f' := by
  simp only [ext_ring_iff, smul_right_apply, one_apply, one_smul]
#align continuous_linear_map.smul_right_one_eq_iff ContinuousLinearMap.smulRight_one_eq_iff

theorem smulRight_comp [ContinuousMul R₁] {x : M₂} {c : R₁} :
    (smulRight (1 : R₁ →L[R₁] R₁) x).comp (smulRight (1 : R₁ →L[R₁] R₁) c) =
      smulRight (1 : R₁ →L[R₁] R₁) (c • x) :=
  by
  ext
  simp [mul_smul]
#align continuous_linear_map.smul_right_comp ContinuousLinearMap.smulRight_comp

end Semiring

section Pi

variable {R : Type _} [Semiring R] {M : Type _} [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  {M₂ : Type _} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂] {ι : Type _} {φ : ι → Type _}
  [∀ i, TopologicalSpace (φ i)] [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]

/-- `pi` construction for continuous linear functions. From a family of continuous linear functions
it produces a continuous linear function into a family of topological modules. -/
def pi (f : ∀ i, M →L[R] φ i) : M →L[R] ∀ i, φ i :=
  ⟨LinearMap.pi fun i => f i, continuous_pi fun i => (f i).Continuous⟩
#align continuous_linear_map.pi ContinuousLinearMap.pi

@[simp]
theorem coe_pi' (f : ∀ i, M →L[R] φ i) : ⇑(pi f) = fun c i => f i c :=
  rfl
#align continuous_linear_map.coe_pi' ContinuousLinearMap.coe_pi'

@[simp]
theorem coe_pi (f : ∀ i, M →L[R] φ i) : (pi f : M →ₗ[R] ∀ i, φ i) = LinearMap.pi fun i => f i :=
  rfl
#align continuous_linear_map.coe_pi ContinuousLinearMap.coe_pi

theorem pi_apply (f : ∀ i, M →L[R] φ i) (c : M) (i : ι) : pi f c i = f i c :=
  rfl
#align continuous_linear_map.pi_apply ContinuousLinearMap.pi_apply

theorem pi_eq_zero (f : ∀ i, M →L[R] φ i) : pi f = 0 ↔ ∀ i, f i = 0 :=
  by
  simp only [ext_iff, pi_apply, Function.funext_iff]
  exact forall_swap
#align continuous_linear_map.pi_eq_zero ContinuousLinearMap.pi_eq_zero

theorem pi_zero : pi (fun i => 0 : ∀ i, M →L[R] φ i) = 0 :=
  ext fun _ => rfl
#align continuous_linear_map.pi_zero ContinuousLinearMap.pi_zero

theorem pi_comp (f : ∀ i, M →L[R] φ i) (g : M₂ →L[R] M) :
    (pi f).comp g = pi fun i => (f i).comp g :=
  rfl
#align continuous_linear_map.pi_comp ContinuousLinearMap.pi_comp

/-- The projections from a family of topological modules are continuous linear maps. -/
def proj (i : ι) : (∀ i, φ i) →L[R] φ i :=
  ⟨LinearMap.proj i, continuous_apply _⟩
#align continuous_linear_map.proj ContinuousLinearMap.proj

@[simp]
theorem proj_apply (i : ι) (b : ∀ i, φ i) : (proj i : (∀ i, φ i) →L[R] φ i) b = b i :=
  rfl
#align continuous_linear_map.proj_apply ContinuousLinearMap.proj_apply

theorem proj_pi (f : ∀ i, M₂ →L[R] φ i) (i : ι) : (proj i).comp (pi f) = f i :=
  ext fun c => rfl
#align continuous_linear_map.proj_pi ContinuousLinearMap.proj_pi

theorem infᵢ_ker_proj : (⨅ i, ker (proj i : (∀ i, φ i) →L[R] φ i) : Submodule R (∀ i, φ i)) = ⊥ :=
  LinearMap.infᵢ_ker_proj
#align continuous_linear_map.infi_ker_proj ContinuousLinearMap.infᵢ_ker_proj

variable (R φ)

/-- If `I` and `J` are complementary index sets, the product of the kernels of the `J`th projections
of `φ` is linearly equivalent to the product over `I`. -/
def infiKerProjEquiv {I J : Set ι} [DecidablePred fun i => i ∈ I] (hd : Disjoint I J)
    (hu : Set.univ ⊆ I ∪ J) :
    (⨅ i ∈ J, ker (proj i : (∀ i, φ i) →L[R] φ i) : Submodule R (∀ i, φ i)) ≃L[R] ∀ i : I, φ i
    where
  toLinearEquiv := LinearMap.infᵢKerProjEquiv R φ hd hu
  continuous_toFun :=
    continuous_pi fun i =>
      by
      have :=
        @continuous_subtype_val _ _ fun x =>
          x ∈ (⨅ i ∈ J, ker (proj i : (∀ i, φ i) →L[R] φ i) : Submodule R (∀ i, φ i))
      have := Continuous.comp (continuous_apply i) this
      exact this
  continuous_invFun :=
    Continuous.subtype_mk
      (continuous_pi fun i => by dsimp;
        split_ifs <;> [apply continuous_apply, exact continuous_zero])
      _
#align continuous_linear_map.infi_ker_proj_equiv ContinuousLinearMap.infiKerProjEquiv

end Pi

section Ring

variable {R : Type _} [Ring R] {R₂ : Type _} [Ring R₂] {R₃ : Type _} [Ring R₃] {M : Type _}
  [TopologicalSpace M] [AddCommGroup M] {M₂ : Type _} [TopologicalSpace M₂] [AddCommGroup M₂]
  {M₃ : Type _} [TopologicalSpace M₃] [AddCommGroup M₃] {M₄ : Type _} [TopologicalSpace M₄]
  [AddCommGroup M₄] [Module R M] [Module R₂ M₂] [Module R₃ M₃] {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃}
  {σ₁₃ : R →+* R₃}

section

protected theorem map_neg (f : M →SL[σ₁₂] M₂) (x : M) : f (-x) = -f x :=
  map_neg _ _
#align continuous_linear_map.map_neg ContinuousLinearMap.map_neg

protected theorem map_sub (f : M →SL[σ₁₂] M₂) (x y : M) : f (x - y) = f x - f y :=
  map_sub _ _ _
#align continuous_linear_map.map_sub ContinuousLinearMap.map_sub

@[simp]
theorem sub_apply' (f g : M →SL[σ₁₂] M₂) (x : M) : ((f : M →ₛₗ[σ₁₂] M₂) - g) x = f x - g x :=
  rfl
#align continuous_linear_map.sub_apply' ContinuousLinearMap.sub_apply'

end

section

variable [Module R M₂] [Module R M₃] [Module R M₄]

theorem range_prod_eq {f : M →L[R] M₂} {g : M →L[R] M₃} (h : ker f ⊔ ker g = ⊤) :
    range (f.Prod g) = (range f).Prod (range g) :=
  LinearMap.range_prod_eq h
#align continuous_linear_map.range_prod_eq ContinuousLinearMap.range_prod_eq

theorem ker_prod_ker_le_ker_coprod [ContinuousAdd M₃] (f : M →L[R] M₃) (g : M₂ →L[R] M₃) :
    (LinearMap.ker f).Prod (LinearMap.ker g) ≤ LinearMap.ker (f.coprod g) :=
  LinearMap.ker_prod_ker_le_ker_coprod f.toLinearMap g.toLinearMap
#align continuous_linear_map.ker_prod_ker_le_ker_coprod ContinuousLinearMap.ker_prod_ker_le_ker_coprod

theorem ker_coprod_of_disjoint_range [ContinuousAdd M₃] (f : M →L[R] M₃) (g : M₂ →L[R] M₃)
    (hd : Disjoint (range f) (range g)) :
    LinearMap.ker (f.coprod g) = (LinearMap.ker f).Prod (LinearMap.ker g) :=
  LinearMap.ker_coprod_of_disjoint_range f.toLinearMap g.toLinearMap hd
#align continuous_linear_map.ker_coprod_of_disjoint_range ContinuousLinearMap.ker_coprod_of_disjoint_range

end

section

variable [TopologicalAddGroup M₂]

instance : Neg (M →SL[σ₁₂] M₂) :=
  ⟨fun f => ⟨-f, f.2.neg⟩⟩

@[simp]
theorem neg_apply (f : M →SL[σ₁₂] M₂) (x : M) : (-f) x = -f x :=
  rfl
#align continuous_linear_map.neg_apply ContinuousLinearMap.neg_apply

@[simp, norm_cast]
theorem coe_neg (f : M →SL[σ₁₂] M₂) : (↑(-f) : M →ₛₗ[σ₁₂] M₂) = -f :=
  rfl
#align continuous_linear_map.coe_neg ContinuousLinearMap.coe_neg

@[norm_cast]
theorem coe_neg' (f : M →SL[σ₁₂] M₂) : ⇑(-f) = -f :=
  rfl
#align continuous_linear_map.coe_neg' ContinuousLinearMap.coe_neg'

instance : Sub (M →SL[σ₁₂] M₂) :=
  ⟨fun f g => ⟨f - g, f.2.sub g.2⟩⟩

instance : AddCommGroup (M →SL[σ₁₂] M₂) := by
  refine'
          { ContinuousLinearMap.addCommMonoid with
            zero := 0
            add := (· + ·)
            neg := Neg.neg
            sub := Sub.sub
            sub_eq_add_neg := _
            nsmul := (· • ·)
            zsmul := (· • ·)
            zsmul_zero' := fun f => by
              ext
              simp
            zsmul_succ' := fun n f => by
              ext
              simp [add_smul, add_comm]
            zsmul_neg' := fun n f => by
              ext
              simp [Nat.succ_eq_add_one, add_smul].. } <;>
        intros <;>
      ext <;>
    apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm, sub_eq_add_neg]

theorem sub_apply (f g : M →SL[σ₁₂] M₂) (x : M) : (f - g) x = f x - g x :=
  rfl
#align continuous_linear_map.sub_apply ContinuousLinearMap.sub_apply

@[simp, norm_cast]
theorem coe_sub (f g : M →SL[σ₁₂] M₂) : (↑(f - g) : M →ₛₗ[σ₁₂] M₂) = f - g :=
  rfl
#align continuous_linear_map.coe_sub ContinuousLinearMap.coe_sub

@[simp, norm_cast]
theorem coe_sub' (f g : M →SL[σ₁₂] M₂) : ⇑(f - g) = f - g :=
  rfl
#align continuous_linear_map.coe_sub' ContinuousLinearMap.coe_sub'

end

@[simp]
theorem comp_neg [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [TopologicalAddGroup M₂] [TopologicalAddGroup M₃]
    (g : M₂ →SL[σ₂₃] M₃) (f : M →SL[σ₁₂] M₂) : g.comp (-f) = -g.comp f :=
  by
  ext
  simp
#align continuous_linear_map.comp_neg ContinuousLinearMap.comp_neg

@[simp]
theorem neg_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [TopologicalAddGroup M₃] (g : M₂ →SL[σ₂₃] M₃)
    (f : M →SL[σ₁₂] M₂) : (-g).comp f = -g.comp f :=
  by
  ext
  simp
#align continuous_linear_map.neg_comp ContinuousLinearMap.neg_comp

@[simp]
theorem comp_sub [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [TopologicalAddGroup M₂] [TopologicalAddGroup M₃]
    (g : M₂ →SL[σ₂₃] M₃) (f₁ f₂ : M →SL[σ₁₂] M₂) : g.comp (f₁ - f₂) = g.comp f₁ - g.comp f₂ :=
  by
  ext
  simp
#align continuous_linear_map.comp_sub ContinuousLinearMap.comp_sub

@[simp]
theorem sub_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [TopologicalAddGroup M₃] (g₁ g₂ : M₂ →SL[σ₂₃] M₃)
    (f : M →SL[σ₁₂] M₂) : (g₁ - g₂).comp f = g₁.comp f - g₂.comp f :=
  by
  ext
  simp
#align continuous_linear_map.sub_comp ContinuousLinearMap.sub_comp

instance [TopologicalAddGroup M] : Ring (M →L[R] M) :=
  { ContinuousLinearMap.semiring,
    ContinuousLinearMap.addCommGroup with
    mul := (· * ·)
    one := 1 }

theorem smulRight_one_pow [TopologicalSpace R] [TopologicalRing R] (c : R) (n : ℕ) :
    smulRight (1 : R →L[R] R) c ^ n = smulRight (1 : R →L[R] R) (c ^ n) :=
  by
  induction' n with n ihn
  · ext
    simp
  · rw [pow_succ, ihn, mul_def, smul_right_comp, smul_eq_mul, pow_succ']
#align continuous_linear_map.smul_right_one_pow ContinuousLinearMap.smulRight_one_pow

section

variable {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁]

/-- Given a right inverse `f₂ : M₂ →L[R] M` to `f₁ : M →L[R] M₂`,
`proj_ker_of_right_inverse f₁ f₂ h` is the projection `M →L[R] f₁.ker` along `f₂.range`. -/
def projKerOfRightInverse [TopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M)
    (h : Function.RightInverse f₂ f₁) : M →L[R] LinearMap.ker f₁ :=
  (id R M - f₂.comp f₁).codRestrict (LinearMap.ker f₁) fun x => by simp [h (f₁ x)]
#align continuous_linear_map.proj_ker_of_right_inverse ContinuousLinearMap.projKerOfRightInverse

@[simp]
theorem coe_projKerOfRightInverse_apply [TopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂)
    (f₂ : M₂ →SL[σ₂₁] M) (h : Function.RightInverse f₂ f₁) (x : M) :
    (f₁.projKerOfRightInverse f₂ h x : M) = x - f₂ (f₁ x) :=
  rfl
#align continuous_linear_map.coe_proj_ker_of_right_inverse_apply ContinuousLinearMap.coe_projKerOfRightInverse_apply

@[simp]
theorem projKerOfRightInverse_apply_idem [TopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂)
    (f₂ : M₂ →SL[σ₂₁] M) (h : Function.RightInverse f₂ f₁) (x : LinearMap.ker f₁) :
    f₁.projKerOfRightInverse f₂ h x = x :=
  Subtype.ext_iff_val.2 <| by simp
#align continuous_linear_map.proj_ker_of_right_inverse_apply_idem ContinuousLinearMap.projKerOfRightInverse_apply_idem

@[simp]
theorem projKerOfRightInverse_comp_inv [TopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂)
    (f₂ : M₂ →SL[σ₂₁] M) (h : Function.RightInverse f₂ f₁) (y : M₂) :
    f₁.projKerOfRightInverse f₂ h (f₂ y) = 0 :=
  Subtype.ext_iff_val.2 <| by simp [h y]
#align continuous_linear_map.proj_ker_of_right_inverse_comp_inv ContinuousLinearMap.projKerOfRightInverse_comp_inv

end

end Ring

section DivisionMonoid

variable {R M : Type _}

/-- A nonzero continuous linear functional is open. -/
protected theorem isOpenMap_of_ne_zero [TopologicalSpace R] [DivisionRing R] [ContinuousSub R]
    [AddCommGroup M] [TopologicalSpace M] [ContinuousAdd M] [Module R M] [ContinuousSMul R M]
    (f : M →L[R] R) (hf : f ≠ 0) : IsOpenMap f :=
  let ⟨x, hx⟩ := exists_ne_zero hf
  IsOpenMap.of_sections fun y =>
    ⟨fun a => y + (a - f y) • (f x)⁻¹ • x, Continuous.continuousAt <| by continuity, by simp,
      fun a => by simp [hx]⟩
#align continuous_linear_map.is_open_map_of_ne_zero ContinuousLinearMap.isOpenMap_of_ne_zero

end DivisionMonoid

section SmulMonoid

-- The M's are used for semilinear maps, and the N's for plain linear maps
variable {R R₂ R₃ S S₃ : Type _} [Semiring R] [Semiring R₂] [Semiring R₃] [Monoid S] [Monoid S₃]
  {M : Type _} [TopologicalSpace M] [AddCommMonoid M] [Module R M] {M₂ : Type _}
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂] {M₃ : Type _} [TopologicalSpace M₃]
  [AddCommMonoid M₃] [Module R₃ M₃] {N₂ : Type _} [TopologicalSpace N₂] [AddCommMonoid N₂]
  [Module R N₂] {N₃ : Type _} [TopologicalSpace N₃] [AddCommMonoid N₃] [Module R N₃]
  [DistribMulAction S₃ M₃] [SMulCommClass R₃ S₃ M₃] [ContinuousConstSMul S₃ M₃]
  [DistribMulAction S N₃] [SMulCommClass R S N₃] [ContinuousConstSMul S N₃] {σ₁₂ : R →+* R₂}
  {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

include σ₁₃

@[simp]
theorem smul_comp (c : S₃) (h : M₂ →SL[σ₂₃] M₃) (f : M →SL[σ₁₂] M₂) :
    (c • h).comp f = c • h.comp f :=
  rfl
#align continuous_linear_map.smul_comp ContinuousLinearMap.smul_comp

omit σ₁₃

variable [DistribMulAction S₃ M₂] [ContinuousConstSMul S₃ M₂] [SMulCommClass R₂ S₃ M₂]

variable [DistribMulAction S N₂] [ContinuousConstSMul S N₂] [SMulCommClass R S N₂]

@[simp]
theorem comp_smul [LinearMap.CompatibleSMul N₂ N₃ S R] (hₗ : N₂ →L[R] N₃) (c : S)
    (fₗ : M →L[R] N₂) : hₗ.comp (c • fₗ) = c • hₗ.comp fₗ :=
  by
  ext x
  exact hₗ.map_smul_of_tower c (fₗ x)
#align continuous_linear_map.comp_smul ContinuousLinearMap.comp_smul

include σ₁₃

@[simp]
theorem comp_smulₛₗ [SMulCommClass R₂ R₂ M₂] [SMulCommClass R₃ R₃ M₃] [ContinuousConstSMul R₂ M₂]
    [ContinuousConstSMul R₃ M₃] (h : M₂ →SL[σ₂₃] M₃) (c : R₂) (f : M →SL[σ₁₂] M₂) :
    h.comp (c • f) = σ₂₃ c • h.comp f := by
  ext x
  simp only [coe_smul', coe_comp', Function.comp_apply, Pi.smul_apply,
    ContinuousLinearMap.map_smulₛₗ]
#align continuous_linear_map.comp_smulₛₗ ContinuousLinearMap.comp_smulₛₗ

omit σ₁₃

instance [ContinuousAdd M₂] : DistribMulAction S₃ (M →SL[σ₁₂] M₂)
    where
  smul_add a f g := ext fun x => smul_add a (f x) (g x)
  smul_zero a := ext fun x => smul_zero _

end SmulMonoid

section Smul

-- The M's are used for semilinear maps, and the N's for plain linear maps
variable {R R₂ R₃ S S₃ : Type _} [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring S] [Semiring S₃]
  {M : Type _} [TopologicalSpace M] [AddCommMonoid M] [Module R M] {M₂ : Type _}
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂] {M₃ : Type _} [TopologicalSpace M₃]
  [AddCommMonoid M₃] [Module R₃ M₃] {N₂ : Type _} [TopologicalSpace N₂] [AddCommMonoid N₂]
  [Module R N₂] {N₃ : Type _} [TopologicalSpace N₃] [AddCommMonoid N₃] [Module R N₃] [Module S₃ M₃]
  [SMulCommClass R₃ S₃ M₃] [ContinuousConstSMul S₃ M₃] [Module S N₂] [ContinuousConstSMul S N₂]
  [SMulCommClass R S N₂] [Module S N₃] [SMulCommClass R S N₃] [ContinuousConstSMul S N₃]
  {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (c : S)
  (h : M₂ →SL[σ₂₃] M₃) (f g : M →SL[σ₁₂] M₂) (x y z : M)

/-- `continuous_linear_map.prod` as an `equiv`. -/
@[simps apply]
def prodEquiv : (M →L[R] N₂) × (M →L[R] N₃) ≃ (M →L[R] N₂ × N₃)
    where
  toFun f := f.1.Prod f.2
  invFun f := ⟨(fst _ _ _).comp f, (snd _ _ _).comp f⟩
  left_inv f := by ext <;> rfl
  right_inv f := by ext <;> rfl
#align continuous_linear_map.prod_equiv ContinuousLinearMap.prodEquiv

theorem prod_ext_iff {f g : M × N₂ →L[R] N₃} :
    f = g ↔ f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _) :=
  by
  simp only [← coe_inj, LinearMap.prod_ext_iff]
  rfl
#align continuous_linear_map.prod_ext_iff ContinuousLinearMap.prod_ext_iff

@[ext]
theorem prod_ext {f g : M × N₂ →L[R] N₃} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
    (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f = g :=
  prod_ext_iff.2 ⟨hl, hr⟩
#align continuous_linear_map.prod_ext ContinuousLinearMap.prod_ext

variable [ContinuousAdd M₂] [ContinuousAdd M₃] [ContinuousAdd N₂]

instance : Module S₃ (M →SL[σ₁₃] M₃)
    where
  zero_smul _ := ext fun _ => zero_smul _ _
  add_smul _ _ _ := ext fun _ => add_smul _ _ _

instance [Module S₃ᵐᵒᵖ M₃] [IsCentralScalar S₃ M₃] : IsCentralScalar S₃ (M →SL[σ₁₃] M₃)
    where op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

variable (S) [ContinuousAdd N₃]

/-- `continuous_linear_map.prod` as a `linear_equiv`. -/
@[simps apply]
def prodₗ : ((M →L[R] N₂) × (M →L[R] N₃)) ≃ₗ[S] M →L[R] N₂ × N₃ :=
  { prodEquiv with
    map_add' := fun f g => rfl
    map_smul' := fun c f => rfl }
#align continuous_linear_map.prodₗ ContinuousLinearMap.prodₗ

/-- The coercion from `M →L[R] M₂` to `M →ₗ[R] M₂`, as a linear map. -/
@[simps]
def coeLm : (M →L[R] N₃) →ₗ[S] M →ₗ[R] N₃
    where
  toFun := coe
  map_add' f g := coe_add f g
  map_smul' c f := coe_smul c f
#align continuous_linear_map.coe_lm ContinuousLinearMap.coeLm

variable {S} (σ₁₃)

/-- The coercion from `M →SL[σ] M₂` to `M →ₛₗ[σ] M₂`, as a linear map. -/
@[simps]
def coeLmₛₗ : (M →SL[σ₁₃] M₃) →ₗ[S₃] M →ₛₗ[σ₁₃] M₃
    where
  toFun := coe
  map_add' f g := coe_add f g
  map_smul' c f := coe_smul c f
#align continuous_linear_map.coe_lmₛₗ ContinuousLinearMap.coeLmₛₗ

variable {σ₁₃}

end Smul

section SmulRightₗ

variable {R S T M M₂ : Type _} [Semiring R] [Semiring S] [Semiring T] [Module R S]
  [AddCommMonoid M₂] [Module R M₂] [Module S M₂] [IsScalarTower R S M₂] [TopologicalSpace S]
  [TopologicalSpace M₂] [ContinuousSMul S M₂] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [ContinuousAdd M₂] [Module T M₂] [ContinuousConstSMul T M₂] [SMulCommClass R T M₂]
  [SMulCommClass S T M₂]

/-- Given `c : E →L[𝕜] 𝕜`, `c.smul_rightₗ` is the linear map from `F` to `E →L[𝕜] F`
sending `f` to `λ e, c e • f`. See also `continuous_linear_map.smul_rightL`. -/
def smulRightₗ (c : M →L[R] S) : M₂ →ₗ[T] M →L[R] M₂
    where
  toFun := c.smul_right
  map_add' x y := by
    ext e
    apply smul_add
  map_smul' a x := by
    ext e
    dsimp
    apply smul_comm
#align continuous_linear_map.smul_rightₗ ContinuousLinearMap.smulRightₗ

@[simp]
theorem coe_smulRightₗ (c : M →L[R] S) : ⇑(smulRightₗ c : M₂ →ₗ[T] M →L[R] M₂) = c.smul_right :=
  rfl
#align continuous_linear_map.coe_smul_rightₗ ContinuousLinearMap.coe_smulRightₗ

end SmulRightₗ

section CommRing

variable {R : Type _} [CommRing R] {M : Type _} [TopologicalSpace M] [AddCommGroup M] {M₂ : Type _}
  [TopologicalSpace M₂] [AddCommGroup M₂] {M₃ : Type _} [TopologicalSpace M₃] [AddCommGroup M₃]
  [Module R M] [Module R M₂] [Module R M₃] [ContinuousConstSMul R M₃]

variable [TopologicalAddGroup M₂] [ContinuousConstSMul R M₂]

instance : Algebra R (M₂ →L[R] M₂) :=
  Algebra.ofModule smul_comp fun _ _ _ => comp_smul _ _ _

end CommRing

section RestrictScalars

variable {A M M₂ : Type _} [Ring A] [AddCommGroup M] [AddCommGroup M₂] [Module A M] [Module A M₂]
  [TopologicalSpace M] [TopologicalSpace M₂] (R : Type _) [Ring R] [Module R M] [Module R M₂]
  [LinearMap.CompatibleSMul M M₂ R A]

/-- If `A` is an `R`-algebra, then a continuous `A`-linear map can be interpreted as a continuous
`R`-linear map. We assume `linear_map.compatible_smul M M₂ R A` to match assumptions of
`linear_map.map_smul_of_tower`. -/
def restrictScalars (f : M →L[A] M₂) : M →L[R] M₂ :=
  ⟨(f : M →ₗ[A] M₂).restrictScalars R, f.Continuous⟩
#align continuous_linear_map.restrict_scalars ContinuousLinearMap.restrictScalars

variable {R}

@[simp, norm_cast]
theorem coe_restrictScalars (f : M →L[A] M₂) :
    (f.restrictScalars R : M →ₗ[R] M₂) = (f : M →ₗ[A] M₂).restrictScalars R :=
  rfl
#align continuous_linear_map.coe_restrict_scalars ContinuousLinearMap.coe_restrictScalars

@[simp]
theorem coe_restrict_scalars' (f : M →L[A] M₂) : ⇑(f.restrictScalars R) = f :=
  rfl
#align continuous_linear_map.coe_restrict_scalars' ContinuousLinearMap.coe_restrict_scalars'

@[simp]
theorem restrictScalars_zero : (0 : M →L[A] M₂).restrictScalars R = 0 :=
  rfl
#align continuous_linear_map.restrict_scalars_zero ContinuousLinearMap.restrictScalars_zero

section

variable [TopologicalAddGroup M₂]

@[simp]
theorem restrictScalars_add (f g : M →L[A] M₂) :
    (f + g).restrictScalars R = f.restrictScalars R + g.restrictScalars R :=
  rfl
#align continuous_linear_map.restrict_scalars_add ContinuousLinearMap.restrictScalars_add

@[simp]
theorem restrictScalars_neg (f : M →L[A] M₂) : (-f).restrictScalars R = -f.restrictScalars R :=
  rfl
#align continuous_linear_map.restrict_scalars_neg ContinuousLinearMap.restrictScalars_neg

end

variable {S : Type _} [Ring S] [Module S M₂] [ContinuousConstSMul S M₂] [SMulCommClass A S M₂]
  [SMulCommClass R S M₂]

@[simp]
theorem restrictScalars_smul (c : S) (f : M →L[A] M₂) :
    (c • f).restrictScalars R = c • f.restrictScalars R :=
  rfl
#align continuous_linear_map.restrict_scalars_smul ContinuousLinearMap.restrictScalars_smul

variable (A M M₂ R S) [TopologicalAddGroup M₂]

/-- `continuous_linear_map.restrict_scalars` as a `linear_map`. See also
`continuous_linear_map.restrict_scalarsL`. -/
def restrictScalarsₗ : (M →L[A] M₂) →ₗ[S] M →L[R] M₂
    where
  toFun := restrictScalars R
  map_add' := restrictScalars_add
  map_smul' := restrictScalars_smul
#align continuous_linear_map.restrict_scalarsₗ ContinuousLinearMap.restrictScalarsₗ

variable {A M M₂ R S}

@[simp]
theorem coe_restrictScalarsₗ : ⇑(restrictScalarsₗ A M M₂ R S) = restrictScalars R :=
  rfl
#align continuous_linear_map.coe_restrict_scalarsₗ ContinuousLinearMap.coe_restrictScalarsₗ

end RestrictScalars

end ContinuousLinearMap

namespace ContinuousLinearEquiv

section AddCommMonoid

variable {R₁ : Type _} {R₂ : Type _} {R₃ : Type _} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
  {σ₁₃ : R₁ →+* R₃} {σ₃₁ : R₃ →+* R₁} [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁] {M₁ : Type _}
  [TopologicalSpace M₁] [AddCommMonoid M₁] {M'₁ : Type _} [TopologicalSpace M'₁] [AddCommMonoid M'₁]
  {M₂ : Type _} [TopologicalSpace M₂] [AddCommMonoid M₂] {M₃ : Type _} [TopologicalSpace M₃]
  [AddCommMonoid M₃] {M₄ : Type _} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R₁ M₁]
  [Module R₁ M'₁] [Module R₂ M₂] [Module R₃ M₃]

include σ₂₁

/-- A continuous linear equivalence induces a continuous linear map. -/
def toContinuousLinearMap (e : M₁ ≃SL[σ₁₂] M₂) : M₁ →SL[σ₁₂] M₂ :=
  { e.toLinearEquiv.toLinearMap with cont := e.continuous_toFun }
#align continuous_linear_equiv.to_continuous_linear_map ContinuousLinearEquiv.toContinuousLinearMap

/-- Coerce continuous linear equivs to continuous linear maps. -/
instance : Coe (M₁ ≃SL[σ₁₂] M₂) (M₁ →SL[σ₁₂] M₂) :=
  ⟨toContinuousLinearMap⟩

instance : ContinuousSemilinearEquivClass (M₁ ≃SL[σ₁₂] M₂) σ₁₂ M₁ M₂
    where
  coe f := f
  inv f := f.invFun
  coe_injective' f g h₁ h₂ := by
    cases' f with f' _
    cases' g with g' _
    cases f'
    cases g'
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  map_add f := f.map_add'
  map_smulₛₗ f := f.map_smul'
  map_continuous := continuous_toFun
  inv_continuous := continuous_invFun

-- see Note [function coercion]
/-- Coerce continuous linear equivs to maps. -/
instance : CoeFun (M₁ ≃SL[σ₁₂] M₂) fun _ => M₁ → M₂ :=
  ⟨fun f => f⟩

@[simp]
theorem coe_def_rev (e : M₁ ≃SL[σ₁₂] M₂) : e.toContinuousLinearMap = e :=
  rfl
#align continuous_linear_equiv.coe_def_rev ContinuousLinearEquiv.coe_def_rev

theorem coe_apply (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁) : (e : M₁ →SL[σ₁₂] M₂) b = e b :=
  rfl
#align continuous_linear_equiv.coe_apply ContinuousLinearEquiv.coe_apply

@[simp]
theorem coe_toLinearEquiv (f : M₁ ≃SL[σ₁₂] M₂) : ⇑f.toLinearEquiv = f :=
  rfl
#align continuous_linear_equiv.coe_to_linear_equiv ContinuousLinearEquiv.coe_toLinearEquiv

@[simp, norm_cast]
theorem coe_coe (e : M₁ ≃SL[σ₁₂] M₂) : ⇑(e : M₁ →SL[σ₁₂] M₂) = e :=
  rfl
#align continuous_linear_equiv.coe_coe ContinuousLinearEquiv.coe_coe

theorem toLinearEquiv_injective :
    Function.Injective (toLinearEquiv : (M₁ ≃SL[σ₁₂] M₂) → M₁ ≃ₛₗ[σ₁₂] M₂)
  | ⟨e, _, _⟩, ⟨e', _, _⟩, rfl => rfl
#align continuous_linear_equiv.to_linear_equiv_injective ContinuousLinearEquiv.toLinearEquiv_injective

@[ext]
theorem ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ → M₂) = g) : f = g :=
  toLinearEquiv_injective <| LinearEquiv.ext <| congr_fun h
#align continuous_linear_equiv.ext ContinuousLinearEquiv.ext

theorem coe_injective : Function.Injective (coe : (M₁ ≃SL[σ₁₂] M₂) → M₁ →SL[σ₁₂] M₂) :=
  fun e e' h => ext <| funext <| ContinuousLinearMap.ext_iff.1 h
#align continuous_linear_equiv.coe_injective ContinuousLinearEquiv.coe_injective

@[simp, norm_cast]
theorem coe_inj {e e' : M₁ ≃SL[σ₁₂] M₂} : (e : M₁ →SL[σ₁₂] M₂) = e' ↔ e = e' :=
  coe_injective.eq_iff
#align continuous_linear_equiv.coe_inj ContinuousLinearEquiv.coe_inj

/-- A continuous linear equivalence induces a homeomorphism. -/
def toHomeomorph (e : M₁ ≃SL[σ₁₂] M₂) : M₁ ≃ₜ M₂ :=
  { e with toEquiv := e.toLinearEquiv.toEquiv }
#align continuous_linear_equiv.to_homeomorph ContinuousLinearEquiv.toHomeomorph

@[simp]
theorem coe_toHomeomorph (e : M₁ ≃SL[σ₁₂] M₂) : ⇑e.toHomeomorph = e :=
  rfl
#align continuous_linear_equiv.coe_to_homeomorph ContinuousLinearEquiv.coe_toHomeomorph

theorem image_closure (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e '' closure s = closure (e '' s) :=
  e.toHomeomorph.image_closure s
#align continuous_linear_equiv.image_closure ContinuousLinearEquiv.image_closure

theorem preimage_closure (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) : e ⁻¹' closure s = closure (e ⁻¹' s) :=
  e.toHomeomorph.preimage_closure s
#align continuous_linear_equiv.preimage_closure ContinuousLinearEquiv.preimage_closure

@[simp]
theorem isClosed_image (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} : IsClosed (e '' s) ↔ IsClosed s :=
  e.toHomeomorph.isClosed_image
#align continuous_linear_equiv.is_closed_image ContinuousLinearEquiv.isClosed_image

theorem map_nhds_eq (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : map e (𝓝 x) = 𝓝 (e x) :=
  e.toHomeomorph.map_nhds_eq x
#align continuous_linear_equiv.map_nhds_eq ContinuousLinearEquiv.map_nhds_eq

-- Make some straightforward lemmas available to `simp`.
@[simp]
theorem map_zero (e : M₁ ≃SL[σ₁₂] M₂) : e (0 : M₁) = 0 :=
  (e : M₁ →SL[σ₁₂] M₂).map_zero
#align continuous_linear_equiv.map_zero ContinuousLinearEquiv.map_zero

@[simp]
theorem map_add (e : M₁ ≃SL[σ₁₂] M₂) (x y : M₁) : e (x + y) = e x + e y :=
  (e : M₁ →SL[σ₁₂] M₂).map_add x y
#align continuous_linear_equiv.map_add ContinuousLinearEquiv.map_add

@[simp]
theorem map_smulₛₗ (e : M₁ ≃SL[σ₁₂] M₂) (c : R₁) (x : M₁) : e (c • x) = σ₁₂ c • e x :=
  (e : M₁ →SL[σ₁₂] M₂).map_smulₛₗ c x
#align continuous_linear_equiv.map_smulₛₗ ContinuousLinearEquiv.map_smulₛₗ

omit σ₂₁

@[simp]
theorem map_smul [Module R₁ M₂] (e : M₁ ≃L[R₁] M₂) (c : R₁) (x : M₁) : e (c • x) = c • e x :=
  (e : M₁ →L[R₁] M₂).map_smul c x
#align continuous_linear_equiv.map_smul ContinuousLinearEquiv.map_smul

include σ₂₁

@[simp]
theorem map_eq_zero_iff (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁} : e x = 0 ↔ x = 0 :=
  e.toLinearEquiv.map_eq_zero_iff
#align continuous_linear_equiv.map_eq_zero_iff ContinuousLinearEquiv.map_eq_zero_iff

attribute [continuity]
  ContinuousLinearEquiv.continuous_toFun ContinuousLinearEquiv.continuous_invFun

@[continuity]
protected theorem continuous (e : M₁ ≃SL[σ₁₂] M₂) : Continuous (e : M₁ → M₂) :=
  e.continuous_toFun
#align continuous_linear_equiv.continuous ContinuousLinearEquiv.continuous

protected theorem continuousOn (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} : ContinuousOn (e : M₁ → M₂) s :=
  e.Continuous.ContinuousOn
#align continuous_linear_equiv.continuous_on ContinuousLinearEquiv.continuousOn

protected theorem continuousAt (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁} : ContinuousAt (e : M₁ → M₂) x :=
  e.Continuous.ContinuousAt
#align continuous_linear_equiv.continuous_at ContinuousLinearEquiv.continuousAt

protected theorem continuousWithinAt (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} {x : M₁} :
    ContinuousWithinAt (e : M₁ → M₂) s x :=
  e.Continuous.ContinuousWithinAt
#align continuous_linear_equiv.continuous_within_at ContinuousLinearEquiv.continuousWithinAt

theorem comp_continuousOn_iff {α : Type _} [TopologicalSpace α] (e : M₁ ≃SL[σ₁₂] M₂) {f : α → M₁}
    {s : Set α} : ContinuousOn (e ∘ f) s ↔ ContinuousOn f s :=
  e.toHomeomorph.comp_continuousOn_iff _ _
#align continuous_linear_equiv.comp_continuous_on_iff ContinuousLinearEquiv.comp_continuousOn_iff

theorem comp_continuous_iff {α : Type _} [TopologicalSpace α] (e : M₁ ≃SL[σ₁₂] M₂) {f : α → M₁} :
    Continuous (e ∘ f) ↔ Continuous f :=
  e.toHomeomorph.comp_continuous_iff
#align continuous_linear_equiv.comp_continuous_iff ContinuousLinearEquiv.comp_continuous_iff

omit σ₂₁

/-- An extensionality lemma for `R ≃L[R] M`. -/
theorem ext₁ [TopologicalSpace R₁] {f g : R₁ ≃L[R₁] M₁} (h : f 1 = g 1) : f = g :=
  ext <| funext fun x => mul_one x ▸ by rw [← smul_eq_mul, map_smul, h, map_smul]
#align continuous_linear_equiv.ext₁ ContinuousLinearEquiv.ext₁

section

variable (R₁ M₁)

/-- The identity map as a continuous linear equivalence. -/
@[refl]
protected def refl : M₁ ≃L[R₁] M₁ :=
  { LinearEquiv.refl R₁ M₁ with
    continuous_toFun := continuous_id
    continuous_invFun := continuous_id }
#align continuous_linear_equiv.refl ContinuousLinearEquiv.refl

end

@[simp, norm_cast]
theorem coe_refl : ↑(ContinuousLinearEquiv.refl R₁ M₁) = ContinuousLinearMap.id R₁ M₁ :=
  rfl
#align continuous_linear_equiv.coe_refl ContinuousLinearEquiv.coe_refl

@[simp, norm_cast]
theorem coe_refl' : ⇑(ContinuousLinearEquiv.refl R₁ M₁) = id :=
  rfl
#align continuous_linear_equiv.coe_refl' ContinuousLinearEquiv.coe_refl'

/-- The inverse of a continuous linear equivalence as a continuous linear equivalence-/
@[symm]
protected def symm (e : M₁ ≃SL[σ₁₂] M₂) : M₂ ≃SL[σ₂₁] M₁ :=
  { e.toLinearEquiv.symm with
    continuous_toFun := e.continuous_invFun
    continuous_invFun := e.continuous_toFun }
#align continuous_linear_equiv.symm ContinuousLinearEquiv.symm

include σ₂₁

@[simp]
theorem symm_toLinearEquiv (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.toLinearEquiv = e.toLinearEquiv.symm :=
  by
  ext
  rfl
#align continuous_linear_equiv.symm_to_linear_equiv ContinuousLinearEquiv.symm_toLinearEquiv

@[simp]
theorem symm_toHomeomorph (e : M₁ ≃SL[σ₁₂] M₂) : e.toHomeomorph.symm = e.symm.toHomeomorph :=
  rfl
#align continuous_linear_equiv.symm_to_homeomorph ContinuousLinearEquiv.symm_toHomeomorph

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : M₁ ≃SL[σ₁₂] M₂) : M₁ → M₂ :=
  h
#align continuous_linear_equiv.simps.apply ContinuousLinearEquiv.Simps.apply

/-- See Note [custom simps projection] -/
def Simps.symmApply (h : M₁ ≃SL[σ₁₂] M₂) : M₂ → M₁ :=
  h.symm
#align continuous_linear_equiv.simps.symm_apply ContinuousLinearEquiv.Simps.symmApply

initialize_simps_projections ContinuousLinearEquiv (to_linear_equiv_to_fun → apply,
  to_linear_equiv_inv_fun → symm_apply)

theorem symm_map_nhds_eq (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : map e.symm (𝓝 (e x)) = 𝓝 x :=
  e.toHomeomorph.symm_map_nhds_eq x
#align continuous_linear_equiv.symm_map_nhds_eq ContinuousLinearEquiv.symm_map_nhds_eq

omit σ₂₁

include σ₂₁ σ₃₂ σ₃₁

/-- The composition of two continuous linear equivalences as a continuous linear equivalence. -/
@[trans]
protected def trans (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) : M₁ ≃SL[σ₁₃] M₃ :=
  {
    e₁.toLinearEquiv.trans
      e₂.toLinearEquiv with
    continuous_toFun := e₂.continuous_toFun.comp e₁.continuous_toFun
    continuous_invFun := e₁.continuous_invFun.comp e₂.continuous_invFun }
#align continuous_linear_equiv.trans ContinuousLinearEquiv.trans

include σ₁₃

@[simp]
theorem trans_toLinearEquiv (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) :
    (e₁.trans e₂).toLinearEquiv = e₁.toLinearEquiv.trans e₂.toLinearEquiv :=
  by
  ext
  rfl
#align continuous_linear_equiv.trans_to_linear_equiv ContinuousLinearEquiv.trans_toLinearEquiv

omit σ₁₃ σ₂₁ σ₃₂ σ₃₁

/-- Product of two continuous linear equivalences. The map comes from `equiv.prod_congr`. -/
def prod [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂) (e' : M₃ ≃L[R₁] M₄) :
    (M₁ × M₃) ≃L[R₁] M₂ × M₄ :=
  {
    e.toLinearEquiv.Prod
      e'.toLinearEquiv with
    continuous_toFun := e.continuous_toFun.Prod_map e'.continuous_toFun
    continuous_invFun := e.continuous_invFun.Prod_map e'.continuous_invFun }
#align continuous_linear_equiv.prod ContinuousLinearEquiv.prod

@[simp, norm_cast]
theorem prod_apply [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
    (e' : M₃ ≃L[R₁] M₄) (x) : e.Prod e' x = (e x.1, e' x.2) :=
  rfl
#align continuous_linear_equiv.prod_apply ContinuousLinearEquiv.prod_apply

@[simp, norm_cast]
theorem coe_prod [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
    (e' : M₃ ≃L[R₁] M₄) :
    (e.Prod e' : M₁ × M₃ →L[R₁] M₂ × M₄) = (e : M₁ →L[R₁] M₂).Prod_map (e' : M₃ →L[R₁] M₄) :=
  rfl
#align continuous_linear_equiv.coe_prod ContinuousLinearEquiv.coe_prod

theorem prod_symm [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
    (e' : M₃ ≃L[R₁] M₄) : (e.Prod e').symm = e.symm.Prod e'.symm :=
  rfl
#align continuous_linear_equiv.prod_symm ContinuousLinearEquiv.prod_symm

include σ₂₁

protected theorem bijective (e : M₁ ≃SL[σ₁₂] M₂) : Function.Bijective e :=
  e.toLinearEquiv.toEquiv.Bijective
#align continuous_linear_equiv.bijective ContinuousLinearEquiv.bijective

protected theorem injective (e : M₁ ≃SL[σ₁₂] M₂) : Function.Injective e :=
  e.toLinearEquiv.toEquiv.Injective
#align continuous_linear_equiv.injective ContinuousLinearEquiv.injective

protected theorem surjective (e : M₁ ≃SL[σ₁₂] M₂) : Function.Surjective e :=
  e.toLinearEquiv.toEquiv.Surjective
#align continuous_linear_equiv.surjective ContinuousLinearEquiv.surjective

include σ₃₂ σ₃₁ σ₁₃

@[simp]
theorem trans_apply (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) (c : M₁) :
    (e₁.trans e₂) c = e₂ (e₁ c) :=
  rfl
#align continuous_linear_equiv.trans_apply ContinuousLinearEquiv.trans_apply

omit σ₃₂ σ₃₁ σ₁₃

@[simp]
theorem apply_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) (c : M₂) : e (e.symm c) = c :=
  e.1.right_inv c
#align continuous_linear_equiv.apply_symm_apply ContinuousLinearEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁) : e.symm (e b) = b :=
  e.1.left_inv b
#align continuous_linear_equiv.symm_apply_apply ContinuousLinearEquiv.symm_apply_apply

include σ₁₂ σ₂₃ σ₁₃ σ₃₁

@[simp]
theorem symm_trans_apply (e₁ : M₂ ≃SL[σ₂₁] M₁) (e₂ : M₃ ≃SL[σ₃₂] M₂) (c : M₁) :
    (e₂.trans e₁).symm c = e₂.symm (e₁.symm c) :=
  rfl
#align continuous_linear_equiv.symm_trans_apply ContinuousLinearEquiv.symm_trans_apply

omit σ₁₂ σ₂₃ σ₁₃ σ₃₁

@[simp]
theorem symm_image_image (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e.symm '' (e '' s) = s :=
  e.toLinearEquiv.toEquiv.symm_image_image s
#align continuous_linear_equiv.symm_image_image ContinuousLinearEquiv.symm_image_image

@[simp]
theorem image_symm_image (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) : e '' (e.symm '' s) = s :=
  e.symm.symm_image_image s
#align continuous_linear_equiv.image_symm_image ContinuousLinearEquiv.image_symm_image

include σ₃₂ σ₃₁

@[simp, norm_cast]
theorem comp_coe (f : M₁ ≃SL[σ₁₂] M₂) (f' : M₂ ≃SL[σ₂₃] M₃) :
    (f' : M₂ →SL[σ₂₃] M₃).comp (f : M₁ →SL[σ₁₂] M₂) = (f.trans f' : M₁ →SL[σ₁₃] M₃) :=
  rfl
#align continuous_linear_equiv.comp_coe ContinuousLinearEquiv.comp_coe

omit σ₃₂ σ₃₁ σ₂₁

@[simp]
theorem coe_comp_coe_symm (e : M₁ ≃SL[σ₁₂] M₂) :
    (e : M₁ →SL[σ₁₂] M₂).comp (e.symm : M₂ →SL[σ₂₁] M₁) = ContinuousLinearMap.id R₂ M₂ :=
  ContinuousLinearMap.ext e.apply_symm_apply
#align continuous_linear_equiv.coe_comp_coe_symm ContinuousLinearEquiv.coe_comp_coe_symm

@[simp]
theorem coe_symm_comp_coe (e : M₁ ≃SL[σ₁₂] M₂) :
    (e.symm : M₂ →SL[σ₂₁] M₁).comp (e : M₁ →SL[σ₁₂] M₂) = ContinuousLinearMap.id R₁ M₁ :=
  ContinuousLinearMap.ext e.symm_apply_apply
#align continuous_linear_equiv.coe_symm_comp_coe ContinuousLinearEquiv.coe_symm_comp_coe

include σ₂₁

@[simp]
theorem symm_comp_self (e : M₁ ≃SL[σ₁₂] M₂) : (e.symm : M₂ → M₁) ∘ (e : M₁ → M₂) = id :=
  by
  ext x
  exact symm_apply_apply e x
#align continuous_linear_equiv.symm_comp_self ContinuousLinearEquiv.symm_comp_self

@[simp]
theorem self_comp_symm (e : M₁ ≃SL[σ₁₂] M₂) : (e : M₁ → M₂) ∘ (e.symm : M₂ → M₁) = id :=
  by
  ext x
  exact apply_symm_apply e x
#align continuous_linear_equiv.self_comp_symm ContinuousLinearEquiv.self_comp_symm

@[simp]
theorem symm_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.symm = e :=
  by
  ext x
  rfl
#align continuous_linear_equiv.symm_symm ContinuousLinearEquiv.symm_symm

omit σ₂₁

@[simp]
theorem refl_symm : (ContinuousLinearEquiv.refl R₁ M₁).symm = ContinuousLinearEquiv.refl R₁ M₁ :=
  rfl
#align continuous_linear_equiv.refl_symm ContinuousLinearEquiv.refl_symm

include σ₂₁

theorem symm_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : e.symm.symm x = e x :=
  rfl
#align continuous_linear_equiv.symm_symm_apply ContinuousLinearEquiv.symm_symm_apply

theorem symm_apply_eq (e : M₁ ≃SL[σ₁₂] M₂) {x y} : e.symm x = y ↔ x = e y :=
  e.toLinearEquiv.symm_apply_eq
#align continuous_linear_equiv.symm_apply_eq ContinuousLinearEquiv.symm_apply_eq

theorem eq_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) {x y} : y = e.symm x ↔ e y = x :=
  e.toLinearEquiv.eq_symm_apply
#align continuous_linear_equiv.eq_symm_apply ContinuousLinearEquiv.eq_symm_apply

protected theorem image_eq_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e '' s = e.symm ⁻¹' s :=
  e.toLinearEquiv.toEquiv.image_eq_preimage s
#align continuous_linear_equiv.image_eq_preimage ContinuousLinearEquiv.image_eq_preimage

protected theorem image_symm_eq_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) :
    e.symm '' s = e ⁻¹' s := by rw [e.symm.image_eq_preimage, e.symm_symm]
#align continuous_linear_equiv.image_symm_eq_preimage ContinuousLinearEquiv.image_symm_eq_preimage

@[simp]
protected theorem symm_preimage_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) :
    e.symm ⁻¹' (e ⁻¹' s) = s :=
  e.toLinearEquiv.toEquiv.symm_preimage_preimage s
#align continuous_linear_equiv.symm_preimage_preimage ContinuousLinearEquiv.symm_preimage_preimage

@[simp]
protected theorem preimage_symm_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) :
    e ⁻¹' (e.symm ⁻¹' s) = s :=
  e.symm.symm_preimage_preimage s
#align continuous_linear_equiv.preimage_symm_preimage ContinuousLinearEquiv.preimage_symm_preimage

protected theorem uniformEmbedding {E₁ E₂ : Type _} [UniformSpace E₁] [UniformSpace E₂]
    [AddCommGroup E₁] [AddCommGroup E₂] [Module R₁ E₁] [Module R₂ E₂] [UniformAddGroup E₁]
    [UniformAddGroup E₂] (e : E₁ ≃SL[σ₁₂] E₂) : UniformEmbedding e :=
  e.toLinearEquiv.toEquiv.UniformEmbedding e.toContinuousLinearMap.UniformContinuous
    e.symm.toContinuousLinearMap.UniformContinuous
#align continuous_linear_equiv.uniform_embedding ContinuousLinearEquiv.uniformEmbedding

protected theorem LinearEquiv.uniformEmbedding {E₁ E₂ : Type _} [UniformSpace E₁] [UniformSpace E₂]
    [AddCommGroup E₁] [AddCommGroup E₂] [Module R₁ E₁] [Module R₂ E₂] [UniformAddGroup E₁]
    [UniformAddGroup E₂] (e : E₁ ≃ₛₗ[σ₁₂] E₂) (h₁ : Continuous e) (h₂ : Continuous e.symm) :
    UniformEmbedding e :=
  ContinuousLinearEquiv.uniformEmbedding
    ({ e with
        continuous_toFun := h₁
        continuous_invFun := h₂ } :
      E₁ ≃SL[σ₁₂] E₂)
#align linear_equiv.uniform_embedding LinearEquiv.uniformEmbedding

omit σ₂₁

/-- Create a `continuous_linear_equiv` from two `continuous_linear_map`s that are
inverse of each other. -/
def equivOfInverse (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M₁) (h₁ : Function.LeftInverse f₂ f₁)
    (h₂ : Function.RightInverse f₂ f₁) : M₁ ≃SL[σ₁₂] M₂ :=
  { f₁ with
    toFun := f₁
    continuous_toFun := f₁.Continuous
    invFun := f₂
    continuous_invFun := f₂.Continuous
    left_inv := h₁
    right_inv := h₂ }
#align continuous_linear_equiv.equiv_of_inverse ContinuousLinearEquiv.equivOfInverse

include σ₂₁

@[simp]
theorem equivOfInverse_apply (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ h₁ h₂ x) :
    equivOfInverse f₁ f₂ h₁ h₂ x = f₁ x :=
  rfl
#align continuous_linear_equiv.equiv_of_inverse_apply ContinuousLinearEquiv.equivOfInverse_apply

@[simp]
theorem symm_equivOfInverse (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ h₁ h₂) :
    (equivOfInverse f₁ f₂ h₁ h₂).symm = equivOfInverse f₂ f₁ h₂ h₁ :=
  rfl
#align continuous_linear_equiv.symm_equiv_of_inverse ContinuousLinearEquiv.symm_equivOfInverse

omit σ₂₁

variable (M₁)

/-- The continuous linear equivalences from `M` to itself form a group under composition. -/
instance automorphismGroup : Group (M₁ ≃L[R₁] M₁)
    where
  mul f g := g.trans f
  one := ContinuousLinearEquiv.refl R₁ M₁
  inv f := f.symm
  mul_assoc f g h := by
    ext
    rfl
  mul_one f := by
    ext
    rfl
  one_mul f := by
    ext
    rfl
  mul_left_inv f := by
    ext
    exact f.left_inv x
#align continuous_linear_equiv.automorphism_group ContinuousLinearEquiv.automorphismGroup

variable {M₁} {R₄ : Type _} [Semiring R₄] [Module R₄ M₄] {σ₃₄ : R₃ →+* R₄} {σ₄₃ : R₄ →+* R₃}
  [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄] {σ₂₄ : R₂ →+* R₄} {σ₁₄ : R₁ →+* R₄}
  [RingHomCompTriple σ₂₁ σ₁₄ σ₂₄] [RingHomCompTriple σ₂₄ σ₄₃ σ₂₃] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]

/-- The continuous linear equivalence between `ulift M₁` and `M₁`. -/
def ulift : ULift M₁ ≃L[R₁] M₁ :=
  { Equiv.ulift with
    map_add' := fun x y => rfl
    map_smul' := fun c x => rfl
    continuous_toFun := continuous_uLift_down
    continuous_invFun := continuous_uLift_up }
#align continuous_linear_equiv.ulift ContinuousLinearEquiv.ulift

include σ₂₁ σ₃₄ σ₂₃ σ₂₄ σ₁₃

/-- A pair of continuous (semi)linear equivalences generates an equivalence between the spaces of
continuous linear maps. See also `continuous_linear_equiv.arrow_congr`. -/
@[simps]
def arrowCongrEquiv (e₁₂ : M₁ ≃SL[σ₁₂] M₂) (e₄₃ : M₄ ≃SL[σ₄₃] M₃) :
    (M₁ →SL[σ₁₄] M₄) ≃ (M₂ →SL[σ₂₃] M₃)
    where
  toFun f := (e₄₃ : M₄ →SL[σ₄₃] M₃).comp (f.comp (e₁₂.symm : M₂ →SL[σ₂₁] M₁))
  invFun f := (e₄₃.symm : M₃ →SL[σ₃₄] M₄).comp (f.comp (e₁₂ : M₁ →SL[σ₁₂] M₂))
  left_inv f :=
    ContinuousLinearMap.ext fun x => by
      simp only [ContinuousLinearMap.comp_apply, symm_apply_apply, coe_coe]
  right_inv f :=
    ContinuousLinearMap.ext fun x => by
      simp only [ContinuousLinearMap.comp_apply, apply_symm_apply, coe_coe]
#align continuous_linear_equiv.arrow_congr_equiv ContinuousLinearEquiv.arrowCongrEquiv

end AddCommMonoid

section AddCommGroup

variable {R : Type _} [Semiring R] {M : Type _} [TopologicalSpace M] [AddCommGroup M] {M₂ : Type _}
  [TopologicalSpace M₂] [AddCommGroup M₂] {M₃ : Type _} [TopologicalSpace M₃] [AddCommGroup M₃]
  {M₄ : Type _} [TopologicalSpace M₄] [AddCommGroup M₄] [Module R M] [Module R M₂] [Module R M₃]
  [Module R M₄]

variable [TopologicalAddGroup M₄]

/-- Equivalence given by a block lower diagonal matrix. `e` and `e'` are diagonal square blocks,
  and `f` is a rectangular block below the diagonal. -/
def skewProd (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) : (M × M₃) ≃L[R] M₂ × M₄ :=
  {
    e.toLinearEquiv.skewProd e'.toLinearEquiv
      ↑f with
    continuous_toFun :=
      (e.continuous_toFun.comp continuous_fst).prod_mk
        ((e'.continuous_toFun.comp continuous_snd).add <| f.Continuous.comp continuous_fst)
    continuous_invFun :=
      (e.continuous_invFun.comp continuous_fst).prod_mk
        (e'.continuous_invFun.comp <|
          continuous_snd.sub <| f.Continuous.comp <| e.continuous_invFun.comp continuous_fst) }
#align continuous_linear_equiv.skew_prod ContinuousLinearEquiv.skewProd

@[simp]
theorem skewProd_apply (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) (x) :
    e.skewProd e' f x = (e x.1, e' x.2 + f x.1) :=
  rfl
#align continuous_linear_equiv.skew_prod_apply ContinuousLinearEquiv.skewProd_apply

@[simp]
theorem skewProd_symm_apply (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) (x) :
    (e.skewProd e' f).symm x = (e.symm x.1, e'.symm (x.2 - f (e.symm x.1))) :=
  rfl
#align continuous_linear_equiv.skew_prod_symm_apply ContinuousLinearEquiv.skewProd_symm_apply

end AddCommGroup

section Ring

variable {R : Type _} [Ring R] {R₂ : Type _} [Ring R₂] {M : Type _} [TopologicalSpace M]
  [AddCommGroup M] [Module R M] {M₂ : Type _} [TopologicalSpace M₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

include σ₂₁

@[simp]
theorem map_sub (e : M ≃SL[σ₁₂] M₂) (x y : M) : e (x - y) = e x - e y :=
  (e : M →SL[σ₁₂] M₂).map_sub x y
#align continuous_linear_equiv.map_sub ContinuousLinearEquiv.map_sub

@[simp]
theorem map_neg (e : M ≃SL[σ₁₂] M₂) (x : M) : e (-x) = -e x :=
  (e : M →SL[σ₁₂] M₂).map_neg x
#align continuous_linear_equiv.map_neg ContinuousLinearEquiv.map_neg

omit σ₂₁

section

/-! The next theorems cover the identification between `M ≃L[𝕜] M`and the group of units of the ring
`M →L[R] M`. -/


variable [TopologicalAddGroup M]

/-- An invertible continuous linear map `f` determines a continuous equivalence from `M` to itself.
-/
def ofUnit (f : (M →L[R] M)ˣ) : M ≃L[R] M
    where
  toLinearEquiv :=
    { toFun := f.val
      map_add' := by simp
      map_smul' := by simp
      invFun := f.inv
      left_inv := fun x =>
        show (f.inv * f.val) x = x by
          rw [f.inv_val]
          simp
      right_inv := fun x =>
        show (f.val * f.inv) x = x by
          rw [f.val_inv]
          simp }
  continuous_toFun := f.val.Continuous
  continuous_invFun := f.inv.Continuous
#align continuous_linear_equiv.of_unit ContinuousLinearEquiv.ofUnit

/-- A continuous equivalence from `M` to itself determines an invertible continuous linear map. -/
def toUnit (f : M ≃L[R] M) : (M →L[R] M)ˣ where
  val := f
  inv := f.symm
  val_inv := by
    ext
    simp
  inv_val := by
    ext
    simp
#align continuous_linear_equiv.to_unit ContinuousLinearEquiv.toUnit

variable (R M)

/-- The units of the algebra of continuous `R`-linear endomorphisms of `M` is multiplicatively
equivalent to the type of continuous linear equivalences between `M` and itself. -/
def unitsEquiv : (M →L[R] M)ˣ ≃* M ≃L[R] M
    where
  toFun := ofUnit
  invFun := toUnit
  left_inv f := by
    ext
    rfl
  right_inv f := by
    ext
    rfl
  map_mul' x y := by
    ext
    rfl
#align continuous_linear_equiv.units_equiv ContinuousLinearEquiv.unitsEquiv

@[simp]
theorem unitsEquiv_apply (f : (M →L[R] M)ˣ) (x : M) : unitsEquiv R M f x = f x :=
  rfl
#align continuous_linear_equiv.units_equiv_apply ContinuousLinearEquiv.unitsEquiv_apply

end

section

variable (R) [TopologicalSpace R] [ContinuousMul R]

/-- Continuous linear equivalences `R ≃L[R] R` are enumerated by `Rˣ`. -/
def unitsEquivAut : Rˣ ≃ R ≃L[R] R
    where
  toFun u :=
    equivOfInverse (ContinuousLinearMap.smulRight (1 : R →L[R] R) ↑u)
      (ContinuousLinearMap.smulRight (1 : R →L[R] R) ↑u⁻¹) (fun x => by simp) fun x => by simp
  invFun e :=
    ⟨e 1, e.symm 1, by rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, symm_apply_apply], by
      rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, apply_symm_apply]⟩
  left_inv u := Units.ext <| by simp
  right_inv e := ext₁ <| by simp
#align continuous_linear_equiv.units_equiv_aut ContinuousLinearEquiv.unitsEquivAut

variable {R}

@[simp]
theorem unitsEquivAut_apply (u : Rˣ) (x : R) : unitsEquivAut R u x = x * u :=
  rfl
#align continuous_linear_equiv.units_equiv_aut_apply ContinuousLinearEquiv.unitsEquivAut_apply

@[simp]
theorem unitsEquivAut_apply_symm (u : Rˣ) (x : R) : (unitsEquivAut R u).symm x = x * ↑u⁻¹ :=
  rfl
#align continuous_linear_equiv.units_equiv_aut_apply_symm ContinuousLinearEquiv.unitsEquivAut_apply_symm

@[simp]
theorem unitsEquivAut_symm_apply (e : R ≃L[R] R) : ↑((unitsEquivAut R).symm e) = e 1 :=
  rfl
#align continuous_linear_equiv.units_equiv_aut_symm_apply ContinuousLinearEquiv.unitsEquivAut_symm_apply

end

variable [Module R M₂] [TopologicalAddGroup M]

open _Root_.ContinuousLinearMap (id fst snd)

open _Root_.LinearMap (mem_ker)

/-- A pair of continuous linear maps such that `f₁ ∘ f₂ = id` generates a continuous
linear equivalence `e` between `M` and `M₂ × f₁.ker` such that `(e x).2 = x` for `x ∈ f₁.ker`,
`(e x).1 = f₁ x`, and `(e (f₂ y)).2 = 0`. The map is given by `e x = (f₁ x, x - f₂ (f₁ x))`. -/
def equivOfRightInverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M) (h : Function.RightInverse f₂ f₁) :
    M ≃L[R] M₂ × ker f₁ :=
  equivOfInverse (f₁.Prod (f₁.projKerOfRightInverse f₂ h)) (f₂.coprod (ker f₁).subtypeL)
    (fun x => by simp) fun ⟨x, y⟩ => by simp [h x]
#align continuous_linear_equiv.equiv_of_right_inverse ContinuousLinearEquiv.equivOfRightInverse

@[simp]
theorem fst_equivOfRightInverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
    (h : Function.RightInverse f₂ f₁) (x : M) : (equivOfRightInverse f₁ f₂ h x).1 = f₁ x :=
  rfl
#align continuous_linear_equiv.fst_equiv_of_right_inverse ContinuousLinearEquiv.fst_equivOfRightInverse

@[simp]
theorem snd_equivOfRightInverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
    (h : Function.RightInverse f₂ f₁) (x : M) :
    ((equivOfRightInverse f₁ f₂ h x).2 : M) = x - f₂ (f₁ x) :=
  rfl
#align continuous_linear_equiv.snd_equiv_of_right_inverse ContinuousLinearEquiv.snd_equivOfRightInverse

@[simp]
theorem equivOfRightInverse_symm_apply (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
    (h : Function.RightInverse f₂ f₁) (y : M₂ × ker f₁) :
    (equivOfRightInverse f₁ f₂ h).symm y = f₂ y.1 + y.2 :=
  rfl
#align continuous_linear_equiv.equiv_of_right_inverse_symm_apply ContinuousLinearEquiv.equivOfRightInverse_symm_apply

end Ring

section

variable (ι R M : Type _) [Unique ι] [Semiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M]

/-- If `ι` has a unique element, then `ι → M` is continuously linear equivalent to `M`. -/
def funUnique : (ι → M) ≃L[R] M :=
  { Homeomorph.funUnique ι M with toLinearEquiv := LinearEquiv.funUnique ι R M }
#align continuous_linear_equiv.fun_unique ContinuousLinearEquiv.funUnique

variable {ι R M}

@[simp]
theorem coe_funUnique : ⇑(funUnique ι R M) = Function.eval default :=
  rfl
#align continuous_linear_equiv.coe_fun_unique ContinuousLinearEquiv.coe_funUnique

@[simp]
theorem coe_funUnique_symm : ⇑(funUnique ι R M).symm = Function.const ι :=
  rfl
#align continuous_linear_equiv.coe_fun_unique_symm ContinuousLinearEquiv.coe_funUnique_symm

variable (R M)

/-- Continuous linear equivalence between dependent functions `Π i : fin 2, M i` and `M 0 × M 1`. -/
@[simps (config := { fullyApplied := false })]
def piFinTwo (M : Fin 2 → Type _) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, TopologicalSpace (M i)] : (∀ i, M i) ≃L[R] M 0 × M 1 :=
  { Homeomorph.piFinTwo M with toLinearEquiv := LinearEquiv.piFinTwo R M }
#align continuous_linear_equiv.pi_fin_two ContinuousLinearEquiv.piFinTwo

/-- Continuous linear equivalence between vectors in `M² = fin 2 → M` and `M × M`. -/
@[simps (config := { fullyApplied := false })]
def finTwoArrow : (Fin 2 → M) ≃L[R] M × M :=
  { piFinTwo R fun _ => M with toLinearEquiv := LinearEquiv.finTwoArrow R M }
#align continuous_linear_equiv.fin_two_arrow ContinuousLinearEquiv.finTwoArrow

end

end ContinuousLinearEquiv

namespace ContinuousLinearMap

open Classical

variable {R : Type _} {M : Type _} {M₂ : Type _} [TopologicalSpace M] [TopologicalSpace M₂]

section

variable [Semiring R]

variable [AddCommMonoid M₂] [Module R M₂]

variable [AddCommMonoid M] [Module R M]

/-- Introduce a function `inverse` from `M →L[R] M₂` to `M₂ →L[R] M`, which sends `f` to `f.symm` if
`f` is a continuous linear equivalence and to `0` otherwise.  This definition is somewhat ad hoc,
but one needs a fully (rather than partially) defined inverse function for some purposes, including
for calculus. -/
noncomputable def inverse : (M →L[R] M₂) → M₂ →L[R] M := fun f =>
  if h : ∃ e : M ≃L[R] M₂, (e : M →L[R] M₂) = f then ((Classical.choose h).symm : M₂ →L[R] M) else 0
#align continuous_linear_map.inverse ContinuousLinearMap.inverse

/-- By definition, if `f` is invertible then `inverse f = f.symm`. -/
@[simp]
theorem inverse_equiv (e : M ≃L[R] M₂) : inverse (e : M →L[R] M₂) = e.symm :=
  by
  have h : ∃ e' : M ≃L[R] M₂, (e' : M →L[R] M₂) = ↑e := ⟨e, rfl⟩
  simp only [inverse, dif_pos h]
  congr
  exact_mod_cast Classical.choose_spec h
#align continuous_linear_map.inverse_equiv ContinuousLinearMap.inverse_equiv

/-- By definition, if `f` is not invertible then `inverse f = 0`. -/
@[simp]
theorem inverse_non_equiv (f : M →L[R] M₂) (h : ¬∃ e' : M ≃L[R] M₂, ↑e' = f) : inverse f = 0 :=
  dif_neg h
#align continuous_linear_map.inverse_non_equiv ContinuousLinearMap.inverse_non_equiv

end

section

variable [Ring R]

variable [AddCommGroup M] [TopologicalAddGroup M] [Module R M]

variable [AddCommGroup M₂] [Module R M₂]

@[simp]
theorem ring_inverse_equiv (e : M ≃L[R] M) : Ring.inverse ↑e = inverse (e : M →L[R] M) :=
  by
  suffices Ring.inverse ((ContinuousLinearEquiv.unitsEquiv _ _).symm e : M →L[R] M) = inverse ↑e by
    convert this
  simp
  rfl
#align continuous_linear_map.ring_inverse_equiv ContinuousLinearMap.ring_inverse_equiv

/-- The function `continuous_linear_equiv.inverse` can be written in terms of `ring.inverse` for the
ring of self-maps of the domain. -/
theorem to_ring_inverse (e : M ≃L[R] M₂) (f : M →L[R] M₂) :
    inverse f = Ring.inverse ((e.symm : M₂ →L[R] M).comp f) ∘L ↑e.symm :=
  by
  by_cases h₁ : ∃ e' : M ≃L[R] M₂, ↑e' = f
  · obtain ⟨e', he'⟩ := h₁
    rw [← he']
    change _ = Ring.inverse ↑(e'.trans e.symm) ∘L ↑e.symm
    ext
    simp
  · suffices ¬IsUnit ((e.symm : M₂ →L[R] M).comp f) by simp [this, h₁]
    contrapose! h₁
    rcases h₁ with ⟨F, hF⟩
    use (ContinuousLinearEquiv.unitsEquiv _ _ F).trans e
    ext
    dsimp
    rw [coeFn_coe_base' F, hF]
    simp
#align continuous_linear_map.to_ring_inverse ContinuousLinearMap.to_ring_inverse

theorem ring_inverse_eq_map_inverse : Ring.inverse = @inverse R M M _ _ _ _ _ _ _ :=
  by
  ext
  simp [to_ring_inverse (ContinuousLinearEquiv.refl R M)]
#align continuous_linear_map.ring_inverse_eq_map_inverse ContinuousLinearMap.ring_inverse_eq_map_inverse

end

end ContinuousLinearMap

namespace Submodule

variable {R : Type _} [Ring R] {M : Type _} [TopologicalSpace M] [AddCommGroup M] [Module R M]
  {M₂ : Type _} [TopologicalSpace M₂] [AddCommGroup M₂] [Module R M₂]

open ContinuousLinearMap

/-- A submodule `p` is called *complemented* if there exists a continuous projection `M →ₗ[R] p`. -/
def ClosedComplemented (p : Submodule R M) : Prop :=
  ∃ f : M →L[R] p, ∀ x : p, f x = x
#align submodule.closed_complemented Submodule.ClosedComplemented

theorem ClosedComplemented.has_closed_complement {p : Submodule R M} [T1Space p]
    (h : ClosedComplemented p) : ∃ (q : Submodule R M)(hq : IsClosed (q : Set M)), IsCompl p q :=
  Exists.elim h fun f hf => ⟨ker f, f.isClosed_ker, LinearMap.isCompl_of_proj hf⟩
#align submodule.closed_complemented.has_closed_complement Submodule.ClosedComplemented.has_closed_complement

protected theorem ClosedComplemented.isClosed [TopologicalAddGroup M] [T1Space M]
    {p : Submodule R M} (h : ClosedComplemented p) : IsClosed (p : Set M) :=
  by
  rcases h with ⟨f, hf⟩
  have : ker (id R M - p.subtypeL.comp f) = p := LinearMap.ker_id_sub_eq_of_proj hf
  exact this ▸ is_closed_ker _
#align submodule.closed_complemented.is_closed Submodule.ClosedComplemented.isClosed

@[simp]
theorem closedComplemented_bot : ClosedComplemented (⊥ : Submodule R M) :=
  ⟨0, fun x => by simp only [zero_apply, eq_zero_of_bot_submodule x]⟩
#align submodule.closed_complemented_bot Submodule.closedComplemented_bot

@[simp]
theorem closedComplemented_top : ClosedComplemented (⊤ : Submodule R M) :=
  ⟨(id R M).codRestrict ⊤ fun x => trivial, fun x => Subtype.ext_iff_val.2 <| by simp⟩
#align submodule.closed_complemented_top Submodule.closedComplemented_top

end Submodule

theorem ContinuousLinearMap.closedComplemented_ker_of_rightInverse {R : Type _} [Ring R]
    {M : Type _} [TopologicalSpace M] [AddCommGroup M] {M₂ : Type _} [TopologicalSpace M₂]
    [AddCommGroup M₂] [Module R M] [Module R M₂] [TopologicalAddGroup M] (f₁ : M →L[R] M₂)
    (f₂ : M₂ →L[R] M) (h : Function.RightInverse f₂ f₁) : (ker f₁).ClosedComplemented :=
  ⟨f₁.projKerOfRightInverse f₂ h, f₁.projKerOfRightInverse_apply_idem f₂ h⟩
#align continuous_linear_map.closed_complemented_ker_of_right_inverse ContinuousLinearMap.closedComplemented_ker_of_rightInverse

section Quotient

namespace Submodule

variable {R M : Type _} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  (S : Submodule R M)

theorem isOpenMap_mkQ [TopologicalAddGroup M] : IsOpenMap S.mkQ :=
  QuotientAddGroup.isOpenMap_coe S.toAddSubgroup
#align submodule.is_open_map_mkq Submodule.isOpenMap_mkQ

instance topologicalAddGroup_quotient [TopologicalAddGroup M] : TopologicalAddGroup (M ⧸ S) :=
  topologicalAddGroup_quotient S.toAddSubgroup
#align submodule.topological_add_group_quotient Submodule.topologicalAddGroup_quotient

instance continuousSMul_quotient [TopologicalSpace R] [TopologicalAddGroup M] [ContinuousSMul R M] :
    ContinuousSMul R (M ⧸ S) := by
  constructor
  have quot : QuotientMap fun au : R × M => (au.1, S.mkq au.2) :=
    IsOpenMap.to_quotientMap (is_open_map.id.prod S.is_open_map_mkq)
      (continuous_id.prod_map continuous_quot_mk)
      (function.surjective_id.prod_map <| surjective_quot_mk _)
  rw [quot.continuous_iff]
  exact continuous_quot_mk.comp continuous_smul
#align submodule.has_continuous_smul_quotient Submodule.continuousSMul_quotient

instance t3_quotient_of_isClosed [TopologicalAddGroup M] [IsClosed (S : Set M)] : T3Space (M ⧸ S) :=
  letI : IsClosed (S.to_add_subgroup : Set M) := ‹_›
  S.to_add_subgroup.t3_quotient_of_is_closed
#align submodule.t3_quotient_of_is_closed Submodule.t3_quotient_of_isClosed

end Submodule

end Quotient

