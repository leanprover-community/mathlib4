/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import Mathlib.Algebra.Module.Opposite
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Theory of topological modules

We use the class `ContinuousSMul` for topological (semi) modules and topological vector spaces.
-/

assert_not_exists Cardinal TrivialStar

open LinearMap (ker range)
open Topology Filter Pointwise

universe u v w u'

section

variable {R : Type*} {M : Type*} [Ring R] [TopologicalSpace R] [TopologicalSpace M]
  [AddCommGroup M] [Module R M]

theorem ContinuousSMul.of_nhds_zero [IsTopologicalRing R] [IsTopologicalAddGroup M]
    (hmul : Tendsto (fun p : R × M => p.1 • p.2) (𝓝 0 ×ˢ 𝓝 0) (𝓝 0))
    (hmulleft : ∀ m : M, Tendsto (fun a : R => a • m) (𝓝 0) (𝓝 0))
    (hmulright : ∀ a : R, Tendsto (fun m : M => a • m) (𝓝 0) (𝓝 0)) : ContinuousSMul R M where
  continuous_smul := by
    rw [← nhds_prod_eq] at hmul
    refine continuous_of_continuousAt_zero₂ (AddMonoidHom.smul : R →+ M →+ M) ?_ ?_ ?_ <;>
      simpa [ContinuousAt]

variable (R M) in
omit [TopologicalSpace R] in
/-- A topological module over a ring has continuous negation.

This cannot be an instance, because it would cause search for `[Module ?R M]` with unknown `R`. -/
theorem ContinuousNeg.of_continuousConstSMul [ContinuousConstSMul R M] : ContinuousNeg M where
  continuous_neg := by simpa using continuous_const_smul (T := M) (-1 : R)

end

section

variable {R : Type*} {M : Type*} [Ring R] [TopologicalSpace R] [TopologicalSpace M]
  [AddCommGroup M] [ContinuousAdd M] [Module R M] [ContinuousSMul R M]

/-- If `M` is a topological module over `R` and `0` is a limit of invertible elements of `R`, then
`⊤` is the only submodule of `M` with a nonempty interior.
This is the case, e.g., if `R` is a nontrivially normed field. -/
theorem Submodule.eq_top_of_nonempty_interior' [NeBot (𝓝[{ x : R | IsUnit x }] 0)]
    (s : Submodule R M) (hs : (interior (s : Set M)).Nonempty) : s = ⊤ := by
  rcases hs with ⟨y, hy⟩
  refine Submodule.eq_top_iff'.2 fun x => ?_
  rw [mem_interior_iff_mem_nhds] at hy
  have : Tendsto (fun c : R => y + c • x) (𝓝[{ x : R | IsUnit x }] 0) (𝓝 (y + (0 : R) • x)) :=
    tendsto_const_nhds.add ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul tendsto_const_nhds)
  rw [zero_smul, add_zero] at this
  obtain ⟨_, hu : y + _ • _ ∈ s, u, rfl⟩ :=
    nonempty_of_mem (inter_mem (Filter.mem_map.1 (this hy)) self_mem_nhdsWithin)
  have hy' : y ∈ ↑s := mem_of_mem_nhds hy
  rwa [s.add_mem_iff_right hy', ← Units.smul_def, s.smul_mem_iff' u] at hu

variable (R M)

/-- Let `R` be a topological ring such that zero is not an isolated point (e.g., a nontrivially
normed field, see `NormedField.punctured_nhds_neBot`). Let `M` be a nontrivial module over `R`
such that `c • x = 0` implies `c = 0 ∨ x = 0`. Then `M` has no isolated points. We formulate this
using `NeBot (𝓝[≠] x)`.

This lemma is not an instance because Lean would need to find `[ContinuousSMul ?m_1 M]` with
unknown `?m_1`. We register this as an instance for `R = ℝ` in `Real.punctured_nhds_module_neBot`.
One can also use `haveI := Module.punctured_nhds_neBot R M` in a proof.
-/
theorem Module.punctured_nhds_neBot [Nontrivial M] [NeBot (𝓝[≠] (0 : R))] [NoZeroSMulDivisors R M]
    (x : M) : NeBot (𝓝[≠] x) := by
  rcases exists_ne (0 : M) with ⟨y, hy⟩
  suffices Tendsto (fun c : R => x + c • y) (𝓝[≠] 0) (𝓝[≠] x) from this.neBot
  refine Tendsto.inf ?_ (tendsto_principal_principal.2 <| ?_)
  · convert tendsto_const_nhds.add ((@tendsto_id R _).smul_const y)
    rw [zero_smul, add_zero]
  · intro c hc
    simpa [hy] using hc

end

section LatticeOps

variable {R M₁ M₂ : Type*} [SMul R M₁] [SMul R M₂] [u : TopologicalSpace R]
  {t : TopologicalSpace M₂} [ContinuousSMul R M₂]
  {F : Type*} [FunLike F M₁ M₂] [MulActionHomClass F R M₁ M₂] (f : F)

theorem continuousSMul_induced : @ContinuousSMul R M₁ _ u (t.induced f) :=
  let _ : TopologicalSpace M₁ := t.induced f
  IsInducing.continuousSMul ⟨rfl⟩ continuous_id (map_smul f _ _)

end LatticeOps

/-- The span of a separable subset with respect to a separable scalar ring is again separable. -/
lemma TopologicalSpace.IsSeparable.span {R M : Type*} [AddCommMonoid M] [Semiring R] [Module R M]
    [TopologicalSpace M] [TopologicalSpace R] [SeparableSpace R]
    [ContinuousAdd M] [ContinuousSMul R M] {s : Set M} (hs : IsSeparable s) :
    IsSeparable (Submodule.span R s : Set M) := by
  rw [Submodule.span_eq_iUnion_nat]
  refine .iUnion fun n ↦ .image ?_ ?_
  · have : IsSeparable {f : Fin n → R × M | ∀ (i : Fin n), f i ∈ Set.univ ×ˢ s} := by
      apply isSeparable_pi (fun i ↦ .prod (.of_separableSpace Set.univ) hs)
    rwa [Set.univ_prod] at this
  · apply continuous_finset_sum _ (fun i _ ↦ ?_)
    exact (continuous_fst.comp (continuous_apply i)).smul (continuous_snd.comp (continuous_apply i))

namespace Submodule

variable {R M : Type*}

instance [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] (s : Submodule R M) :
    ContinuousAdd s := AddSubmonoid.continuousAdd s.toAddSubmonoid

instance topologicalAddGroup [Ring R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] (S : Submodule R M) : IsTopologicalAddGroup S :=
  inferInstanceAs (IsTopologicalAddGroup S.toAddSubgroup)

instance [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousConstSMul R M] (s : Submodule R M) :
    ContinuousConstSMul R s where
  continuous_const_smul r :=
    ((continuous_const_smul r).comp continuous_subtype_val).subtype_mk _

instance [Semiring R] [AddCommMonoid M] [Module R M]
    [UniformSpace M] [UniformContinuousConstSMul R M] (s : Submodule R M) :
    UniformContinuousConstSMul R s where
  uniformContinuous_const_smul r :=
    ((uniformContinuous_const_smul r).comp uniformContinuous_subtype_val).subtype_mk _

end Submodule

section closure

variable {R : Type u} {M : Type v} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [ContinuousConstSMul R M]

theorem Submodule.mapsTo_smul_closure (s : Submodule R M) (c : R) :
    Set.MapsTo (c • ·) (closure s : Set M) (closure s) :=
  have : Set.MapsTo (c • ·) (s : Set M) s := fun _ h ↦ s.smul_mem c h
  this.closure (continuous_const_smul c)

theorem Submodule.smul_closure_subset (s : Submodule R M) (c : R) :
    c • closure (s : Set M) ⊆ closure (s : Set M) :=
  (s.mapsTo_smul_closure c).image_subset

variable [ContinuousAdd M]

/-- The (topological-space) closure of a submodule of a topological `R`-module `M` is itself
a submodule. -/
def Submodule.topologicalClosure (s : Submodule R M) : Submodule R M :=
  { s.toAddSubmonoid.topologicalClosure with
    smul_mem' := s.mapsTo_smul_closure }

@[simp]
lemma Submodule.mem_topologicalClosure_iff (s : Submodule R M) (x : M) :
    x ∈ s.topologicalClosure ↔ x ∈ closure s := by
  simp only [Submodule.topologicalClosure, AddSubmonoid.topologicalClosure,
    Submodule.coe_toAddSubmonoid, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk]

lemma Submodule.mem_topologicalClosure (s : Submodule R M) (L : s) :
    (L : M) ∈ s.topologicalClosure := by
  rw [Submodule.mem_topologicalClosure_iff]
  exact subset_closure L.2

@[simp, norm_cast]
theorem Submodule.topologicalClosure_coe (s : Submodule R M) :
    (s.topologicalClosure : Set M) = closure (s : Set M) :=
  rfl

theorem Submodule.le_topologicalClosure (s : Submodule R M) : s ≤ s.topologicalClosure :=
  subset_closure

theorem Submodule.closure_subset_topologicalClosure_span (s : Set M) :
    closure s ⊆ (span R s).topologicalClosure := by
  rw [Submodule.topologicalClosure_coe]
  exact closure_mono subset_span

theorem Submodule.isClosed_topologicalClosure (s : Submodule R M) :
    IsClosed (s.topologicalClosure : Set M) := isClosed_closure

theorem Submodule.topologicalClosure_minimal (s : Submodule R M) {t : Submodule R M} (h : s ≤ t)
    (ht : IsClosed (t : Set M)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

theorem Submodule.topologicalClosure_mono {s : Submodule R M} {t : Submodule R M} (h : s ≤ t) :
    s.topologicalClosure ≤ t.topologicalClosure :=
  closure_mono h

/-- The topological closure of a closed submodule `s` is equal to `s`. -/
theorem IsClosed.submodule_topologicalClosure_eq {s : Submodule R M} (hs : IsClosed (s : Set M)) :
    s.topologicalClosure = s :=
  SetLike.ext' hs.closure_eq

/-- A subspace is dense iff its topological closure is the entire space. -/
theorem Submodule.dense_iff_topologicalClosure_eq_top {s : Submodule R M} :
    Dense (s : Set M) ↔ s.topologicalClosure = ⊤ := by
  rw [← SetLike.coe_set_eq, dense_iff_closure_eq]
  simp

instance Submodule.topologicalClosure.completeSpace {M' : Type*} [AddCommMonoid M'] [Module R M']
    [UniformSpace M'] [ContinuousAdd M'] [ContinuousConstSMul R M'] [CompleteSpace M']
    (U : Submodule R M') : CompleteSpace U.topologicalClosure :=
  isClosed_closure.completeSpace_coe

/-- A maximal proper subspace of a topological module (i.e a `Submodule` satisfying `IsCoatom`)
is either closed or dense. -/
theorem Submodule.isClosed_or_dense_of_isCoatom (s : Submodule R M) (hs : IsCoatom s) :
    IsClosed (s : Set M) ∨ Dense (s : Set M) := by
  refine (hs.le_iff.mp s.le_topologicalClosure).symm.imp ?_ dense_iff_topologicalClosure_eq_top.mpr
  exact fun h ↦ h ▸ isClosed_closure

/-- Coercion from a submodule to its topological closure. -/
@[coe] def coeClosure {s : Submodule R M} :
    s → s.topologicalClosure := fun L ↦ ⟨L, Submodule.mem_topologicalClosure s L⟩

instance {s : Submodule R M} : Coe s s.topologicalClosure := ⟨coeClosure⟩

@[simp, norm_cast]
lemma coeClosure_add {s : Submodule R M} (x y : s) :
    ((x + y : s) : s.topologicalClosure)
      = (x : s.topologicalClosure) + (y : s.topologicalClosure) := by
  simp [coeClosure]

@[simp, norm_cast]
lemma coeClosure_sub {M R : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousConstSMul R M] {s : Submodule R M} (x y : s) :
    ((x - y : s) : s.topologicalClosure)
      = (x : s.topologicalClosure) - (y : s.topologicalClosure) := by
  simp only [coeClosure, AddSubgroupClass.coe_sub]
  norm_cast

@[simp, norm_cast]
lemma coeClosure_smul {s : Submodule R M} (r : R) (x : s) :
    ((r • x : s) : s.topologicalClosure) = r • (x : s.topologicalClosure) := by
  simp [coeClosure]

@[fun_prop, continuity]
lemma continuous_coeClosure (s : Submodule R M) :
    Continuous (coeClosure : s → s.topologicalClosure) := by
  unfold coeClosure
  fun_prop

end closure

section Completion

variable {M R F : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [UniformSpace M] [T0Space M] [ContinuousAdd M] [UniformContinuousConstSMul R M]
    [CompleteSpace M]
    [UniformSpace F] [T0Space F]
    {s : Submodule R M}

@[elab_as_elim]
theorem induction_topologicalClosure {p : s.topologicalClosure → Prop} (a : s.topologicalClosure)
    (hp : IsClosed { a | p a }) (ih : ∀ a : s, p a) :
    p a :=
  AbstractCompletion.induction_on (AbstractCompletion.closure s.carrier) a hp ih

@[elab_as_elim]
lemma induction_topologicalClosure₂
    {p : s.topologicalClosure → s.topologicalClosure → Prop} (a b : s.topologicalClosure)
    (hp : IsClosed { x : s.topologicalClosure × s.topologicalClosure | p x.1 x.2 })
    (ih : ∀ (a b : s), p a b) :
    p a b :=
  AbstractCompletion.induction_on₂ (AbstractCompletion.closure s.carrier)
    (AbstractCompletion.closure s.carrier) a b hp ih

lemma funext_topologicalClosure {f g : s.topologicalClosure → F} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ a : s, f a = g a) : f = g :=
  funext fun a ↦ induction_topologicalClosure a (isClosed_eq hf hg) h

/-- Extension of a function from a submodule to the closure of that submodule.
Meaningful only if `f` is uniformly continuous. -/
noncomputable
def closureExtension (s : Submodule R M) (f : s → F) : s.topologicalClosure → F :=
  AbstractCompletion.extend (AbstractCompletion.closure s.carrier) f

@[simp]
lemma closureExtension_coe {f : s → F} (hf : UniformContinuous f) (a : s) :
  closureExtension s f a = f a := (AbstractCompletion.closure s.carrier).extend_coe hf a

omit [T0Space F] in
@[fun_prop, continuity]
lemma continuous_closureExtension [CompleteSpace F] (s : Submodule R M) (f : s → F) :
    Continuous (closureExtension s f) := AbstractCompletion.continuous_extend _

end Completion

namespace Submodule

variable {ι R : Type*} {M : ι → Type*} [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, TopologicalSpace (M i)] [DecidableEq ι]

/-- If `s i` is a family of submodules, each is in its module,
then the closure of their span in the indexed product of the modules
is the product of their closures.

In case of a finite index type, this statement immediately follows from `Submodule.iSup_map_single`.
However, the statement is true for an infinite index type as well. -/
theorem closure_coe_iSup_map_single (s : ∀ i, Submodule R (M i)) :
    closure (↑(⨆ i, (s i).map (LinearMap.single R M i)) : Set (∀ i, M i)) =
      Set.univ.pi fun i ↦ closure (s i) := by
  rw [← closure_pi_set]
  refine (closure_mono ?_).antisymm <| closure_minimal ?_ isClosed_closure
  · exact SetLike.coe_mono <| iSup_map_single_le
  · simp only [Set.subset_def, mem_closure_iff]
    intro x hx U hU hxU
    rcases isOpen_pi_iff.mp hU x hxU with ⟨t, V, hV, hVU⟩
    refine ⟨∑ i ∈ t, Pi.single i (x i), hVU ?_, ?_⟩
    · simp_all [Finset.sum_pi_single]
    · exact sum_mem fun i hi ↦ mem_iSup_of_mem i <| mem_map_of_mem <| hx _ <| Set.mem_univ _

/-- If `s i` is a family of submodules, each is in its module,
then the closure of their span in the indexed product of the modules
is the product of their closures.

In case of a finite index type, this statement immediately follows from `Submodule.iSup_map_single`.
However, the statement is true for an infinite index type as well.

This version is stated in terms of `Submodule.topologicalClosure`,
thus assumes that `M i`s are topological modules over `R`.
However, the statement is true without assuming continuity of the operations,
see `Submodule.closure_coe_iSup_map_single` above. -/
theorem topologicalClosure_iSup_map_single [∀ i, ContinuousAdd (M i)]
    [∀ i, ContinuousConstSMul R (M i)] (s : ∀ i, Submodule R (M i)) :
    topologicalClosure (⨆ i, (s i).map (LinearMap.single R M i)) =
      pi Set.univ fun i ↦ (s i).topologicalClosure :=
  SetLike.coe_injective <| closure_coe_iSup_map_single _

end Submodule

section Pi

theorem LinearMap.continuous_on_pi {ι : Type*} {R : Type*} {M : Type*} [Finite ι] [Semiring R]
    [TopologicalSpace R] [AddCommMonoid M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] (f : (ι → R) →ₗ[R] M) : Continuous f := by
  cases nonempty_fintype ι
  classical
    -- for the proof, write `f` in the standard basis, and use that each coordinate is a continuous
    -- function.
    have : (f : (ι → R) → M) = fun x => ∑ i : ι, x i • f fun j => if i = j then 1 else 0 := by
      ext x
      exact f.pi_apply_eq_sum_univ x
    rw [this]
    refine continuous_finset_sum _ fun i _ => ?_
    exact (continuous_apply i).smul continuous_const

end Pi

section PointwiseLimits

variable {M₁ M₂ α R S : Type*} [TopologicalSpace M₂] [T2Space M₂] [Semiring R] [Semiring S]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module S M₂] [ContinuousConstSMul S M₂]

variable [ContinuousAdd M₂] {σ : R →+* S} {l : Filter α}

/-- Constructs a bundled linear map from a function and a proof that this function belongs to the
closure of the set of linear maps. -/
@[simps -fullyApplied]
def linearMapOfMemClosureRangeCoe (f : M₁ → M₂)
    (hf : f ∈ closure (Set.range ((↑) : (M₁ →ₛₗ[σ] M₂) → M₁ → M₂))) : M₁ →ₛₗ[σ] M₂ :=
  { addMonoidHomOfMemClosureRangeCoe f hf with
    map_smul' := (isClosed_setOf_map_smul M₁ M₂ σ).closure_subset_iff.2
      (Set.range_subset_iff.2 LinearMap.map_smulₛₗ) hf }

/-- Construct a bundled linear map from a pointwise limit of linear maps -/
@[simps! -fullyApplied]
def linearMapOfTendsto (f : M₁ → M₂) (g : α → M₁ →ₛₗ[σ] M₂) [l.NeBot]
    (h : Tendsto (fun a x => g a x) l (𝓝 f)) : M₁ →ₛₗ[σ] M₂ :=
  linearMapOfMemClosureRangeCoe f <|
    mem_closure_of_tendsto h <| Eventually.of_forall fun _ => Set.mem_range_self _

variable (M₁ M₂ σ)

theorem LinearMap.isClosed_range_coe : IsClosed (Set.range ((↑) : (M₁ →ₛₗ[σ] M₂) → M₁ → M₂)) :=
  isClosed_of_closure_subset fun f hf => ⟨linearMapOfMemClosureRangeCoe f hf, rfl⟩

end PointwiseLimits

section Quotient

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  (S : Submodule R M)

instance _root_.QuotientModule.Quotient.topologicalSpace : TopologicalSpace (M ⧸ S) :=
  inferInstanceAs (TopologicalSpace (Quotient S.quotientRel))

theorem isOpenMap_mkQ [ContinuousAdd M] : IsOpenMap S.mkQ :=
  QuotientAddGroup.isOpenMap_coe

theorem isOpenQuotientMap_mkQ [ContinuousAdd M] : IsOpenQuotientMap S.mkQ :=
  QuotientAddGroup.isOpenQuotientMap_mk

instance topologicalAddGroup_quotient [IsTopologicalAddGroup M] : IsTopologicalAddGroup (M ⧸ S) :=
  inferInstanceAs <| IsTopologicalAddGroup (M ⧸ S.toAddSubgroup)

instance continuousSMul_quotient [TopologicalSpace R] [IsTopologicalAddGroup M]
    [ContinuousSMul R M] : ContinuousSMul R (M ⧸ S) where
  continuous_smul := by
    rw [← (IsOpenQuotientMap.id.prodMap S.isOpenQuotientMap_mkQ).continuous_comp_iff]
    exact continuous_quot_mk.comp continuous_smul

instance t3_quotient_of_isClosed [IsTopologicalAddGroup M] [IsClosed (S : Set M)] :
    T3Space (M ⧸ S) :=
  letI : IsClosed (S.toAddSubgroup : Set M) := ‹_›
  QuotientAddGroup.instT3Space S.toAddSubgroup

end Submodule

end Quotient
