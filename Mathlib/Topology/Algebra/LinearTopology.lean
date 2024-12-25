/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Anatole Dedecker
-/

import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Linear topologies on modules and rings

Following Bourbaki, *Algebra II*, chapter 4, §2, n° 3, a topology on a ring `R` is *linear* if
it is invariant by translation and admits a basis of neighborhoods of 0 consisting of
two-sided ideals.

- `tendsto_mul_zero_of_left`: for `f, g : ι → R` such that `f i` converges to `0`,
`f i * g i` converges to `0`.

- `tendsto_mul_zero_of_right`: for `f, g : ι → R` such that `g i` converges to `0`,
`f i * g i` converges to `0`.

## Instances

- A discrete topology is a linear topology

## Note on the implementation

The definition of Bourbaki doesn't presuppose, but implies, that a linear topology on a ring `R` is
a ring topology. However, in some of our lemmas, we already assume that `R` is a topological ring.
This unnecessary assumption will be made unnecessary by results in the ongoing PR #18437.
Anyway, the idea will be to first define a topology on `R`, and then
prove that it makes `R` a topological ring, and that it is a linear topology.

TODO: SMulCommClass and explicitness
-/

open scoped Topology
open Filter

namespace IsLinearTopology

section Module

variable {R R' M : Type*} [Ring R] [Ring R'] [AddCommGroup M] [Module R M] [Module R' M]
  [SMulCommClass R R' M] [TopologicalSpace M]

variable (R M) in
/-- Consider a (left-)module `M` over a ring `R`. A topology on `M` is *`R`-linear*
if the open sub-`R`-modules of `M` form a basis of neighborhoods of zero.

Typically one would also that the topology is invariant by translation (`ContinuousConstVAdd M M`),
or equivalently that `M` is a topological group, but we do not assume it for the definition.

In particular, we say that a topology on the ring `R` is *linear* if it is both
`R`-linear and `Rᵐᵒᵖ`-linear for the obvious module structures. To spell this in Lean,
simply use `[IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R]`. -/
class _root_.IsLinearTopology where
  hasBasis_submodule' : (𝓝 (0 : M)).HasBasis
    (fun N : Submodule R M ↦ (N : Set M) ∈ 𝓝 0) (fun N : Submodule R M ↦ (N : Set M))

variable (R) in
lemma hasBasis_submodule [IsLinearTopology R M] : (𝓝 (0 : M)).HasBasis
    (fun N : Submodule R M ↦ (N : Set M) ∈ 𝓝 0) (fun N : Submodule R M ↦ (N : Set M)) :=
  IsLinearTopology.hasBasis_submodule'

variable (R) in
lemma hasBasis_open_submodule [ContinuousAdd M] [IsLinearTopology R M] :
    (𝓝 (0 : M)).HasBasis
      (fun N : Submodule R M ↦ IsOpen (N : Set M)) (fun N : Submodule R M ↦ (N : Set M)) :=
  hasBasis_submodule R |>.congr
    (fun N ↦ ⟨N.toAddSubgroup.isOpen_of_mem_nhds, fun hN ↦ hN.mem_nhds (zero_mem N)⟩)
    (fun _ _ ↦ rfl)

variable (R) in
/-- A variant of `IsLinearTopology.mk_of_hasBasis` asking for an explicit proof that `S`
is a class of submodules instead of relying on (fragile) typeclass inference of `SMulCommClass`. -/
lemma mk_of_hasBasis' {ι : Sort*} {S : Type*} [SetLike S M]
    [AddSubmonoidClass S M]
    {p : ι → Prop} {s : ι → S}
    (h : (𝓝 0).HasBasis p (fun i ↦ (s i : Set M)))
    (hsmul : ∀ s : S, ∀ r : R, ∀ m ∈ s, r • m ∈ s) :
    IsLinearTopology R M where
  hasBasis_submodule' := h.to_hasBasis
    (fun i hi ↦ ⟨
      { carrier := s i,
        add_mem' := add_mem,
        zero_mem' := zero_mem _,
        smul_mem' := hsmul _},
      h.mem_of_mem hi, subset_rfl⟩)
    (fun _ ↦ h.mem_iff.mp)

variable (R) in
/-- To show that `M` is linearly-topologized as an `R`-module, it suffices to show
that it has a basis of neighborhoods of zero made of `R`-submodules.

Note: for technical reasons detailed in the module docstring, Lean sometimes struggle to find the
right `SMulMemClass` instance. See `IsLinearTopology.mk_of_hasBasis'` for a more
explicit variant. -/
lemma mk_of_hasBasis {ι : Sort*} {S : Type*} [SetLike S M]
    [SMulMemClass S R M] [AddSubmonoidClass S M]
    {p : ι → Prop} {s : ι → S}
    (h : (𝓝 0).HasBasis p (fun i ↦ (s i : Set M))) :
    IsLinearTopology R M :=
  mk_of_hasBasis' R h fun _ ↦ SMulMemClass.smul_mem

theorem _root_.isLinearTopology_iff_hasBasis_submodule :
    IsLinearTopology R M ↔ (𝓝 0).HasBasis
      (fun N : Submodule R M ↦ (N : Set M) ∈ 𝓝 0) (fun N : Submodule R M ↦ (N : Set M)) :=
  ⟨fun _ ↦ hasBasis_submodule R, fun h ↦ .mk_of_hasBasis R h⟩

theorem _root_.isLinearTopology_iff_hasBasis_open_submodule [ContinuousAdd M] :
    IsLinearTopology R M ↔ (𝓝 0).HasBasis
      (fun N : Submodule R M ↦ IsOpen (N : Set M)) (fun N : Submodule R M ↦ (N : Set M)) :=
  ⟨fun _ ↦ hasBasis_open_submodule R, fun h ↦ .mk_of_hasBasis R h⟩

/-- The discrete topology on any `R`-module is `R`-linear. -/
instance [DiscreteTopology M] : IsLinearTopology R M :=
  have : HasBasis (𝓝 0 : Filter M) (fun _ ↦ True) (fun (_ : Unit) ↦ (⊥ : Submodule R M)) := by
    rw [nhds_discrete]
    exact hasBasis_pure _
  mk_of_hasBasis R this

variable (R R') in
open Set Pointwise in
/-- Assume that `M` is a module over two rings `R` and `R'`, and that its topology
is linear with respect to each of these rings. Then, it has a basis of neighborhoods of zero
made of sub-`(R, R')`-bimodules.

The proof is inspired by lemma 9 in [I. Kaplansky, *Topological Rings*](kaplansky_topological_1947).
TODO: Formalize the lemma in its full strength.

Note: due to the lack of a satisfying theory of bimodules, we use `AddSubgroup`s with
extra conditions. -/
lemma hasBasis_subbimodule [IsLinearTopology R M] [IsLinearTopology R' M] :
    (𝓝 (0 : M)).HasBasis
      (fun I : AddSubgroup M ↦ (I : Set M) ∈ 𝓝 0 ∧
        (∀ r : R, ∀ x ∈ I, r • x ∈ I) ∧ (∀ r' : R', ∀ x ∈ I, r' • x ∈ I))
      (fun I : AddSubgroup M ↦ (I : Set M)) := by
  -- Start from a neighborhood `V`. It contains some open sub-`R`-module `I`.
  refine IsLinearTopology.hasBasis_submodule R |>.to_hasBasis (fun I hI ↦ ?_)
    (fun I hI ↦ ⟨{I with smul_mem' := fun r x hx ↦ hI.2.1 r x hx}, hI.1, subset_rfl⟩)
  -- `I` itself is a neighborhood of zero, so it contains some open sub-`R'`-module `J`.
  rcases (hasBasis_submodule R').mem_iff.mp hI with ⟨J, hJ, J_sub_I⟩
  set uR : Set R := univ -- Convenient to avoid type ascriptions
  set uR' : Set R' := univ
  have hRR : uR * uR ⊆ uR := subset_univ _
  have hRR' : uR' * uR' ⊆ uR' := subset_univ _
  have hRI : uR • (I : Set M) ⊆ I := smul_subset_iff.mpr fun x _ i hi ↦ I.smul_mem x hi
  have hJR : uR' • (J : Set M) ⊆ J := smul_subset_iff.mpr fun x _ j hj ↦ J.smul_mem x hj
  have hRJ : uR • (J : Set M) ⊆ I := subset_trans (smul_subset_smul_left J_sub_I) hRI
  -- Note that, on top of the obvious `R • I ⊆ I` and `R' • J ⊆ J`, we have `R • J ⊆ R • I ⊆ I`.
  -- Now set `S := J ∪ (R • J)`. We have:
  -- 1. `R • S = (R • J) ∪ (R • R • J) ⊆ R • J ⊆ S`.
  -- 2. `R' • S = (R' • J) ∪ (R' • R • J) ⊆ J ∪ (R • R' • J) ⊆ J ∪ (R • J) = S`.
  -- Hence the subgroup `A` generated by `S` is a sub-`(R, R')`-bimodule,
  -- which we claim is open and contained in `I`.
  -- Indeed, we have `J ⊆ S ⊆ I`, hence `J ⊆ A ⊆ I`, and `J` is open by hypothesis.
  set S : Set M := J ∪ uR • J
  have S_sub_I : S ⊆ I := union_subset J_sub_I hRJ
  have hRS : uR • S ⊆ S := calc
    uR • S = uR • (J : Set M) ∪ (uR * uR) • (J : Set M) := by simp_rw [S, smul_union, mul_smul]
    _ ⊆ uR • (J : Set M) ∪ uR • (J : Set M) := by gcongr
    _ = uR • (J : Set M) := union_self _
    _ ⊆ S := subset_union_right
  have hRS' : uR' • S ⊆ S := calc
    uR' • S = uR' • (J : Set M) ∪ uR • uR' • (J : Set M) := by simp_rw [S, smul_union, smul_comm]
    _ ⊆ J ∪ uR • J := by gcongr
    _ = S := rfl
  set A : AddSubgroup M := .closure S
  have hRA : ∀ r : R, ∀ i ∈ A, r • i ∈ A := fun r i hi ↦ by
    refine AddSubgroup.closure_induction (fun x hx => ?base) ?zero (fun x y _ _ hx hy ↦ ?add)
      (fun x _ hx ↦ ?neg) hi
    case base => exact AddSubgroup.subset_closure <| hRS <| Set.smul_mem_smul trivial hx
    case zero => simp_rw [smul_zero]; exact zero_mem _
    case add => simp_rw [smul_add]; exact add_mem hx hy
    case neg => simp_rw [smul_neg]; exact neg_mem hx
  have hRA' : ∀ r' : R', ∀ i ∈ A, r' • i ∈ A := fun r' i hi ↦ by
    refine AddSubgroup.closure_induction (fun x hx => ?base) ?zero (fun x y _ _ hx hy ↦ ?add)
      (fun x _ hx ↦ ?neg) hi
    case base => exact AddSubgroup.subset_closure <| hRS' <| Set.smul_mem_smul trivial hx
    case zero => simp_rw [smul_zero]; exact zero_mem _
    case add => simp_rw [smul_add]; exact add_mem hx hy
    case neg => simp_rw [smul_neg]; exact neg_mem hx
  have A_sub_I : (A : Set M) ⊆ I := by
    exact I.toAddSubgroup.closure_le.mpr S_sub_I
  have J_sub_A : (J : Set M) ⊆ A := by
    exact subset_trans subset_union_left AddSubgroup.subset_closure
  exact ⟨A, ⟨mem_of_superset hJ J_sub_A, hRA, hRA'⟩, A_sub_I⟩

variable (R R') in
open Set Pointwise in
/-- A variant of `IsLinearTopology.hasBasis_subbimodule` using `IsOpen I` instead of `I ∈ 𝓝 0`. -/
lemma hasBasis_open_subbimodule [ContinuousAdd M] [IsLinearTopology R M] [IsLinearTopology R' M] :
    (𝓝 (0 : M)).HasBasis
      (fun I : AddSubgroup M ↦ IsOpen (I : Set M) ∧
        (∀ r : R, ∀ x ∈ I, r • x ∈ I) ∧ (∀ r' : R', ∀ x ∈ I, r' • x ∈ I))
      (fun I : AddSubgroup M ↦ (I : Set M)) :=
  hasBasis_subbimodule R R' |>.congr
    (fun N ↦ and_congr_left' ⟨N.isOpen_of_mem_nhds, fun hN ↦ hN.mem_nhds (zero_mem N)⟩)
    (fun _ _ ↦ rfl)

-- Even though `R` can be recovered from `a`, the nature of this lemma means that `a` will
-- often be left for Lean to infer, so making `R` explicit is useful in practice.
variable (R) in
/-- If `M` is a linearly topologized `R`-module and `i ↦ m i` tends to zero,
then `i ↦ a i • m i` still tends to zero for any family `a : ι → R`. -/
theorem tendsto_smul_zero [IsLinearTopology R M] {ι : Type*} {f : Filter ι}
    (a : ι → R) (m : ι → M) (ha : Tendsto m f (𝓝 0)) :
    Tendsto (a • m) f (𝓝 0) := by
  rw [hasBasis_submodule R |>.tendsto_right_iff] at ha ⊢
  intro I hI
  filter_upwards [ha I hI] with i ai_mem
  exact I.smul_mem _ ai_mem

end Module

section Ring

variable {R : Type*} [Ring R] [TopologicalSpace R]

theorem hasBasis_ideal [IsLinearTopology R R] :
    (𝓝 0).HasBasis (fun I : Ideal R ↦ (I : Set R) ∈ 𝓝 0) (fun I : Ideal R ↦ (I : Set R)) :=
  hasBasis_submodule R

theorem hasBasis_open_ideal [ContinuousAdd R] [IsLinearTopology R R] :
    (𝓝 0).HasBasis (fun I : Ideal R ↦ IsOpen (I : Set R)) (fun I : Ideal R ↦ (I : Set R)) :=
  hasBasis_open_submodule R

theorem _root_.isLinearTopology_iff_hasBasis_ideal :
    IsLinearTopology R R ↔ (𝓝 0).HasBasis
      (fun I : Ideal R ↦ (I : Set R) ∈ 𝓝 0) (fun I : Ideal R ↦ (I : Set R)) :=
  isLinearTopology_iff_hasBasis_submodule

theorem _root_.isLinearTopology_iff_hasBasis_open_ideal [TopologicalRing R] :
    IsLinearTopology R R ↔ (𝓝 0).HasBasis
      (fun I : Ideal R ↦ IsOpen (I : Set R)) (fun I : Ideal R ↦ (I : Set R)) :=
  isLinearTopology_iff_hasBasis_open_submodule

open Set Pointwise in
/-- If a ring `R` is linearly ordered as a left *and* right module over itself,
then it has a basis of neighborhoods of zero made of *two-sided* ideals.

This is usually called a *linearly topologized ring*, but we do not add a specific spelling:
you should use `[IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R]` instead. -/
lemma hasBasis_twoSidedIdeal [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    (𝓝 (0 : R)).HasBasis (fun I : TwoSidedIdeal R ↦ (I : Set R) ∈ 𝓝 0)
      (fun I : TwoSidedIdeal R ↦ (I : Set R)) :=
  hasBasis_subbimodule R Rᵐᵒᵖ |>.to_hasBasis
    (fun I ⟨hI, hRI, hRI'⟩ ↦ ⟨.mk' I (zero_mem _) add_mem neg_mem (hRI _ _) (hRI' _ _),
      by simpa using hI, by simp⟩)
    (fun I hI ↦ ⟨I.asIdeal.toAddSubgroup,
      ⟨hI, I.mul_mem_left, fun r x hx ↦ I.mul_mem_right x (r.unop) hx⟩, subset_rfl⟩)

lemma hasBasis_open_twoSidedIdeal [ContinuousAdd R]
    [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    (𝓝 (0 : R)).HasBasis
      (fun I : TwoSidedIdeal R ↦ IsOpen (I : Set R)) (fun I : TwoSidedIdeal R ↦ (I : Set R)) :=
  hasBasis_twoSidedIdeal.congr
    (fun I ↦ ⟨I.asIdeal.toAddSubgroup.isOpen_of_mem_nhds, fun hI ↦ hI.mem_nhds (zero_mem I)⟩)
    (fun _ _ ↦ rfl)

theorem _root_.isLinearTopology_iff_hasBasis_twoSidedIdeal :
    IsLinearTopology R R ∧ IsLinearTopology Rᵐᵒᵖ R ↔
      (𝓝 0).HasBasis
        (fun I : TwoSidedIdeal R ↦ (I : Set R) ∈ 𝓝 0) (fun I : TwoSidedIdeal R ↦ (I : Set R)) :=
  ⟨fun ⟨_, _⟩ ↦ hasBasis_twoSidedIdeal, fun h ↦
    ⟨.mk_of_hasBasis' R h fun I r x hx ↦ I.mul_mem_left r x hx,
      .mk_of_hasBasis' Rᵐᵒᵖ h fun I r x hx ↦ I.mul_mem_right x r.unop hx⟩⟩

theorem _root_.isLinearTopology_iff_hasBasis_open_twoSidedIdeal [ContinuousAdd R] :
    IsLinearTopology R R ∧ IsLinearTopology Rᵐᵒᵖ R ↔ (𝓝 0).HasBasis
      (fun I : TwoSidedIdeal R ↦ IsOpen (I : Set R)) (fun I : TwoSidedIdeal R ↦ (I : Set R)) :=
  ⟨fun ⟨_, _⟩ ↦ hasBasis_open_twoSidedIdeal, fun h ↦
    ⟨.mk_of_hasBasis' R h fun I r x hx ↦ I.mul_mem_left r x hx,
      .mk_of_hasBasis' Rᵐᵒᵖ h fun I r x hx ↦ I.mul_mem_right x r.unop hx⟩⟩

theorem tendsto_mul_zero_of_left [IsLinearTopology Rᵐᵒᵖ R] {ι : Type*} {f : Filter ι}
    (a b : ι → R) (ha : Tendsto a f (𝓝 0)) :
    Tendsto (a * b) f (𝓝 0) :=
  tendsto_smul_zero (R := Rᵐᵒᵖ) _ _ ha

theorem tendsto_mul_zero_of_right [IsLinearTopology R R] {ι : Type*} {f : Filter ι}
    (a b : ι → R) (hb : Tendsto b f (𝓝 0)) :
    Tendsto (a * b) f (𝓝 0) :=
  tendsto_smul_zero (R := R) _ _ hb

end Ring

section CommRing

variable {R M : Type*} [CommRing R] [TopologicalSpace R]

/-- If `R` is commutative and left-linearly topologized, it is also right-linearly topologized. -/
instance (priority := 100) [IsLinearTopology R R] :
    IsLinearTopology Rᵐᵒᵖ R :=
  mk_of_hasBasis' Rᵐᵒᵖ (IsLinearTopology.hasBasis_ideal) (fun I _ _ ↦ I.mul_mem_right _)

end CommRing

end IsLinearTopology
