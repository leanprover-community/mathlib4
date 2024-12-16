/-
Copyright (c) 2024 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Delta-generated topological spaces

This file defines delta-generated spaces, as topological spaces whose topology is coinduced by all
maps from euclidean spaces into them. This is the strongest topological property that holds for
all CW-complexes and is closed under quotients and disjoint unions; every delta-generated space is
locally path-connected, sequential and in particular compactly generated.

See https://ncatlab.org/nlab/show/Delta-generated+topological+space.

Adapted from `Mathlib.Topology.Compactness.CompactlyGeneratedSpace`.

## TODO
* All locally convex spaces and convex subsets thereof are delta-generated, in particular the
  standard simplices and the unit interval.
* CW-complexes are delta-generated, even when they're not first-countable.
-/

variable {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]

open TopologicalSpace Topology unitInterval

/-- The topology coinduced by all maps from ℝⁿ into a space. -/
def TopologicalSpace.deltaGenerated (X : Type*) [TopologicalSpace X] : TopologicalSpace X :=
  ⨆ f : (n : ℕ) × C(((Fin n) → ℝ), X), coinduced f.2 inferInstance

/-- The delta-generated topology is also coinduced by a single map out of a sigma type. -/
lemma deltaGenerated_eq_coinduced : deltaGenerated X = coinduced
    (fun x : (f : (n : ℕ) × C(Fin n → ℝ, X)) × (Fin f.1 → ℝ) ↦ x.1.2 x.2) inferInstance := by
  rw [deltaGenerated, instTopologicalSpaceSigma, coinduced_iSup]; rfl

/-- The delta-generated topology is at least as fine as the original one. -/
lemma deltaGenerated_le : deltaGenerated X ≤ tX :=
  iSup_le_iff.mpr fun f ↦ f.2.continuous.coinduced_le

/-- A set is open in `deltaGenerated X` iff all its preimages under continuous functions ℝⁿ → X are
  open. -/
lemma isOpen_deltaGenerated_iff {u : Set X} :
    IsOpen[deltaGenerated X] u ↔ ∀ n (p : C(Fin n → ℝ, X)), IsOpen (p ⁻¹' u) := by
  simp_rw [deltaGenerated, isOpen_iSup_iff, isOpen_coinduced, Sigma.forall]

/-- A map from ℝⁿ to X is continuous iff it is continuous regarding the
  delta-generated topology on X. Outside of this file, use the more general
  `continuous_to_deltaGenerated` instead. -/
private lemma continuous_euclidean_to_deltaGenerated {n : ℕ} {f : (Fin n → ℝ) → X} :
    Continuous[_, deltaGenerated X] f ↔ Continuous f := by
  simp_rw [continuous_iff_coinduced_le]
  refine ⟨fun h ↦ h.trans deltaGenerated_le, fun h ↦ ?_⟩
  simp_rw [deltaGenerated]
  exact le_iSup_of_le (i := ⟨n, f, continuous_iff_coinduced_le.mpr h⟩) le_rfl

/-- `deltaGenerated` is idempotent as a function `TopologicalSpace X → TopologicalSpace X`. -/
lemma deltaGenerated_deltaGenerated_eq :
    @deltaGenerated X (deltaGenerated X) = deltaGenerated X := by
  ext u; simp_rw [isOpen_deltaGenerated_iff]; refine forall_congr' fun n ↦ ?_
  -- somewhat awkward because `ContinuousMap` doesn't play well with multiple topologies.
  refine ⟨fun h p ↦ h <| @ContinuousMap.mk _ _ _ (_) p ?_, fun h p ↦ h ⟨p, ?_⟩⟩
  · exact continuous_euclidean_to_deltaGenerated.mpr p.2
  · exact continuous_euclidean_to_deltaGenerated.mp <| @ContinuousMap.continuous_toFun _ _ _ (_) p

/-- A space is delta-generated if its topology is equal to the delta-generated topology, i.e.
  coinduced by all continuous maps ℝⁿ → X. Since the delta-generated topology is always finer
  than the original one, it suffices to show that it is also coarser. -/
class DeltaGeneratedSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  le_deltaGenerated : t ≤ deltaGenerated X

lemma eq_deltaGenerated [DeltaGeneratedSpace X] : tX = deltaGenerated X :=
  eq_of_le_of_le DeltaGeneratedSpace.le_deltaGenerated deltaGenerated_le

/-- A subset of a delta-generated space is open iff its preimage is open for every
  continuous map from ℝⁿ to X. -/
lemma DeltaGeneratedSpace.isOpen_iff [DeltaGeneratedSpace X] {u : Set X} :
    IsOpen u ↔ ∀ (n : ℕ) (p : ContinuousMap ((Fin n) → ℝ) X), IsOpen (p ⁻¹' u) := by
  nth_rewrite 1 [eq_deltaGenerated (X := X)]; exact isOpen_deltaGenerated_iff

/-- A map out of a delta-generated space is continuous iff it preserves continuity of maps
  from ℝⁿ into X. -/
lemma DeltaGeneratedSpace.continuous_iff [DeltaGeneratedSpace X] {f : X → Y} :
    Continuous f ↔ ∀ (n : ℕ) (p : C(((Fin n) → ℝ), X)), Continuous (f ∘ p) := by
  simp_rw [continuous_iff_coinduced_le]
  nth_rewrite 1 [eq_deltaGenerated (X := X), deltaGenerated]
  simp [coinduced_compose]
  constructor
  · intro h n p; apply h ⟨n, p⟩
  · rintro h ⟨n, p⟩; apply h n p

/-- A map out of a delta-generated space is continuous iff it is continuous with respect
  to the delta-generated topology on the codomain. -/
lemma continuous_to_deltaGenerated [DeltaGeneratedSpace X] {f : X → Y} :
    Continuous[_, deltaGenerated Y] f ↔ Continuous f := by
  simp_rw [DeltaGeneratedSpace.continuous_iff, continuous_euclidean_to_deltaGenerated]

/-- The delta-generated topology on `X` does in fact turn `X` into a delta-generated space. -/
lemma deltaGeneratedSpace_deltaGenerated {X : Type*} {t : TopologicalSpace X} :
    @DeltaGeneratedSpace X (@deltaGenerated X t) := by
  let _ := @deltaGenerated X t; constructor; rw [@deltaGenerated_deltaGenerated_eq X t]

lemma deltaGenerated_mono {X : Type*} {t₁ t₂ : TopologicalSpace X} (h : t₁ ≤ t₂) :
    @deltaGenerated X t₁ ≤ @deltaGenerated X t₂ := by
  rw [← continuous_id_iff_le, @continuous_to_deltaGenerated _ _
    (@deltaGenerated X t₁) t₂ deltaGeneratedSpace_deltaGenerated id]
  exact continuous_id_iff_le.2 <| (@deltaGenerated_le X t₁).trans h

namespace DeltaGeneratedSpace

/-- Type synonym to be equipped with the delta-generated topology. -/
def of (X : Type*) := X

instance : TopologicalSpace (of X) := deltaGenerated X

instance : DeltaGeneratedSpace (of X) :=
  deltaGeneratedSpace_deltaGenerated

/-- The natural map from `DeltaGeneratedSpace.of X` to `X`. -/
def counit : (of X) → X := id

lemma continuous_counit : Continuous (counit : _ → X) := by
  rw [continuous_iff_coinduced_le]; exact deltaGenerated_le

/-- Delta-generated spaces are locally path-connected. -/
instance [DeltaGeneratedSpace X] : LocPathConnectedSpace X := by
  rw [eq_deltaGenerated (X := X), deltaGenerated_eq_coinduced]
  exact LocPathConnectedSpace.coinduced _

/-- Delta-generated spaces are sequential. -/
instance [DeltaGeneratedSpace X] : SequentialSpace X := by
  rw [eq_deltaGenerated (X := X)]
  exact SequentialSpace.iSup fun p ↦ SequentialSpace.coinduced p.2

end DeltaGeneratedSpace

omit tY in
/-- Any topology coinduced by a delta-generated topology is delta-generated. -/
lemma DeltaGeneratedSpace.coinduced [DeltaGeneratedSpace X] (f : X → Y) :
    @DeltaGeneratedSpace Y (tX.coinduced f) :=
  let _ := tX.coinduced f
  ⟨(continuous_to_deltaGenerated.2 continuous_coinduced_rng).coinduced_le⟩

/-- Suprema of delta-generated topologies are delta-generated. -/
protected lemma DeltaGeneratedSpace.iSup {X : Type*} {ι : Sort*} {t : ι → TopologicalSpace X}
    (h : ∀ i, @DeltaGeneratedSpace X (t i)) : @DeltaGeneratedSpace X (⨆ i, t i) :=
  let _ := ⨆ i, t i
  ⟨iSup_le_iff.2 fun i ↦ (h i).le_deltaGenerated.trans <| deltaGenerated_mono <| le_iSup t i⟩

/-- Suprema of delta-generated topologies are delta-generated. -/
protected lemma DeltaGeneratedSpace.sup {X : Type*} {t₁ t₂ : TopologicalSpace X}
    (h₁ : @DeltaGeneratedSpace X t₁) (h₂ : @DeltaGeneratedSpace X t₂) :
    @DeltaGeneratedSpace X (t₁ ⊔ t₂) := by
  rw [sup_eq_iSup]
  exact .iSup <| Bool.forall_bool.2 ⟨h₂, h₁⟩

/-- Quotients of delta-generated spaces are delta-generated. -/
lemma Topology.IsQuotientMap.deltaGeneratedSpace [DeltaGeneratedSpace X]
    {f : X → Y} (h : IsQuotientMap f) : DeltaGeneratedSpace Y :=
  h.2 ▸ DeltaGeneratedSpace.coinduced f

/-- Quotients of delta-generated spaces are delta-generated. -/
instance Quot.deltaGeneratedSpace [DeltaGeneratedSpace X] {r : X → X → Prop} :
    DeltaGeneratedSpace (Quot r) :=
  isQuotientMap_quot_mk.deltaGeneratedSpace

/-- Quotients of delta-generated spaces are delta-generated. -/
instance Quotient.deltaGeneratedSpace [DeltaGeneratedSpace X] {s : Setoid X} :
    DeltaGeneratedSpace (Quotient s) :=
  isQuotientMap_quotient_mk'.deltaGeneratedSpace

/-- Disjoint unions of delta-generated spaces are delta-generated. -/
instance Sum.deltaGeneratedSpace [DeltaGeneratedSpace X] [DeltaGeneratedSpace Y] :
    DeltaGeneratedSpace (X ⊕ Y) :=
  DeltaGeneratedSpace.sup (.coinduced Sum.inl) (.coinduced Sum.inr)

/-- Disjoint unions of delta-generated spaces are delta-generated. -/
instance Sigma.deltaGeneratedSpace {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, DeltaGeneratedSpace (X i)] : DeltaGeneratedSpace (Σ i, X i) :=
  .iSup fun _ ↦ .coinduced _

/-- In a first-countable locally path-connected space, every point has a neighbourhood basis
  that is a decreasing sequence of path-connected sets.
  TODO: move to the right file. -/
lemma LocPathConnectedSpace.exists_isPathConnected_antitone_basis {X : Type*} [TopologicalSpace X]
    [LocPathConnectedSpace X] [FirstCountableTopology X] (x : X) :
    ∃ (b : ℕ → Set X), (𝓝 x).HasAntitoneBasis b ∧ ∀ i, IsPathConnected (b i) := by
  let ⟨b, hb⟩ := (𝓝 x).exists_antitone_basis
  refine ⟨pathComponentIn x ∘ b, ⟨?_, ?_⟩, ?_⟩
  · refine hb.1.to_subset (fun _ _ ↦ pathComponentIn_subset) fun _ _ ↦ ?_
    exact pathComponentIn_mem_nhds <| hb.1.mem_of_mem trivial
  · exact fun _ _ h ↦ pathComponentIn_mono <| hb.2 h
  · exact fun i ↦ isPathConnected_pathComponentIn <| mem_of_mem_nhds <| hb.mem i

/-- The concatenation of countably many paths leading up to some point `x`. -/
noncomputable def Path.sigmaConcat {X : Type*} [TopologicalSpace X] {s : ℕ → X}
    (γ : (n : ℕ) → Path (s n) (s n.succ)) (x : X) {b : ℕ → Set X} (hb : (𝓝 x).HasAntitoneBasis b)
    (hγ : ∀ n t, γ n t ∈ b n) : Path (s 0) x where
  toFun t := by
    refine if ht : t < 1 then ?_ else x
    have ht' : 0 < σ t := by rw [unitInterval.lt_symm_comm]; simp [ht]
    let n := Nat.floor (- Real.logb 2 (σ t))
    let t' : I := ⟨2 * (1 - σ t * 2 ^ (n : ℝ)), by
      have hn : (n : ℝ) ≤ _ := Nat.floor_le (a := - Real.logb 2 (σ t)) <|
        Left.nonneg_neg_iff.2 <| Real.logb_nonpos one_lt_two (σ t).2.1 (σ t).2.2
      have h : (2 : ℝ) ^ (n : ℝ) ≤ (σ t).1 ⁻¹ := by
        refine (Real.rpow_le_rpow_of_exponent_le one_le_two hn).trans ?_
        rw [Real.rpow_neg zero_le_two, Real.rpow_logb two_pos (by simp) (by simp [ht])]
      have h' : (σ t) * (2 : ℝ) ^ (n : ℝ) ≤ 1 := by
        refine (mul_le_mul_of_nonneg_left h (σ t).2.1).trans (mul_inv_cancel₀ ?_).le
        exact (unitInterval.coe_pos.2 ht').ne.symm
      linarith
      /-simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, sub_nonneg]
      refine (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two hn)
        (σ t).2.1).trans ?_
      rw [Real.rpow_neg zero_le_two, Real.rpow_logb two_pos (by simp) (by simp [ht])]
      refine (mul_inv_cancel₀ ?_).le
      rw [unitInterval.coe_ne_zero, ← unitInterval.pos_iff_ne_zero]
      exact ht'-/, by
      have hn : _ < (n.succ : ℝ) := Nat.lt_succ_floor _
      have h : (σ t).1⁻¹ ≤ 2 * 2 ^ (n : ℝ) := by
        rw [Real.rpow_natCast, ← pow_succ', ← Real.rpow_natCast]
        refine (Eq.le ?_).trans <| Real.rpow_le_rpow_of_exponent_le one_le_two hn.le
        rw [Real.rpow_neg zero_le_two, Real.rpow_logb two_pos (by simp) (by simp [ht])]
      suffices h : 1 ≤ (σ t) * (2 * (2 : ℝ) ^ (n : ℝ)) by rw [mul_left_comm] at h; linarith
      refine (mul_inv_cancel₀ ?_).symm.le.trans <| mul_le_mul_of_nonneg_left h (σ t).2.1
      exact (unitInterval.coe_pos.2 ht').ne.symm⟩
    exact γ n t'
  continuous_toFun := by
    refine continuous_iff_continuousAt.2 fun t ↦ ?_
    by_cases ht : t < 1
    · sorry
    · rw [unitInterval.lt_one_iff_ne_one, not_ne_iff] at ht
      --simp_rw [eq_false ht.not_lt]
      sorry
  source' := by simp
  target' := by simp

/-- Evaluating `Path.sigmaConcat` at 1-(1-t/2)/2^n yields `γ n t`. -/
lemma Path.sigmaConcat_applyAt {X : Type*} [TopologicalSpace X] {s : ℕ → X}
    {γ : (n : ℕ) → Path (s n) (s n.succ)} {x : X} {b : ℕ → Set X} {hb : (𝓝 x).HasAntitoneBasis b}
    {hγ : ∀ n t, γ n t ∈ b n} (n : ℕ) (t : I) :
    Path.sigmaConcat γ x hb hγ (σ ⟨(1 - t / 2) / 2 ^ n,
      div_nonneg (by linarith [t.2.2]) (by simp),
      (div_le_one₀ (by simp)).2 <| by
        linarith [one_le_pow₀ (M₀ := ℝ) one_le_two (n := n), t.2.1]⟩) =
    γ n t := by
  dsimp [sigmaConcat]; rw [dite_cond_eq_true <| by
    simp [← unitInterval.coe_lt_one, (by linarith [t.2.2] : t.1 / 2 < 1)]]
  by_cases ht : t < 1
  · sorry
    --simp_rw [sub_sub_cancel 1 ((1 - t.1 / 2) / 2 ^ n)]
  · rw [unitInterval.lt_one_iff_ne_one, not_ne_iff] at ht; rw [ht]
    rw [(γ n).target, ← (γ n.succ).source]
    have h : Nat.floor (- Real.logb 2 (1 - (1 - (1 - (1 : I).1 / 2) / 2 ^ n))) = n.succ := by
      convert Nat.floor_natCast n.succ
      rw [Set.Icc.coe_one, sub_half, div_div, ← pow_succ', ← Real.rpow_natCast]; simp
    refine congr (by rw [h]) ?_
    ext; dsimp [-Set.Icc.coe_one]; rw [h, Real.rpow_natCast, pow_succ']
    field_simp; ring

/-- On locally path-connected first-countable spaces, the topology is coinduced by all paths in
  the space. This is the core argument behind the following sequence of lemmas. -/
private lemma LocPathConnectedSpace.eq_coinduced_paths [FirstCountableTopology X]
    [LocPathConnectedSpace X] : tX = ⨆ γ : C(I, X), .coinduced γ inferInstance := by
  refine le_antisymm ?_ <| iSup_le_iff.mpr fun f ↦ f.continuous.coinduced_le
  -- It suffices to show that any set `u` whose preimages under all paths are open is open.
  intro u hu; simp_rw [isOpen_iSup_iff, isOpen_coinduced] at hu
  -- For that it suffices to show `uᶜ` contains all limit points `x` of sequences `s` in it.
  rw [← isClosed_compl_iff]; refine IsSeqClosed.isClosed fun s x hs hsx ↦ ?_
  -- Let `b` be a sequence of nested path-connected sets that form a neighbourhood basis of `x`.
  let ⟨b, hbx, hb⟩ := exists_isPathConnected_antitone_basis x
  -- Let `s'` be a subsequence of `s` such that `s' n ∈ b n`
  simp_rw [hbx.1.tendsto_right_iff, Filter.eventually_atTop, true_implies] at hsx
  let s' := fun n ↦ s (hsx n).choose
  have hs' : ∀ n, s' n ∈ b n := fun n ↦ (hsx n).choose_spec _ le_rfl
  -- For each `n`, let `γ n` be a path from `s' n` to `s' (n+1)` in `b n`.
  set γ := fun n ↦ ((hb n).joinedIn _ (hs' n) _ (hbx.2 n.le_succ <| hs' n.succ)).choose
  have hγ : ∀ n t, γ n t ∈ _ := fun n ↦
    ((hb n).joinedIn _ (hs' n) _ (hbx.2 n.le_succ <| hs' n.succ)).choose_spec
  -- Then we can concatenate all `γ n` into a single path `γ'` from `s' 0` to `x`.
  let γ' := Path.sigmaConcat γ x hbx hγ
  -- It suffices to show that `1` is in the preimage of `uᶜ` under `γ'`.
  suffices 1 ∈ γ' ⁻¹' uᶜ by rw [← γ'.target]; assumption
  -- By assumption, this preimage is closed.
  specialize hu γ'; rw [γ'.coe_mk, ← isClosed_compl_iff, ← u.preimage_compl] at hu
  -- It thus suffices that the sequence `1, 1/2, 3/4, ...` lies in this preimage and tends to `1`.
  refine hu.isSeqClosed (x := fun n ↦ σ ⟨1 / 2 ^ n, by simp [inv_le_one₀, one_le_pow₀]⟩) ?_ ?_
  · intro n; rw [Set.mem_preimage]; dsimp [γ']
    have h := Path.sigmaConcat_applyAt (γ := γ) (x := x) (hb := hbx) (hγ := hγ) n 0
    simp_rw [Set.Icc.coe_zero, zero_div, sub_zero, Path.source] at h
    rw [h]; exact hs _
  · rw [tendsto_subtype_rng]
    simp_rw [coe_symm_eq, Set.Icc.coe_one]; rw [← sub_zero 1]
    refine Filter.Tendsto.sub (by simp) ?_
    simp_rw [sub_zero, ← one_div_pow]
    apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    rw [abs_of_pos (by simp)]; exact one_half_lt_one

/-- A first-countable space is delta-generated iff it is locally path-connected.-/
theorem FirstCountableTopology.deltaGeneratedSpace_iff [FirstCountableTopology X] :
    DeltaGeneratedSpace X ↔ LocPathConnectedSpace X := by
  refine ⟨fun _ ↦ inferInstance, fun h ↦ ⟨?_⟩⟩
  nth_rewrite 1 [LocPathConnectedSpace.eq_coinduced_paths (X := X)]
  refine iSup_mono' fun γ ↦ ?_
  have _ : Fact ((0 : ℝ) ≤ 1) := ⟨zero_le_one⟩
  use ⟨1, γ.comp (ContinuousMap.projIccCM.comp (Homeomorph.funUnique (Fin 1) ℝ))⟩
  rw [ContinuousMap.coe_comp, ← coinduced_compose]; apply Eq.le; congr
  exact ((isQuotientMap_projIcc (h := zero_le_one)).comp (Homeomorph.funUnique _ _).isQuotientMap).2

/-- Any locally path-connected first-countable space is delta-generated. This applies in particular
  to all normed spaces.

  This forms a loop with `DeltaGeneratedSpace.instLocPathConnectedSpace`, but that doesn't seem to
  lead to any problems (yet). -/
instance [LocPathConnectedSpace X] [FirstCountableTopology X] : DeltaGeneratedSpace X :=
  FirstCountableTopology.deltaGeneratedSpace_iff.2 inferInstance

/-- Convex subsets of first-countable locally convex spaces are delta-generated.
  Applies in particular to all convex subsets of normed spaces. -/
theorem Convex.deltaGeneratedSpace {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [TopologicalAddGroup E] [Module ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [FirstCountableTopology E] {S : Set E} (hS : Convex ℝ S) : DeltaGeneratedSpace S := by
  have := hS.locPathConnectedSpace; infer_instance

/-- The unit interval is delta-generated. -/
instance : DeltaGeneratedSpace I := Convex.deltaGeneratedSpace (convex_Icc 0 1)

/-- The standard simplices are delta-generated. -/
instance {ι : Type*} [Fintype ι] : DeltaGeneratedSpace (stdSimplex ℝ ι) :=
  (convex_stdSimplex ℝ ι).deltaGeneratedSpace

/-- The delta-generated topology on `X` is coinduced by all continuous maps from the unit interval
  to `X`. -/
theorem deltaGenerated_eq_coinduced_unitInterval :
    deltaGenerated X = ⨆ γ : C(I, X), coinduced γ inferInstance := by
  apply le_antisymm
  · refine iSup_le fun f ↦ ?_
    rw [coinduced_le_iff_le_induced]
    refine LocPathConnectedSpace.eq_coinduced_paths.le.trans <| iSup_le fun γ ↦ ?_
    rw [← coinduced_le_iff_le_induced, coinduced_compose]
    exact le_iSup_of_le  ⟨f.2 ∘ γ, f.2.2.comp γ.2⟩ <| Eq.le rfl
  · rw [← continuous_id_iff_le, @continuous_to_deltaGenerated _ _ (_) _ ?_ id]
    · exact continuous_id_iff_le.2 <| iSup_le fun γ ↦ γ.2.coinduced_le
    exact DeltaGeneratedSpace.iSup fun γ ↦ DeltaGeneratedSpace.coinduced γ

/-- The delta-generated topology on `X` is coinduced by all continuous maps from the standard
  simplices to `X`. -/
theorem deltaGenerated_eq_coinduced_stdSimplex : deltaGenerated X =
    ⨆ f : (n : ℕ) × C(stdSimplex ℝ (Fin n), X), coinduced f.2 inferInstance := by
  apply le_antisymm
  · rw [deltaGenerated_eq_coinduced_unitInterval]
    refine iSup_le fun f ↦ le_iSup_of_le ⟨2, f.comp stdSimplexHomeomorphUnitInterval⟩ ?_
    dsimp; rw [← coinduced_compose, Homeomorph.coinduced_eq]
  · rw [← continuous_id_iff_le, @continuous_to_deltaGenerated _ _ (_) _ ?_ id]
    · exact continuous_id_iff_le.2 <| iSup_le fun f ↦ f.2.2.coinduced_le
    exact DeltaGeneratedSpace.iSup fun f ↦ DeltaGeneratedSpace.coinduced f.2
