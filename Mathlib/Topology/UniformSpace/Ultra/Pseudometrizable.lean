/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.MetricSpace.BundledFun
import Mathlib.Topology.UniformSpace.Ultra.Basic

/-!
# Ultrametric (nonarchimedean) uniform spaces induced by pseudometrics

Ultrametric (nonarchimedean) uniform spaces are such that they are induced by systems
of pseudometrics having a uniformity based on equivalence relations.

## Main results

* `UniformSpace.pseudoMetrizable.IsUltraUniformity.ofPseudoMetricSystem_pseudoMetricSystem_eq`:
  Any uniform space has a natural system of pseudometrics definable on it,
  comprised of those pseudometrics constructed from a descending chain of
  equivalence relation entourages. In a nonarchimedean uniformity, this pseudometric system
  induces the uniformity.

## Implementation notes

The proof follows the construction in
[D. Windisch, *Equivalent characterizations of non-Archimedean uniform spaces*][windisch2021],
with conditions on the descending chain of equivalence relation entourages simplified
to easily expose API of the entourages.

-/

open scoped Uniformity

variable {X : Type*}

/-- Any set of pseudometrics can induce a uniform space, where the entourages are
any open ball of positive radius for any of the pseudometrics. -/
def UniformSpace.Core.ofPseudoMetricSystem (M : Set (PseudoMetric X ℝ)) :
    UniformSpace.Core X where
  uniformity := .generate <| (fun εd ↦ {xy | εd.2 xy.1 xy.2 < εd.1}) '' ((Set.Ioi 0 : Set ℝ) ×ˢ M)
  refl := by
    simp only [Filter.principal, idRel_subset, Filter.le_generate_iff, Set.image_subset_iff,
      Set.preimage_setOf_eq, Set.mem_setOf_eq, PseudoMetric.refl]
    intro
    aesop
  symm := by
    rw [Filter.tendsto_iff_comap]
    refine (Filter.generate_image_preimage_le_comap _ _).trans' ?_
    rw [← Set.image_swap_eq_preimage_swap, Set.image_image, Set.image_swap_eq_preimage_swap]
    simp [PseudoMetric.symm]
  comp := by
    rw [Filter.le_generate_iff]
    intro s
    simp only [Set.mem_image, Set.mem_prod, Set.mem_Ioi, Prod.exists, Filter.mem_sets,
      forall_exists_index, and_imp]
    rintro ε d εpos hd rfl
    rw [Filter.mem_lift'_sets (Monotone.compRel _ _)]
    · refine ⟨{xy | d xy.1 xy.2 < ε / 2}, Filter.mem_generate_of_mem ?_, ?_⟩
      · simp only [Set.mem_image, Set.mem_prod, Set.mem_Ioi, Prod.exists]
        exact ⟨ε / 2, d, ⟨by simp [εpos], hd⟩, rfl⟩
      · intro ⟨a, b⟩
        rw [mem_compRel]
        simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
        intro c hac hcb
        refine (d.triangle _ _ _).trans_lt ((add_lt_add hac hcb).trans_le ?_)
        simp
    · exact monotone_id
    · exact monotone_id

/-- For the uniform space induced by a family of pseudometrics, the uniform space is
nonarchimedean if all the pseudometrics are nonarchimedean. -/
lemma IsUltraUniformity.ofCore_ofPseudoMetricSystem_of_isUltra {M : Set (PseudoMetric X ℝ)}
    (hM : ∀ d ∈ M, d.IsUltra) :
    @IsUltraUniformity _ (.ofCore <| .ofPseudoMetricSystem M) := by
  letI : UniformSpace X := .ofCore <| .ofPseudoMetricSystem M
  refine .mk_of_hasBasis (Filter.hasBasis_generate _) ?_ ?_
  · intro s
    simp only [Set.subset_image_iff, and_imp, forall_exists_index]
    rintro hs s hs' rfl
    refine .sInter ?_
    simp only [Set.mem_image]
    rintro _ ⟨⟨ε, d⟩, _, rfl⟩
    exact d.isSymmetricRel_ball
  · intro s
    simp only [Set.subset_image_iff, and_imp, forall_exists_index]
    rintro hs s hs' rfl
    refine .sInter ?_
    simp only [Set.mem_image]
    rintro _ ⟨⟨ε, d⟩, hd, rfl⟩
    exact (hM _ (hs' hd).right).isTransitiveRel_ball

namespace UniformSpace.pseudoMetrizable

variable [UniformSpace X]

/-- A chain of nested equivalence relation entourages in a uniform space that can used to construct
a pseudometric. -/
structure descChainEquivRel (D : ℕ → Set (X × X)) : Prop where
  top : D 0 = Set.univ
  chain {n} : D (n + 1) ⊆ D n
  mem_uniformity' {n : ℕ} (hn : n > 0) : D n ∈ 𝓤 X
  isSymmetricRel' {n : ℕ} (hn : n > 0) : IsSymmetricRel (D n)
  isTransitiveRel' {n : ℕ} (hn : n > 0) : IsTransitiveRel (D n)

lemma descChainEquivRel.mem_uniformity {D : ℕ → Set (X × X)} (hD : descChainEquivRel D) (n : ℕ) :
    D n ∈ 𝓤 X := by
  rcases n with _|n
  · simp [hD.top]
  · exact hD.mem_uniformity' (Nat.succ_pos _)

lemma descChainEquivRel.isSymmetricRel {D : ℕ → Set (X × X)} (hD : descChainEquivRel D) (n : ℕ) :
    IsSymmetricRel (D n) := by
  rcases n with _|n
  · simp [hD.top, IsSymmetricRel]
  · exact hD.isSymmetricRel' (Nat.succ_pos _)

lemma descChainEquivRel.isTransitiveRel {D : ℕ → Set (X × X)} (hD : descChainEquivRel D) (n : ℕ) :
    IsTransitiveRel (D n) := by
  rcases n with _|n
  · simp [hD.top, IsTransitiveRel]
  · exact hD.isTransitiveRel' (Nat.succ_pos _)

lemma descChainEquivRel.subset_of_le
    {D : ℕ → Set (X × X)} (hD : descChainEquivRel D) {n m : ℕ} (hmn : n ≤ m) :
    D m ⊆ D n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn; clear hmn
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc]
    exact hD.chain.trans ih

lemma descChainEquivRel.refl_mem
    {D : ℕ → Set (X × X)} (hD : descChainEquivRel D) (n : ℕ) (x : X) :
    (x, x) ∈ D n := by
  rcases n with _|n
  · simp [hD.top]
  · exact refl_mem_uniformity (hD.mem_uniformity _)

/-- The underlying function for the bundled pseudometric defined below.
Given a descending chain of equivalence relations in a uniform space,
two points are measured to be close as the minimum level of the chain where they are
not equivalent under the relation, if such a minimum exists. Otherwise, they are always close,
and the distance is 0. -/
noncomputable
def descChainEquivRel.pseudometric_aux (D : ℕ → Set (X × X))
    [∀ x y, DecidablePred fun n ↦ (x, y) ∉ D n]
    [∀ x y, Decidable (∃ n, (x, y) ∉ D n)] :
    X → X → ℝ := fun x y ↦
  (if h : ∃ n, (x, y) ∉ D n then Nat.find h else 0)⁻¹

lemma descChainEquivRel.pseudometric_aux_apply_lt_inv_natCast_iff_of_ne_zero
    {D : ℕ → Set (X × X)} (hD : descChainEquivRel D)
    [∀ x y, DecidablePred fun n ↦ (x, y) ∉ D n]
    [∀ x y, Decidable (∃ n, (x, y) ∉ D n)] {x y : X} {k : ℕ} (hk : k ≠ 0) :
    pseudometric_aux D x y < (k : ℝ)⁻¹ ↔ (x, y) ∈ D k := by
  simp only [pseudometric_aux, one_div, PseudoMetric.coe_mk]
  split_ifs with h
  · rw [inv_lt_inv₀]
    · simp only [Nat.cast_lt, Nat.lt_find_iff, not_not]
      constructor
      · intro h'
        exact h' _ le_rfl
      · intro hk m hm
        exact hD.subset_of_le hm hk
    · simp [hD.top]
    · simp [Nat.pos_of_ne_zero hk]
  · push_neg at h
    simp [h, Nat.pos_of_ne_zero hk]

lemma descChainEquivRel.pseudometric_aux_apply_eq_zero_iff
    {D : ℕ → Set (X × X)} (hD : descChainEquivRel D)
    [∀ x y, DecidablePred fun n ↦ (x, y) ∉ D n]
    [∀ x y, Decidable (∃ n, (x, y) ∉ D n)] {x y : X} :
    pseudometric_aux D x y = 0 ↔ ∀ n, (x, y) ∈ D n := by
  simp only [pseudometric_aux]
  split_ifs with h
  · simp [hD.top, h]
  · simpa using h

omit [UniformSpace X] in
lemma descChainEquivRel.exists_inv_natCast_eq_pseudometric_aux
    (D : ℕ → Set (X × X))
    [∀ x y, DecidablePred fun n ↦ (x, y) ∉ D n]
    [∀ x y, Decidable (∃ n, (x, y) ∉ D n)] (x y : X) :
    ∃ (k : ℕ), pseudometric_aux D x y = (k : ℝ)⁻¹ := by
  rw [pseudometric_aux]
  split_ifs with h
  · simp
  · use 0
    simp

lemma descChainEquivRel.pseudometric_aux_comm
    {D : ℕ → Set (X × X)} (hD : descChainEquivRel D)
    [∀ x y, DecidablePred fun n ↦ (x, y) ∉ D n]
    [∀ x y, Decidable (∃ n, (x, y) ∉ D n)] (x y : X) :
    pseudometric_aux D x y = pseudometric_aux D y x := by
  simp [pseudometric_aux, (hD.isSymmetricRel _).mk_mem_comm]

/-- An auxiliary result about the descending chain pseudometric, used for both
constructing the bundled pseudometric, as well as proving the nonarchimedean property. -/
lemma descChainEquivRel.isUltra_pseudometric_aux
    {D : ℕ → Set (X × X)} (hD : descChainEquivRel D)
    [∀ x y, DecidablePred fun n ↦ (x, y) ∉ D n]
    [∀ x y, Decidable (∃ n, (x, y) ∉ D n)]
    (x y z : X) :
    pseudometric_aux D x z ≤ pseudometric_aux D x y ⊔ pseudometric_aux D y z := by
  -- we have to show that the minimum level `n` where x !~ z is at least the minimum level
  -- of where x !~ y (`k`) or y !~ z (`l`)
  -- suffices in the case where k ≤ l
  wlog hkl : pseudometric_aux D y z ≤ pseudometric_aux D x y generalizing x y z
  · push_neg at hkl
    rw [hD.pseudometric_aux_comm x z, hD.pseudometric_aux_comm x y, hD.pseudometric_aux_comm y z,
      sup_comm]
    apply this z y x
    rw [hD.pseudometric_aux_comm y x, hD.pseudometric_aux_comm z y]
    exact hkl.le
  obtain ⟨n, hn⟩ := descChainEquivRel.exists_inv_natCast_eq_pseudometric_aux D x z
  obtain ⟨k, hk⟩ := descChainEquivRel.exists_inv_natCast_eq_pseudometric_aux D x y
  obtain ⟨l, hl⟩ := descChainEquivRel.exists_inv_natCast_eq_pseudometric_aux D y z
  simp_rw [hn, hk, hl] at hkl ⊢
  -- x !~ y is k-deep, x !~ z is n-deep, prove n ≤ k; (y !~ z is l-deep, k ≤ l)
  refine le_sup_of_le_left ?_
  -- assume n < k, in the reciprocal k⁻¹ < n⁻¹ form
  -- show that x !~ z not at n, by showing that x ~ y, y ~ z at n => x ~ z at n
  contrapose! hn
  -- trivial case, n = 0, x ~ z everywhere
  rcases eq_or_ne n 0 with rfl|npos
  · simp [(Nat.cast_nonneg k).not_lt] at hn
  refine ne_of_lt ?_
  have hkn := hk.trans_lt hn
  have hln := (hkl.trans_eq' hl).trans_lt hn
  rw [hD.pseudometric_aux_apply_lt_inv_natCast_iff_of_ne_zero npos] at hkn hln ⊢
  exact hD.isTransitiveRel _ hkn hln

/-- Given a descending chain of equivalence relations in a uniform space,
two points are measured to be close as the minimum level of the chain where they are
not equivalent under the relation, if such a minimum exists. Otherwise, they are always close,
and the distance is 0. This defines a nonarchimedean pseudometric on the space. -/
noncomputable
def descChainEquivRel.PseudoMetric
    {D : ℕ → Set (X × X)} (hD : descChainEquivRel D)
    [∀ x y, DecidablePred fun n ↦ (x, y) ∉ D n]
    [∀ x y, Decidable (∃ n, (x, y) ∉ D n)] :
    PseudoMetric X ℝ where
  toFun x y := descChainEquivRel.pseudometric_aux D x y
  refl' := by simp [descChainEquivRel.pseudometric_aux, hD.refl_mem]
  symm' _ _ := hD.pseudometric_aux_comm _ _
  triangle' x y z := by
    refine (hD.isUltra_pseudometric_aux x y z).trans ?_
    simp only [sup_le_iff, le_add_iff_nonneg_right, le_add_iff_nonneg_left]
    dsimp only [descChainEquivRel.pseudometric_aux]
    split_ifs <;>
    simp [- Nat.cast_add]

lemma descChainEquivRel.isUltra_pseudoMetric
    {D : ℕ → Set (X × X)} (hD : descChainEquivRel D)
    [∀ x y, DecidablePred fun n ↦ (x, y) ∉ D n]
    [∀ x y, Decidable (∃ n, (x, y) ∉ D n)] :
    hD.PseudoMetric.IsUltra :=
  hD.isUltra_pseudometric_aux

lemma descChainEquivRel.pseudoMetric_apply_lt_inv_natCast_iff_of_ne_zero
    {D : ℕ → Set (X × X)} {hD : descChainEquivRel D}
    [∀ x y, DecidablePred fun n ↦ (x, y) ∉ D n]
    [∀ x y, Decidable (∃ n, (x, y) ∉ D n)] {x y : X} {k : ℕ} (hk : k ≠ 0) :
    hD.PseudoMetric x y < (k : ℝ)⁻¹ ↔ (x, y) ∈ D k := by
  simp only [PseudoMetric, pseudometric_aux, one_div, PseudoMetric.coe_mk]
  split_ifs with h
  · rw [inv_lt_inv₀]
    · simp only [Nat.cast_lt, Nat.lt_find_iff, not_not]
      constructor
      · intro h'
        exact h' _ le_rfl
      · intro hk m hm
        exact hD.subset_of_le hm hk
    · simp [hD.top]
    · simp [Nat.pos_of_ne_zero hk]
  · push_neg at h
    simp [h, Nat.pos_of_ne_zero hk]

open Classical in
/-- Any uniform space has a natural system of pseudometrics definable on it,
comprised of those pseudometrics constructed from a descending chain of
equivalence relation entourages. In a nonarchimedean uniformity, this pseudometric system
induces the uniformity, as show in
`UniformSpace.pseudoMetrizable.IsUltraUniformity.ofPseudoMetricSystem_pseudoMetricSystem_eq`. -/
noncomputable def pseudoMetricSystem :
    Set (PseudoMetric X ℝ) :=
  Set.range (fun s : Finset (Subtype (descChainEquivRel (X := X))) ↦
    s.sup fun k ↦ k.prop.PseudoMetric)

lemma isUltra_of_mem_pseudoMetricSystem
    {d : PseudoMetric X ℝ} (hd : d ∈ pseudoMetricSystem) :
    d.IsUltra := by
  obtain ⟨s, rfl⟩ := hd
  refine PseudoMetric.IsUltra.finsetSup ?_
  intro d hd
  classical
  exact d.prop.isUltra_pseudoMetric

/-- Any uniform space has a natural system of pseudometrics definable on it,
comprised of those pseudometrics constructed from a descending chain of
equivalence relation entourages. In a nonarchimedean uniformity, this pseudometric system
induces the uniformity. -/
lemma IsUltraUniformity.ofPseudoMetricSystem_pseudoMetricSystem_eq {X : Type*} [U : UniformSpace X]
    [IsUltraUniformity X] :
    .ofCore (.ofPseudoMetricSystem pseudoMetricSystem) = U := by
  -- to prove the two uniform spaces are equal we need to show that the uniformity filters are equal
  -- by showing that an arbitrary entourage of one is necessarily an entourage of the other
  ext t
  -- we have that the "canonical" uniform space `U` is nonarchimedean;
  -- for the proof, we also have a local instance that the uniform space induced by the
  -- pseudometric system is nonarchimedean
  have : @IsUltraUniformity X <|
    .ofCore (.ofPseudoMetricSystem pseudoMetricSystem) :=
      IsUltraUniformity.ofCore_ofPseudoMetricSystem_of_isUltra
      fun _ a ↦ isUltra_of_mem_pseudoMetricSystem a
  -- the entourage is a member of one iff a member of the other -- over the bases of the uniformity
  -- which means there is an equivalence relation entourage
  -- that is a subset of our arbitrary entourage
  rw [IsUltraUniformity.hasBasis.mem_iff, IsUltraUniformity.hasBasis.mem_iff]
  -- unfold the pseudo metric system entourage definition, which is the filter generated by
  -- all balls of positive radius for any of the pseudometrics
  simp only [Core.ofPseudoMetricSystem, mem_uniformity_ofCore_iff,
    Set.exists_subset_image_iff, Set.sInter_image, id_eq]
  constructor
  · -- in this case, we have that our arbitrary entourage is supported by a set in the
    -- filter generated by open balls
    simp_rw [Filter.mem_generate_iff, Set.subset_image_iff]
    rintro ⟨s, ⟨⟨u, ⟨u, h, rfl⟩, hf, hu⟩, hsymm, htrans⟩, hst⟩
    -- which means after rearrangement that there is a set of (radius, pseudometric) pairs such that
    -- 1. the radii are positive
    -- 2. the pseudometrics are constructed as finite infima of pseudometics derived
    --    from descending chains of equivalence relations
    -- 3. the set of balls of all such pairs is finite
    -- 4. the intersection of all these balls is a subset of the original entourage
    -- the proof goes through by finding ε, lower than all radii in the set
    -- which will give a ball at least ε-deep in all of the chains that were used to construct
    -- the pseudometrics, and this ball will necessarily be a subset of all the balls
    -- (and the ball is an equivalence relation)
    -- so it is will be in the intersection, and thus in the parent set
    -- first, pass the existing sets of a Finset, so that it is easier to discuss finite infima
    obtain ⟨s', hs'⟩ := hf.exists_finset
    classical
    obtain ⟨p, hp⟩ : ∃ p : Finset ((Set.Ioi 0 : Set ℝ) × pseudoMetricSystem (X := X)),
      p.image (fun εd ↦ {xy | εd.2.1 xy.1 xy.2 < εd.1}) = s' := by
      have hs'' : ∀ a ∈ s', ∃ ε d, (ε, d) ∈ u ∧ a = {xy | d xy.1 xy.2 < ε} := by
        simp only [Set.mem_image, Prod.exists] at hs'
        simp [hs', eq_comm]
      choose! fε fd hfu hfeq using hs''
      have hinv : Set.LeftInvOn (fun εd ↦ {xy | εd.2 xy.1 xy.2 < εd.1})
          (fun ball ↦ (fε ball, fd ball)) s' := by
        intro a ha
        simp only [Set.mem_image, Prod.exists, Finset.mem_coe] at hs' ha
        symm
        exact hfeq _ ha
      refine ⟨s'.attach.image (fun ball ↦ (⟨fε ball.1, (h (hfu _ ball.prop)).left⟩,
        ⟨fd ball.1, (h (hfu _ ball.prop)).right⟩)), ?_⟩
      · ext t
        simp only [Finset.mem_image, Finset.mem_attach, true_and, Prod.exists, Prod.mk.injEq,
          exists_exists_and_eq_and]
        constructor
        · rintro ⟨ε, ⟨a, ha⟩, rfl, rfl⟩
          rwa [hinv.eq ha]
        · intro ha
          refine ⟨_, ⟨t, ha⟩, rfl, ?_⟩
          rw [hinv.eq ha]
    rcases p.eq_empty_or_nonempty with rfl|hpn
    · -- trivial case, the set of balls is empty, so the intersection is the whole space
      simp only [Finset.not_mem_empty, Set.mem_image, Prod.exists, false_iff, not_exists,
      not_and] at hs'
      rcases u.eq_empty_or_nonempty with rfl|⟨⟨ε, d⟩, hu⟩
      · simp only [Set.image_empty, Set.sInter_empty, Set.univ_subset_iff] at hu
        refine ⟨Set.univ, ?_, hu.ge.trans hst⟩
        simp [IsSymmetricRel, isTransitiveRel_univ]
      · exfalso
        simp only [Finset.image_empty] at hp
        simp only [← hp, Finset.not_mem_empty, false_iff, not_exists, not_and] at hs'
        exact hs' _ _ _ hu rfl
    let ε : ℝ := p.inf' hpn (fun εd ↦ εd.1)
    have εpos : 0 < ε := by simp +contextual [ε]
    -- get a `k` such that `k⁻¹ < ε`, which will be the depth at which we get balls
    obtain ⟨k, kpos, hk⟩ := Real.exists_nat_pos_inv_lt εpos
    -- get the `k`-th ball for the each chain underlying each pseudometric, and intersect them
    let Ds : Set (X × X) := p.inf (fun εd ↦ εd.2.prop.choose.inf (fun x ↦ x.val k))
    -- this intersection of balls is a subset of the intersection of larger balls
    have hDs : Ds ⊆ ⋂₀ ((fun εd ↦ {xy | εd.2 xy.1 xy.2 < εd.1}) '' u) := by
      -- convert goal to discuss the finset we constructed
      suffices Ds ⊆ ⋂₀ s' by
        refine this.trans (Set.sInter_mono ?_)
        intro a
        simp [hs']
      simp only [Finset.inf_set_eq_iInter, Set.iInter_coe_set, ← hp, Finset.coe_image,
        Set.sInter_image, Finset.mem_coe, Set.subset_iInter_iff, Prod.forall, Subtype.forall,
        Set.mem_Ioi, Ds]
      -- we've deconstructed to discuss a single larger ball,
      -- need to show that our k-inter-ball is a subset
      -- by showing that the radius is necessarily larger than our chosen ε which is larger than k
      rintro ε' εpos' Dm hDm hp ⟨x, y⟩
      have hε : ε ≤ ε' := by
        simp only [Finset.inf'_le_iff, Prod.exists, exists_and_right, Subtype.exists, Set.mem_Ioi,
          ε]
        exact ⟨_, ⟨‹_›, ⟨_, _, hp⟩⟩, le_rfl⟩
      simp only [Set.mem_iInter, Prod.forall, Subtype.forall, Set.mem_Ioi, Set.mem_setOf_eq]
      intro h
      -- instead of deconstructing, since we need to prove membership later
      -- carry around the `Exists.choose` object directly
      rw [← hDm.choose_spec]
      rcases hDm.choose.eq_empty_or_nonempty with hv'|hv'
      · simp [hv', εpos']
      refine (hk.trans_le hε).trans' ?_
      rw [PseudoMetric.finsetSup_apply hv', Finset.sup'_lt_iff]
      intro D hD
      rw [D.prop.pseudoMetric_apply_lt_inv_natCast_iff_of_ne_zero kpos.ne']
      exact h _ εpos' _ _ hp _ _ hD
    -- we have our intersection of k-balls, each one is an entourage and an equivalence relation
    -- so now we just have to show that those properties are preserved under intersection
    refine ⟨_, ⟨?_, ?_, ?_⟩, hDs.trans (hu.trans hst)⟩
    · dsimp [Ds] at hDs ⊢
      simp only [Finset.inf_set_eq_iInter, Filter.biInter_finset_mem]
      simp only [Subtype.forall, Prod.forall, Set.mem_Ioi, Ds]
      rintro - - d hd hdp D hD hDm
      exact hD.mem_uniformity _
    · simp only [Finset.inf_set_eq_iInter, Ds]
      refine IsSymmetricRel.sInter ?_
      simp only [Set.mem_range, Prod.exists, Subtype.exists, Set.mem_Ioi,
        forall_exists_index]
      rintro _ _ _ _ _ rfl
      refine IsSymmetricRel.iInter ?_
      intro
      refine IsSymmetricRel.iInter ?_
      intro ⟨D, hD⟩
      refine IsSymmetricRel.iInter ?_
      simp [hD.isSymmetricRel]
    · simp only [Finset.inf_set_eq_iInter, Ds]
      refine IsTransitiveRel.sInter ?_
      simp only [Set.mem_range, Prod.exists, Subtype.exists, Set.mem_Ioi, forall_exists_index]
      rintro _ _ _ _ _ rfl
      refine IsTransitiveRel.sInter ?_
      simp only [Set.mem_range, exists_prop, and_imp, forall_apply_eq_imp_iff]
      intros
      refine IsTransitiveRel.iInter ?_
      intro ⟨D, hD⟩
      refine IsTransitiveRel.sInter ?_
      simp [hD.isTransitiveRel]
  · -- in this case, we have that our arbitrary entourage is supported by an
    -- equivalence relation entourage, and we need to provide a set of balls
    -- from pseudometrics made from descending chains -- which will be the "ball" we just assumed
    rintro ⟨s, ⟨hs, hsymm, htrans⟩, hst⟩
    -- create the "trivial" chain which is constant of our equivalence relation entourage
    let D (n : ℕ) : Set (X × X) := if n = 0 then Set.univ else s
    have hD : descChainEquivRel D := by
      refine ⟨by simp [D], ?_, ?_, ?_, ?_⟩
      all_goals rintro (_|n) <;>
        simp [D, hs, hsymm, htrans]
    classical
    -- use an arbitrary threshold radius (any positive natural would do)
    refine ⟨{xy | hD.PseudoMetric xy.1 xy.2 < 1⁻¹}, ⟨?_, ?_, ?_⟩, subset_trans ?_ hst⟩
    · refine Filter.mem_generate_of_mem ?_
      simp only [pseudoMetricSystem, Set.mem_image, Set.mem_prod, Set.mem_Ioi, Set.mem_range,
        Prod.exists, D]
      exact ⟨_, _, ⟨by norm_num, {⟨D, hD⟩}, by simp⟩, rfl⟩
    · exact hD.PseudoMetric.isSymmetricRel_ball
    · exact hD.isUltra_pseudoMetric.isTransitiveRel_ball
    · intro
      simp only [Set.mem_setOf_eq, D]
      have : (1 : ℝ)⁻¹ = ((1 : ℕ) : ℝ)⁻¹ := by norm_num
      rw [this, descChainEquivRel.pseudoMetric_apply_lt_inv_natCast_iff_of_ne_zero] <;>
      norm_num

end UniformSpace.pseudoMetrizable
