/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.MetricSpace.BundledFun
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Basic
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
def UniformSpace.ofPseudoMetricSystem (M : Set (PseudoMetric X ℝ)) :
    UniformSpace X :=
  ⨅ d : M, .ofDist d d.val.refl d.val.symm d.val.triangle

lemma hasBasis_ofDist
    (d : X → X → ℝ) (refl : ∀ x, d x x = 0) (symm : ∀ x y, d x y = d y x)
    (triangle : ∀ x y z, d x z ≤ d x y + d y z) :
    𝓤[.ofDist d refl symm triangle].HasBasis ((0 : ℝ) < ·) (fun ε => { x | d x.1 x.2 < ε }) :=
  UniformSpace.hasBasis_ofFun (⟨1, zero_lt_one⟩) _ _ _ _ _

lemma hasBasis_ofPseudoMetric (d : PseudoMetric X ℝ) :
    𝓤[.ofDist d d.refl d.symm d.triangle].HasBasis ((0 : ℝ) < ·) (fun ε => { x | d x.1 x.2 < ε }) :=
  hasBasis_ofDist _ _ _ _

lemma hasBasis_ofPseudoMetricSystem (M : Set (PseudoMetric X ℝ)) :
    𝓤[.ofPseudoMetricSystem M].HasBasis
      (fun s : Finset (PseudoMetric X ℝ × ℝ) ↦ ∀ p ∈ s, p.1 ∈ M ∧ 0 < p.2)
      (fun s ↦ s.inf (fun p ↦ { x | p.1 x.1 x.2 < p.2 })) := by
  have := Filter.HasBasis.iInf' (fun d : M ↦ hasBasis_ofPseudoMetric d.val)
  have h : 𝓤[.ofPseudoMetricSystem M] =
    ⨅ d : M, 𝓤[.ofDist d d.val.refl d.val.symm d.val.triangle] :=
    iInf_uniformity
  rw [← h] at this
  classical
  refine this.to_hasBasis ?_ ?_
  · intro s ⟨hs, hs'⟩
    refine ⟨hs.toFinset.image (fun d ↦ ⟨d.val, s.2 d⟩), ?_⟩
    simp only [Finset.mem_image, Set.Finite.mem_toFinset, Subtype.exists, forall_exists_index,
      and_imp, Prod.forall, Prod.mk.injEq, Finset.inf_image, Finset.inf_set_eq_iInter,
      Function.comp_apply, Set.iInter_coe_set, subset_refl, and_true]
    rintro d ε d hd hd' rfl rfl
    exact ⟨hd, hs' _ hd'⟩
  · intro s hs
    refine ⟨
      ⟨((s.attach.image (fun p ↦ ⟨p.1.1, (hs p.1 p.prop).1⟩) : Finset M) : Set M),
      fun d ↦ if hd : d.1 ∈ s.image Prod.fst
        then ((s.filter (fun p ↦ p.1 = d.1)).image Prod.snd).min' ?_ else 0⟩, ?_⟩
    · simp only [Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right] at hd
      obtain ⟨x, hd⟩ := hd
      simp only [Finset.image_nonempty]
      refine ⟨⟨d, x⟩, ?_⟩
      simp [hd]
    simp only [Finset.coe_image, Finset.coe_attach, Set.image_univ, Set.finite_range, Set.mem_range,
      Subtype.exists, Prod.exists, Finset.mem_image, exists_and_right, exists_eq_right,
      forall_exists_index, Subtype.forall, Subtype.mk.injEq, true_and, Set.iInter_exists,
      Set.iInter_coe_set, Finset.inf_set_eq_iInter, Set.subset_iInter_iff, Prod.forall]
    refine ⟨?_, ?_⟩
    · rintro _ _ _ _ hd' rfl
      rw [dif_pos ⟨_, hd'⟩]
      simp only [Finset.lt_min'_iff, Finset.mem_image, Finset.mem_filter, Prod.exists,
        exists_eq_right]
      intro _ hy
      exact (hs _ hy).2
    · intro d ε hd x
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro hx
      refine (hx d (hs _ hd).1 d ε hd rfl).trans_le ?_
      rw [dif_pos ⟨_, hd⟩]
      refine Finset.min'_le _ _ ?_
      simp [hd]

/-- For the uniform space induced by a family of pseudometrics, the uniform space is
nonarchimedean if all the pseudometrics are nonarchimedean. -/
lemma IsUltraUniformity.ofPseudoMetricSystem_of_isUltra {M : Set (PseudoMetric X ℝ)}
    (hM : ∀ d ∈ M, d.IsUltra) :
    @IsUltraUniformity _ (.ofPseudoMetricSystem M) := by
  letI : UniformSpace X := .ofPseudoMetricSystem M
  refine .mk_of_hasBasis (hasBasis_ofPseudoMetricSystem M) ?_ ?_
  · intro s hs
    rw [Finset.inf_eq_iInf]
    refine .iInter ?_
    simp only [Set.iInf_eq_iInter, Prod.forall]
    intro d _
    refine .iInter ?_
    intro
    exact d.isSymmetricRel_ball
  · intro s hs
    rw [Finset.inf_eq_iInf]
    refine .iInter ?_
    simp only [Set.iInf_eq_iInter, Prod.forall]
    intro d _
    refine .sInter ?_
    simp only [Set.mem_range, exists_prop, and_imp, forall_apply_eq_imp_iff]
    intro hd
    exact (hM _ (hs _ hd).left).isTransitiveRel_ball

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
  · simp [(Nat.cast_nonneg k).not_gt] at hn
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
  ⟨hD.isUltra_pseudometric_aux⟩

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

lemma descChainEquivRel.pseudoMetric_apply_lt_iff_of_pos
    {D : ℕ → Set (X × X)} {hD : descChainEquivRel D}
    [∀ x y, DecidablePred fun n ↦ (x, y) ∉ D n]
    [∀ x y, Decidable (∃ n, (x, y) ∉ D n)] {x y : X} {ε : ℝ} (hε : 0 < ε) :
    hD.PseudoMetric x y < ε ↔ ∀ (k : ℕ), ε ≤ (k : ℝ)⁻¹ → (x, y) ∈ D k := by
  constructor
  · intro h n hn
    rcases eq_or_ne n 0 with rfl|hn'
    · simp [hD.top]
    rw [← hD.pseudoMetric_apply_lt_inv_natCast_iff_of_ne_zero hn']
    exact hn.trans_lt' h
  · intro h
    simp only [PseudoMetric, pseudometric_aux, PseudoMetric.coe_mk]
    split_ifs with h'
    · rw [← not_le]
      intro H
      exact (Nat.find_spec h') (h _ H)
    · simp [hε]

lemma descChainEquivRel.setOf_pseudoMetric_apply_lt_eq_biInter
    {D : ℕ → Set (X × X)} (hD : descChainEquivRel D)
    [∀ x y, DecidablePred fun n ↦ (x, y) ∉ D n]
    [∀ x y, Decidable (∃ n, (x, y) ∉ D n)] {ε : ℝ} (hε : 0 < ε) :
    {xy | hD.PseudoMetric xy.1 xy.2 < ε} = ⋂ k ∈ {k : ℕ | ε ≤ (k : ℝ)⁻¹}, D k := by
  ext
  simp [hD.pseudoMetric_apply_lt_iff_of_pos hε]

lemma descChainEquivRel.setOf_pseudoMetric_apply_lt_eq_univ_of_one_lt
    {D : ℕ → Set (X × X)} (hD : descChainEquivRel D)
    [∀ x y, DecidablePred fun n ↦ (x, y) ∉ D n]
    [∀ x y, Decidable (∃ n, (x, y) ∉ D n)] {ε : ℝ} (hε : 0 < ε) (hε' : 1 < ε) :
    {xy : X × X | hD.PseudoMetric xy.1 xy.2 < ε} = Set.univ := by
  rw [hD.setOf_pseudoMetric_apply_lt_eq_biInter hε]
  ext
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_univ, iff_true]
  rintro (_|k) hk
  · simp [hD.top]
  replace hk := hε'.trans_le hk
  rw [one_lt_inv₀ (by positivity)] at hk
  absurd hk
  simp

lemma descChainEquivRel.setOf_pseudoMetric_apply_lt_eq_apply_find_sub_one
    {D : ℕ → Set (X × X)} (hD : descChainEquivRel D)
    [∀ x y, DecidablePred fun n ↦ (x, y) ∉ D n]
    [∀ x y, Decidable (∃ n, (x, y) ∉ D n)] {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1)
    (hn : ∃ (n : ℕ), 1 / ((n : ℝ) + 1) < ε := exists_nat_one_div_lt hε) :
    {xy | hD.PseudoMetric xy.1 xy.2 < ε} = D (Nat.find hn) := by
  rw [hD.setOf_pseudoMetric_apply_lt_eq_biInter hε]
  ext
  simp only [Set.mem_setOf_eq, Set.mem_iInter]
  have := Nat.find_spec hn
  have hn0 : 0 < Nat.find hn := by simp [hε']
  constructor
  · intro h
    apply h
    have hn1 := Nat.find_min (m := Nat.find hn - 1) hn (Nat.sub_one_lt_of_lt hn0)
    push_neg at hn1
    rw [Nat.cast_sub hn0] at hn1
    simpa using hn1
  · intro h n hn'
    apply hD.subset_of_le _ h
    simp only [one_div, Nat.le_find_iff, not_lt]
    intro m hm
    refine hn'.trans ?_
    refine inv_anti₀ ?_ (by exact_mod_cast hm)
    positivity

lemma descChainEquivRel.setOf_pseudoMetric_apply_lt_mem_uniformity
    {D : ℕ → Set (X × X)} (hD : descChainEquivRel D)
    [∀ x y, DecidablePred fun n ↦ (x, y) ∉ D n]
    [∀ x y, Decidable (∃ n, (x, y) ∉ D n)] {ε : ℝ} (hε : 0 < ε) :
    {xy | hD.PseudoMetric xy.1 xy.2 < ε} ∈ 𝓤 X := by
  rcases le_or_gt ε 1 with hε' | hε'
  · rw [hD.setOf_pseudoMetric_apply_lt_eq_apply_find_sub_one hε hε']
    exact hD.mem_uniformity _
  · rw [hD.setOf_pseudoMetric_apply_lt_eq_univ_of_one_lt hε hε']
    simp

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
    .ofPseudoMetricSystem pseudoMetricSystem = U := by
  -- to prove the two uniform spaces are equal we need to show that the uniformity filters are equal
  -- by showing that an arbitrary entourage of one is necessarily an entourage of the other
  ext t
  rcases isEmpty_or_nonempty X with _|_
  · simp [Filter.filter_eq_bot_of_isEmpty]
  -- we have that the "canonical" uniform space `U` is nonarchimedean;
  -- for the proof, we also have a local instance that the uniform space induced by the
  -- pseudometric system is nonarchimedean
  have : @IsUltraUniformity X <|
    (.ofPseudoMetricSystem pseudoMetricSystem) :=
      IsUltraUniformity.ofPseudoMetricSystem_of_isUltra
      fun _ a ↦ isUltra_of_mem_pseudoMetricSystem a
  -- the entourage is a member of one iff a member of the other -- over the bases of the uniformity
  -- which means there is an equivalence relation entourage
  -- that is a subset of our arbitrary entourage
  rw [IsUltraUniformity.hasBasis.mem_iff, IsUltraUniformity.hasBasis.mem_iff]
  simp_rw [(hasBasis_ofPseudoMetricSystem pseudoMetricSystem).mem_iff]
  constructor
  · rintro ⟨s, ⟨⟨u, hu, hi'⟩, hsymm, htrans⟩, hst⟩
    rw [Finset.inf_eq_iInf] at hi'
    refine ⟨⨅ _, _, ⟨?_, ?_, ?_⟩, hi'.trans hst⟩
    · refine (Filter.biInter_finset_mem _).mpr ?_
      intro d hd
      obtain ⟨D, hD⟩ := (hu d hd).1
      rw [← hD]
      simp only at hD ⊢
      classical
      rcases D.eq_empty_or_nonempty with rfl | hD'
      · simp [(hu d hd).2]
      have hs' : {xy : X × X | (D.sup fun k ↦ k.prop.PseudoMetric) xy.1 xy.2 < d.2} =
        ⋂ f ∈ D, {x : X × X | f.prop.PseudoMetric x.1 x.2 < d.2} := by
        ext
        simp [PseudoMetric.finsetSup_apply hD']
      rw [hs']
      simp only [Filter.biInter_finset_mem, Subtype.forall]
      intro f hf hf'
      exact hf.setOf_pseudoMetric_apply_lt_mem_uniformity (hu d hd).2
    · simp_rw [Set.iInf_eq_iInter]
      refine IsSymmetricRel.iInter ?_
      intro d
      classical
      rw [Set.iInter_eq_if]
      split_ifs
      · exact d.1.isSymmetricRel_ball
      · simp [IsSymmetricRel]
    · simp_rw [Set.iInf_eq_iInter]
      refine IsTransitiveRel.iInter ?_
      intro d
      classical
      rw [Set.iInter_eq_if]
      split_ifs with hd
      · have : d.1.IsUltra := by
          obtain ⟨D, hD⟩ := (hu d hd).1
          rw [← hD]
          refine PseudoMetric.IsUltra.finsetSup ?_
          simp [descChainEquivRel.isUltra_pseudoMetric]
        exact PseudoMetric.IsUltra.isTransitiveRel_ball _
      · exact isTransitiveRel_univ
  · rintro ⟨s, ⟨hs, hsymm, htrans⟩, hst⟩
    let D (n : ℕ) : Set (X × X) := if n = 0 then Set.univ else s
    have hD : descChainEquivRel D := by
      refine ⟨by simp [D], ?_, ?_, ?_, ?_⟩
      all_goals rintro (_|n) <;>
        simp [D, hs, hsymm, htrans]
    classical
    refine ⟨s, ⟨?_, hsymm, htrans⟩, hst⟩
    refine ⟨{⟨hD.PseudoMetric, 2⁻¹⟩}, ?_, ?_⟩
    · simp only [Finset.mem_singleton, forall_eq, inv_pos, Nat.ofNat_pos, and_true, D]
      use {⟨D, hD⟩}
      simp
    · simp only [descChainEquivRel.PseudoMetric, descChainEquivRel.pseudometric_aux,
        Set.mem_ite_univ_left, Classical.not_imp, exists_and_right, Finset.inf_singleton,
        PseudoMetric.coe_mk, Prod.mk.eta, D]
      intro x
      simp only [Set.mem_setOf_eq]
      split_ifs with h
      · generalize_proofs H
        have : Nat.find H = 1 := by simp_all [Nat.find_eq_iff]
        rw [this]
        norm_num
      · simp only [not_and, Decidable.not_not, forall_exists_index] at h
        simpa using h 1

end UniformSpace.pseudoMetrizable
