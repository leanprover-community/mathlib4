/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.UniformSpace.Ultra.Basic

/-!
# Ultrametric (nonarchimedean) uniform spaces induced by pseudometrics

Ultrametric (nonarchimedean) uniform spaces are such that they are induces by systems
of pseudometrics
having a uniformity based on equivalence relations.

## Main results

* `TopologicalSpace.isTopologicalBasis_clopens`: a uniform space with a nonarchimedean uniformity
  has a topological basis of clopen sets in the topology, meaning that it is topologically
  zero-dimensional.

## Implementation notes

-/

open scoped Uniformity

variable {X : Type*} (M : Set (X → X → ℝ))

variable (X) in
@[ext]
structure PseudoMetricFun where
  toFun : X → X → ℝ
  refl' x : toFun x x = 0
  symm' x y : toFun x y = toFun y x
  triangle' x y z : toFun x z ≤ toFun x y + toFun y z

namespace PseudoMetricFun

instance : FunLike (PseudoMetricFun X) X (X → ℝ) where
  coe := PseudoMetricFun.toFun
  coe_injective' := by
    intro a
    aesop

variable (d : PseudoMetricFun X)

@[simp]
lemma mk_apply (d refl symm triangle) (x y : X) :
    PseudoMetricFun.mk d refl symm triangle x y = d x y :=
  rfl

@[simp]
protected lemma refl (x : X) : d x x = 0 := d.refl' x
protected lemma symm (x y : X) : d x y = d y x := d.symm' x y
protected lemma triangle (x y z : X) : d x z ≤ d x y + d y z := d.triangle' x y z
protected lemma nonneg (x y : X) : 0 ≤ d x y := by
  by_contra! H
  have : d x x < 0 := by
    calc d x x ≤ d x y + d y x := d.triangle' x y x
      _ < 0 + 0 := by refine add_lt_add H (d.symm x y ▸ H)
      _ = 0 := by simp
  exact this.not_le (d.refl' x).ge

@[simp]
protected def sup (d' : PseudoMetricFun X) : PseudoMetricFun X where
  toFun := fun x y ↦ (d x y) ⊔ (d' x y)
  refl' _ := by simp
  symm' x y := by simp [d.symm, d'.symm]
  triangle' := by
    intro x y z
    simp only [sup_le_iff]
    refine ⟨(d.triangle x y z).trans ?_, (d'.triangle x y z).trans ?_⟩ <;>
    apply add_le_add <;> simp

instance : LE (PseudoMetricFun X) := ⟨fun d d' ↦ ∀ x y, d x y ≤ d' x y⟩

@[simp]
protected lemma le_iff_coe_le_coe (d d' : PseudoMetricFun X) :
    d ≤ d' ↔ (d : X → X → ℝ) ≤ d' :=
  Iff.rfl

instance : PartialOrder (PseudoMetricFun X) where
  le_refl := by simp
  le_trans f _ _ := le_trans (a := ⇑f)
  le_antisymm f g := by simpa [PseudoMetricFun.ext_iff] using le_antisymm

instance : Max (PseudoMetricFun X) where
  max := PseudoMetricFun.sup

@[simp]
protected lemma sup_eq_sup (d' : PseudoMetricFun X) :
    (d.sup d') = d ⊔ d' := rfl

@[simp]
protected lemma sup_apply (d' : PseudoMetricFun X) (x y : X) :
    (d ⊔ d') x y = (d x y) ⊔ (d' x y) := rfl

instance : SemilatticeSup (PseudoMetricFun X) where
  sup := max
  le_sup_left := by simp [Pi.le_def]
  le_sup_right := by simp [Pi.le_def]
  sup_le _ _ _ := fun h h' _ _ ↦ sup_le (h _ _) (h' _ _)

protected def bot : PseudoMetricFun X where
  toFun := 0
  refl' _ := rfl
  symm' _ _ := rfl
  triangle' _ _ _ := by simp

instance : Bot (PseudoMetricFun X) where
  bot := PseudoMetricFun.bot

@[simp]
protected lemma bot_eq_bot : PseudoMetricFun.bot (X := X) = ⊥ := rfl

@[simp]
protected lemma bot_apply (x y : X) :
    (⊥ : PseudoMetricFun X) x y = 0 :=
  rfl

instance : OrderBot (PseudoMetricFun X) where
  bot_le f _ _ := f.nonneg _ _

lemma finset_sup_apply {Y : Type*} {f : Y → PseudoMetricFun X} {s : Finset Y} (hs : s.Nonempty)
    (x y : X) :
    (s.sup f) x y = s.sup' hs fun i ↦ (f i) x y := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons a s ha hs ih => simp [hs, ih]

def IsTriangleMax (d : PseudoMetricFun X) : Prop :=
  ∀ x y z, d x z ≤ d x y ⊔ d y z

lemma isTriangleMax_bot : IsTriangleMax (⊥ : PseudoMetricFun X) := by
  simp [IsTriangleMax]

lemma isTriangleMax_sup {d d' : PseudoMetricFun X} (hd : IsTriangleMax d)
    (hd' : IsTriangleMax d') : IsTriangleMax (d ⊔ d') := by
  intro x y z
  simp only [PseudoMetricFun.sup_apply]
  calc d x z ⊔ d' x z ≤ d x y ⊔ d y z ⊔ (d' x y ⊔ d' y z) := sup_le_sup (hd x y z) (hd' x y z)
  _ ≤ d x y ⊔ d' x y ⊔ (d y z ⊔ d' y z) := by simp [sup_comm, sup_assoc, sup_left_comm]

lemma isTriangleMax_finset_sup {Y : Type*} {f : Y → PseudoMetricFun X} {s : Finset Y}
    (h : ∀ d ∈ s, IsTriangleMax (f d)) :
    IsTriangleMax (s.sup f) := by
  intro x y z
  rcases s.eq_empty_or_nonempty with rfl|hs
  · simp
  simp_rw [finset_sup_apply hs]
  apply Finset.sup'_le
  simp only [le_sup_iff, Finset.le_sup'_iff]
  intro i hi
  specialize h i hi x y z
  simp only [le_sup_iff] at h
  refine h.imp ?_ ?_ <;>
  intro H <;>
  exact ⟨i, hi, H⟩

lemma isSymmetricRel_ball (ε : ℝ) :
    IsSymmetricRel {xy | d xy.1 xy.2 < ε} := by
  ext
  simp [d.symm]

lemma isTransitiveRel_ball_of_isTriangleMax {d : PseudoMetricFun X} (ε : ℝ) (h : d.IsTriangleMax) :
    IsTransitiveRel {xy | d xy.1 xy.2 < ε} :=
  fun x y z hxy hyz ↦ (h x y z).trans_lt (max_lt hxy hyz)

end PseudoMetricFun

lemma Filter.generate_image_preimage_le_comap {α β : Type*} (X : Set (Set α)) (f : β → α) :
  .generate ((f ⁻¹' ·) '' X) ≤ Filter.comap f (.generate X) := by
  intro s
  simp only [Filter.mem_comap, Filter.mem_generate_iff, Set.exists_subset_image_iff,
    Set.sInter_image]
  rintro ⟨t, ⟨u, hu, huf, hut⟩, hts⟩
  refine ⟨u, hu, huf.image _, subset_trans ?_ hts⟩
  rw [← Set.preimage_sInter]
  exact Set.preimage_mono hut

def UniformSpace.core_ofPseudoMetricSystem (M : Set (PseudoMetricFun X)) :
    UniformSpace.Core X where
  uniformity := .generate <| (fun εd ↦ {xy | εd.2 xy.1 xy.2 < εd.1}) '' ((Set.Ioi 0 : Set ℝ) ×ˢ M)
  refl := by
    simp only [Filter.principal, idRel_subset, Filter.le_generate_iff, Set.image_subset_iff,
      Set.preimage_setOf_eq, Set.mem_setOf_eq, PseudoMetricFun.refl]
    intro
    aesop
  symm := by
    rw [Filter.tendsto_iff_comap]
    refine (Filter.generate_image_preimage_le_comap _ _).trans' ?_
    rw [← Set.image_swap_eq_preimage_swap, Set.image_image, Set.image_swap_eq_preimage_swap]
    simp [PseudoMetricFun.symm]
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

lemma isSymmetricRel_iInter {ι : Sort*} {s : ι → Set (X × X)} (h : ∀ i, IsSymmetricRel (s i)) :
    IsSymmetricRel (⋂ i, s i) := by
  simp [IsSymmetricRel, Set.preimage_iInter, Set.iInter_congr h]

lemma isSymmetricRel_sInter {s : Set (Set (X × X))} (h : ∀ i ∈ s, IsSymmetricRel i) :
    IsSymmetricRel (⋂₀ s) := by
  rw [Set.sInter_eq_iInter]
  exact isSymmetricRel_iInter (by simpa)

lemma isTransitiveRel_iInter {ι : Sort*} {s : ι → Set (X × X)} (h : ∀ i, IsTransitiveRel (s i)) :
    IsTransitiveRel (⋂ i, s i) := by
  intro x y z hxy hyz
  simp only [Set.mem_iInter] at hxy hyz ⊢
  intro i
  exact h i (hxy i) (hyz i)

lemma isTransitiveRel_sInter {s : Set (Set (X × X))} (h : ∀ i ∈ s, IsTransitiveRel i) :
    IsTransitiveRel (⋂₀ s) := by
  rw [Set.sInter_eq_iInter]
  exact isTransitiveRel_iInter (by simpa)

lemma IsUltraUniformity.ofPseudoMetricSystem_of_isTriangleMax {M : Set (PseudoMetricFun X)}
    (hM : ∀ d ∈ M, d.IsTriangleMax) :
    @IsUltraUniformity _ (.ofCore <| UniformSpace.core_ofPseudoMetricSystem M) := by
  letI : UniformSpace X := .ofCore <| UniformSpace.core_ofPseudoMetricSystem M
  refine .mk_of_hasBasis (Filter.hasBasis_generate _) ?_ ?_
  · intro s
    simp only [Set.subset_image_iff, and_imp, forall_exists_index]
    rintro hs s hs' rfl
    refine isSymmetricRel_sInter ?_
    simp only [Set.mem_image]
    rintro _ ⟨⟨ε, d⟩, _, rfl⟩
    exact d.isSymmetricRel_ball ε
  · intro s
    simp only [Set.subset_image_iff, and_imp, forall_exists_index]
    rintro hs s hs' rfl
    refine isTransitiveRel_sInter ?_
    simp only [Set.mem_image]
    rintro _ ⟨⟨ε, d⟩, hd, rfl⟩
    exact d.isTransitiveRel_ball_of_isTriangleMax ε (hM _ (hs' hd).right)

def IsUltraUniformity.aux_desc_chains [UniformSpace X] :
    Set (ℕ → Set (X × X)) :=
  {D | D 0 = Set.univ ∧ (∀ n, D (n + 1) ⊆ D n) ∧
    ∀ n > 0, D n ∈ 𝓤 X ∧ IsSymmetricRel (D n) ∧ IsTransitiveRel (D n)}

lemma IsUltraUniformity.mem_aux_desc_chains_subset_of_le [UniformSpace X]
    {D : ℕ → Set (X × X)} (hD : D ∈ IsUltraUniformity.aux_desc_chains) {n m : ℕ} (hmn : n ≤ m) :
    D m ⊆ D n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn; clear hmn
  induction k generalizing n with
  | zero => simp [hD.left]
  | succ k ih =>
    rw [← add_assoc]
    exact (hD.right.left _).trans ih

lemma IsUltraUniformity.refl_mem_of_mem_aux_desc_chains [UniformSpace X]
    {D : ℕ → Set (X × X)} (hD : D ∈ IsUltraUniformity.aux_desc_chains) (n : ℕ) (x : X) :
    (x, x) ∈ D n := by
  simp only [gt_iff_lt, Set.mem_setOf_eq, IsUltraUniformity.aux_desc_chains] at hD
  rcases n with _|n
  · simp [hD.left]
  · exact refl_mem_uniformity (hD.right.right _ (Nat.succ_pos _)).left

lemma IsUltraUniformity.isSymmetricRel_of_mem_aux_desc_chains [UniformSpace X]
    {D : ℕ → Set (X × X)} (hD : D ∈ IsUltraUniformity.aux_desc_chains) (n : ℕ) :
    IsSymmetricRel (D n) := by
  simp only [gt_iff_lt, Set.mem_setOf_eq, IsUltraUniformity.aux_desc_chains] at hD
  rcases n with _|n
  · ext
    simp [hD.left]
  · exact (hD.right.right _ (Nat.succ_pos _)).right.left

lemma IsUltraUniformity.isTransitiveRel_of_mem_aux_desc_chains [UniformSpace X]
    {D : ℕ → Set (X × X)} (hD : D ∈ IsUltraUniformity.aux_desc_chains) (n : ℕ) :
    IsTransitiveRel (D n) := by
  simp only [gt_iff_lt, Set.mem_setOf_eq, IsUltraUniformity.aux_desc_chains] at hD
  rcases n with _|n
  · intro
    simp [hD.left]
  · exact (hD.right.right _ (Nat.succ_pos _)).right.right

lemma IsUltraUniformity.triangle_max_pseudoMetricFun_aux [UniformSpace X]
    {D : ℕ → Set (X × X)} (hD : D ∈ IsUltraUniformity.aux_desc_chains)
    [∀ x y, DecidablePred fun n ↦ (x, y) ∈ D n ∧ ∀ m > n, (x, y) ∉ D m]
    [∀ x y, Decidable (∃ n, (x, y) ∈ D n ∧ ∀ m > n, (x, y) ∉ D m)] (x y z : X) :
    let d x y := if h : ∃ n, (x, y) ∈ D n ∧ ∀ m > n, (x, y) ∉ D m
      then (1 / (Nat.find h + 1 : ℕ) : ℝ) else 0
    d x z ≤ d x y ⊔ d y z := by
  dsimp only [gt_iff_lt]
  split; rotate_left
  · simp only [gt_iff_lt, one_div, le_sup_iff]
    left
    split <;> simp [- Nat.cast_add]
  rename_i hxz
  split_ifs with hxy hyz hyz
  · rcases le_total (Nat.find hxy) (Nat.find hyz) with H|H
    -- Is there a way to wlog or `swap_var` here?
    · refine le_sup_of_le_left ?_
      simp only [gt_iff_lt, one_div]
      rw [inv_le_inv₀]
      any_goals simp only [Nat.cast_pos, Nat.succ_pos]
      simp only [Nat.cast_le, add_le_add_iff_right, Nat.le_find_iff, Nat.lt_find_iff, not_and,
        not_forall, Classical.not_imp, not_not]
      intro n IH hn
      simp only [gt_iff_lt, Nat.le_find_iff, Nat.lt_find_iff, not_and, not_forall,
        Classical.not_imp, not_not] at H
      specialize H n IH
      refine ⟨n + 1, Nat.lt_succ_self _, ?_⟩
      have hxyn : (x, y) ∈ D n := by
        clear hn H
        induction n with
        | zero => simp [hD.left]
        | succ n ih =>
          specialize ih ?_
          · intro m hm hxym
            apply IH _ _ hxym
            linarith
          · obtain ⟨k, hk, hk'⟩ := IH _ n.le_succ ih
            exact mem_aux_desc_chains_subset_of_le hD hk hk'
      replace H : (y, z) ∈ D (n + 1) := by
        obtain ⟨k, hk, hk'⟩ := H (isTransitiveRel_of_mem_aux_desc_chains hD
          _ ((isSymmetricRel_of_mem_aux_desc_chains hD _).mk_mem_comm.mpr hxyn) hn)
        exact mem_aux_desc_chains_subset_of_le hD hk hk'
      refine isTransitiveRel_of_mem_aux_desc_chains hD _ ?_ H
      obtain ⟨k, hk, hk'⟩ := IH _ le_rfl hxyn
      exact mem_aux_desc_chains_subset_of_le hD hk hk'
    · refine le_sup_of_le_right ?_
      simp only [gt_iff_lt, one_div]
      rw [inv_le_inv₀]
      any_goals simp only [Nat.cast_pos, Nat.succ_pos]
      simp only [Nat.cast_le, add_le_add_iff_right, Nat.le_find_iff, Nat.lt_find_iff, not_and,
        not_forall, Classical.not_imp, not_not]
      intro n IH hn
      simp only [gt_iff_lt, Nat.le_find_iff, Nat.lt_find_iff, not_and, not_forall,
        Classical.not_imp, not_not] at H
      specialize H n IH
      refine ⟨n + 1, Nat.lt_succ_self _, ?_⟩
      have hxyn : (y, z) ∈ D n := by
        clear hn H
        induction n with
        | zero => simp [hD.left]
        | succ n ih =>
          specialize ih ?_
          · intro m hm hxym
            apply IH _ _ hxym
            linarith
          · obtain ⟨k, hk, hk'⟩ := IH _ n.le_succ ih
            exact mem_aux_desc_chains_subset_of_le hD hk hk'
      replace H : (x, y) ∈ D (n + 1) := by
        obtain ⟨k, hk, hk'⟩ := H (isTransitiveRel_of_mem_aux_desc_chains hD
          _ hn ((isSymmetricRel_of_mem_aux_desc_chains hD _).mk_mem_comm.mpr hxyn))
        exact mem_aux_desc_chains_subset_of_le hD hk hk'
      refine isTransitiveRel_of_mem_aux_desc_chains hD _ H ?_
      obtain ⟨k, hk, hk'⟩ := IH _ le_rfl hxyn
      exact mem_aux_desc_chains_subset_of_le hD hk hk'
  · push_neg at hyz
    replace hyz : ∀ n, (y, z) ∈ D n := by
      intro n
      induction n with
      | zero => simp [hD.left]
      | succ n ih =>
        obtain ⟨m, hm, hm'⟩ := hyz n ih
        rw [gt_iff_lt, ← Nat.succ_le_iff] at hm
        exact mem_aux_desc_chains_subset_of_le hD hm hm'
    simp only [gt_iff_lt, one_div, inv_nonneg, Nat.cast_nonneg, sup_of_le_left, ge_iff_le]
    rw [inv_le_inv₀]
    any_goals simp only [Nat.cast_pos, Nat.succ_pos]
    simp only [Nat.cast_le, add_le_add_iff_right, Nat.le_find_iff, Nat.lt_find_iff, not_and,
    not_forall, Classical.not_imp, not_not]
    intro n IH hn
    obtain ⟨k, hk, hk'⟩ := IH _ le_rfl (isTransitiveRel_of_mem_aux_desc_chains hD _ hn
      ((isSymmetricRel_of_mem_aux_desc_chains hD _).mk_mem_comm.mpr <| hyz _))
    refine ⟨k, hk, ?_⟩
    exact isTransitiveRel_of_mem_aux_desc_chains hD _ hk' (hyz _)
  · push_neg at hxy
    replace hxy : ∀ n, (x, y) ∈ D n := by
      intro n
      induction n with
      | zero => simp [hD.left]
      | succ n ih =>
        obtain ⟨m, hm, hm'⟩ := hxy n ih
        rw [gt_iff_lt, ← Nat.succ_le_iff] at hm
        exact mem_aux_desc_chains_subset_of_le hD hm hm'
    simp only [gt_iff_lt, one_div, inv_nonneg, Nat.cast_nonneg, sup_of_le_right, ge_iff_le]
    rw [inv_le_inv₀]
    any_goals simp only [Nat.cast_pos, Nat.succ_pos]
    simp only [Nat.cast_le, add_le_add_iff_right, Nat.le_find_iff, Nat.lt_find_iff, not_and,
    not_forall, Classical.not_imp, not_not]
    intro n IH hn
    obtain ⟨k, hk, hk'⟩ := IH _ le_rfl (isTransitiveRel_of_mem_aux_desc_chains hD _
      ((isSymmetricRel_of_mem_aux_desc_chains hD _).mk_mem_comm.mpr <| hxy _) hn)
    refine ⟨k, hk, ?_⟩
    exact isTransitiveRel_of_mem_aux_desc_chains hD _ (hxy _) hk'
  · push_neg at hxy hyz
    replace hxy : ∀ n, (x, y) ∈ D n := by
      intro n
      induction n with
      | zero => simp [hD.left]
      | succ n ih =>
        obtain ⟨m, hm, hm'⟩ := hxy n ih
        rw [gt_iff_lt, ← Nat.succ_le_iff] at hm
        exact mem_aux_desc_chains_subset_of_le hD hm hm'
    replace hyz : ∀ n, (y, z) ∈ D n := by
      intro n
      induction n with
      | zero => simp [hD.left]
      | succ n ih =>
        obtain ⟨m, hm, hm'⟩ := hyz n ih
        rw [gt_iff_lt, ← Nat.succ_le_iff] at hm
        exact mem_aux_desc_chains_subset_of_le hD hm hm'
    have key n : (x, z) ∈ D n := isTransitiveRel_of_mem_aux_desc_chains hD _ (hxy _) (hyz _)
    obtain ⟨k, hk, hk'⟩ := hxz
    absurd hk' (k + 1) (Nat.lt_succ_self _)
    exact key _

noncomputable
def IsUltraUniformity.pseudoMetricFun_of_mem_aux_desc_chains [UniformSpace X]
    {D : ℕ → Set (X × X)} (hD : D ∈ IsUltraUniformity.aux_desc_chains)
    [∀ x y, DecidablePred fun n ↦ (x, y) ∈ D n ∧ ∀ m > n, (x, y) ∉ D m]
    [∀ x y, Decidable (∃ n, (x, y) ∈ D n ∧ ∀ m > n, (x, y) ∉ D m)] :
    PseudoMetricFun X where
  toFun x y := if h : ∃ n, (x, y) ∈ D n ∧ ∀ m > n, (x, y) ∉ D m then 1 / (Nat.find h + 1 : ℕ) else 0
  refl' := by
    intro
    simp only [gt_iff_lt, one_div, dite_eq_right_iff, inv_eq_zero, Nat.cast_eq_zero,
      AddLeftCancelMonoid.add_eq_zero, Nat.find_eq_zero, one_ne_zero, and_false, imp_false,
      not_exists, not_and, not_forall, Classical.not_imp, not_not]
    intro n hn
    exact ⟨n + 1, Nat.lt_succ_self _, refl_mem_of_mem_aux_desc_chains hD _ _⟩
  symm' _ _ := by simp [(isSymmetricRel_of_mem_aux_desc_chains hD _).mk_mem_comm]
  triangle' x y z := by
    dsimp only [gt_iff_lt]
    refine (triangle_max_pseudoMetricFun_aux hD x y z).trans ?_
    simp only [gt_iff_lt, one_div, sup_le_iff, le_add_iff_nonneg_right, le_add_iff_nonneg_left]
    split_ifs <;>
    simp [- Nat.cast_add]

lemma IsUltraUniformity.isTriangleMax_pseudoMetricFun_of_mem_aux_desc_chains [UniformSpace X]
    {D : ℕ → Set (X × X)} (hD : D ∈ IsUltraUniformity.aux_desc_chains)
    [∀ x y, DecidablePred fun n ↦ (x, y) ∈ D n ∧ ∀ m > n, (x, y) ∉ D m]
    [∀ x y, Decidable (∃ n, (x, y) ∈ D n ∧ ∀ m > n, (x, y) ∉ D m)] :
    (IsUltraUniformity.pseudoMetricFun_of_mem_aux_desc_chains hD).IsTriangleMax :=
  triangle_max_pseudoMetricFun_aux hD

open Classical in
noncomputable
def IsUltraUniformity.pseudoMetricSystem [UniformSpace X] :
    Set (PseudoMetricFun X) :=
  {D | ∃ (s : Finset (IsUltraUniformity.aux_desc_chains (X := X))),
    D = (s.sup fun k ↦ pseudoMetricFun_of_mem_aux_desc_chains k.prop)}

lemma IsUltraUniformity.isTriangleMax_of_mem_pseudoMetricSystem [UniformSpace X]
    {d : PseudoMetricFun X} (hd : d ∈ IsUltraUniformity.pseudoMetricSystem) :
    d.IsTriangleMax := by
  obtain ⟨s, rfl⟩ := hd
  refine PseudoMetricFun.isTriangleMax_finset_sup ?_
  intro d hd
  classical
  exact isTriangleMax_pseudoMetricFun_of_mem_aux_desc_chains d.prop

-- TODO
lemma UniformSpace.mem_uniformity_ofCore {u : UniformSpace.Core X} {s : Set (X × X)} :
    s ∈ 𝓤[.ofCore u] ↔ s ∈ u.uniformity :=
  Iff.rfl

lemma IsUltraUniformity.ofPseudoMetricSystem_pseudoMetricSystem_eq [U : UniformSpace X]
    [IsUltraUniformity X] :
    .ofCore (UniformSpace.core_ofPseudoMetricSystem (IsUltraUniformity.pseudoMetricSystem)) =
    U := by
  ext t
  have : @IsUltraUniformity X <|
    .ofCore (UniformSpace.core_ofPseudoMetricSystem (IsUltraUniformity.pseudoMetricSystem)) :=
    IsUltraUniformity.ofPseudoMetricSystem_of_isTriangleMax
      fun _ a ↦ isTriangleMax_of_mem_pseudoMetricSystem a
  rw [IsUltraUniformity.hasBasis.mem_iff, IsUltraUniformity.hasBasis.mem_iff]
  simp only [UniformSpace.core_ofPseudoMetricSystem, UniformSpace.mem_uniformity_ofCore,
    Set.exists_subset_image_iff, Set.sInter_image, id_eq]
  constructor
  · simp_rw [Filter.mem_generate_iff, Set.subset_image_iff]
    rintro ⟨s, ⟨⟨u, ⟨u, h, rfl⟩, hf, hu⟩, hsymm, htrans⟩, hst⟩
    obtain ⟨s', hs'⟩ := hf.exists_finset
    classical
    obtain ⟨p, hp⟩ : ∃ p : Finset ((Set.Ioi 0 : Set ℝ) × pseudoMetricSystem (X := X)),
      p.image (fun εd ↦ {xy | εd.2.1 xy.1 xy.2 < εd.1}) = s' := by
      have hs'' : ∀ a ∈ s', ∃ ε d, (ε, d) ∈ u ∧ a = {xy | d xy.1 xy.2 < ε} := by
        simp only [Set.mem_image, Prod.exists] at hs'
        simp [hs', eq_comm]
      choose! fε fd hfu hfeq using hs''
      have hf' := hf.image (fun ball ↦ (fε ball, fd ball))
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
    · simp only [Finset.not_mem_empty, Set.mem_image, Prod.exists, false_iff, not_exists,
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
    obtain ⟨k, kpos, hk⟩ : ∃ (k : ℕ) (_ : 0 < k), (k : ℝ)⁻¹ < ε := by -- TODO
      refine (exists_nat_gt ε⁻¹).imp fun k hk ↦ ?_
      have := (inv_pos_of_pos εpos).trans hk
      refine ⟨by exact_mod_cast this, ?_⟩
      rwa [inv_lt_comm₀ this εpos]
    let Ds : Set (X × X) := p.inf (fun εd ↦ εd.2.prop.choose.inf (fun x ↦ x.val k))
    have hDs : Ds ⊆ ⋂₀ ((fun εd ↦ {xy | εd.2 xy.1 xy.2 < εd.1}) '' u) := by
      suffices Ds ⊆ ⋂₀ s' by
        refine this.trans (Set.sInter_mono ?_)
        intro a
        simp [hs']
      simp only [Finset.inf_set_eq_iInter, Set.iInter_coe_set, ← hp, Finset.coe_image,
        Set.sInter_image, Finset.mem_coe, Set.subset_iInter_iff, Prod.forall, Subtype.forall,
        Set.mem_Ioi, Ds]
      rintro ε' εpos' Dm hDm hp ⟨x, y⟩
      simp only [Set.mem_iInter, Prod.forall, Subtype.forall, Set.mem_Ioi, Set.mem_setOf_eq]
      intro h
      -- instead of deconstructing, since we need to prove membership later
      -- carry around the `Exists.choose` object directly
      rw [hDm.choose_spec]
      rcases hDm.choose.eq_empty_or_nonempty with hv'|hv'
      · simp [hv', εpos']
      have hε : ε ≤ ε' := by
        simp only [Finset.inf'_le_iff, Prod.exists, exists_and_right, Subtype.exists, Set.mem_Ioi,
          ε]
        exact ⟨_, ⟨‹_›, ⟨_, _, hp⟩⟩, le_rfl⟩
      rw [PseudoMetricFun.finset_sup_apply hv', Finset.sup'_lt_iff]
      intro ⟨D, hD⟩ hDv
      simp only [pseudoMetricFun_of_mem_aux_desc_chains, gt_iff_lt, one_div,
        PseudoMetricFun.mk_apply]
      refine (hk.trans_le hε).trans' ?_
      split_ifs with h'
      · rw [inv_lt_inv₀]
        · norm_cast
          simp only [Nat.lt_succ, Nat.le_find_iff, not_and, not_forall, Classical.not_imp, not_not]
          intro m hm hm'
          exact ⟨k, hm, h _ ‹_› _ _ hp D hD hDv⟩
        · simp [- Nat.cast_add]
        · simp [kpos]
      · simp [kpos]
    refine ⟨_, ⟨?_, ?_, ?_⟩, hDs.trans (hu.trans hst)⟩
    · dsimp [Ds] at hDs ⊢
      simp only [Finset.inf_set_eq_iInter, Filter.biInter_finset_mem]
      simp only [Subtype.forall, Prod.forall, Set.mem_Ioi, Ds]
      rintro - - d hd hdp D hD hDm
      rcases k with (_|k)
      · simp [hD.left]
      · simp [hD.right]
    · simp only [Finset.inf_set_eq_iInter, Ds]
      refine isSymmetricRel_sInter ?_
      simp only [Set.mem_range, Prod.exists, Subtype.exists, Set.mem_Ioi,
        forall_exists_index]
      rintro s ε _ d _ rfl
      refine isSymmetricRel_iInter ?_
      intro hd
      refine isSymmetricRel_iInter ?_
      intro ⟨D, hD⟩
      refine isSymmetricRel_iInter ?_
      rcases k with (_|k)
      · simp [hD.left, IsSymmetricRel]
      · simp [hD.right]
    · simp only [Finset.inf_set_eq_iInter, Ds]
      refine isTransitiveRel_sInter ?_
      simp only [Set.mem_range, Prod.exists, Subtype.exists, Set.mem_Ioi,
        forall_exists_index]
      rintro s ε _ d _ rfl
      refine isTransitiveRel_iInter ?_
      intro hd
      refine isTransitiveRel_iInter ?_
      intro ⟨D, hD⟩
      refine isTransitiveRel_iInter ?_
      rcases k with (_|k)
      · simp [hD.left, IsTransitiveRel]
      · simp [hD.right]
  · rintro ⟨s, ⟨hs, hsymm, htrans⟩, hst⟩
    let D (n : ℕ) : Set (X × X) := if n = 0 then Set.univ else s
    have hD : D ∈ IsUltraUniformity.aux_desc_chains := by
      refine ⟨by simp [D], ?_, ?_⟩
      · rintro (_|n) <;>
        simp [D]
      · rintro (_|n) <;>
        simp [D, hs, hsymm, htrans]
    classical
    let d := IsUltraUniformity.pseudoMetricFun_of_mem_aux_desc_chains hD
    refine ⟨{xy | d xy.1 xy.2 < 4⁻¹}, ⟨?_, ?_, ?_⟩, subset_trans ?_ hst⟩
    · refine Filter.mem_generate_of_mem ?_
      simp only [pseudoMetricSystem, Set.mem_image, Set.mem_prod, Set.mem_Ioi, Set.mem_setOf_eq,
        Prod.exists]
      exact ⟨_, d, ⟨by norm_num, {⟨D, hD⟩}, by simp [d]⟩, rfl⟩
    · exact d.isSymmetricRel_ball _
    · exact d.isTransitiveRel_ball_of_isTriangleMax _ (isTriangleMax_of_mem_pseudoMetricSystem
        ⟨{⟨D, hD⟩}, by simp [d]⟩)
    · intro
      simp only [pseudoMetricFun_of_mem_aux_desc_chains, Set.mem_ite_univ_left, gt_iff_lt,
        Classical.not_imp, one_div, PseudoMetricFun.mk_apply, Prod.mk.eta, Set.mem_setOf_eq, d, D]
      split_ifs with h
      · generalize_proofs H
        rw [inv_lt_inv₀]
        · norm_cast
          simp only [Nat.succ_lt_succ_iff, Nat.lt_find_iff, not_and, not_forall, Classical.not_imp,
            Decidable.not_not, D, d]
          intro h
          obtain ⟨m, hm, hm'⟩ := h 0 (Nat.zero_le _) (by simp)
          simp [hm' hm.ne']
        · simp [- Nat.cast_add]
        · norm_num
      · push_neg at h
        obtain ⟨m, hm, hm'⟩ := h 0 (by simp)
        simp [hm' hm.ne']
