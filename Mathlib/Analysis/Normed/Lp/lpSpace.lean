/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Set.Image
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# ℓp space

This file describes properties of elements `f` of a pi-type `∀ i, E i` with finite "norm",
defined for `p : ℝ≥0∞` as the size of the support of `f` if `p=0`, `(∑' a, ‖f a‖^p) ^ (1/p)` for
`0 < p < ∞` and `⨆ a, ‖f a‖` for `p=∞`.

The Prop-valued `Memℓp f p` states that a function `f : ∀ i, E i` has finite norm according
to the above definition; that is, `f` has finite support if `p = 0`, `Summable (fun a ↦ ‖f a‖^p)` if
`0 < p < ∞`, and `BddAbove (norm '' (Set.range f))` if `p = ∞`.

The space `lp E p` is the subtype of elements of `∀ i : α, E i` which satisfy `Memℓp f p`. For
`1 ≤ p`, the "norm" is genuinely a norm and `lp` is a complete metric space.

## Main definitions

* `Memℓp f p` : property that the function `f` satisfies, as appropriate, `f` finitely supported
  if `p = 0`, `Summable (fun a ↦ ‖f a‖^p)` if `0 < p < ∞`, and `BddAbove (norm '' (Set.range f))` if
  `p = ∞`.
* `lp E p` : elements of `∀ i : α, E i` such that `Memℓp f p`. Defined as an `AddSubgroup` of
  a type synonym `PreLp` for `∀ i : α, E i`, and equipped with a `NormedAddCommGroup` structure.
  Under appropriate conditions, this is also equipped with the instances `lp.normedSpace`,
  `lp.completeSpace`. For `p=∞`, there is also `lp.inftyNormedRing`,
  `lp.inftyNormedAlgebra`, `lp.inftyStarRing` and `lp.inftyCStarRing`.

## Main results

* `Memℓp.of_exponent_ge`: For `q ≤ p`, a function which is `Memℓp` for `q` is also `Memℓp` for `p`.
* `lp.memℓp_of_tendsto`, `lp.norm_le_of_tendsto`: A pointwise limit of functions in `lp`, all with
  `lp` norm `≤ C`, is itself in `lp` and has `lp` norm `≤ C`.
* `lp.tsum_mul_le_mul_norm`: basic form of Hölder's inequality

## Implementation

Since `lp` is defined as an `AddSubgroup`, dot notation does not work. Use `lp.norm_neg f` to
say that `‖-f‖ = ‖f‖`, instead of the non-working `f.norm_neg`.

## TODO

* More versions of Hölder's inequality (for example: the case `p = 1`, `q = ∞`; a version for normed
  rings which has `‖∑' i, f i * g i‖` rather than `∑' i, ‖f i‖ * g i‖` on the RHS; a version for
  three exponents satisfying `1 / r = 1 / p + 1 / q`)

-/

noncomputable section

open scoped NNReal ENNReal Function

variable {𝕜 𝕜' : Type*} {α : Type*} {E : α → Type*} {p q : ℝ≥0∞} [∀ i, NormedAddCommGroup (E i)]

/-!
### `Memℓp` predicate

-/


/-- The property that `f : ∀ i : α, E i`
* is finitely supported, if `p = 0`, or
* admits an upper bound for `Set.range (fun i ↦ ‖f i‖)`, if `p = ∞`, or
* has the series `∑' i, ‖f i‖ ^ p` be summable, if `0 < p < ∞`. -/
def Memℓp (f : ∀ i, E i) (p : ℝ≥0∞) : Prop :=
  if p = 0 then Set.Finite { i | f i ≠ 0 }
  else if p = ∞ then BddAbove (Set.range fun i => ‖f i‖)
  else Summable fun i => ‖f i‖ ^ p.toReal

theorem memℓp_zero_iff {f : ∀ i, E i} : Memℓp f 0 ↔ Set.Finite { i | f i ≠ 0 } := by
  dsimp [Memℓp]
  rw [if_pos rfl]

theorem memℓp_zero {f : ∀ i, E i} (hf : Set.Finite { i | f i ≠ 0 }) : Memℓp f 0 :=
  memℓp_zero_iff.2 hf

theorem memℓp_infty_iff {f : ∀ i, E i} : Memℓp f ∞ ↔ BddAbove (Set.range fun i => ‖f i‖) := by
  simp [Memℓp]

theorem memℓp_infty {f : ∀ i, E i} (hf : BddAbove (Set.range fun i => ‖f i‖)) : Memℓp f ∞ :=
  memℓp_infty_iff.2 hf

theorem memℓp_gen_iff (hp : 0 < p.toReal) {f : ∀ i, E i} :
    Memℓp f p ↔ Summable fun i => ‖f i‖ ^ p.toReal := by
  rw [ENNReal.toReal_pos_iff] at hp
  dsimp [Memℓp]
  rw [if_neg hp.1.ne', if_neg hp.2.ne]

theorem memℓp_gen {f : ∀ i, E i} (hf : Summable fun i => ‖f i‖ ^ p.toReal) : Memℓp f p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    have H : Summable fun _ : α => (1 : ℝ) := by simpa using hf
    exact (Set.Finite.of_summable_const (by simp) H).subset (Set.subset_univ _)
  · apply memℓp_infty
    have H : Summable fun _ : α => (1 : ℝ) := by simpa using hf
    simpa using ((Set.Finite.of_summable_const (by simp) H).image fun i => ‖f i‖).bddAbove
  exact (memℓp_gen_iff hp).2 hf

theorem memℓp_gen' {C : ℝ} {f : ∀ i, E i} (hf : ∀ s : Finset α, ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ C) :
    Memℓp f p := by
  apply memℓp_gen
  use ⨆ s : Finset α, ∑ i ∈ s, ‖f i‖ ^ p.toReal
  apply hasSum_of_isLUB_of_nonneg
  · intro b
    exact Real.rpow_nonneg (norm_nonneg _) _
  apply isLUB_ciSup
  use C
  rintro - ⟨s, rfl⟩
  exact hf s

theorem zero_memℓp : Memℓp (0 : ∀ i, E i) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    simp
  · apply memℓp_infty
    simp only [norm_zero, Pi.zero_apply]
    exact bddAbove_singleton.mono Set.range_const_subset
  · apply memℓp_gen
    simp [Real.zero_rpow hp.ne', summable_zero]

theorem zero_mem_ℓp' : Memℓp (fun i : α => (0 : E i)) p :=
  zero_memℓp

namespace Memℓp

theorem finite_dsupport {f : ∀ i, E i} (hf : Memℓp f 0) : Set.Finite { i | f i ≠ 0 } :=
  memℓp_zero_iff.1 hf

theorem bddAbove {f : ∀ i, E i} (hf : Memℓp f ∞) : BddAbove (Set.range fun i => ‖f i‖) :=
  memℓp_infty_iff.1 hf

theorem summable (hp : 0 < p.toReal) {f : ∀ i, E i} (hf : Memℓp f p) :
    Summable fun i => ‖f i‖ ^ p.toReal :=
  (memℓp_gen_iff hp).1 hf

theorem neg {f : ∀ i, E i} (hf : Memℓp f p) : Memℓp (-f) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    simp [hf.finite_dsupport]
  · apply memℓp_infty
    simpa using hf.bddAbove
  · apply memℓp_gen
    simpa using hf.summable hp

@[simp]
theorem neg_iff {f : ∀ i, E i} : Memℓp (-f) p ↔ Memℓp f p :=
  ⟨fun h => neg_neg f ▸ h.neg, Memℓp.neg⟩

theorem of_exponent_ge {p q : ℝ≥0∞} {f : ∀ i, E i} (hfq : Memℓp f q) (hpq : q ≤ p) : Memℓp f p := by
  rcases ENNReal.trichotomy₂ hpq with
    (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hp⟩ | ⟨rfl, rfl⟩ | ⟨hq, rfl⟩ | ⟨hq, _, hpq'⟩)
  · exact hfq
  · apply memℓp_infty
    obtain ⟨C, hC⟩ := (hfq.finite_dsupport.image fun i => ‖f i‖).bddAbove
    use max 0 C
    rintro x ⟨i, rfl⟩
    by_cases hi : f i = 0
    · simp [hi]
    · exact (hC ⟨i, hi, rfl⟩).trans (le_max_right _ _)
  · apply memℓp_gen
    have : ∀ i ∉ hfq.finite_dsupport.toFinset, ‖f i‖ ^ p.toReal = 0 := by
      intro i hi
      have : f i = 0 := by simpa using hi
      simp [this, Real.zero_rpow hp.ne']
    exact summable_of_ne_finset_zero this
  · exact hfq
  · apply memℓp_infty
    obtain ⟨A, hA⟩ := (hfq.summable hq).tendsto_cofinite_zero.bddAbove_range_of_cofinite
    use A ^ q.toReal⁻¹
    rintro x ⟨i, rfl⟩
    have : 0 ≤ ‖f i‖ ^ q.toReal := by positivity
    simpa [← Real.rpow_mul, mul_inv_cancel₀ hq.ne'] using
      Real.rpow_le_rpow this (hA ⟨i, rfl⟩) (inv_nonneg.mpr hq.le)
  · apply memℓp_gen
    have hf' := hfq.summable hq
    refine .of_norm_bounded_eventually hf' (@Set.Finite.subset _ { i | 1 ≤ ‖f i‖ } ?_ _ ?_)
    · have H : { x : α | 1 ≤ ‖f x‖ ^ q.toReal }.Finite := by
        simpa using hf'.tendsto_cofinite_zero.eventually_lt_const (by simp)
      exact H.subset fun i hi => Real.one_le_rpow hi hq.le
    · change ∀ i, ¬|‖f i‖ ^ p.toReal| ≤ ‖f i‖ ^ q.toReal → 1 ≤ ‖f i‖
      intro i hi
      have : 0 ≤ ‖f i‖ ^ p.toReal := Real.rpow_nonneg (norm_nonneg _) p.toReal
      simp only [abs_of_nonneg, this] at hi
      contrapose! hi
      exact Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hi.le hq.le hpq'

theorem add {f g : ∀ i, E i} (hf : Memℓp f p) (hg : Memℓp g p) : Memℓp (f + g) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    refine (hf.finite_dsupport.union hg.finite_dsupport).subset fun i => ?_
    simp only [Pi.add_apply, Ne, Set.mem_union, Set.mem_setOf_eq]
    contrapose!
    rintro ⟨hf', hg'⟩
    simp [hf', hg']
  · apply memℓp_infty
    obtain ⟨A, hA⟩ := hf.bddAbove
    obtain ⟨B, hB⟩ := hg.bddAbove
    refine ⟨A + B, ?_⟩
    rintro a ⟨i, rfl⟩
    exact le_trans (norm_add_le _ _) (add_le_add (hA ⟨i, rfl⟩) (hB ⟨i, rfl⟩))
  apply memℓp_gen
  let C : ℝ := if p.toReal < 1 then 1 else (2 : ℝ) ^ (p.toReal - 1)
  refine .of_nonneg_of_le ?_ (fun i => ?_) (((hf.summable hp).add (hg.summable hp)).mul_left C)
  · intro; positivity
  · refine (Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) hp.le).trans ?_
    dsimp only [C]
    split_ifs with h
    · simpa using NNReal.coe_le_coe.2 (NNReal.rpow_add_le_add_rpow ‖f i‖₊ ‖g i‖₊ hp.le h.le)
    · let F : Fin 2 → ℝ≥0 := ![‖f i‖₊, ‖g i‖₊]
      simp only [not_lt] at h
      simpa [Fin.sum_univ_succ] using
        Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Finset.univ h fun i _ => (F i).coe_nonneg

theorem sub {f g : ∀ i, E i} (hf : Memℓp f p) (hg : Memℓp g p) : Memℓp (f - g) p := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem finset_sum {ι} (s : Finset ι) {f : ι → ∀ i, E i} (hf : ∀ i ∈ s, Memℓp (f i) p) :
    Memℓp (fun a => ∑ i ∈ s, f i a) p := by
  haveI : DecidableEq ι := Classical.decEq _
  revert hf
  refine Finset.induction_on s ?_ ?_
  · simp only [zero_mem_ℓp', Finset.sum_empty, imp_true_iff]
  · intro i s his ih hf
    simp only [his, Finset.sum_insert, not_false_iff]
    exact (hf i (s.mem_insert_self i)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

section IsBoundedSMul

variable [NormedRing 𝕜] [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)]

theorem const_smul {f : ∀ i, E i} (hf : Memℓp f p) (c : 𝕜) : Memℓp (c • f) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    refine hf.finite_dsupport.subset fun i => (?_ : ¬c • f i = 0 → ¬f i = 0)
    exact not_imp_not.mpr fun hf' => hf'.symm ▸ smul_zero c
  · obtain ⟨A, hA⟩ := hf.bddAbove
    refine memℓp_infty ⟨‖c‖ * A, ?_⟩
    rintro a ⟨i, rfl⟩
    dsimp only [Pi.smul_apply]
    refine (norm_smul_le _ _).trans ?_
    gcongr
    exact hA ⟨i, rfl⟩
  · apply memℓp_gen
    dsimp only [Pi.smul_apply]
    have := (hf.summable hp).mul_left (↑(‖c‖₊ ^ p.toReal) : ℝ)
    simp_rw [← coe_nnnorm, ← NNReal.coe_rpow, ← NNReal.coe_mul, NNReal.summable_coe,
      ← NNReal.mul_rpow] at this ⊢
    refine NNReal.summable_of_le ?_ this
    intro i
    gcongr
    apply nnnorm_smul_le

theorem const_mul {f : α → 𝕜} (hf : Memℓp f p) (c : 𝕜) : Memℓp (fun x => c * f x) p :=
  hf.const_smul c

end IsBoundedSMul

end Memℓp

/-!
### lp space

The space of elements of `∀ i, E i` satisfying the predicate `Memℓp`.
-/


/-- We define `PreLp E` to be a type synonym for `∀ i, E i` which, importantly, does not inherit
the `pi` topology on `∀ i, E i` (otherwise this topology would descend to `lp E p` and conflict
with the normed group topology we will later equip it with.)

We choose to deal with this issue by making a type synonym for `∀ i, E i` rather than for the `lp`
subgroup itself, because this allows all the spaces `lp E p` (for varying `p`) to be subgroups of
the same ambient group, which permits lemma statements like `lp.monotone` (below). -/
@[nolint unusedArguments]
def PreLp (E : α → Type*) [∀ i, NormedAddCommGroup (E i)] : Type _ :=
  ∀ i, E i --deriving AddCommGroup

instance : AddCommGroup (PreLp E) := by unfold PreLp; infer_instance

instance PreLp.unique [IsEmpty α] : Unique (PreLp E) :=
  Pi.uniqueOfIsEmpty E

/-- lp space
The `p=∞` case has notation `ℓ^∞(ι, E)` resp. `ℓ^∞(ι)` (for `E = ℝ`) in the `lp` namespace. -/
def lp (E : α → Type*) [∀ i, NormedAddCommGroup (E i)] (p : ℝ≥0∞) : AddSubgroup (PreLp E) where
  carrier := { f | Memℓp f p }
  zero_mem' := zero_memℓp
  add_mem' := Memℓp.add
  neg_mem' := Memℓp.neg

@[inherit_doc] scoped[lp] notation "ℓ^∞(" ι ", " E ")" => lp (fun i : ι => E) ∞
@[inherit_doc] scoped[lp] notation "ℓ^∞(" ι ")" => lp (fun i : ι => ℝ) ∞

namespace lp

instance : CoeOut (lp E p) (∀ i, E i) :=
  ⟨Subtype.val (α := ∀ i, E i)⟩

instance coeFun : CoeFun (lp E p) fun _ => ∀ i, E i :=
  ⟨fun f => (f : ∀ i, E i)⟩

@[ext]
theorem ext {f g : lp E p} (h : (f : ∀ i, E i) = g) : f = g :=
  Subtype.ext h

theorem eq_zero' [IsEmpty α] (f : lp E p) : f = 0 :=
  Subsingleton.elim f 0

protected theorem monotone {p q : ℝ≥0∞} (hpq : q ≤ p) : lp E q ≤ lp E p :=
  fun _ hf => Memℓp.of_exponent_ge hf hpq

protected theorem memℓp (f : lp E p) : Memℓp f p :=
  f.prop

variable (E p)

@[simp]
theorem coeFn_zero : ⇑(0 : lp E p) = 0 :=
  rfl

variable {E p}

@[simp]
theorem coeFn_neg (f : lp E p) : ⇑(-f) = -f :=
  rfl

@[simp]
theorem coeFn_add (f g : lp E p) : ⇑(f + g) = f + g :=
  rfl

variable (p E) in
/-- Coercion to function as an `AddMonoidHom`. -/
def coeFnAddMonoidHom : lp E p →+ (∀ i, E i) where
  toFun := (⇑)
  __ := AddSubgroup.subtype _

@[simp]
theorem coeFnAddMonoidHom_apply (x : lp E p) : coeFnAddMonoidHom E p x = ⇑x := rfl

theorem coeFn_sum {ι : Type*} (f : ι → lp E p) (s : Finset ι) :
    ⇑(∑ i ∈ s, f i) = ∑ i ∈ s, ⇑(f i) := by
  simp

@[simp]
theorem coeFn_sub (f g : lp E p) : ⇑(f - g) = f - g :=
  rfl

instance : Norm (lp E p) where
  norm f :=
    if hp : p = 0 then by
      subst hp
      exact ((lp.memℓp f).finite_dsupport.toFinset.card : ℝ)
    else if p = ∞ then ⨆ i, ‖f i‖ else (∑' i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)

theorem norm_eq_card_dsupport (f : lp E 0) : ‖f‖ = (lp.memℓp f).finite_dsupport.toFinset.card :=
  dif_pos rfl

theorem norm_eq_ciSup (f : lp E ∞) : ‖f‖ = ⨆ i, ‖f i‖ := rfl

theorem isLUB_norm [Nonempty α] (f : lp E ∞) : IsLUB (Set.range fun i => ‖f i‖) ‖f‖ := by
  rw [lp.norm_eq_ciSup]
  exact isLUB_ciSup (lp.memℓp f)

theorem norm_eq_tsum_rpow (hp : 0 < p.toReal) (f : lp E p) :
    ‖f‖ = (∑' i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal) := by
  dsimp [norm]
  rw [ENNReal.toReal_pos_iff] at hp
  rw [dif_neg hp.1.ne', if_neg hp.2.ne]

theorem norm_rpow_eq_tsum (hp : 0 < p.toReal) (f : lp E p) :
    ‖f‖ ^ p.toReal = ∑' i, ‖f i‖ ^ p.toReal := by
  rw [norm_eq_tsum_rpow hp, ← Real.rpow_mul]
  · field_simp
    simp
  apply tsum_nonneg
  intro i
  calc
    (0 : ℝ) = (0 : ℝ) ^ p.toReal := by rw [Real.zero_rpow hp.ne']
    _ ≤ _ := by gcongr; apply norm_nonneg

theorem hasSum_norm (hp : 0 < p.toReal) (f : lp E p) :
    HasSum (fun i => ‖f i‖ ^ p.toReal) (‖f‖ ^ p.toReal) := by
  rw [norm_rpow_eq_tsum hp]
  exact ((lp.memℓp f).summable hp).hasSum

theorem norm_nonneg' (f : lp E p) : 0 ≤ ‖f‖ := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · simp [lp.norm_eq_card_dsupport f]
  · rcases isEmpty_or_nonempty α with _i | _i
    · rw [lp.norm_eq_ciSup]
      simp [Real.iSup_of_isEmpty]
    inhabit α
    exact (norm_nonneg (f default)).trans ((lp.isLUB_norm f).1 ⟨default, rfl⟩)
  · rw [lp.norm_eq_tsum_rpow hp f]
    refine Real.rpow_nonneg (tsum_nonneg ?_) _
    exact fun i => Real.rpow_nonneg (norm_nonneg _) _

@[simp]
theorem norm_zero : ‖(0 : lp E p)‖ = 0 := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · simp [lp.norm_eq_card_dsupport]
  · simp [lp.norm_eq_ciSup]
  · rw [lp.norm_eq_tsum_rpow hp]
    have hp' : 1 / p.toReal ≠ 0 := one_div_ne_zero hp.ne'
    simpa [Real.zero_rpow hp.ne'] using Real.zero_rpow hp'

theorem norm_eq_zero_iff {f : lp E p} : ‖f‖ = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, by rintro rfl; exact norm_zero⟩
  rcases p.trichotomy with (rfl | rfl | hp)
  · ext i
    have : { i : α | ¬f i = 0 } = ∅ := by simpa [lp.norm_eq_card_dsupport f] using h
    have : (¬f i = 0) = False := congr_fun this i
    tauto
  · rcases isEmpty_or_nonempty α with _i | _i
    · simp [eq_iff_true_of_subsingleton]
    have H : IsLUB (Set.range fun i => ‖f i‖) 0 := by simpa [h] using lp.isLUB_norm f
    ext i
    have : ‖f i‖ = 0 := le_antisymm (H.1 ⟨i, rfl⟩) (norm_nonneg _)
    simpa using this
  · have hf : HasSum (fun i : α => ‖f i‖ ^ p.toReal) 0 := by
      have := lp.hasSum_norm hp f
      rwa [h, Real.zero_rpow hp.ne'] at this
    have : ∀ i, 0 ≤ ‖f i‖ ^ p.toReal := fun i => Real.rpow_nonneg (norm_nonneg _) _
    rw [hasSum_zero_iff_of_nonneg this] at hf
    ext i
    have : f i = 0 ∧ p.toReal ≠ 0 := by
      simpa [Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg (f i))] using congr_fun hf i
    exact this.1

theorem eq_zero_iff_coeFn_eq_zero {f : lp E p} : f = 0 ↔ ⇑f = 0 := by
  rw [lp.ext_iff, coeFn_zero]

@[simp]
theorem norm_neg ⦃f : lp E p⦄ : ‖-f‖ = ‖f‖ := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · simp only [norm_eq_card_dsupport, coeFn_neg, Pi.neg_apply, ne_eq, neg_eq_zero]
  · cases isEmpty_or_nonempty α
    · simp only [lp.eq_zero' f, neg_zero, norm_zero]
    apply (lp.isLUB_norm (-f)).unique
    simpa only [coeFn_neg, Pi.neg_apply, norm_neg] using lp.isLUB_norm f
  · suffices ‖-f‖ ^ p.toReal = ‖f‖ ^ p.toReal by
      exact Real.rpow_left_injOn hp.ne' (norm_nonneg' _) (norm_nonneg' _) this
    apply (lp.hasSum_norm hp (-f)).unique
    simpa only [coeFn_neg, Pi.neg_apply, _root_.norm_neg] using lp.hasSum_norm hp f

instance normedAddCommGroup [hp : Fact (1 ≤ p)] : WithNormedAddGroup (lp E p) := fast_instance%
  AddGroupNorm.toNormedAddGroup
    { toFun := norm
      map_zero' := norm_zero
      neg' := norm_neg
      add_le' := fun f g => by
        rcases p.dichotomy with (rfl | hp')
        · cases isEmpty_or_nonempty α
          · simp only [lp.eq_zero' f, zero_add, norm_zero, le_refl]
          refine (lp.isLUB_norm (f + g)).2 ?_
          rintro x ⟨i, rfl⟩
          refine le_trans ?_ (add_mem_upperBounds_add
            (lp.isLUB_norm f).1 (lp.isLUB_norm g).1 ⟨_, ⟨i, rfl⟩, _, ⟨i, rfl⟩, rfl⟩)
          exact norm_add_le (f i) (g i)
        · have hp'' : 0 < p.toReal := zero_lt_one.trans_le hp'
          have hf₁ : ∀ i, 0 ≤ ‖f i‖ := fun i => norm_nonneg _
          have hg₁ : ∀ i, 0 ≤ ‖g i‖ := fun i => norm_nonneg _
          have hf₂ := lp.hasSum_norm hp'' f
          have hg₂ := lp.hasSum_norm hp'' g
          -- apply Minkowski's inequality
          obtain ⟨C, hC₁, hC₂, hCfg⟩ :=
            Real.Lp_add_le_hasSum_of_nonneg hp' hf₁ hg₁ (norm_nonneg' _) (norm_nonneg' _) hf₂ hg₂
          refine le_trans ?_ hC₂
          rw [← Real.rpow_le_rpow_iff (norm_nonneg' (f + g)) hC₁ hp'']
          refine hasSum_le ?_ (lp.hasSum_norm hp'' (f + g)) hCfg
          intro i
          gcongr
          apply norm_add_le
      eq_zero_of_map_eq_zero' := fun _ => norm_eq_zero_iff.1 }

-- TODO: define an `ENNReal` version of `HolderConjugate`, and then express this inequality
-- in a better version which also covers the case `p = 1, q = ∞`.
/-- Hölder inequality -/
protected theorem tsum_mul_le_mul_norm {p q : ℝ≥0∞} (hpq : p.toReal.HolderConjugate q.toReal)
    (f : lp E p) (g : lp E q) :
    (Summable fun i => ‖f i‖ * ‖g i‖) ∧ ∑' i, ‖f i‖ * ‖g i‖ ≤ ‖f‖ * ‖g‖ := by
  have hf₁ : ∀ i, 0 ≤ ‖f i‖ := fun i => norm_nonneg _
  have hg₁ : ∀ i, 0 ≤ ‖g i‖ := fun i => norm_nonneg _
  have hf₂ := lp.hasSum_norm hpq.pos f
  have hg₂ := lp.hasSum_norm hpq.symm.pos g
  obtain ⟨C, -, hC', hC⟩ :=
    Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg hpq (norm_nonneg' _) (norm_nonneg' _) hf₁ hg₁ hf₂ hg₂
  rw [← hC.tsum_eq] at hC'
  exact ⟨hC.summable, hC'⟩

protected theorem summable_mul {p q : ℝ≥0∞} (hpq : p.toReal.HolderConjugate q.toReal)
    (f : lp E p) (g : lp E q) : Summable fun i => ‖f i‖ * ‖g i‖ :=
  (lp.tsum_mul_le_mul_norm hpq f g).1

protected theorem tsum_mul_le_mul_norm' {p q : ℝ≥0∞} (hpq : p.toReal.HolderConjugate q.toReal)
    (f : lp E p) (g : lp E q) : ∑' i, ‖f i‖ * ‖g i‖ ≤ ‖f‖ * ‖g‖ :=
  (lp.tsum_mul_le_mul_norm hpq f g).2

section ComparePointwise

theorem norm_apply_le_norm (hp : p ≠ 0) (f : lp E p) (i : α) : ‖f i‖ ≤ ‖f‖ := by
  rcases eq_or_ne p ∞ with (rfl | hp')
  · haveI : Nonempty α := ⟨i⟩
    exact (isLUB_norm f).1 ⟨i, rfl⟩
  have hp'' : 0 < p.toReal := ENNReal.toReal_pos hp hp'
  have : ∀ i, 0 ≤ ‖f i‖ ^ p.toReal := fun i => Real.rpow_nonneg (norm_nonneg _) _
  rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg' _) hp'']
  convert le_hasSum (hasSum_norm hp'' f) i fun i _ => this i

theorem sum_rpow_le_norm_rpow (hp : 0 < p.toReal) (f : lp E p) (s : Finset α) :
    ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ ‖f‖ ^ p.toReal := by
  rw [lp.norm_rpow_eq_tsum hp f]
  have : ∀ i, 0 ≤ ‖f i‖ ^ p.toReal := fun i => Real.rpow_nonneg (norm_nonneg _) _
  refine Summable.sum_le_tsum _ (fun i _ => this i) ?_
  exact (lp.memℓp f).summable hp

theorem norm_le_of_forall_le' [Nonempty α] {f : lp E ∞} (C : ℝ) (hCf : ∀ i, ‖f i‖ ≤ C) :
    ‖f‖ ≤ C := by
  refine (isLUB_norm f).2 ?_
  rintro - ⟨i, rfl⟩
  exact hCf i

theorem norm_le_of_forall_le {f : lp E ∞} {C : ℝ} (hC : 0 ≤ C) (hCf : ∀ i, ‖f i‖ ≤ C) :
    ‖f‖ ≤ C := by
  cases isEmpty_or_nonempty α
  · simpa [eq_zero' f] using hC
  · exact norm_le_of_forall_le' C hCf

theorem norm_le_of_tsum_le (hp : 0 < p.toReal) {C : ℝ} (hC : 0 ≤ C) {f : lp E p}
    (hf : ∑' i, ‖f i‖ ^ p.toReal ≤ C ^ p.toReal) : ‖f‖ ≤ C := by
  rw [← Real.rpow_le_rpow_iff (norm_nonneg' _) hC hp, norm_rpow_eq_tsum hp]
  exact hf

theorem norm_le_of_forall_sum_le (hp : 0 < p.toReal) {C : ℝ} (hC : 0 ≤ C) {f : lp E p}
    (hf : ∀ s : Finset α, ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ C ^ p.toReal) : ‖f‖ ≤ C :=
  norm_le_of_tsum_le hp hC (((lp.memℓp f).summable hp).tsum_le_of_sum_le hf)

end ComparePointwise

section IsBoundedSMul

variable [NormedRing 𝕜] [NormedRing 𝕜']
variable [∀ i, Module 𝕜 (E i)] [∀ i, Module 𝕜' (E i)]

instance : Module 𝕜 (PreLp E) :=
  Pi.module α E 𝕜

instance [∀ i, SMulCommClass 𝕜' 𝕜 (E i)] : SMulCommClass 𝕜' 𝕜 (PreLp E) :=
  Pi.smulCommClass

instance [SMul 𝕜' 𝕜] [∀ i, IsScalarTower 𝕜' 𝕜 (E i)] : IsScalarTower 𝕜' 𝕜 (PreLp E) :=
  Pi.isScalarTower

instance [∀ i, Module 𝕜ᵐᵒᵖ (E i)] [∀ i, IsCentralScalar 𝕜 (E i)] : IsCentralScalar 𝕜 (PreLp E) :=
  Pi.isCentralScalar

variable [∀ i, IsBoundedSMul 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜' (E i)]

theorem mem_lp_const_smul (c : 𝕜) (f : lp E p) : c • (f : PreLp E) ∈ lp E p :=
  (lp.memℓp f).const_smul c

variable (𝕜 E p)

/-- The `𝕜`-submodule of elements of `∀ i : α, E i` whose `lp` norm is finite. This is `lp E p`,
with extra structure. -/
def _root_.lpSubmodule : Submodule 𝕜 (PreLp E) :=
  { lp E p with smul_mem' := fun c f hf => by simpa using mem_lp_const_smul c ⟨f, hf⟩ }

variable {𝕜 E p}

theorem coe_lpSubmodule : (lpSubmodule 𝕜 E p).toAddSubgroup = lp E p :=
  rfl

instance : Module 𝕜 (lp E p) :=
  { (lpSubmodule 𝕜 E p).module with }

@[simp]
theorem coeFn_smul (c : 𝕜) (f : lp E p) : ⇑(c • f) = c • ⇑f :=
  rfl

instance [∀ i, SMulCommClass 𝕜' 𝕜 (E i)] : SMulCommClass 𝕜' 𝕜 (lp E p) :=
  ⟨fun _ _ _ => Subtype.ext <| smul_comm _ _ _⟩

instance [SMul 𝕜' 𝕜] [∀ i, IsScalarTower 𝕜' 𝕜 (E i)] : IsScalarTower 𝕜' 𝕜 (lp E p) :=
  ⟨fun _ _ _ => Subtype.ext <| smul_assoc _ _ _⟩

instance [∀ i, Module 𝕜ᵐᵒᵖ (E i)] [∀ i, IsCentralScalar 𝕜 (E i)] : IsCentralScalar 𝕜 (lp E p) :=
  ⟨fun _ _ => Subtype.ext <| op_smul_eq_smul _ _⟩

theorem norm_const_smul_le (hp : p ≠ 0) (c : 𝕜) (f : lp E p) : ‖c • f‖ ≤ ‖c‖ * ‖f‖ := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · exact absurd rfl hp
  · cases isEmpty_or_nonempty α
    · simp [lp.eq_zero' f]
    have hcf := lp.isLUB_norm (c • f)
    have hfc := (lp.isLUB_norm f).mul_left (norm_nonneg c)
    simp_rw [← Set.range_comp, Function.comp_def] at hfc
    -- TODO: some `IsLUB` API should make it a one-liner from here.
    refine hcf.right ?_
    have := hfc.left
    simp_rw [mem_upperBounds, Set.mem_range,
      forall_exists_index, forall_apply_eq_imp_iff] at this ⊢
    intro a
    exact (norm_smul_le _ _).trans (this a)
  · letI inst : NNNorm (lp E p) := ⟨fun f => ⟨‖f‖, norm_nonneg' _⟩⟩
    have coe_nnnorm : ∀ f : lp E p, ↑‖f‖₊ = ‖f‖ := fun _ => rfl
    suffices ‖c • f‖₊ ^ p.toReal ≤ (‖c‖₊ * ‖f‖₊) ^ p.toReal by
      rwa [NNReal.rpow_le_rpow_iff hp] at this
    clear_value inst
    rw [NNReal.mul_rpow]
    have hLHS := lp.hasSum_norm hp (c • f)
    have hRHS := (lp.hasSum_norm hp f).mul_left (‖c‖ ^ p.toReal)
    simp_rw [← coe_nnnorm, ← _root_.coe_nnnorm, ← NNReal.coe_rpow, ← NNReal.coe_mul,
      NNReal.hasSum_coe] at hRHS hLHS
    refine hasSum_mono hLHS hRHS fun i => ?_
    dsimp only
    rw [← NNReal.mul_rpow, lp.coeFn_smul, Pi.smul_apply]
    gcongr
    apply nnnorm_smul_le

instance [Fact (1 ≤ p)] : IsBoundedSMul 𝕜 (lp E p) :=
  IsBoundedSMul.of_norm_smul_le <| norm_const_smul_le (zero_lt_one.trans_le <| Fact.out).ne'

end IsBoundedSMul

section DivisionRing

variable [NormedDivisionRing 𝕜] [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)]

theorem norm_const_smul (hp : p ≠ 0) {c : 𝕜} (f : lp E p) : ‖c • f‖ = ‖c‖ * ‖f‖ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  refine le_antisymm (norm_const_smul_le hp c f) ?_
  have := mul_le_mul_of_nonneg_left (norm_const_smul_le hp c⁻¹ (c • f)) (norm_nonneg c)
  rwa [inv_smul_smul₀ hc, norm_inv, mul_inv_cancel_left₀ (norm_ne_zero_iff.mpr hc)] at this

end DivisionRing

section NormedSpace

variable [NormedField 𝕜] [∀ i, NormedSpace 𝕜 (E i)]

instance instNormedSpace [Fact (1 ≤ p)] : NormSMulClass 𝕜 (lp E p) :=
  NormedDivisionRing.toNormSMulClass

end NormedSpace

section NormedStarGroup

variable [∀ i, StarAddMonoid (E i)] [∀ i, NormedStarGroup (E i)]

theorem _root_.Memℓp.star_mem {f : ∀ i, E i} (hf : Memℓp f p) : Memℓp (star f) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    simp [hf.finite_dsupport]
  · apply memℓp_infty
    simpa using hf.bddAbove
  · apply memℓp_gen
    simpa using hf.summable hp

@[simp]
theorem _root_.Memℓp.star_iff {f : ∀ i, E i} : Memℓp (star f) p ↔ Memℓp f p :=
  ⟨fun h => star_star f ▸ Memℓp.star_mem h, Memℓp.star_mem⟩

instance : Star (lp E p) where
  star f := ⟨(star f : ∀ i, E i), f.property.star_mem⟩

@[simp]
theorem coeFn_star (f : lp E p) : ⇑(star f) = star (⇑f) :=
  rfl

@[simp]
protected theorem star_apply (f : lp E p) (i : α) : star f i = star (f i) :=
  rfl

instance instInvolutiveStar : InvolutiveStar (lp E p) where
  star_involutive x := by simp [star]

instance instStarAddMonoid : StarAddMonoid (lp E p) where
  star_add _f _g := ext <| star_add (R := ∀ i, E i) _ _

instance [hp : Fact (1 ≤ p)] : NormedStarGroup (lp E p) where
  norm_star_le f := le_of_eq <| by
    rcases p.trichotomy with (rfl | rfl | h)
    · exfalso
      have := ENNReal.toReal_mono ENNReal.zero_ne_top hp.elim
      norm_num at this
    · simp only [lp.norm_eq_ciSup, lp.star_apply, norm_star]
    · simp only [lp.norm_eq_tsum_rpow h, lp.star_apply, norm_star]

variable [Star 𝕜] [NormedRing 𝕜]
variable [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)] [∀ i, StarModule 𝕜 (E i)]

instance : StarModule 𝕜 (lp E p) where
  star_smul _r _f := ext <| star_smul (A := ∀ i, E i) _ _

end NormedStarGroup

section NonUnitalNormedRing

variable {I : Type*} {B : I → Type*} [∀ i, NonUnitalNormedRing (B i)]

theorem _root_.Memℓp.infty_mul {f g : ∀ i, B i} (hf : Memℓp f ∞) (hg : Memℓp g ∞) :
    Memℓp (f * g) ∞ := by
  rw [memℓp_infty_iff]
  obtain ⟨⟨Cf, hCf⟩, ⟨Cg, hCg⟩⟩ := hf.bddAbove, hg.bddAbove
  refine ⟨Cf * Cg, ?_⟩
  rintro _ ⟨i, rfl⟩
  calc
    ‖(f * g) i‖ ≤ ‖f i‖ * ‖g i‖ := norm_mul_le (f i) (g i)
    _ ≤ Cf * Cg :=
      mul_le_mul (hCf ⟨i, rfl⟩) (hCg ⟨i, rfl⟩) (norm_nonneg _)
        ((norm_nonneg _).trans (hCf ⟨i, rfl⟩))

instance : Mul (lp B ∞) where
  mul f g := ⟨HMul.hMul (α := ∀ i, B i) _ _, f.property.infty_mul g.property⟩

@[simp]
theorem infty_coeFn_mul (f g : lp B ∞) : ⇑(f * g) = ⇑f * ⇑g :=
  rfl

instance nonUnitalRing : NonUnitalRing (lp B ∞) :=
  Function.Injective.nonUnitalRing lp.coeFun.coe Subtype.coe_injective (lp.coeFn_zero B ∞)
    lp.coeFn_add infty_coeFn_mul lp.coeFn_neg lp.coeFn_sub (fun _ _ => rfl) fun _ _ => rfl

set_option synthInstance.maxHeartbeats 100000 in
-- something wrong here, investigate
instance nonUnitalNormedRing : WithNormedRing (lp B ∞) :=
  { lp.normedAddCommGroup with
    norm_mul_le f g := lp.norm_le_of_forall_le (by positivity) fun i ↦ calc
      ‖(f * g) i‖ ≤ ‖f i‖ * ‖g i‖ := norm_mul_le _ _
      _ ≤ ‖f‖ * ‖g‖ := mul_le_mul (lp.norm_apply_le_norm ENNReal.top_ne_zero f i)
        (lp.norm_apply_le_norm ENNReal.top_ne_zero g i) (norm_nonneg _) (norm_nonneg _) }

instance nonUnitalCommRing {B : I → Type*} [∀ i, NonUnitalNormedCommRing (B i)] :
    NonUnitalCommRing (lp B ∞) where
  mul_comm _ _ := ext <| mul_comm ..

-- we also want a `NonUnitalNormedCommRing` instance, but this has to wait for https://github.com/leanprover-community/mathlib3/pull/13719
instance infty_isScalarTower {𝕜} [NormedRing 𝕜] [∀ i, Module 𝕜 (B i)] [∀ i, IsBoundedSMul 𝕜 (B i)]
    [∀ i, IsScalarTower 𝕜 (B i) (B i)] : IsScalarTower 𝕜 (lp B ∞) (lp B ∞) :=
  ⟨fun r f g => lp.ext <| smul_assoc (N := ∀ i, B i) (α := ∀ i, B i) r (⇑f) (⇑g)⟩

instance infty_smulCommClass {𝕜} [NormedRing 𝕜] [∀ i, Module 𝕜 (B i)] [∀ i, IsBoundedSMul 𝕜 (B i)]
    [∀ i, SMulCommClass 𝕜 (B i) (B i)] : SMulCommClass 𝕜 (lp B ∞) (lp B ∞) :=
  ⟨fun r f g => lp.ext <| smul_comm (N := ∀ i, B i) (α := ∀ i, B i) r (⇑f) (⇑g)⟩

section StarRing

variable [∀ i, StarRing (B i)] [∀ i, NormedStarGroup (B i)]

instance inftyStarRing : StarRing (lp B ∞) :=
  { lp.instStarAddMonoid with
    star_mul := fun _f _g => ext <| star_mul (R := ∀ i, B i) _ _ }

instance inftyCStarRing [∀ i, CStarRing (B i)] : CStarRing (lp B ∞) where
  norm_mul_self_le f := by
    rw [← sq, ← Real.le_sqrt (norm_nonneg _) (norm_nonneg _)]
    refine lp.norm_le_of_forall_le ‖star f * f‖.sqrt_nonneg fun i => ?_
    rw [Real.le_sqrt (norm_nonneg _) (norm_nonneg _), sq, ← CStarRing.norm_star_mul_self]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero (star f * f) i

end StarRing

end NonUnitalNormedRing

section NormedRing

variable {I : Type*} {B : I → Type*} [∀ i, NormedRing (B i)]

instance _root_.PreLp.ring : Ring (PreLp B) :=
  Pi.ring

variable [∀ i, NormOneClass (B i)]

theorem _root_.one_memℓp_infty : Memℓp (1 : ∀ i, B i) ∞ :=
  ⟨1, by rintro i ⟨i, rfl⟩; exact norm_one.le⟩

variable (B) in
/-- The `𝕜`-subring of elements of `∀ i : α, B i` whose `lp` norm is finite. This is `lp E ∞`,
with extra structure. -/
def _root_.lpInftySubring : Subring (PreLp B) :=
  { lp B ∞ with
    carrier := { f | Memℓp f ∞ }
    one_mem' := one_memℓp_infty
    mul_mem' := Memℓp.infty_mul }

instance inftyRing : Ring (lp B ∞) :=
  (lpInftySubring B).toRing

theorem _root_.Memℓp.infty_pow {f : ∀ i, B i} (hf : Memℓp f ∞) (n : ℕ) : Memℓp (f ^ n) ∞ :=
  (lpInftySubring B).pow_mem hf n

theorem _root_.natCast_memℓp_infty (n : ℕ) : Memℓp (n : ∀ i, B i) ∞ :=
  natCast_mem (lpInftySubring B) n

theorem _root_.intCast_memℓp_infty (z : ℤ) : Memℓp (z : ∀ i, B i) ∞ :=
  intCast_mem (lpInftySubring B) z

@[simp]
theorem infty_coeFn_one : ⇑(1 : lp B ∞) = 1 :=
  rfl

@[simp]
theorem infty_coeFn_pow (f : lp B ∞) (n : ℕ) : ⇑(f ^ n) = (⇑f) ^ n :=
  rfl

@[simp]
theorem infty_coeFn_natCast (n : ℕ) : ⇑(n : lp B ∞) = n :=
  rfl

@[simp]
theorem infty_coeFn_intCast (z : ℤ) : ⇑(z : lp B ∞) = z :=
  rfl

instance [Nonempty I] : NormOneClass (lp B ∞) where
  norm_one := by simp_rw [lp.norm_eq_ciSup, infty_coeFn_one, Pi.one_apply, norm_one, ciSup_const]

end NormedRing

section NormedCommRing

variable {I : Type*} {B : I → Type*} [∀ i, NormedCommRing (B i)] [∀ i, NormOneClass (B i)]

instance inftyCommRing : CommRing (lp B ∞) where
  mul_comm := mul_comm

example : NormedCommRing (lp B ∞) := by infer_instance

end NormedCommRing

section Algebra

variable {I : Type*} {B : I → Type*}
variable [NormedField 𝕜] [∀ i, NormedRing (B i)] [∀ i, NormedAlgebra 𝕜 (B i)]

instance _root_.PreLp.algebra : Algebra 𝕜 (PreLp B) :=
  inferInstanceAs (Algebra 𝕜 (∀ i, B i))

variable [∀ i, NormOneClass (B i)]

theorem _root_.algebraMap_memℓp_infty (k : 𝕜) : Memℓp (algebraMap 𝕜 (∀ i, B i) k) ∞ := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (one_memℓp_infty.const_smul k : Memℓp (k • (1 : ∀ i, B i)) ∞)

variable (𝕜 B)

/-- The `𝕜`-subalgebra of elements of `∀ i : α, B i` whose `lp` norm is finite. This is `lp E ∞`,
with extra structure. -/
def _root_.lpInftySubalgebra : Subalgebra 𝕜 (PreLp B) :=
  { lpInftySubring B with
    carrier := { f | Memℓp f ∞ }
    algebraMap_mem' := algebraMap_memℓp_infty }

variable {𝕜 B}

instance inftyAlgebra : Algebra 𝕜 (lp B ∞) := (lpInftySubalgebra 𝕜 B).algebra

set_option synthInstance.maxHeartbeats 100000 in
-- something wrong here, investigate
example : NormedAlgebra 𝕜 (lp B ∞) := by infer_instance

end Algebra

section Single

variable [NormedRing 𝕜] [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)]
variable [DecidableEq α]

/-- The element of `lp E p` which is `a : E i` at the index `i`, and zero elsewhere. -/
protected def single (p) (i : α) (a : E i) : lp E p :=
  ⟨Pi.single i a, by
    refine (memℓp_zero ?_).of_exponent_ge (zero_le p)
    refine (Set.finite_singleton i).subset ?_
    intro j
    simp only [Set.mem_singleton_iff, Ne,
      Set.mem_setOf_eq]
    rw [not_imp_comm]
    intro h
    exact Pi.single_eq_of_ne h _⟩

@[norm_cast]
protected theorem coeFn_single (p) (i : α) (a : E i) :
    ⇑(lp.single p i a) = Pi.single i a := rfl

@[simp]
protected theorem single_apply (p) (i : α) (a : E i) (j : α) :
    lp.single p i a j = Pi.single i a j :=
  rfl

protected theorem single_apply_self (p) (i : α) (a : E i) : lp.single p i a i = a :=
  Pi.single_eq_same _ _

protected theorem single_apply_ne (p) (i : α) (a : E i) {j : α} (hij : j ≠ i) :
    lp.single p i a j = 0 :=
  Pi.single_eq_of_ne hij _

@[simp]
protected theorem single_zero (p) (i : α) :
    lp.single p i (0 : E i) = 0 :=
  ext <| Pi.single_zero _

@[simp]
protected theorem single_add (p) (i : α) (a b : E i) :
    lp.single p i (a + b) = lp.single p i a + lp.single p i b :=
  ext <| Pi.single_add _ _ _

/-- `single` as an `AddMonoidHom`. -/
@[simps]
def singleAddMonoidHom (p) (i : α) : E i →+ lp E p where
  toFun := lp.single p i
  map_zero' := lp.single_zero _ _
  map_add' := lp.single_add _ _

@[simp]
protected theorem single_neg (p) (i : α) (a : E i) : lp.single p i (-a) = -lp.single p i a :=
  ext <| Pi.single_neg _ _

@[simp]
protected theorem single_sub (p) (i : α) (a b : E i) :
    lp.single p i (a - b) = lp.single p i a - lp.single p i b :=
  ext <| Pi.single_sub _ _ _

@[simp]
protected theorem single_smul (p) (i : α) (c : 𝕜) (a : E i) :
    lp.single p i (c • a) = c • lp.single p i a :=
  ext <| Pi.single_smul _ _ _

/-- `single` as a `LinearMap`. -/
@[simps]
def lsingle (p) (i : α) : E i →ₗ[𝕜] lp E p where
  toFun := lp.single p i
  __ := singleAddMonoidHom p i
  map_smul' := lp.single_smul p i

protected theorem norm_sum_single (hp : 0 < p.toReal) (f : ∀ i, E i) (s : Finset α) :
    ‖∑ i ∈ s, lp.single p i (f i)‖ ^ p.toReal = ∑ i ∈ s, ‖f i‖ ^ p.toReal := by
  refine (hasSum_norm hp (∑ i ∈ s, lp.single p i (f i))).unique ?_
  simp only [lp.coeFn_single, coeFn_sum, Finset.sum_apply, Finset.sum_pi_single]
  have h : ∀ i ∉ s, ‖ite (i ∈ s) (f i) 0‖ ^ p.toReal = 0 := fun i hi ↦ by
    simp [if_neg hi, Real.zero_rpow hp.ne']
  have h' : ∀ i ∈ s, ‖f i‖ ^ p.toReal = ‖ite (i ∈ s) (f i) 0‖ ^ p.toReal := by
    intro i hi
    rw [if_pos hi]
  simpa [Finset.sum_congr rfl h'] using hasSum_sum_of_ne_finset_zero h

@[simp]
protected theorem norm_single (hp : 0 < p) (i : α) (x : E i) : ‖lp.single p i x‖ = ‖x‖ := by
  haveI : Nonempty α := ⟨i⟩
  induction p with
  | top =>
    simp only [norm_eq_ciSup, lp.coeFn_single]
    refine
      ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun j => ?_) fun n hn => ⟨i, hn.trans_eq ?_⟩
    · obtain rfl | hij := Decidable.eq_or_ne i j
      · rw [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne' hij, _root_.norm_zero]
        exact norm_nonneg _
    · rw [Pi.single_eq_same]
  | coe p =>
    have : 0 < (p : ℝ≥0∞).toReal := by simpa using hp
    rw [norm_eq_tsum_rpow this, tsum_eq_single i, lp.coeFn_single, one_div,
      Real.rpow_rpow_inv _ this.ne', Pi.single_eq_same]
    · exact norm_nonneg _
    · intro j hji
      rw [lp.coeFn_single, Pi.single_eq_of_ne hji, _root_.norm_zero, Real.zero_rpow this.ne']

theorem isometry_single [Fact (1 ≤ p)] (i : α) : Isometry (lp.single (E := E) p i) :=
  AddMonoidHomClass.isometry_of_norm (lp.singleAddMonoidHom (E := E) p i) fun _ ↦
    lp.norm_single (zero_lt_one.trans_le Fact.out) _ _

variable (p E) in
/-- `lp.single` as a continuous morphism of additive monoids. -/
def singleContinuousAddMonoidHom [Fact (1 ≤ p)] (i : α) :
    ContinuousAddMonoidHom (E i) (lp E p) where
  __ := singleAddMonoidHom p i
  continuous_toFun := isometry_single i |>.continuous

@[simp]
theorem singleContinuousAddMonoidHom_apply [Fact (1 ≤ p)] (i : α) (x : E i) :
    singleContinuousAddMonoidHom E p i x = lp.single p i x :=
  rfl

variable (𝕜 p E) in
/-- `lp.single` as a continuous linear map. -/
def singleContinuousLinearMap [Fact (1 ≤ p)] (i : α) : E i →L[𝕜] lp E p where
  __ := lsingle p i
  cont := isometry_single i |>.continuous

@[simp]
theorem singleContinuousLinearMap_apply [Fact (1 ≤ p)] (i : α) (x : E i) :
    singleContinuousLinearMap 𝕜 E p i x = lp.single p i x :=
  rfl

protected theorem norm_sub_norm_compl_sub_single (hp : 0 < p.toReal) (f : lp E p) (s : Finset α) :
    ‖f‖ ^ p.toReal - ‖f - ∑ i ∈ s, lp.single p i (f i)‖ ^ p.toReal =
      ∑ i ∈ s, ‖f i‖ ^ p.toReal := by
  refine ((hasSum_norm hp f).sub (hasSum_norm hp (f - ∑ i ∈ s, lp.single p i (f i)))).unique ?_
  let F : α → ℝ := fun i => ‖f i‖ ^ p.toReal - ‖(f - ∑ i ∈ s, lp.single p i (f i)) i‖ ^ p.toReal
  have hF : ∀ i ∉ s, F i = 0 := by
    intro i hi
    suffices ‖f i‖ ^ p.toReal - ‖f i - ite (i ∈ s) (f i) 0‖ ^ p.toReal = 0 by
      simpa only [coeFn_sub, coeFn_sum, lp.coeFn_single, Pi.sub_apply, Finset.sum_apply,
        Finset.sum_pi_single, F] using this
    simp only [if_neg hi, sub_zero, sub_self]
  have hF' : ∀ i ∈ s, F i = ‖f i‖ ^ p.toReal := by
    intro i hi
    simp only [F, coeFn_sum, lp.single_apply, if_pos hi, sub_self, coeFn_sub,
      Pi.sub_apply, Finset.sum_apply, Finset.sum_pi_single, sub_eq_self]
    simp [Real.zero_rpow hp.ne']
  have : HasSum F (∑ i ∈ s, F i) := hasSum_sum_of_ne_finset_zero hF
  rwa [Finset.sum_congr rfl hF'] at this

protected theorem norm_compl_sum_single (hp : 0 < p.toReal) (f : lp E p) (s : Finset α) :
    ‖f - ∑ i ∈ s, lp.single p i (f i)‖ ^ p.toReal = ‖f‖ ^ p.toReal - ∑ i ∈ s, ‖f i‖ ^ p.toReal := by
  linarith [lp.norm_sub_norm_compl_sub_single hp f s]

/-- The canonical finitely-supported approximations to an element `f` of `lp` converge to it, in the
`lp` topology. -/
protected theorem hasSum_single [Fact (1 ≤ p)] (hp : p ≠ ⊤) (f : lp E p) :
    HasSum (fun i : α => lp.single p i (f i : E i)) f := by
  have hp₀ : 0 < p := zero_lt_one.trans_le Fact.out
  have hp' : 0 < p.toReal := ENNReal.toReal_pos hp₀.ne' hp
  have := lp.hasSum_norm hp' f
  rw [HasSum, Metric.tendsto_nhds] at this ⊢
  intro ε hε
  refine (this _ (Real.rpow_pos_of_pos hε p.toReal)).mono ?_
  intro s hs
  rw [← Real.rpow_lt_rpow_iff dist_nonneg (le_of_lt hε) hp']
  rw [dist_comm] at hs
  simp only [dist_eq_norm, Real.norm_eq_abs] at hs ⊢
  have H : ‖(∑ i ∈ s, lp.single p i (f i : E i)) - f‖ ^ p.toReal =
      ‖f‖ ^ p.toReal - ∑ i ∈ s, ‖f i‖ ^ p.toReal := by
    simpa only [coeFn_neg, Pi.neg_apply, lp.single_neg, Finset.sum_neg_distrib, neg_sub_neg,
      norm_neg, _root_.norm_neg] using lp.norm_compl_sum_single hp' (-f) s
  rw [← H] at hs
  have : |‖(∑ i ∈ s, lp.single p i (f i : E i)) - f‖ ^ p.toReal| =
      ‖(∑ i ∈ s, lp.single p i (f i : E i)) - f‖ ^ p.toReal := by
    simp only [Real.abs_rpow_of_nonneg (norm_nonneg _), abs_norm]
  exact this ▸ hs

/-- Two continuous additive maps from `lp E p` agree if they agree on `lp.single`.

See note [partially-applied ext lemmas]. -/
@[local ext] -- not globally `ext` due to `hp`
theorem ext_continuousAddMonoidHom
    {F : Type*} [AddCommMonoid F] [TopologicalSpace F] [T2Space F]
    [Fact (1 ≤ p)] (hp : p ≠ ⊤) ⦃f g : ContinuousAddMonoidHom (lp E p) F⦄
    (h : ∀ i,
      f.comp (singleContinuousAddMonoidHom E p i) = g.comp (singleContinuousAddMonoidHom E p i)) :
    f = g := by
  ext x
  classical
  have := lp.hasSum_single hp x
  rw [← (this.map f f.continuous).tsum_eq, ← (this.map g g.continuous).tsum_eq]
  congr! 2 with i
  exact DFunLike.congr_fun (h i) (x i)

/-- Two continuous linear maps from `lp E p` agree if they agree on `lp.single`.

See note [partially-applied ext lemmas]. -/
@[local ext] -- not globally `ext` due to `hp`
theorem ext_continuousLinearMap
    {F : Type*} [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F] [T2Space F]
    [Fact (1 ≤ p)] (hp : p ≠ ⊤) ⦃f g : lp E p →L[𝕜] F⦄
    (h : ∀ i,
      f.comp (singleContinuousLinearMap 𝕜 E p i) = g.comp (singleContinuousLinearMap 𝕜 E p i)) :
    f = g :=
  ContinuousLinearMap.toContinuousAddMonoidHom_injective <|
    ext_continuousAddMonoidHom hp fun i => ContinuousLinearMap.toContinuousAddMonoidHom_inj.2 (h i)

end Single

section Topology

open Filter

open scoped Topology uniformity

/-- The coercion from `lp E p` to `∀ i, E i` is uniformly continuous. -/
theorem uniformContinuous_coe [_i : Fact (1 ≤ p)] :
    UniformContinuous (α := lp E p) ((↑) : lp E p → ∀ i, E i) := by
  have hp : p ≠ 0 := (zero_lt_one.trans_le _i.elim).ne'
  rw [uniformContinuous_pi]
  intro i
  rw [NormedAddCommGroup.uniformity_basis_dist.uniformContinuous_iff
    NormedAddCommGroup.uniformity_basis_dist]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  rintro f g (hfg : ‖f - g‖ < ε)
  have : ‖f i - g i‖ ≤ ‖f - g‖ := norm_apply_le_norm hp (f - g) i
  exact this.trans_lt hfg

variable {ι : Type*} {l : Filter ι} [Filter.NeBot l]

theorem norm_apply_le_of_tendsto {C : ℝ} {F : ι → lp E ∞} (hCF : ∀ᶠ k in l, ‖F k‖ ≤ C)
    {f : ∀ a, E a} (hf : Tendsto (id fun i => F i : ι → ∀ a, E a) l (𝓝 f)) (a : α) : ‖f a‖ ≤ C := by
  have : Tendsto (fun k => ‖F k a‖) l (𝓝 ‖f a‖) :=
    (Tendsto.comp (continuous_apply a).continuousAt hf).norm
  refine le_of_tendsto this (hCF.mono ?_)
  intro k hCFk
  exact (norm_apply_le_norm ENNReal.top_ne_zero (F k) a).trans hCFk

variable [_i : Fact (1 ≤ p)]

theorem sum_rpow_le_of_tendsto (hp : p ≠ ∞) {C : ℝ} {F : ι → lp E p} (hCF : ∀ᶠ k in l, ‖F k‖ ≤ C)
    {f : ∀ a, E a} (hf : Tendsto (id fun i => F i : ι → ∀ a, E a) l (𝓝 f)) (s : Finset α) :
    ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ C ^ p.toReal := by
  have hp' : p ≠ 0 := (zero_lt_one.trans_le _i.elim).ne'
  have hp'' : 0 < p.toReal := ENNReal.toReal_pos hp' hp
  let G : (∀ a, E a) → ℝ := fun f => ∑ a ∈ s, ‖f a‖ ^ p.toReal
  have hG : Continuous G := by
    refine continuous_finset_sum s ?_
    intro a _
    have : Continuous fun f : ∀ a, E a => f a := continuous_apply a
    exact this.norm.rpow_const fun _ => Or.inr hp''.le
  refine le_of_tendsto (hG.continuousAt.tendsto.comp hf) ?_
  refine hCF.mono ?_
  intro k hCFk
  refine (lp.sum_rpow_le_norm_rpow hp'' (F k) s).trans ?_
  gcongr

/-- "Semicontinuity of the `lp` norm": If all sufficiently large elements of a sequence in `lp E p`
have `lp` norm `≤ C`, then the pointwise limit, if it exists, also has `lp` norm `≤ C`. -/
theorem norm_le_of_tendsto {C : ℝ} {F : ι → lp E p} (hCF : ∀ᶠ k in l, ‖F k‖ ≤ C) {f : lp E p}
    (hf : Tendsto (id fun i => F i : ι → ∀ a, E a) l (𝓝 f)) : ‖f‖ ≤ C := by
  obtain ⟨i, hi⟩ := hCF.exists
  have hC : 0 ≤ C := (norm_nonneg _).trans hi
  rcases eq_top_or_lt_top p with (rfl | hp)
  · apply norm_le_of_forall_le hC
    exact norm_apply_le_of_tendsto hCF hf
  · have : 0 < p := zero_lt_one.trans_le _i.elim
    have hp' : 0 < p.toReal := ENNReal.toReal_pos this.ne' hp.ne
    apply norm_le_of_forall_sum_le hp' hC
    exact sum_rpow_le_of_tendsto hp.ne hCF hf

/-- If `f` is the pointwise limit of a bounded sequence in `lp E p`, then `f` is in `lp E p`. -/
theorem memℓp_of_tendsto {F : ι → lp E p} (hF : Bornology.IsBounded (Set.range F)) {f : ∀ a, E a}
    (hf : Tendsto (id fun i => F i : ι → ∀ a, E a) l (𝓝 f)) : Memℓp f p := by
  obtain ⟨C, hCF⟩ : ∃ C, ∀ k, ‖F k‖ ≤ C := hF.exists_norm_le.imp fun _ ↦ Set.forall_mem_range.1
  rcases eq_top_or_lt_top p with (rfl | hp)
  · apply memℓp_infty
    use C
    rintro _ ⟨a, rfl⟩
    exact norm_apply_le_of_tendsto (Eventually.of_forall hCF) hf a
  · apply memℓp_gen'
    exact sum_rpow_le_of_tendsto hp.ne (Eventually.of_forall hCF) hf

/-- If a sequence is Cauchy in the `lp E p` topology and pointwise convergent to an element `f` of
`lp E p`, then it converges to `f` in the `lp E p` topology. -/
theorem tendsto_lp_of_tendsto_pi {F : ℕ → lp E p} (hF : CauchySeq F) {f : lp E p}
    (hf : Tendsto (id fun i => F i : ℕ → ∀ a, E a) atTop (𝓝 f)) : Tendsto F atTop (𝓝 f) := by
  rw [Metric.nhds_basis_closedBall.tendsto_right_iff]
  intro ε hε
  have hε' : { p : lp E p × lp E p | ‖p.1 - p.2‖ < ε } ∈ uniformity (lp E p) :=
    NormedAddCommGroup.uniformity_basis_dist.mem_of_mem hε
  refine (hF.eventually_eventually hε').mono ?_
  rintro n (hn : ∀ᶠ l in atTop, ‖(fun f => F n - f) (F l)‖ < ε)
  refine norm_le_of_tendsto (hn.mono fun k hk => hk.le) ?_
  rw [tendsto_pi_nhds]
  intro a
  exact (hf.apply_nhds a).const_sub (F n a)

variable [∀ a, CompleteSpace (E a)]

instance completeSpace : CompleteSpace (lp E p) :=
  Metric.complete_of_cauchySeq_tendsto (by
    intro F hF
    -- A Cauchy sequence in `lp E p` is pointwise convergent; let `f` be the pointwise limit.
    obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete
      ((uniformContinuous_coe (p := p)).comp_cauchySeq hF)
    -- Since the Cauchy sequence is bounded, its pointwise limit `f` is in `lp E p`.
    have hf' : Memℓp f p := memℓp_of_tendsto hF.isBounded_range hf
    -- And therefore `f` is its limit in the `lp E p` topology as well as pointwise.
    exact ⟨⟨f, hf'⟩, tendsto_lp_of_tendsto_pi hF hf⟩)

end Topology

end lp

section Lipschitz

open ENNReal lp
variable {ι : Type*}

lemma LipschitzWith.uniformly_bounded [PseudoMetricSpace α] (g : α → ι → ℝ) {K : ℝ≥0}
    (hg : ∀ i, LipschitzWith K (g · i)) (a₀ : α) (hga₀b : Memℓp (g a₀) ∞) (a : α) :
    Memℓp (g a) ∞ := by
  rcases hga₀b with ⟨M, hM⟩
  use ↑K * dist a a₀ + M
  rintro - ⟨i, rfl⟩
  calc
    |g a i| = |g a i - g a₀ i + g a₀ i| := by simp
    _ ≤ |g a i - g a₀ i| + |g a₀ i| := abs_add _ _
    _ ≤ ↑K * dist a a₀ + M := by
        gcongr
        · exact lipschitzWith_iff_dist_le_mul.1 (hg i) a a₀
        · exact hM ⟨i, rfl⟩

theorem LipschitzOnWith.coordinate [PseudoMetricSpace α] (f : α → ℓ^∞(ι)) (s : Set α) (K : ℝ≥0) :
    LipschitzOnWith K f s ↔ ∀ i : ι, LipschitzOnWith K (fun a : α ↦ f a i) s := by
  simp_rw [lipschitzOnWith_iff_dist_le_mul]
  constructor
  · intro hfl i x hx y hy
    calc
      dist (f x i) (f y i) ≤ dist (f x) (f y) := lp.norm_apply_le_norm top_ne_zero (f x - f y) i
      _ ≤ K * dist x y := hfl x hx y hy
  · intro hgl x hx y hy
    apply lp.norm_le_of_forall_le
    · positivity
    intro i
    apply hgl i x hx y hy

theorem LipschitzWith.coordinate [PseudoMetricSpace α] {f : α → ℓ^∞(ι)} (K : ℝ≥0) :
    LipschitzWith K f ↔ ∀ i : ι, LipschitzWith K (fun a : α ↦ f a i) := by
  simp_rw [← lipschitzOnWith_univ]
  apply LipschitzOnWith.coordinate

end Lipschitz
