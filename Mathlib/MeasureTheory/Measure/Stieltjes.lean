/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Order.LeftRightLim

/-!
# Stieltjes measures on the real line

Consider a function `f : ℝ → ℝ` which is monotone and right-continuous. Then one can define a
corresponding measure, giving mass `f b - f a` to the interval `(a, b]`. We implement more
generally this notion for `f : R → ℝ` where `R` is a conditionally complete dense linear order.

## Main definitions

* `StieltjesFunction R` is a structure containing a function from `R → ℝ`, together with the
  assertions that it is monotone and right-continuous. To `f : StieltjesFunction R`, one associates
  a Borel measure `f.measure`.
* `f.measure_Ioc` asserts that `f.measure (Ioc a b) = ofReal (f b - f a)`
* `f.measure_Ioo` asserts that `f.measure (Ioo a b) = ofReal (leftLim f b - f a)`.
* `f.measure_Icc` and `f.measure_Ico` are analogous.
* `Monotone.stieltjesFunction`: to a monotone function `f`, associate the Stieltjes function
  equal to the right limit of `f`. This makes it possible to associate a Stieltjes measure to
  any monotone function.

## Implementation

We define Stieltjes functions over any conditionally complete dense linear order, to be able
to cover the cases of `ℝ≥0` and `[0, T]` in addition to the classical case of `ℝ`. This creates
a few issues, mostly with the management of bottom and top elements. To handle these, we need
two technical definitions:
* `Iotop a b` is the interval `Ioo a b` if `b` is not top, and `Ioc a b` if `b` is top.
* `botSet` is the empty set if there is no bot element, and `{x}` if `x` is bot.

These definitions are just handy tools for some proofs of this file, so they are only included
there, and not exported.

Note that the theory of Stieltjes measures is not completely satisfactory when there is a bot
element `x`: any Stieltjes measure gives zero mass to `{x}` in this case, so the Dirac mass at `x`
is not representable as a Stieltjes measure.
-/

noncomputable section

open Set Filter Function ENNReal NNReal Topology MeasureTheory

open ENNReal (ofReal)

section Prerequisites

variable {R : Type*} [LinearOrder R]

set_option backward.privateInPublic true in
open scoped Classical in
/-- `Iotop a b` is the interval `Ioo a b` if `b` is not top, and `Ioc a b` if `b` is top.
This makes sure that any element which is not bot belongs to an interval `Iotop a b`, and also
that these intervals are all open. These two properties together are important in the proof of
`StieltjesFunction.outer_Ioc`. -/
def Iotop (a b : R) : Set R := if IsTop b then Ioc a b else Ioo a b

lemma Iotop_subset_Ioc {a b : R} : Iotop a b ⊆ Ioc a b := by
  simp only [Iotop]
  split_ifs with h <;> simp [Ioo_subset_Ioc_self]

lemma Ioo_subset_Iotop {a b : R} : Ioo a b ⊆ Iotop a b := by
  simp only [Iotop]
  split_ifs with h <;> simp [Ioo_subset_Ioc_self]

lemma isOpen_Iotop [TopologicalSpace R] [OrderTopology R] (a b : R) : IsOpen (Iotop a b) := by
  simp only [Iotop]
  split_ifs with h
  · have : Ioc a b = Ioi a := Subset.antisymm (fun x hx ↦ hx.1) (fun x hx ↦ by exact ⟨hx, h _⟩)
    simp [this, isOpen_Ioi]
  · simp [isOpen_Ioo]

set_option backward.privateInPublic true in
open scoped Classical in
/-- `botSet` is the set of all bottom elements. -/
def botSet : Set R := {x | IsBot x}

@[simp] lemma Ioc_diff_botSet (a b : R) : Ioc a b \ botSet = Ioc a b := by
  rw [sdiff_eq_left, disjoint_iff_forall_ne]
  rintro c ⟨hc, _⟩ _ hc' rfl
  exact (hc' a).not_gt hc

lemma notMem_botSet_of_lt {x y : R} (h : x < y) : y ∉ botSet := by
  contrapose! h
  exact h x

lemma subsingleton_botSet : (botSet (R := R)).Subsingleton :=
  subsingleton_isBot _

lemma measurableSet_botSet [MeasurableSpace R] [MeasurableSingletonClass R] :
    MeasurableSet (botSet (R := R)) :=
  subsingleton_botSet.measurableSet

end Prerequisites

@[expose] public section

variable (R : Type*) [LinearOrder R] [TopologicalSpace R]

/-! ### Basic properties of Stieltjes functions -/

/-- Bundled monotone right-continuous real functions, used to construct Stieltjes measures. -/
structure StieltjesFunction where
  /-- The underlying function `R → ℝ`.

  Do NOT use directly. Use the coercion instead. -/
  toFun : R → ℝ
  mono' : Monotone toFun
  right_continuous' : ∀ x, ContinuousWithinAt toFun (Ici x) x

namespace StieltjesFunction

variable {R}

attribute [coe] toFun

instance instCoeFun : CoeFun (StieltjesFunction R) fun _ => R → ℝ :=
  ⟨toFun⟩

initialize_simps_projections StieltjesFunction (toFun → apply)

@[ext] lemma ext {f g : StieltjesFunction R} (h : ∀ x, f x = g x) : f = g := by
  exact (StieltjesFunction.mk.injEq ..).mpr (funext h)

variable (f : StieltjesFunction R)

theorem mono : Monotone f :=
  f.mono'

theorem right_continuous (x : R) : ContinuousWithinAt f (Ici x) x :=
  f.right_continuous' x

theorem rightLim_eq [OrderTopology R]
    (f : StieltjesFunction R) (x : R) : Function.rightLim f x = f x := by
  rw [← f.mono.continuousWithinAt_Ioi_iff_rightLim_eq, continuousWithinAt_Ioi_iff_Ici]
  exact f.right_continuous' x

theorem iInf_Ioi_eq [OrderTopology R] [DenselyOrdered R] [NoMaxOrder R]
     (f : StieltjesFunction R) (x : R) : ⨅ r : Ioi x, f r = f x := by
  suffices Function.rightLim f x = ⨅ r : Ioi x, f r by rw [← this, f.rightLim_eq]
  rw [f.mono.rightLim_eq_sInf, sInf_image']
  rw [← neBot_iff]
  infer_instance

theorem iInf_rat_gt_eq (f : StieltjesFunction ℝ) (x : ℝ) :
    ⨅ r : { r' : ℚ // x < r' }, f r = f x := by
  rw [← iInf_Ioi_eq f x]
  refine (Real.iInf_Ioi_eq_iInf_rat_gt _ ?_ f.mono).symm
  refine ⟨f x, fun y => ?_⟩
  rintro ⟨y, hy_mem, rfl⟩
  exact f.mono (le_of_lt hy_mem)

/-- The identity of `ℝ` as a Stieltjes function, used to construct Lebesgue measure. -/
@[simps]
protected def id : StieltjesFunction ℝ where
  toFun := id
  mono' _ _ := id
  right_continuous' _ := continuousWithinAt_id

@[simp]
theorem id_leftLim (x : ℝ) : leftLim StieltjesFunction.id x = x :=
  continuousWithinAt_id.leftLim_eq

variable (R) in
/-- A constant function is a Stieltjes function. -/
protected def const (c : ℝ) : StieltjesFunction R where
  toFun := fun _ ↦ c
  mono' _ _ := by simp
  right_continuous' _ := continuousWithinAt_const

instance instInhabited : Inhabited (StieltjesFunction R) :=
  ⟨StieltjesFunction.const R 0⟩

@[simp] lemma const_apply (c : ℝ) (x : R) : (StieltjesFunction.const R c) x = c := rfl

/-- The sum of two Stieltjes functions is a Stieltjes function. -/
protected def add (f g : StieltjesFunction R) : StieltjesFunction R where
  toFun := fun x => f x + g x
  mono' := f.mono.add g.mono
  right_continuous' := fun x => (f.right_continuous x).add (g.right_continuous x)

instance : AddZeroClass (StieltjesFunction R) where
  add := StieltjesFunction.add
  zero := StieltjesFunction.const R 0
  zero_add _ := ext fun _ ↦ zero_add _
  add_zero _ := ext fun _ ↦ add_zero _

instance : AddCommMonoid (StieltjesFunction R) where
  nsmul n f := nsmulRec n f
  add_assoc _ _ _ := ext fun _ ↦ add_assoc _ _ _
  add_comm _ _ := ext fun _ ↦ add_comm _ _
  __ := StieltjesFunction.instAddZeroClass

instance : Module ℝ≥0 (StieltjesFunction R) where
  smul c f := {
    toFun := fun x ↦ c * f x
    mono' := f.mono.const_mul c.2
    right_continuous' := fun x ↦ (f.right_continuous x).const_smul c.1 }
  one_smul _ := ext fun _ ↦ one_mul _
  mul_smul _ _ _ := ext fun _ ↦ mul_assoc _ _ _
  smul_zero _ := ext fun _ ↦ mul_zero _
  smul_add _ _ _ := ext fun _ ↦ mul_add _ _ _
  add_smul _ _ _ := ext fun _ ↦ add_mul _ _ _
  zero_smul _ := ext fun _ ↦ zero_mul _

@[simp] lemma zero_apply (x : R) : (0 : StieltjesFunction R) x = 0 := rfl

@[simp] lemma add_apply (f g : StieltjesFunction R) (x : R) : (f + g) x = f x + g x := rfl

/-- If a function `f : R → ℝ` is monotone, then the function mapping `x` to the right limit of `f`
at `x` is a Stieltjes function, i.e., it is monotone and right-continuous. -/
noncomputable def _root_.Monotone.stieltjesFunction [OrderTopology R]
    {f : R → ℝ} (hf : Monotone f) : StieltjesFunction R where
  toFun := rightLim f
  mono' _ _ hxy := hf.rightLim hxy
  right_continuous' := by
    intro x s hs
    change ∀ᶠ y in 𝓝[≥] x, rightLim f y ∈ s
    obtain ⟨l, u, hlu, lus⟩ : ∃ l u : ℝ, rightLim f x ∈ Ioo l u ∧ Ioo l u ⊆ s :=
      mem_nhds_iff_exists_Ioo_subset.1 hs
    by_cases! hx : ∀ y, y ≤ x
    · filter_upwards [self_mem_nhdsWithin] with y (hy : x ≤ y)
      rw [show y = x by exact le_antisymm (hx y) hy]
      exact lus hlu
    rcases hx with ⟨y₀, hy₀⟩
    obtain ⟨y, xy, h'y⟩ : ∃ (y : R), x < y ∧ Ioo x y ⊆ f ⁻¹' Ioo l u :=
      (mem_nhdsGT_iff_exists_Ioo_subset' hy₀).1 (hf.tendsto_rightLim x (Ioo_mem_nhds hlu.1 hlu.2))
    filter_upwards [Ico_mem_nhdsGE xy] with z hz
    apply lus
    refine ⟨hlu.1.trans_le (hf.rightLim hz.1), ?_⟩
    rcases hz.1.eq_or_lt with rfl | h''z
    · exact hlu.2
    rcases Filter.eq_or_neBot (𝓝[>] z) with h'z | h'z
    · rw [rightLim_eq_of_eq_bot _ h'z]
      have : z ∈ Ioo x y := ⟨h''z, hz.2⟩
      exact (h'y this).2
    · obtain ⟨a, za, ay⟩ : ∃ a : R, z < a ∧ a < y := Filter.nonempty_of_mem (Ioo_mem_nhdsGT hz.2)
      calc
        rightLim f z ≤ f a := hf.rightLim_le za
        _ < u := (h'y ⟨hz.1.trans_lt za, ay⟩).2

theorem _root_.Monotone.stieltjesFunction_eq
    [OrderTopology R] {f : R → ℝ} (hf : Monotone f) (x : R) :
    hf.stieltjesFunction x = rightLim f x :=
  rfl

theorem countable_leftLim_ne [OrderTopology R] (f : StieltjesFunction R) :
    Set.Countable {x | leftLim f x ≠ f x} := by
  refine Countable.mono ?_ f.mono.countable_not_continuousAt
  intro x hx h'x
  apply hx
  exact (Monotone.continuousWithinAt_Iio_iff_leftLim_eq f.mono).1 h'x.continuousWithinAt

/-! ### The outer measure associated to a Stieltjes function -/


set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
open scoped Classical in
/-- Length of an interval. This is the largest monotone function which correctly measures all
intervals. -/
def length (s : Set R) : ℝ≥0∞ :=
  -- we treat separately the empty case, where the formula below would give `∞`.
  if IsEmpty R then 0
  -- if there is a bot element `x`, it does not belong to any interval `Ioc a b`. So we remove it
  -- when measuring the size of a set (the set `{x}` will have measure `0` in our construction).
  else ⨅ (a) (b) (_ : s \ botSet ⊆ Ioc a b), ofReal (f b - f a)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
lemma length_eq [Nonempty R] (s : Set R) :
    f.length s = ⨅ (a) (b) (_ : s \ botSet ⊆ Ioc a b), ofReal (f b - f a) := by
  simp [length]

lemma length_eq_of_isEmpty [IsEmpty R] (s : Set R) : f.length s = 0 := by
  simp only [length, if_pos]

@[simp]
theorem length_empty : f.length ∅ = 0 := by
  rcases isEmpty_or_nonempty R with hR | hR
  · simp [length_eq_of_isEmpty]
  inhabit R
  rw [length_eq]
  exact nonpos_iff_eq_zero.1 <| iInf_le_of_le default <| iInf_le_of_le default <| by simp

@[simp]
theorem length_Ioc (a b : R) : f.length (Ioc a b) = ofReal (f b - f a) := by
  have : Nonempty R := ⟨a⟩
  rw [length_eq]
  refine
    le_antisymm (iInf_le_of_le a <| iInf₂_le b diff_subset)
      (le_iInf fun a' => le_iInf fun b' => le_iInf fun h => ENNReal.coe_le_coe.2 ?_)
  rcases le_or_gt b a with ab | ab
  · rw [Real.toNNReal_of_nonpos (sub_nonpos.2 (f.mono ab))]
    apply zero_le
  simp only [Ioc_diff_botSet] at h
  obtain ⟨h₁, h₂⟩ := (Ioc_subset_Ioc_iff ab).1 h
  exact Real.toNNReal_le_toNNReal (sub_le_sub (f.mono h₁) (f.mono h₂))

theorem length_mono {s₁ s₂ : Set R} (h : s₁ ⊆ s₂) : f.length s₁ ≤ f.length s₂ := by
  rcases isEmpty_or_nonempty R with hR | hR
  · simp [length_eq_of_isEmpty]
  simp only [length_eq]
  exact iInf_mono fun a => biInf_mono fun b h' => (diff_subset_diff_left h).trans h'

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem length_diff_botSet {s : Set R} : f.length (s \ botSet) = f.length s := by
  rcases isEmpty_or_nonempty R with hR | hR
  · simp [length_eq_of_isEmpty]
  · simp [length_eq]

open MeasureTheory

/-- The Stieltjes outer measure associated to a Stieltjes function. -/
protected def outer : OuterMeasure R :=
  OuterMeasure.ofFunction f.length f.length_empty

theorem outer_le_length (s : Set R) : f.outer s ≤ f.length s :=
  OuterMeasure.ofFunction_le _

variable [OrderTopology R] [CompactIccSpace R]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- If a compact interval `[a, b]` is covered by a union of open interval `(c i, d i)`, then
`f b - f a ≤ ∑ f (d i) - f (c i)`. This is an auxiliary technical statement to prove the same
statement for half-open intervals, the point of the current statement being that one can use
compactness to reduce it to a finite sum, and argue by induction on the size of the covering set.

To be able to handle also the top element if there is one, we use `Iotop` instead of `Ioo` in the
statement. As these intervals are all open, this does not change the proof. -/
theorem length_subadditive_Icc_Ioo {a b : R} {c d : ℕ → R} (ss : Icc a b ⊆ ⋃ i, Iotop (c i) (d i)) :
    ofReal (f b - f a) ≤ ∑' i, ofReal (f (d i) - f (c i)) := by
  suffices
    ∀ (s : Finset ℕ) (b), Icc a b ⊆ (⋃ i ∈ (s : Set ℕ), Iotop (c i) (d i)) →
      (ofReal (f b - f a) : ℝ≥0∞) ≤ ∑ i ∈ s, ofReal (f (d i) - f (c i)) by
    rcases isCompact_Icc.elim_finite_subcover_image
        (fun (i : ℕ) (_ : i ∈ univ) => @isOpen_Iotop _ _ _ _ (c i) (d i)) (by simpa using ss) with
      ⟨s, _, hf, hs⟩
    have e : ⋃ i ∈ (hf.toFinset : Set ℕ), Iotop (c i) (d i) = ⋃ i ∈ s, Iotop (c i) (d i) := by
      simp only [Finset.set_biUnion_coe,
        Finite.mem_toFinset]
    rw [ENNReal.tsum_eq_iSup_sum]
    refine le_trans ?_ (le_iSup _ hf.toFinset)
    exact this hf.toFinset _ (by simpa only [e])
  clear ss b
  refine fun s => Finset.strongInductionOn s fun s IH b cv => ?_
  rcases le_total b a with ab | ab
  · rw [ENNReal.ofReal_eq_zero.2 (sub_nonpos.2 (f.mono ab))]
    exact zero_le _
  obtain ⟨i, is, bcd⟩ : ∃ i ∈ s, b ∈ Iotop (c i) (d i) := by
    simpa only [SetLike.mem_coe, mem_iUnion, exists_prop] using cv ⟨ab, le_rfl⟩
  rw [← Finset.insert_erase is] at cv ⊢
  rw [Finset.coe_insert, biUnion_insert] at cv
  rw [Finset.sum_insert (Finset.notMem_erase _ _)]
  replace bcd : b ∈ Ioc (c i) (d i) := Iotop_subset_Ioc bcd
  grw [← IH _ (Finset.erase_ssubset is) (c i), ← ENNReal.ofReal_add_le]
  · gcongr
    rw [sub_add_sub_cancel]
    exact sub_le_sub_right (f.mono bcd.2) _
  · rintro x ⟨h₁, h₂⟩
    apply (cv ⟨h₁, le_trans h₂ (le_of_lt bcd.1)⟩).resolve_left (fun h ↦ ?_)
    order [(Iotop_subset_Ioc h).1]

@[simp]
theorem outer_Ioc [DenselyOrdered R] (a b : R) : f.outer (Ioc a b) = ofReal (f b - f a) := by
  /- It suffices to show that, if `(a, b]` is covered by sets `s i`, then `f b - f a` is bounded
    by `∑ f.length (s i) + ε`. The difficulty is that `f.length` is expressed in terms of half-open
    intervals, while we would like to have a compact interval covered by open intervals to use
    compactness and finite sums, as provided by `length_subadditive_Icc_Ioo`. The trick is to use
    the right-continuity of `f`. If `a'` is close enough to `a` on its right, then `[a', b]` is
    still covered by the sets `s i` and moreover `f b - f a'` is very close to `f b - f a`
    (up to `ε/2`).
    Also, by definition one can cover `s i` by a half-closed interval `(p i, q i]` with `f`-length
    very close to that of `s i` (within a suitably small `ε' i`, say). If one moves `q i` very
    slightly to the right, then the `f`-length will change very little by right continuity, and we
    will get an open interval `(p i, q' i)` covering `s i` with `f (q' i) - f (p i)` within `ε' i`
    of the `f`-length of `s i`. This is not possible if `q i` is top, but this is not an issue
    as the interval `(p i, q i]` is already open in this case. However, this means that we can
    not use `Ioo` in this proof -- instead, we use `Iotop` precisely to avoid this issue. -/
  refine le_antisymm ?_ ?_
  · rw [← f.length_Ioc]
    apply outer_le_length
  rcases le_or_gt b a with hab | hab
  · have : ofReal (f b - f a) = 0 := by simpa using f.mono hab
    simp [this]
  apply (le_iInf₂ fun s hs => ENNReal.le_of_forall_pos_le_add fun ε εpos h => ?_)
  let δ := ε / 2
  have δpos : 0 < (δ : ℝ≥0∞) := by simpa [δ] using εpos.ne'
  rcases ENNReal.exists_pos_sum_of_countable δpos.ne' ℕ with ⟨ε', ε'0, hε⟩
  obtain ⟨a', ha', aa'⟩ : ∃ a', f a' - f a < δ ∧ a < a' := by
    have A : ContinuousWithinAt (fun r => f r - f a) (Ioi a) a := by
      refine ContinuousWithinAt.sub ?_ continuousWithinAt_const
      exact (f.right_continuous a).mono Ioi_subset_Ici_self
    have B : f a - f a < δ := by rwa [sub_self, NNReal.coe_pos, ← ENNReal.coe_pos]
    have : (𝓝[>] a).NeBot := nhdsGT_neBot_of_exists_gt ⟨b, hab⟩
    exact (((tendsto_order.1 A).2 _ B).and self_mem_nhdsWithin).exists
  have : Nonempty R := ⟨a⟩
  have : ∀ i, ∃ p : R × R, Icc a' b ∩ s i ⊆ Iotop p.1 p.2 ∧
      (ofReal (f p.2 - f p.1) : ℝ≥0∞) < f.length (s i) + ε' i := by
    intro i
    have hl :=
      ENNReal.lt_add_right ((ENNReal.le_tsum i).trans_lt h).ne (ENNReal.coe_ne_zero.2 (ε'0 i).ne')
    conv at hl =>
      lhs
      rw [length_eq]
    simp only [iInf_lt_iff, exists_prop] at hl
    rcases hl with ⟨p, q', spq, hq'⟩
    have A : Icc a' b ∩ s i ⊆ Ioc p q' := by
      rintro x ⟨hx, h'x⟩
      apply spq
      simp [h'x, notMem_botSet_of_lt (aa'.trans_le hx.1)]
    by_cases htq' : IsTop q'
    · refine ⟨(p, q'), ?_, hq'⟩
      rintro x hx
      simp only [Iotop, htq', ↓reduceIte, mem_Ioc]
      exact ⟨(A hx).1, htq' _⟩
    have : (𝓝[>] q').NeBot := by simp [Filter.neBot_iff, nhdsGT_eq_bot_iff, htq', not_covBy]
    have : ContinuousWithinAt (fun r => ofReal (f r - f p)) (Ioi q') q' := by
      apply ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt
      refine ContinuousWithinAt.sub ?_ continuousWithinAt_const
      exact (f.right_continuous q').mono Ioi_subset_Ici_self
    rcases (((tendsto_order.1 this).2 _ hq').and self_mem_nhdsWithin).exists with ⟨q, hq, q'q⟩
    exact ⟨⟨p, q⟩, A.trans ((Ioc_subset_Ioo_right q'q).trans Ioo_subset_Iotop), hq⟩
  choose g hg using this
  have I_subset : Icc a' b ⊆ ⋃ i, Iotop (g i).1 (g i).2 :=
    calc
      Icc a' b ⊆ Icc a' b ∩ Ioc a b := fun x hx => ⟨hx, aa'.trans_le hx.1, hx.2⟩
      _ ⊆ Icc a' b ∩ ⋃ i, s i := by gcongr
      _ = ⋃ i, Icc a' b ∩ s i := inter_iUnion (Icc a' b) s
      _ ⊆ ⋃ i, Iotop (g i).1 (g i).2 := iUnion_mono fun i => (hg i).1
  calc
    ofReal (f b - f a) = ofReal (f b - f a' + (f a' - f a)) := by rw [sub_add_sub_cancel]
    _ ≤ ofReal (f b - f a') + ofReal (f a' - f a) := ENNReal.ofReal_add_le
    _ ≤ ∑' i, ofReal (f (g i).2 - f (g i).1) + ofReal δ :=
      (add_le_add (f.length_subadditive_Icc_Ioo I_subset) (ENNReal.ofReal_le_ofReal ha'.le))
    _ ≤ ∑' i, (f.length (s i) + ε' i) + δ :=
      (add_le_add (ENNReal.tsum_le_tsum fun i => (hg i).2.le)
        (by simp only [ENNReal.ofReal_coe_nnreal, le_rfl]))
    _ = ∑' i, f.length (s i) + ∑' i, (ε' i : ℝ≥0∞) + δ := by rw [ENNReal.tsum_add]
    _ ≤ ∑' i, f.length (s i) + δ + δ := add_le_add (add_le_add le_rfl hε.le) le_rfl
    _ = ∑' i : ℕ, f.length (s i) + ε := by simp [δ, add_assoc, ENNReal.add_halves]

omit [OrderTopology R] [CompactIccSpace R] in
theorem measurableSet_Ioi {c : R} : MeasurableSet[f.outer.caratheodory] (Ioi c) := by
  refine OuterMeasure.ofFunction_caratheodory fun t => ?_
  have : Nonempty R := ⟨c⟩
  simp only [length_eq]
  refine le_iInf fun a => le_iInf fun b => le_iInf fun h => ?_
  simp only [← length_eq]
  rw [← length_diff_botSet, inter_diff_right_comm, ← length_diff_botSet (s := t \ Ioi c),
    diff_diff_comm]
  refine
    le_trans
      (add_le_add (f.length_mono <| inter_subset_inter_left _ h)
        (f.length_mono <| diff_subset_diff_left h)) ?_
  rcases le_total a c with hac | hac <;> rcases le_total b c with hbc | hbc
  · simp only [Ioc_inter_Ioi, f.length_Ioc, hac, hbc, le_refl, Ioc_eq_empty,
      max_eq_right, min_eq_left, Ioc_diff_Ioi, f.length_empty, zero_add, not_lt]
  · simp only [hac, hbc, Ioc_inter_Ioi, Ioc_diff_Ioi, f.length_Ioc, min_eq_right,
      ← ENNReal.ofReal_add, f.mono hac, f.mono hbc, sub_nonneg,
      sub_add_sub_cancel, le_refl,
      max_eq_right]
  · simp only [hbc, le_refl, Ioc_eq_empty, Ioc_inter_Ioi, min_eq_left, Ioc_diff_Ioi, f.length_empty,
      zero_add, or_true, le_sup_iff, f.length_Ioc, not_lt]
  · simp only [hac, hbc, Ioc_inter_Ioi, Ioc_diff_Ioi, f.length_Ioc, min_eq_right,
      le_refl, Ioc_eq_empty, add_zero, max_eq_left, f.length_empty, not_lt]

theorem outer_trim [MeasurableSpace R] [BorelSpace R] [DenselyOrdered R] :
    f.outer.trim = f.outer := by
  refine le_antisymm (fun s => ?_) (OuterMeasure.le_trim _)
  rw [OuterMeasure.trim_eq_iInf]
  refine le_iInf fun t => le_iInf fun ht => ENNReal.le_of_forall_pos_le_add fun ε ε0 h => ?_
  rcases ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 ε0).ne' ℕ with ⟨ε', ε'0, hε⟩
  grw [← hε]
  rw [← ENNReal.tsum_add]
  choose g hg using
    show ∀ i, ∃ s, t i ⊆ s ∧ MeasurableSet s ∧ f.outer s ≤ f.length (t i) + ofReal (ε' i) by
      intro i
      rcases isEmpty_or_nonempty R with hR | hR
      · refine ⟨∅, ?_, MeasurableSet.empty, by simp⟩
        simpa using eq_empty_of_isEmpty (t i)
      have hl :=
        ENNReal.lt_add_right ((ENNReal.le_tsum i).trans_lt h).ne (ENNReal.coe_pos.2 (ε'0 i)).ne'
      conv at hl =>
        lhs
        rw [length_eq]
      simp only [iInf_lt_iff] at hl
      rcases hl with ⟨a, b, h₁, h₂⟩
      rw [← f.outer_Ioc] at h₂
      rw [diff_subset_iff] at h₁
      refine ⟨_, h₁, measurableSet_botSet.union measurableSet_Ioc, le_of_lt ?_⟩
      calc f.outer (botSet ∪ Ioc a b)
      _ ≤ f.outer botSet + f.outer (Ioc a b) := measure_union_le _ _
      _ ≤ f.length botSet + f.outer (Ioc a b) := by gcongr; apply outer_le_length
      _ = 0 + f.outer (Ioc a b) := by
        simp only [← length_diff_botSet, sdiff_self, bot_eq_empty, empty_diff, outer_Ioc, zero_add]
        simp [empty_diff]
      _ = f.outer (Ioc a b) := by simp
      _ < f.length (t i) + ofReal ↑(ε' i) := by simpa using h₂
  simp only [ofReal_coe_nnreal] at hg
  apply iInf_le_of_le (iUnion g) _
  apply iInf_le_of_le (ht.trans <| iUnion_mono fun i => (hg i).1) _
  apply iInf_le_of_le (MeasurableSet.iUnion fun i => (hg i).2.1) _
  exact le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun i => (hg i).2.2)

omit [CompactIccSpace R] in
theorem borel_le_measurable [SecondCountableTopology R] :
    borel R ≤ f.outer.caratheodory := by
  rw [borel_eq_generateFrom_Ioi]
  refine MeasurableSpace.generateFrom_le ?_
  simp +contextual [f.measurableSet_Ioi]

/-! ### The measure associated to a Stieltjes function -/

variable [MeasurableSpace R] [BorelSpace R] [SecondCountableTopology R] [DenselyOrdered R]

/-- The measure associated to a Stieltjes function, giving mass `f b - f a` to the
interval `(a, b]`. If there is a bot element, it gives zero mass to it. -/
protected irreducible_def measure : Measure R where
  toOuterMeasure := f.outer
  m_iUnion _s hs := f.outer.iUnion_eq_of_caratheodory fun i => f.borel_le_measurable _ <| by
    borelize R
    exact hs i
  trim_le := f.outer_trim.le

@[simp]
theorem measure_Ioc (a b : R) : f.measure (Ioc a b) = ofReal (f b - f a) := by
  rw [StieltjesFunction.measure]
  exact f.outer_Ioc a b

@[simp]
theorem measure_singleton (a : R) : f.measure {a} = ofReal (f a - leftLim f a) := by
  by_cases ha : IsBot a
  · have : leftLim f a = f a := by
      apply leftLim_eq_of_eq_bot
      simp [nhdsLT_eq_bot_iff, ha]
    simp only [this, sub_self, ofReal_zero]
    apply eq_bot_iff.2
    rw [StieltjesFunction.measure]
    apply (outer_le_length _ _).trans
    rw [← length_diff_botSet]
    simp [subsingleton_botSet.eq_singleton_of_mem ha]
  obtain ⟨b, hb⟩ : ∃ b, b < a := by simpa only [IsBot, not_forall, not_le] using ha
  obtain ⟨u, u_mono, u_lt_a, u_lim⟩ :
    ∃ u : ℕ → R, StrictMono u ∧ (∀ n : ℕ, u n ∈ Ioo b a) ∧ Tendsto u atTop (𝓝 a) :=
    exists_seq_strictMono_tendsto' hb
  replace u_lt_a n : u n < a := (u_lt_a n).2
  have A : {a} = ⋂ n, Ioc (u n) a := by
    refine Subset.antisymm (fun x hx => by simp [mem_singleton_iff.1 hx, u_lt_a]) fun x hx => ?_
    replace hx : ∀ (i : ℕ), u i < x ∧ x ≤ a := by simpa using hx
    have : a ≤ x := le_of_tendsto' u_lim fun n => (hx n).1.le
    simp [le_antisymm this (hx 0).2]
  have L1 : Tendsto (fun n => f.measure (Ioc (u n) a)) atTop (𝓝 (f.measure {a})) := by
    rw [A]
    refine tendsto_measure_iInter_atTop (fun n => nullMeasurableSet_Ioc)
      (fun m n hmn => ?_) ?_
    · exact Ioc_subset_Ioc_left (u_mono.monotone hmn)
    · exact ⟨0, by simpa only [measure_Ioc] using ENNReal.ofReal_ne_top⟩
  have L2 :
      Tendsto (fun n => f.measure (Ioc (u n) a)) atTop (𝓝 (ofReal (f a - leftLim f a))) := by
    simp only [measure_Ioc]
    have : Tendsto (fun n => f (u n)) atTop (𝓝 (leftLim f a)) := by
      apply (f.mono.tendsto_leftLim a).comp
      exact
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ u_lim
          (Eventually.of_forall fun n => u_lt_a n)
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.sub this)
  exact tendsto_nhds_unique L1 L2

@[simp]
theorem measure_Icc (a b : R) : f.measure (Icc a b) = ofReal (f b - leftLim f a) := by
  rcases le_or_gt a b with (hab | hab)
  · have A : Disjoint {a} (Ioc a b) := by simp
    simp [← Icc_union_Ioc_eq_Icc le_rfl hab, -singleton_union, ← ENNReal.ofReal_add,
      f.mono.leftLim_le, measure_union A measurableSet_Ioc, f.mono hab]
  · simp only [hab, measure_empty, Icc_eq_empty, not_le]
    symm
    simp [ENNReal.ofReal_eq_zero, f.mono.le_leftLim hab]

@[simp]
theorem measure_Ioo {a b : R} : f.measure (Ioo a b) = ofReal (leftLim f b - f a) := by
  rcases le_or_gt b a with (hab | hab)
  · simp only [hab, measure_empty, Ioo_eq_empty, not_lt]
    symm
    simp [ENNReal.ofReal_eq_zero, f.mono.leftLim_le hab]
  · have A : Disjoint (Ioo a b) {b} := by simp
    have D : f b - f a = f b - leftLim f b + (leftLim f b - f a) := by abel
    have := f.measure_Ioc a b
    simp only [← Ioo_union_Icc_eq_Ioc hab le_rfl, measure_singleton,
      measure_union A (measurableSet_singleton b), Icc_self] at this
    rw [D, ENNReal.ofReal_add, add_comm] at this
    · simpa only [ENNReal.add_right_inj ENNReal.ofReal_ne_top]
    · simp only [f.mono.leftLim_le le_rfl, sub_nonneg]
    · simp only [f.mono.le_leftLim hab, sub_nonneg]

@[simp]
theorem measure_Ico (a b : R) : f.measure (Ico a b) = ofReal (leftLim f b - leftLim f a) := by
  rcases le_or_gt b a with (hab | hab)
  · simp only [hab, measure_empty, Ico_eq_empty, not_lt]
    symm
    simp [ENNReal.ofReal_eq_zero, f.mono.leftLim hab]
  · have A : Disjoint {a} (Ioo a b) := by simp
    simp [← Icc_union_Ioo_eq_Ico le_rfl hab, -singleton_union, f.mono.leftLim_le,
      measure_union A measurableSet_Ioo, f.mono.le_leftLim hab, ← ENNReal.ofReal_add]

theorem measure_Iic [NoMinOrder R] {l : ℝ} (hf : Tendsto f atBot (𝓝 l)) (x : R) :
    f.measure (Iic x) = ofReal (f x - l) := by
  have : Nonempty R := ⟨x⟩
  refine tendsto_nhds_unique (tendsto_measure_Ioc_atBot _ _) ?_
  simp_rw [measure_Ioc]
  exact ENNReal.tendsto_ofReal (Tendsto.const_sub _ hf)

lemma measure_Iio [NoMinOrder R] {l : ℝ} (hf : Tendsto f atBot (𝓝 l)) (x : R) :
    f.measure (Iio x) = ofReal (leftLim f x - l) := by
  have : Nonempty R := ⟨x⟩
  rw [← Iic_diff_right, measure_diff _ (nullMeasurableSet_singleton x), measure_singleton,
    f.measure_Iic hf, ← ofReal_sub _ (sub_nonneg.mpr <| Monotone.leftLim_le f.mono' le_rfl)]
    <;> simp

theorem measure_Ici [NoMaxOrder R] {l : ℝ} (hf : Tendsto f atTop (𝓝 l)) (x : R) :
    f.measure (Ici x) = ofReal (l - leftLim f x) := by
  have : Nonempty R := ⟨x⟩
  refine tendsto_nhds_unique (tendsto_measure_Ico_atTop _ _) ?_
  simp_rw [measure_Ico]
  refine ENNReal.tendsto_ofReal (Tendsto.sub_const ?_ _)
  apply tendsto_order.2 ⟨fun m hm ↦ ?_, fun M hM ↦ ?_⟩
  · obtain ⟨a, ha⟩ : ∃ a, ∀ (b : R), a ≤ b → m < f b := by simpa using (tendsto_order.1 hf).1 m hm
    obtain ⟨a', ha'⟩ : ∃ a', a < a' := exists_gt a
    simp only [eventually_atTop]
    refine ⟨a', fun b hb ↦ ?_⟩
    apply (ha _ le_rfl).trans_le
    exact f.mono.le_leftLim (ha'.trans_le hb)
  · filter_upwards [(tendsto_order.1 hf).2 M hM] with a ha
    exact (f.mono.leftLim_le le_rfl).trans_lt ha

lemma measure_Ioi [NoMaxOrder R] {l : ℝ} (hf : Tendsto f atTop (𝓝 l)) (x : R) :
    f.measure (Ioi x) = ofReal (l - f x) := by
  rw [← Ici_diff_left, measure_diff _ (nullMeasurableSet_singleton x), measure_singleton,
    f.measure_Ici hf, ← ofReal_sub _ (sub_nonneg.mpr <| Monotone.leftLim_le f.mono' le_rfl)]
    <;> simp

lemma measure_Ioi_of_tendsto_atTop_atTop (hf : Tendsto f atTop atTop) (x : R) :
    f.measure (Ioi x) = ∞ := by
  have : Nonempty R := ⟨x⟩
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_atTop.mp hf (r + f x))
  exact (f.measure_Ioc x (max x N) ▸ ENNReal.coe_nnreal_eq r ▸ (ENNReal.ofReal_le_ofReal <|
    le_tsub_of_add_le_right <| hN _ (le_max_right x N))).trans (measure_mono Ioc_subset_Ioi_self)

lemma measure_Ici_of_tendsto_atTop_atTop (hf : Tendsto f atTop atTop) (x : R) :
    f.measure (Ici x) = ∞ := by
  rw [← top_le_iff, ← f.measure_Ioi_of_tendsto_atTop_atTop hf x]
  exact measure_mono Ioi_subset_Ici_self

lemma measure_Iic_of_tendsto_atBot_atBot (hf : Tendsto f atBot atBot) (x : R) :
    f.measure (Iic x) = ∞ := by
  have : Nonempty R := ⟨x⟩
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atBot.mp (tendsto_atBot.mp hf (f x - r))
  exact (f.measure_Ioc (min x N) x ▸ ENNReal.coe_nnreal_eq r ▸ (ENNReal.ofReal_le_ofReal <|
    le_sub_comm.mp <| hN _ (min_le_right x N))).trans (measure_mono Ioc_subset_Iic_self)

lemma measure_Iio_of_tendsto_atBot_atBot [NoMinOrder R] (hf : Tendsto f atBot atBot) (x : R) :
    f.measure (Iio x) = ∞ := by
  have : Nonempty R := ⟨x⟩
  obtain ⟨y, hy⟩ : ∃ y, y < x := exists_lt x
  rw [← top_le_iff, ← f.measure_Iic_of_tendsto_atBot_atBot hf y]
  exact measure_mono <| Set.Iic_subset_Iio.mpr <| hy

theorem measure_univ [Nonempty R] [NoMinOrder R]
    {l u : ℝ} (hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) :
    f.measure univ = ofReal (u - l) := by
  refine tendsto_nhds_unique (tendsto_measure_Iic_atTop _) ?_
  simp_rw [measure_Iic f hfl]
  exact ENNReal.tendsto_ofReal (Tendsto.sub_const hfu _)

lemma measure_univ_of_tendsto_atTop_atTop [Nonempty R] (hf : Tendsto f atTop atTop) :
    f.measure univ = ∞ := by
  inhabit R
  rw [← top_le_iff, ← f.measure_Ioi_of_tendsto_atTop_atTop hf default]
  exact measure_mono (subset_univ _)

lemma measure_univ_of_tendsto_atBot_atBot [Nonempty R] [NoMinOrder R] (hf : Tendsto f atBot atBot) :
    f.measure univ = ∞ := by
  inhabit R
  rw [← top_le_iff, ← f.measure_Iio_of_tendsto_atBot_atBot hf default]
  exact measure_mono (subset_univ _)

lemma isFiniteMeasure [NoMinOrder R] {l u : ℝ}
    (hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) :
    IsFiniteMeasure f.measure := by
  constructor
  cases isEmpty_or_nonempty R
  · simp [eq_empty_of_isEmpty]
  · simp [f.measure_univ hfl hfu]

lemma isProbabilityMeasure [Nonempty R] [NoMinOrder R]
    (hf_bot : Tendsto f atBot (𝓝 0)) (hf_top : Tendsto f atTop (𝓝 1)) :
    IsProbabilityMeasure f.measure := ⟨by simp [f.measure_univ hf_bot hf_top]⟩

instance instIsLocallyFiniteMeasure : IsLocallyFiniteMeasure f.measure := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨b, c, -, h, -⟩ : ∃ b c, x ∈ Icc b c ∧ Icc b c ∈ 𝓝 x ∧ Icc b c ⊆ univ :=
    exists_Icc_mem_subset_of_mem_nhds (by simp)
  exact ⟨Icc b c, h, by simp⟩

lemma eq_of_measure_of_tendsto_atBot [NoMinOrder R] (g : StieltjesFunction R) {l : ℝ}
    (hfg : f.measure = g.measure) (hfl : Tendsto f atBot (𝓝 l)) (hgl : Tendsto g atBot (𝓝 l)) :
    f = g := by
  ext x
  have hf := measure_Iic f hfl x
  rw [hfg, measure_Iic g hgl x, ENNReal.ofReal_eq_ofReal_iff, eq_comm] at hf
  · simpa using hf
  · rw [sub_nonneg]
    exact Monotone.le_of_tendsto g.mono hgl x
  · rw [sub_nonneg]
    exact Monotone.le_of_tendsto f.mono hfl x

lemma eq_of_measure_of_eq (g : StieltjesFunction R) {y : R}
    (hfg : f.measure = g.measure) (hy : f y = g y) :
    f = g := by
  ext x
  cases le_total x y with
  | inl hxy =>
    have hf := measure_Ioc f x y
    rw [hfg, measure_Ioc g x y, ENNReal.ofReal_eq_ofReal_iff, eq_comm, hy] at hf
    · simpa using hf
    · rw [sub_nonneg]
      exact g.mono hxy
    · rw [sub_nonneg]
      exact f.mono hxy
  | inr hxy =>
    have hf := measure_Ioc f y x
    rw [hfg, measure_Ioc g y x, ENNReal.ofReal_eq_ofReal_iff, eq_comm, hy] at hf
    · simpa using hf
    · rw [sub_nonneg]
      exact g.mono hxy
    · rw [sub_nonneg]
      exact f.mono hxy

@[simp]
lemma measure_const (c : ℝ) : (StieltjesFunction.const R c).measure = 0 := by
  apply Measure.ext_of_Icc _ _ (fun a b hab ↦ ?_)
  simp only [measure_Icc, const_apply, Measure.coe_zero, Pi.ofNat_apply, ofReal_eq_zero,
    tsub_le_iff_right, zero_add]
  rw [ContinuousWithinAt.leftLim_eq]
  · simp
  · exact continuousWithinAt_const

@[simp]
lemma measure_zero : (0 : StieltjesFunction R).measure = 0 := measure_const 0

@[simp]
lemma measure_add (f g : StieltjesFunction R) : (f + g).measure = f.measure + g.measure := by
  refine Measure.ext_of_Icc _ _ (fun a b h ↦ ?_)
  have : leftLim (f + g) a = leftLim f a + leftLim g a := by
    rcases Filter.eq_or_neBot (𝓝[<] a) with ha | ha
    · simp [leftLim_eq_of_eq_bot _ ha]
    · exact tendsto_nhds_unique ((f + g).mono.tendsto_leftLim a)
        ((f.mono.tendsto_leftLim a).add (g.mono.tendsto_leftLim a))
  simp only [measure_Icc, add_apply, Measure.coe_add, Pi.add_apply, this]
  rw [← ENNReal.ofReal_add (sub_nonneg_of_le (f.mono.leftLim_le h))
    (sub_nonneg_of_le (g.mono.leftLim_le h))]
  ring_nf

@[simp]
lemma measure_smul (c : ℝ≥0) (f : StieltjesFunction R) : (c • f).measure = c • f.measure := by
  refine Measure.ext_of_Icc _ _ (fun a b h ↦ ?_)
  simp only [measure_Icc, Measure.smul_apply]
  change ofReal (c * f b - leftLim (c • f) a) = c • ofReal (f b - leftLim f a)
  have : leftLim (c • f) a = c * leftLim f a := by
    rcases Filter.eq_or_neBot (𝓝[<] a) with ha | ha
    · simp [leftLim_eq_of_eq_bot _ ha]
      rfl
    · exact tendsto_nhds_unique ((c • f).mono.tendsto_leftLim a)
        ((f.mono.tendsto_leftLim a).const_smul c)
  rw [this, ← _root_.mul_sub, ENNReal.ofReal_mul zero_le_coe, ofReal_coe_nnreal, ← smul_eq_mul]
  rfl

end StieltjesFunction
