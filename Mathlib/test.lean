import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Instances.Real
import Mathlib.LinearAlgebra.Finrank
import Mathlib.Analysis.Convolution
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.ULift

open LinearMap Set

open BigOperators Classical Convex Pointwise

open scoped Cardinal

universe u v

namespace Cardinal


open Function Order

@[simp]
lemma mk_preimage_down {s : Set α} : #(ULift.down.{v} ⁻¹' s) = Cardinal.lift.{v} (#s) := by
  rw [← mk_uLift, Cardinal.eq]
  constructor
  let f : ULift.down ⁻¹' s → ULift s := fun x ↦ ULift.up (restrictPreimage s ULift.down x)
  have : Function.Bijective f :=
    ULift.up_bijective.comp (restrictPreimage_bijective _ (ULift.down_bijective))
  exact Equiv.ofBijective f this

lemma glourtet {α : Type _} [Fintype α] :
  (Fintype.card α : Cardinal) = #α := by exact Eq.symm (mk_fintype α)

/-- In a countable monotone sequence of sets, if all the sets have cardinality at most `a`,
so does the union. Supersed by `card_iUnion_le_of_monotone_countable` which does not assume
that the indexing set lives in the same universe. -/
lemma mk_iUnion_le_of_monotone_countable_aux {α ι : Type u} {a : Cardinal}
    [Preorder ι] [IsDirected ι (· ≤ ·)] [Countable ι] {f : ι → Set α} (hf : Monotone f)
    (h'f : ∀ i, #(f i) ≤ a) : #(⋃ i, f i) ≤ a := by
  rcases isEmpty_or_nonempty ι with hι|hι
  · simp only [iUnion_of_empty, mk_fintype, Fintype.card_of_isEmpty, CharP.cast_eq_zero, zero_le]
  rcases lt_or_le a ℵ₀ with ha|ha
  /- case `a` finite. In this case, choose `i` such that the cardinality of `f i` is maximal.
  Then each `f j` is included in this `f i`, so is the union `⋃ j, f j`, and therefore its
  cardinality is at most `#(f i) ≤ a`. -/
  · have : ∀ i, Fintype (f i) := fun i ↦ (lt_aleph0_iff_fintype.1 ((h'f i).trans_lt ha)).some
    let b := ⨆ i, #(f i)
    have Ib : ∀ i, #(f i) ≤ b := by
      intro i
      apply le_ciSup (f := fun j ↦ #(f j))
      refine ⟨a, ?_⟩
      simpa only [upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff',
        mem_setOf_eq] using h'f
    -- choose `i` for which the cardinality of `f i` is maximal.
    obtain ⟨i, ib⟩ : ∃ i, #(f i) = b := by
      by_contra H
      have Ib : ∀ i, #(f i) < b := by
        intro i
        push_neg at H
        exact lt_of_le_of_ne (Ib i) (H i)
      obtain ⟨c, hc⟩ : ∃ (c : Cardinal), b = succ c := by
        obtain ⟨n, hn⟩ : ∃ (n : ℕ), b = n := lt_aleph0.1 ((ciSup_le h'f).trans_lt ha)
        refine ⟨n.pred, ?_⟩
        have : n.pred.succ = n := by
          apply Nat.succ_pred
          rintro rfl
          rcases hι with ⟨i⟩
          simpa [hn] using Ib i
        rw [hn, ← nat_succ, this]
      have Ic : ∀ i, #(f i) ≤ c := by
        intro i
        apply le_of_lt_succ
        rw [← hc]
        exact Ib i
      exact lt_irrefl _ (((ciSup_le Ic).trans_lt (lt_succ c)).trans_le (hc.symm.le))
    -- then `f i` contains all the other `f j`. Indeed, choosing `k` with `i ≤ k` and `j ≤ k`,
    -- we have `f i ⊆ f k` by monotonicity, so `f i = f k` as the cardinality of `f i` is maximal.
    -- as `f j ⊆ f k` by monotonicity, this gives `f j ⊆ f i`.
    have If : ∀ j, f j ⊆ f i := by
      intro j
      obtain ⟨k, jk, ik⟩ : ∃ k, j ≤ k ∧ i ≤ k := directed_of _ j i
      have : f i = f k := by
        apply Set.eq_of_subset_of_card_le (hf ik)
        rw [← natCast_le, ← mk_fintype, ← mk_fintype, ib]
        exact Ib k
      simpa [← this] using hf jk
    -- as `⋃ j, f j ⊆ f i` and `#(f i) ≤ a`, we get the desired bound on `#(⋃ j, f j)`.
    exact (mk_le_mk_of_subset (iUnion_subset If)).trans (h'f i)
  -- case `a` infinite
  · refine (Cardinal.mk_iUnion_le_sum_mk (f := f)).trans ((sum_le_sum _ _ h'f).trans ?_)
    simp only [sum_const, lift_id]
    calc #ι * a ≤ ℵ₀ * a := by exact mul_le_mul_right' mk_le_aleph0 a
         _      = a := by exact aleph0_mul_eq ha

/-- In a countable monotone sequence of sets, if all the sets have cardinality at most `a`,
so does the union. -/
lemma mk_iUnion_le_of_monotone_countable {α : Type u} {ι : Type v} {a : Cardinal}
    [Preorder ι] [IsDirected ι (· ≤ ·)] [Countable ι] {f : ι → Set α} (hf : Monotone f)
    (h'f : ∀ i, #(f i) ≤ a) : #(⋃ i, f i) ≤ a := by
  let g : ULift.{u, v} ι → Set (ULift.{v, u} α) := (ULift.down ⁻¹' ·) ∘ f ∘ ULift.down
  have A : #(⋃ i, g i) ≤ Cardinal.lift.{v, u} a := by
    apply mk_iUnion_le_of_monotone_countable_aux
    · intro i j hij
      apply preimage_mono
      exact hf hij
    · intro i
      simpa using h'f i.down
  have B : ⋃ i, g i = ULift.down ⁻¹' (⋃ i, f i) := by
    simp only [Function.comp_apply, preimage_iUnion]
    rw [ULift.down_bijective.surjective.iUnion_comp (g := fun i ↦ ULift.down ⁻¹' (f i))]
  simp_rw [B, mk_preimage_down, lift_le] at A
  exact A

/-- Given a countable monotone sequence of sets covering the space, if all the sets have cardinality
at most `a`, so does the whole space. -/
lemma mk_le_of_monotone_countable {α : Type u} {ι : Type v} {a : Cardinal}
    [Preorder ι] [IsDirected ι (· ≤ ·)] [Countable ι] {f : ι → Set α} (hf : Monotone f)
    (h'f : ∀ i, #(f i) ≤ a) (H : Set.univ ⊆ ⋃ i, f i) : #α ≤ a := by
  rw [← mk_univ, ← univ_subset_iff.1 H]
  exact mk_iUnion_le_of_monotone_countable hf h'f

/-- In a countable monotone sequence of sets, if all the sets have cardinality `a`,
so does the union. -/
lemma mk_iUnion_of_monotone_countable {α : Type u} {ι : Type v}
    [Preorder ι] [IsDirected ι (· ≤ ·)] [Countable ι] [hι : Nonempty ι]
    {f : ι → Set α} (hf : Monotone f) {a : Cardinal}
    (h'f : ∀ i, #(f i) = a) : #(⋃ i, f i) = a := by
  apply le_antisymm
  · exact mk_iUnion_le_of_monotone_countable hf (fun i ↦ (h'f i).le)
  · rcases hι with ⟨i⟩
    rw [← h'f i]
    exact Cardinal.mk_le_mk_of_subset (subset_iUnion f i)

/-- Given a countable monotone sequence of sets covering the space, if all the sets have
cardinality `a`, so does the whole space. -/
lemma mk_of_monotone_countable {α : Type u} {ι : Type v}
    [Preorder ι] [IsDirected ι (· ≤ ·)] [Countable ι] [hι : Nonempty ι]
    {f : ι → Set α} (hf : Monotone f) {a : Cardinal}
    (h'f : ∀ i, #(f i) = a) (H : Set.univ ⊆ ⋃ i, f i) : #α = a := by
  rw [← mk_univ, ← univ_subset_iff.1 H]
  exact mk_iUnion_of_monotone_countable hf h'f



#exit

lemma foo {E : Type _} [AddCommGroup E] [Module ℝ E] (x y : E) (h : LinearIndependent ℝ ![x, y])
    (s t : ℝ) (hs : s ≠ t) : [x -[ℝ]- t • y] ∩ [x -[ℝ]- s • y] ⊆ {x} := by
  intro z ⟨hzt, hzs⟩
  rw [segment_eq_image, mem_image] at hzt hzs
  rcases hzt with ⟨p, ⟨p0, p1⟩, rfl⟩
  rcases hzs with ⟨q, ⟨q0, q1⟩, H⟩
  simp only [smul_smul] at H
  obtain rfl : q = p := by simpa using (h.eq_of_pair H).1
  rcases q0.eq_or_gt with rfl|hq0'
  · simp
  · have A : s = t := by simpa [mul_eq_mul_left_iff, hq0'.ne'] using (h.eq_of_pair H).2
    exact (hs A).elim

theorem glouglou1 {E : Type _} [TopologicalSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NonTrivial E] (s : Set E) (hs : s.Countable) : Dense sᶜ := by
  exact?



theorem glouglou {E : Type _} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (h : 2 ≤ Module.rank ℝ E) (s : Set E) (hs : s.Countable) :
    IsConnected sᶜ := by
  sorry
