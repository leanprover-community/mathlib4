/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Combinatorics.Additive.AP.Three.Behrend
import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite
import Mathlib.Tactic.Rify

/-!
# The Ruzsa-Szemerédi problem

This file proves the lower bound of the Ruzsa-Szemerédi problem. The problem is to find the maximum
number of edges that a graph on `n` vertices can have if all edges belong to at most one triangle.

The lower bound comes from turning the big 3AP-free set from Behrend's construction into a graph
that has the property that every triangle gives a (possibly trivial) arithmetic progression on the
original set.

## Main declarations

* `ruzsaSzemerediNumberNat n`: Maximum number of edges a graph on `n` vertices can have such that
  each edge belongs to exactly one triangle.
* `ruzsaSzemerediNumberNat_asymptotic_lower_bound`: There exists a graph with `n` vertices and
  `Ω((n ^ 2 * exp (-4 * √(log n))))` edges such that each edge belongs to exactly one triangle.
-/

open Finset Nat Real SimpleGraph Sum3 SimpleGraph.TripartiteFromTriangles
open Fintype (card)
open scoped Pointwise

variable {α β : Type*}

/-! ### The Ruzsa-Szemerédi number -/

section ruzsaSzemerediNumber
variable [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] {G H : SimpleGraph α}

variable (α) in
/-- The **Ruzsa-Szemerédi number** of a fintype is the maximum number of edges a locally linear
graph on that type can have.

In other words, `ruzsaSzemerediNumber α` is the maximum number of edges a graph on `α` can have such
that each edge belongs to exactly one triangle. -/
noncomputable def ruzsaSzemerediNumber : ℕ := by
  classical
  exact Nat.findGreatest (fun m ↦ ∃ (G : SimpleGraph α) (_ : DecidableRel G.Adj),
    #(G.cliqueFinset 3) = m ∧ G.LocallyLinear) ((card α).choose 3)

open scoped Classical in
lemma ruzsaSzemerediNumber_le : ruzsaSzemerediNumber α ≤ (card α).choose 3 := Nat.findGreatest_le _

lemma ruzsaSzemerediNumber_spec :
    ∃ (G : SimpleGraph α) (_ : DecidableRel G.Adj),
      #(G.cliqueFinset 3) = ruzsaSzemerediNumber α ∧ G.LocallyLinear := by
  classical
  exact @Nat.findGreatest_spec _
    (fun m ↦ ∃ (G : SimpleGraph α) (_ : DecidableRel G.Adj),
      #(G.cliqueFinset 3) = m ∧ G.LocallyLinear) _ _ (Nat.zero_le _)
    ⟨⊥, inferInstance, by simp, locallyLinear_bot⟩

variable {n : ℕ}

lemma SimpleGraph.LocallyLinear.le_ruzsaSzemerediNumber [DecidableRel G.Adj]
    (hG : G.LocallyLinear) : #(G.cliqueFinset 3) ≤ ruzsaSzemerediNumber α := by
  classical
  exact le_findGreatest card_cliqueFinset_le ⟨G, inferInstance, by congr, hG⟩

lemma ruzsaSzemerediNumber_mono (f : α ↪ β) : ruzsaSzemerediNumber α ≤ ruzsaSzemerediNumber β := by
  classical
  refine findGreatest_mono ?_ (choose_mono _ <| Fintype.card_le_of_embedding f)
  rintro n ⟨G, _, rfl, hG⟩
  refine ⟨G.map f, inferInstance, ?_, hG.map _⟩
  rw [← card_map ⟨map f, Finset.map_injective _⟩, ← cliqueFinset_map G f]
  decide

lemma ruzsaSzemerediNumber_congr (e : α ≃ β) : ruzsaSzemerediNumber α = ruzsaSzemerediNumber β :=
  (ruzsaSzemerediNumber_mono (e : α ↪ β)).antisymm <| ruzsaSzemerediNumber_mono e.symm

/-- The `n`-th **Ruzsa-Szemerédi number** is the maximum number of edges a locally linear graph on
`n` vertices can have.

In other words, `ruzsaSzemerediNumberNat n` is the maximum number of edges a graph on `n` vertices
can have such that each edge belongs to exactly one triangle. -/
noncomputable def ruzsaSzemerediNumberNat (n : ℕ) : ℕ := ruzsaSzemerediNumber (Fin n)

@[simp]
lemma ruzsaSzemerediNumberNat_card : ruzsaSzemerediNumberNat (card α) = ruzsaSzemerediNumber α :=
  ruzsaSzemerediNumber_congr (Fintype.equivFin _).symm

lemma ruzsaSzemerediNumberNat_mono : Monotone ruzsaSzemerediNumberNat := fun _m _n h =>
  ruzsaSzemerediNumber_mono (Fin.castLEEmb h)

lemma ruzsaSzemerediNumberNat_le : ruzsaSzemerediNumberNat n ≤ n.choose 3 :=
  ruzsaSzemerediNumber_le.trans_eq <| by rw [Fintype.card_fin]

@[simp] lemma ruzsaSzemerediNumberNat_zero : ruzsaSzemerediNumberNat 0 = 0 :=
  le_zero_iff.1 ruzsaSzemerediNumberNat_le

@[simp] lemma ruzsaSzemerediNumberNat_one : ruzsaSzemerediNumberNat 1 = 0 :=
  le_zero_iff.1 ruzsaSzemerediNumberNat_le

@[simp] lemma ruzsaSzemerediNumberNat_two : ruzsaSzemerediNumberNat 2 = 0 :=
  le_zero_iff.1 ruzsaSzemerediNumberNat_le

end ruzsaSzemerediNumber

/-! ### The Ruzsa-Szemerédi construction -/

section RuzsaSzemeredi
variable [Fintype α] [CommRing α] {s : Finset α} {x : α × α × α}

/-- The triangle indices for the Ruzsa-Szemerédi construction. -/
private def triangleIndices (s : Finset α) : Finset (α × α × α) :=
  (univ ×ˢ s).map
    ⟨fun xa ↦ (xa.1, xa.1 + xa.2, xa.1 + 2 * xa.2), by
      rintro ⟨x, a⟩ ⟨y, b⟩ h
      simp only [Prod.ext_iff] at h
      obtain rfl := h.1
      obtain rfl := add_right_injective _ h.2.1
      rfl⟩

@[simp]
private lemma mem_triangleIndices :
    x ∈ triangleIndices s ↔ ∃ y, ∃ a ∈ s, (y, y + a, y + 2 * a) = x := by simp [triangleIndices]

@[simp]
private lemma card_triangleIndices : #(triangleIndices s) = card α * #s := by
  simp [triangleIndices]

private lemma noAccidental (hs : ThreeAPFree (s : Set α)) :
    NoAccidental (triangleIndices s : Finset (α × α × α)) where
  eq_or_eq_or_eq := by
    simp only [mem_triangleIndices, Prod.mk_inj, forall_exists_index, and_imp]
    rintro _ _ _ _ _ _ d a ha rfl rfl rfl b' b hb rfl rfl h₁ d' c hc rfl h₂ rfl
    have : a + c = b + b := by linear_combination h₁.symm - h₂.symm
    obtain rfl := hs ha hb hc this
    simp_all

variable [Fact <| IsUnit (2 : α)]

private instance : ExplicitDisjoint (triangleIndices s : Finset (α × α × α)) where
  inj₀ := by
    simp only [mem_triangleIndices, Prod.mk_inj, forall_exists_index, and_imp]
    rintro _ _ _ _ x a ha rfl rfl rfl y b hb rfl h₁ h₂
    linear_combination 2 * h₁.symm - h₂.symm
  inj₁ := by
    simp only [mem_triangleIndices, Prod.mk_inj, forall_exists_index, and_imp]
    rintro _ _ _ _ x a ha rfl rfl rfl y b hb rfl rfl h
    simpa [(Fact.out (p := IsUnit (2 : α))).mul_right_inj, eq_comm] using h
  inj₂ := by
    simp only [mem_triangleIndices, Prod.mk_inj, forall_exists_index, and_imp]
    rintro _ _ _ _ x a ha rfl rfl rfl y b hb rfl h rfl
    simpa [(Fact.out (p := IsUnit (2 : α))).mul_right_inj, eq_comm] using h

private lemma locallyLinear (hs : ThreeAPFree (s : Set α)) :
    (graph <| triangleIndices s).LocallyLinear :=
  haveI := noAccidental hs; TripartiteFromTriangles.locallyLinear _

private lemma card_edgeFinset (hs : ThreeAPFree (s : Set α)) [DecidableEq α] :
    #(graph <| triangleIndices s).edgeFinset = 3 * card α * #s := by
  haveI := noAccidental hs
  rw [(locallyLinear hs).card_edgeFinset, card_triangles, card_triangleIndices, mul_assoc]

end RuzsaSzemeredi

variable (α) [Fintype α] [DecidableEq α] [CommRing α] [Fact <| IsUnit (2 : α)]

lemma addRothNumber_le_ruzsaSzemerediNumber :
    card α * addRothNumber (univ : Finset α) ≤ ruzsaSzemerediNumber (Sum α (Sum α α)) := by
  obtain ⟨s, -, hscard, hs⟩ := addRothNumber_spec (univ : Finset α)
  haveI := noAccidental hs
  rw [← hscard, ← card_triangleIndices, ← card_triangles]
  exact (locallyLinear hs).le_ruzsaSzemerediNumber

lemma rothNumberNat_le_ruzsaSzemerediNumberNat (n : ℕ) :
    (2 * n + 1) * rothNumberNat n ≤ ruzsaSzemerediNumberNat (6 * n + 3) := by
  let α := Fin (2 * n + 1)
  have : Nat.Coprime 2 (2 * n + 1) := by simp
  haveI : Fact (IsUnit (2 : Fin (2 * n + 1))) := ⟨by simpa using (ZMod.unitOfCoprime 2 this).isUnit⟩
  open scoped Fin.CommRing in
  calc
    (2 * n + 1) * rothNumberNat n
    _ = Fintype.card α * addRothNumber (Iio (n : α)) := by
      rw [Fin.addRothNumber_eq_rothNumberNat le_rfl, Fintype.card_fin]
    _ ≤ Fintype.card α * addRothNumber (univ : Finset α) := by
      gcongr; exact subset_univ _
    _ ≤ ruzsaSzemerediNumber (Sum α (Sum α α)) := addRothNumber_le_ruzsaSzemerediNumber _
    _ = ruzsaSzemerediNumberNat (6 * n + 3) := by
      simp_rw [← ruzsaSzemerediNumberNat_card, Fintype.card_sum, α, Fintype.card_fin]
      ring_nf

/-- Lower bound on the **Ruzsa-Szemerédi problem** in terms of 3AP-free sets.

If there exists a 3AP-free subset of `[1, ..., (n - 3) / 6]` of size `m`, then there exists a graph
with `n` vertices and `(n / 3 - 2) * m` edges such that each edge belongs to exactly one triangle.
-/
theorem rothNumberNat_le_ruzsaSzemerediNumberNat' :
    ∀ n : ℕ, (n / 3 - 2 : ℝ) * rothNumberNat ((n - 3) / 6) ≤ ruzsaSzemerediNumberNat n
  | 0 => by simp
  | 1 => by simp
  | 2 => by simp
  | n + 3 => by
    calc
      _ ≤ (↑(2 * (n / 6) + 1) : ℝ) * rothNumberNat (n / 6) :=
        mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      _ ≤ (ruzsaSzemerediNumberNat (6 * (n / 6) + 3) : ℝ) := ?_
      _ ≤ _ :=
        Nat.cast_le.2 (ruzsaSzemerediNumberNat_mono <| add_le_add_right (Nat.mul_div_le _ _) _)
    · norm_num
      rw [← div_add_one (three_ne_zero' ℝ), ← le_sub_iff_add_le, div_le_iff₀ (zero_lt_three' ℝ),
        add_assoc, add_sub_assoc, add_mul, mul_right_comm]
      norm_num
      norm_cast
      rw [← mul_add_one]
      exact (Nat.lt_mul_div_succ _ <| by norm_num).le
    · norm_cast
      exact rothNumberNat_le_ruzsaSzemerediNumberNat _

/-- Explicit lower bound on the **Ruzsa-Szemerédi problem**.

There exists a graph with `n` vertices and
`(n / 3 - 2) * (n - 3) / 6 * exp (-4 * √(log ((n - 3) / 6)))` edges such that each edge belongs
to exactly one triangle. -/
theorem ruzsaSzemerediNumberNat_lower_bound (n : ℕ) :
    (n / 3 - 2 : ℝ) * ↑((n - 3) / 6) * exp (-4 * √(log ↑((n - 3) / 6))) ≤
      ruzsaSzemerediNumberNat n := by
  rw [mul_assoc]
  obtain hn | hn := le_total (n / 3 - 2 : ℝ) 0
  · exact (mul_nonpos_of_nonpos_of_nonneg hn <| by positivity).trans (Nat.cast_nonneg _)
  exact
    (mul_le_mul_of_nonneg_left Behrend.roth_lower_bound hn).trans
      (rothNumberNat_le_ruzsaSzemerediNumberNat' _)

open Asymptotics Filter

/-- Asymptotic lower bound on the **Ruzsa-Szemerédi problem**.

There exists a graph with `n` vertices and `Ω((n ^ 2 * exp (-4 * √(log n))))` edges such that
each edge belongs to exactly one triangle. -/
theorem ruzsaSzemerediNumberNat_asymptotic_lower_bound :
    (fun n ↦ n ^ 2 * exp (-4 * √(log n)) : ℕ → ℝ) =O[atTop]
     fun n ↦ (ruzsaSzemerediNumberNat n : ℝ) := by
  trans fun n ↦ (n / 3 - 2) * ↑((n - 3) / 6) * exp (-4 * √(log ↑((n - 3) / 6)))
  · simp_rw [sq]
    refine (IsBigO.mul ?_ ?_).mul ?_
    · trans fun n ↦ n / 3
      · simp_rw [div_eq_inv_mul]
        exact (isBigO_refl ..).const_mul_right (by norm_num)
      refine IsLittleO.right_isBigO_sub ?_
      simpa [div_eq_inv_mul, Function.comp_def] using
        .atTop_of_const_mul₀ zero_lt_three (by simp [tendsto_natCast_atTop_atTop])
    · rw [IsBigO_def]
      refine ⟨12, ?_⟩
      simp only [IsBigOWith, norm_natCast, eventually_atTop]
      exact ⟨15, fun x hx ↦ by norm_cast; omega⟩
    · rw [isBigO_exp_comp_exp_comp]
      refine ⟨0, ?_⟩
      simp only [neg_mul, eventually_map, Pi.sub_apply, sub_neg_eq_add, neg_add_le_iff_le_add,
        add_zero, ofNat_pos, _root_.mul_le_mul_left, eventually_atTop]
      refine ⟨9, fun x hx ↦ ?_⟩
      gcongr
      · simp
        omega
      · omega
  · refine .of_norm_eventuallyLE ?_
    filter_upwards [eventually_ge_atTop 6] with n hn
    have : (0 : ℝ) ≤ n / 3 - 2 := by rify at hn; linarith
    simpa [neg_mul, abs_mul, abs_of_nonneg this] using ruzsaSzemerediNumberNat_lower_bound n
