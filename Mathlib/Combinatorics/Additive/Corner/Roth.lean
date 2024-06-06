/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Combinatorics.Additive.Corner.Defs
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite

/-!
# The corners theorem and Roth's theorem

This file proves the corners theorem and Roth's theorem on arithmetic progressions of length three.

## References

* [Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
* [Wikipedia, *Corners theorem*](https://en.wikipedia.org/wiki/Corners_theorem)
-/

open Finset SimpleGraph TripartiteFromTriangles
open Function hiding graph
open Fintype (card)

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {A B : Finset (G × G)}
  {a b c d x y : G} {n : ℕ} {ε : ℝ}

namespace Corners

/-- The triangle indices for the proof of the corners theorem construction. -/
private def triangleIndices (A : Finset (G × G)) : Finset (G × G × G) :=
  A.map ⟨fun (a, b) ↦ (a, b, a + b), by rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨⟩; rfl⟩

@[simp]
private lemma mk_mem_triangleIndices : (a, b, c) ∈ triangleIndices A ↔ (a, b) ∈ A ∧ c = a + b := by
  simp only [triangleIndices, Prod.ext_iff, mem_map, Embedding.coeFn_mk, exists_prop, Prod.exists,
    eq_comm]
  refine ⟨?_, fun h ↦ ⟨_, _, h.1, rfl, rfl, h.2⟩⟩
  rintro ⟨_, _, h₁, rfl, rfl, h₂⟩
  exact ⟨h₁, h₂⟩

@[simp] private lemma card_triangleIndices : (triangleIndices A).card = A.card := card_map _

private instance triangleIndices.instExplicitDisjoint : ExplicitDisjoint (triangleIndices A) := by
  constructor
  all_goals
    simp only [mk_mem_triangleIndices, Prod.mk.inj_iff, exists_prop, forall_exists_index, and_imp]
    rintro a b _ a' - rfl - h'
    simp [Fin.val_eq_val, *] at * <;> assumption

private lemma noAccidental (hs : IsCornerFree (A : Set (G × G))) :
    NoAccidental (triangleIndices A) where
  eq_or_eq_or_eq a a' b b' c c' ha hb hc := by
    simp only [mk_mem_triangleIndices] at ha hb hc
    exact .inl $ hs ⟨hc.1, hb.1, ha.1, hb.2.symm.trans ha.2⟩

private lemma farFromTriangleFree_graph (hε : ε * card G ^ 2 ≤ A.card) :
    (graph $ triangleIndices A).FarFromTriangleFree (ε / 9) := by
  refine farFromTriangleFree _ ?_
  simp_rw [card_triangleIndices, mul_comm_div, Nat.cast_pow, Nat.cast_add]
  ring_nf
  simpa only [mul_comm] using hε

end Corners

open Corners


/-- An explicit form for the constant in the corners theorem.

Note that this depends on `SzemerediRegularity.bound`, which is a tower-type exponential. This means
`cornersTheoremBound` is in practice absolutely tiny. -/
noncomputable def cornersTheoremBound (ε : ℝ) : ℕ := ⌊(triangleRemovalBound (ε / 9) * 27)⁻¹⌋₊ + 1

/-- The **corners theorem** for finite abelian groups.

The maximum density of a corner-free set in `G × G` goes to zero as `|G|` tends to infinity. -/
theorem corners_theorem (ε : ℝ) (hε : 0 < ε) (hG : cornersTheoremBound ε ≤ card G)
    (A : Finset (G × G)) (hAε : ε * card G ^ 2 ≤ A.card) : ¬ IsCornerFree (A : Set (G × G)) := by
  rintro hA
  rw [cornersTheoremBound, Nat.add_one_le_iff] at hG
  have hε₁ : ε ≤ 1 := by
    have := hAε.trans (Nat.cast_le.2 A.card_le_univ)
    simp only [sq, Nat.cast_mul, Fintype.card_prod, Fintype.card_fin] at this
    rwa [mul_le_iff_le_one_left] at this
    positivity
  have := noAccidental hA
  rw [Nat.floor_lt' (by positivity), inv_pos_lt_iff_one_lt_mul'] at hG
  refine hG.not_le (le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < card G ^ 2))
  classical
  have h₁ := (farFromTriangleFree_graph hAε).le_card_cliqueFinset
  rw [card_triangles, card_triangleIndices] at h₁
  convert h₁.trans (Nat.cast_le.2 $ card_le_univ _) using 1 <;> simp <;> ring
  · have : ε / 9 ≤ 1 := by linarith
    positivity

/-- The **corners theorem** for `ℕ`.

The maximum density of a corner-free set in `{1, ..., n} × {1, ..., n}` goes to zero as `n` tends to
infinity. -/
theorem corners_theorem_nat (hε : 0 < ε) (hn : cornersTheoremBound (ε / 9) ≤ n)
    (A : Finset (ℕ × ℕ)) (hAn : A ⊆ range n ×ˢ range n) (hAε : ε * n ^ 2 ≤ A.card) :
    ¬ IsCornerFree (A : Set (ℕ × ℕ)) := by
  rintro hA
  rw [← coe_subset, coe_product] at hAn
  have : A = Prod.map Fin.val Fin.val ''
      (Prod.map Nat.cast Nat.cast '' A : Set (Fin (2 * n).succ × Fin (2 * n).succ)) := by
    rw [Set.image_image, Set.image_congr, Set.image_id]
    simp only [mem_coe, Nat.succ_eq_add_one, Prod_map, Fin.val_natCast, id_eq, Prod.forall,
      Prod.mk.injEq, Nat.mod_succ_eq_iff_lt]
    rintro a b hab
    have := hAn hab
    simp at this
    omega
  rw [this] at hA
  have := Fin.isAddFreimanIso_Iio two_ne_zero (le_refl (2 * n))
  have := hA.of_image this.isAddFreimanHom Fin.val_injective.injOn $ by
    refine Set.image_subset_iff.2 $ hAn.trans fun x hx ↦ ?_
    simp only [coe_range, Set.mem_prod, Set.mem_Iio] at hx
    exact ⟨Fin.natCast_strictMono (by omega) hx.1, Fin.natCast_strictMono (by omega) hx.2⟩
  rw [← coe_image] at this
  refine corners_theorem (ε / 9) (by positivity) (by simp; omega) _ ?_ this
  calc
    _ = ε / 9 * (2 * n + 1) ^ 2 := by simp
    _ ≤ ε / 9 * (2 * n + n) ^ 2 := by gcongr; simp; unfold cornersTheoremBound at hn; omega
    _ = ε * n ^ 2 := by ring
    _ ≤ A.card := hAε
    _ = _ := by
      rw [card_image_of_injOn]
      have : Set.InjOn Nat.cast (range n) :=
        (CharP.natCast_injOn_Iio (Fin (2 * n).succ) (2 * n).succ).mono (by simp; omega)
      exact (this.prodMap this).mono hAn

/-- **Roth's theorem** for finite abelian groups.

The maximum density of a 3AP-free set in `G` goes to zero as `|G|` tends to infinity. -/
theorem roth_3ap_theorem (ε : ℝ) (hε : 0 < ε) (hG : cornersTheoremBound ε ≤ card G)
    (A : Finset G) (hAε : ε * card G ≤ A.card) : ¬ ThreeAPFree (A : Set G) := by
  rintro hA
  classical
  let B : Finset (G × G) := univ.filter fun (x, y) ↦ y - x ∈ A
  have : ε * card G ^ 2 ≤ B.card := by
    calc
      _ = card G * (ε * card G) := by ring
      _ ≤ card G * A.card := by gcongr
      _ = B.card := ?_
    norm_cast
    rw [← card_univ, ← card_product]
    exact card_equiv ((Equiv.refl _).prodShear fun a ↦ Equiv.addLeft a) (by simp [B])
  obtain ⟨x₁, y₁, x₂, y₂, hx₁y₁, hx₁y₂, hx₂y₁, hxy, hx₁x₂⟩ :
      ∃ x₁ y₁ x₂ y₂, y₁ - x₁ ∈ A ∧ y₂ - x₁ ∈ A ∧ y₁ - x₂ ∈ A ∧ x₁ + y₂ = x₂ + y₁ ∧ x₁ ≠ x₂ := by
    simpa [IsCornerFree, isCorner_iff, B, -exists_and_left, -exists_and_right]
      using corners_theorem ε hε hG B this
  have := hA hx₂y₁ hx₁y₁ hx₁y₂ $ by -- TODO: This really ought to just be `by linear_combination h`
    rw [sub_add_sub_comm, add_comm, add_sub_add_comm, add_right_cancel_iff,
      sub_eq_sub_iff_add_eq_add, add_comm, hxy, add_comm]
  exact hx₁x₂ $ by simpa using this.symm

/-- **Roth's theorem** for `ℕ`.

The maximum density of a 3AP-free set in `{1, ..., n}` goes to zero as `n` tends to infinity. -/
theorem roth_3ap_theorem_nat (ε : ℝ) (hε : 0 < ε) (hG : cornersTheoremBound (ε / 3) ≤ n)
    (A : Finset ℕ) (hAn : A ⊆ range n) (hAε : ε * n ≤ A.card) : ¬ ThreeAPFree (A : Set ℕ) := by
  rintro hA
  rw [← coe_subset, coe_range] at hAn
  have : A = Fin.val '' (Nat.cast '' A : Set (Fin (2 * n).succ)) := by
    rw [Set.image_image, Set.image_congr, Set.image_id]
    simp only [mem_coe, Nat.succ_eq_add_one, Fin.val_natCast, id_eq, Nat.mod_succ_eq_iff_lt]
    rintro a ha
    have := hAn ha
    simp at this
    omega
  rw [this] at hA
  have := Fin.isAddFreimanIso_Iio two_ne_zero (le_refl (2 * n))
  have := hA.of_image this.isAddFreimanHom Fin.val_injective.injOn $ Set.image_subset_iff.2 $
      hAn.trans fun x hx ↦ Fin.natCast_strictMono (by omega) $ by
        simpa only [coe_range, Set.mem_Iio] using hx
  rw [← coe_image] at this
  refine roth_3ap_theorem (ε / 3) (by positivity) (by simp; omega) _ ?_ this
  calc
    _ = ε / 3 * (2 * n + 1) := by simp
    _ ≤ ε / 3 * (2 * n + n) := by gcongr; simp; unfold cornersTheoremBound at hG; omega
    _ = ε * n := by ring
    _ ≤ A.card := hAε
    _ = _ := by
      rw [card_image_of_injOn]
      exact (CharP.natCast_injOn_Iio (Fin (2 * n).succ) (2 * n).succ).mono $ hAn.trans $ by
        simp; omega

open Asymptotics Filter

/-- **Roth's theorem** for `ℕ` as an asymptotic statement.

The maximum density of a 3AP-free set in `{1, ..., n}` goes to zero as `n` tends to infinity. -/
theorem rothNumberNat_isLittleO_id :
    IsLittleO atTop (fun N ↦ (rothNumberNat N : ℝ)) (fun N ↦ (N : ℝ)) := by
  simp only [isLittleO_iff, eventually_atTop, RCLike.norm_natCast]
  refine fun ε hε ↦ ⟨cornersTheoremBound (ε / 3), fun n hn ↦ ?_⟩
  obtain ⟨A, hs₁, hs₂, hs₃⟩ := rothNumberNat_spec n
  rw [← hs₂, ← not_lt]
  exact fun hδn ↦ roth_3ap_theorem_nat ε hε hn _ hs₁ hδn.le hs₃
