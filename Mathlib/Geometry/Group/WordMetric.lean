/-
Copyright (c) 2026 Hang Lu Su, Valerio Proietti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su, Valerio Proietti
-/
module

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.GroupTheory.Presentation
public import Mathlib.Topology.MetricSpace.QuasiIsometry

/-!
# The word metric on a finitely generated group

Given a generating family `S : Group.Generators G α`, the *word norm* `S.wordNorm g` is the least
length of a word in the generators and their inverses representing `g`, and the *word metric* is
`dist g h = S.wordNorm (g⁻¹ * h)`.

The word metric depends on the generating family, so it is carried by the type synonym
`Group.Generators.Space S` rather than by `G` itself. The point of the construction is that this
dependence is invisible to coarse geometry: for two *finite* generating families the identity map
is a quasi-isometry (`Group.Generators.isQuasiIsometry_cast`). This is the first and most basic
quasi-isometry invariance statement in geometric group theory, and it is what makes "the" large
scale geometry of a finitely generated group well defined.

## Main definitions

* `Group.Generators.wordNorm`: the word norm, `ℕ`-valued.
* `Group.Generators.groupNorm`: the word norm packaged as a `GroupNorm G`.
* `Group.Generators.Space`: `G` carrying the word metric of a chosen generating family.

## Main results

* `Group.Generators.wordNorm_mul_le`, `wordNorm_inv`, `wordNorm_eq_zero`: the word norm is a norm.
* `Group.Generators.exists_wordNorm_le`: for a finite generating family `S`, any other word norm is
  bounded by a constant multiple of `S`'s.
* `Group.Generators.isQuasiIsometry_cast`: **the word metrics of two finite generating families of
  the same group are quasi-isometric**, via the identity map.

## Tags

word metric, word norm, generating set, quasi-isometry, geometric group theory
-/

@[expose] public section

variable {G : Type*} [Group G] {α α' : Type*}

namespace Group.Generators

variable (S : Group.Generators G α)

/-- The set of lengths of words in the generators of `S` (and their inverses) representing `g`. -/
def wordLengths (g : G) : Set ℕ :=
  {n | ∃ l : List (α × Bool), l.length = n ∧ FreeGroup.lift S.val (FreeGroup.mk l) = g}

theorem wordLengths_nonempty (g : G) : (S.wordLengths g).Nonempty := by
  obtain ⟨w, hw⟩ := S.lift_surjective g
  obtain ⟨l, hl⟩ := Quot.exists_rep w
  rw [FreeGroup.quot_mk_eq_mk] at hl
  exact ⟨l.length, l, rfl, by rw [hl]; exact hw⟩

/-- The word norm of `g`: the least length of a word in the generators of `S` and their inverses
representing `g`. -/
noncomputable def wordNorm (g : G) : ℕ := sInf (S.wordLengths g)

theorem wordNorm_mem_wordLengths (g : G) : S.wordNorm g ∈ S.wordLengths g :=
  Nat.sInf_mem (S.wordLengths_nonempty g)

theorem wordNorm_le {g : G} {n : ℕ} (h : n ∈ S.wordLengths g) : S.wordNorm g ≤ n :=
  Nat.sInf_le h

/-- A word of length `S.wordNorm g` representing `g`. -/
theorem exists_list_length_eq_wordNorm (g : G) :
    ∃ l : List (α × Bool), l.length = S.wordNorm g ∧ FreeGroup.lift S.val (FreeGroup.mk l) = g :=
  S.wordNorm_mem_wordLengths g

theorem wordNorm_le_of_mk {l : List (α × Bool)} {g : G}
    (h : FreeGroup.lift S.val (FreeGroup.mk l) = g) : S.wordNorm g ≤ l.length :=
  S.wordNorm_le ⟨l, rfl, h⟩

@[simp]
theorem wordNorm_one : S.wordNorm (1 : G) = 0 :=
  Nat.le_zero.mp (S.wordNorm_le_of_mk (l := []) (by simp))

theorem wordNorm_mul_le (g h : G) : S.wordNorm (g * h) ≤ S.wordNorm g + S.wordNorm h := by
  obtain ⟨l, hl, hlg⟩ := S.exists_list_length_eq_wordNorm g
  obtain ⟨k, hk, hkh⟩ := S.exists_list_length_eq_wordNorm h
  refine le_trans (S.wordNorm_le_of_mk (l := l ++ k) ?_) (by simp [hl, hk])
  rw [← FreeGroup.mul_mk, map_mul, hlg, hkh]

@[simp]
theorem wordNorm_inv (g : G) : S.wordNorm g⁻¹ = S.wordNorm g := by
  have key : ∀ x : G, S.wordNorm x⁻¹ ≤ S.wordNorm x := by
    intro x
    obtain ⟨l, hl, hlx⟩ := S.exists_list_length_eq_wordNorm x
    refine le_trans (S.wordNorm_le_of_mk (l := FreeGroup.invRev l) ?_) ?_
    · rw [← FreeGroup.inv_mk, map_inv, hlx]
    · rw [FreeGroup.invRev_length, hl]
  exact le_antisymm (key g) (by simpa using key g⁻¹)

@[simp]
theorem wordNorm_eq_zero {g : G} : S.wordNorm g = 0 ↔ g = 1 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  obtain ⟨l, hl, hlg⟩ := S.exists_list_length_eq_wordNorm g
  rw [h, List.length_eq_zero_iff] at hl
  rw [← hlg, hl]
  simp

/-- The word norm of `S`, packaged as a `GroupNorm G`. -/
noncomputable def groupNorm : GroupNorm G where
  toFun g := S.wordNorm g
  map_one' := by simp
  mul_le' g h := by exact_mod_cast S.wordNorm_mul_le g h
  inv' g := by simp
  eq_one_of_map_eq_zero' g h := by
    simpa using (S.wordNorm_eq_zero (g := g)).mp (by exact_mod_cast h)

/-! ### The word metric -/

/-- `G` equipped with the word metric of the generating family `S`. This is a type synonym for `G`;
the metric is `dist g h = S.wordNorm (g⁻¹ * h)`.

Two generating families give two genuinely different metrics on the same group, so they must live
on different types. See `Group.Generators.isQuasiIsometry_cast`: for finite generating families the
two metrics are quasi-isometric, which is the sense in which the choice does not matter. -/
def Space (_S : Group.Generators G α) : Type _ := G

instance : Group S.Space := inferInstanceAs (Group G)

/-- The identity map `G → S.Space`. -/
def toSpace : G → S.Space := _root_.id

/-- The identity map `S.Space → G`. -/
def ofSpace : S.Space → G := _root_.id

@[simp] theorem ofSpace_toSpace (g : G) : S.ofSpace (S.toSpace g) = g := rfl

noncomputable instance : NormedGroup S.Space :=
  @GroupNorm.toNormedGroup S.Space _ S.groupNorm

theorem dist_eq (g h : S.Space) : dist g h = S.wordNorm ((S.ofSpace g)⁻¹ * S.ofSpace h) := rfl

@[simp]
theorem dist_toSpace (g h : G) :
    dist (S.toSpace g) (S.toSpace h) = S.wordNorm (g⁻¹ * h) := rfl

theorem dist_nonneg' (g h : S.Space) : (0 : ℝ) ≤ dist g h := dist_nonneg

/-! ### Change of generating family -/

/-- Each generator of `S` is a word of bounded length in the generators of `T`. -/
theorem exists_wordNorm_val_le [Finite α] (S : Group.Generators G α)
    (T : Group.Generators G α') : ∃ M, ∀ a : α, T.wordNorm (S.val a) ≤ M :=
  (Set.finite_range fun a : α => T.wordNorm (S.val a)).bddAbove.imp
    fun _ hM _ => hM (Set.mem_range_self _)

/-- **Comparison of word norms.** For a finite generating family `S`, the word norm of any other
generating family `T` is bounded by a constant multiple of `S`'s. -/
theorem exists_wordNorm_le [Finite α] (S : Group.Generators G α) (T : Group.Generators G α') :
    ∃ M, ∀ g : G, T.wordNorm g ≤ M * S.wordNorm g := by
  obtain ⟨M, hM⟩ := S.exists_wordNorm_val_le T
  refine ⟨M, fun g => ?_⟩
  obtain ⟨l, hl, hlg⟩ := S.exists_list_length_eq_wordNorm g
  -- Each letter of the `S`-word contributes at most `M` to the `T`-word norm.
  have key : ∀ k : List (α × Bool), T.wordNorm (FreeGroup.lift S.val (FreeGroup.mk k))
      ≤ M * k.length := by
    intro k
    induction k with
    | nil => simp
    | cons x k ih =>
      have hx : (FreeGroup.mk (x :: k) : FreeGroup α) = FreeGroup.mk [x] * FreeGroup.mk k := by
        rw [FreeGroup.mul_mk]; rfl
      have hone : T.wordNorm (FreeGroup.lift S.val (FreeGroup.mk [x])) ≤ M := by
        obtain ⟨a, b⟩ := x
        cases b
        · have : (FreeGroup.mk [(a, false)] : FreeGroup α) = (FreeGroup.of a)⁻¹ := by
            rw [show (FreeGroup.of a : FreeGroup α) = FreeGroup.mk [(a, true)] from rfl,
              FreeGroup.inv_mk]
            rfl
          rw [this, map_inv, wordNorm_inv, FreeGroup.lift_apply_of]
          exact hM a
        · rw [show (FreeGroup.mk [(a, true)] : FreeGroup α) = FreeGroup.of a from rfl,
            FreeGroup.lift_apply_of]
          exact hM a
      rw [hx, map_mul]
      calc T.wordNorm (FreeGroup.lift S.val (FreeGroup.mk [x])
            * FreeGroup.lift S.val (FreeGroup.mk k))
          ≤ T.wordNorm (FreeGroup.lift S.val (FreeGroup.mk [x]))
              + T.wordNorm (FreeGroup.lift S.val (FreeGroup.mk k)) := T.wordNorm_mul_le _ _
        _ ≤ M + M * k.length := Nat.add_le_add hone ih
        _ = M * (x :: k).length := by rw [List.length_cons, Nat.mul_succ]; omega
  calc T.wordNorm g = T.wordNorm (FreeGroup.lift S.val (FreeGroup.mk l)) := by rw [hlg]
    _ ≤ M * l.length := key l
    _ = M * S.wordNorm g := by rw [hl]

/-- The identity map, viewed as a map between the word metrics of two generating families. -/
def cast (S : Group.Generators G α) (T : Group.Generators G α') : S.Space → T.Space := _root_.id

/-- **The word metric of a finitely generated group is well defined up to quasi-isometry**: for any
two finite generating families the identity map is a quasi-isometry between the two word metrics.

This is the basic quasi-isometry invariance statement of geometric group theory. It is what allows
one to speak of "the" large scale geometry of a finitely generated group, and hence to ask whether
an invariant such as the Dehn function depends on the presentation. -/
theorem isQuasiIsometry_cast [Finite α] [Finite α'] (S : Group.Generators G α)
    (T : Group.Generators G α') : IsQuasiIsometry (S.cast T) := by
  obtain ⟨M, hM⟩ := S.exists_wordNorm_le T
  obtain ⟨N, hN⟩ := T.exists_wordNorm_le S
  refine ⟨(max M N : ℕ), 0, ⟨⟨by positivity, le_rfl, fun x y => ?_, fun x y => ?_⟩,
    fun y => ⟨y, le_of_eq (dist_self y)⟩⟩⟩
  · change (S.wordNorm (x⁻¹ * y) : ℝ) ≤ (max M N : ℕ) * (T.wordNorm (x⁻¹ * y) : ℝ) + 0
    have h : S.wordNorm (x⁻¹ * y) ≤ max M N * T.wordNorm (x⁻¹ * y) :=
      (hN _).trans (Nat.mul_le_mul (le_max_right M N) le_rfl)
    push_cast
    exact_mod_cast le_trans (by exact_mod_cast h) (by simp)
  · change (T.wordNorm (x⁻¹ * y) : ℝ) ≤ (max M N : ℕ) * (S.wordNorm (x⁻¹ * y) : ℝ) + 0
    have h : T.wordNorm (x⁻¹ * y) ≤ max M N * S.wordNorm (x⁻¹ * y) :=
      (hM _).trans (Nat.mul_le_mul (le_max_left M N) le_rfl)
    push_cast
    exact_mod_cast le_trans (by exact_mod_cast h) (by simp)

/-- Two finite generating families of the same group give quasi-isometric word metrics. -/
theorem isQuasiIsometricTo_space [Finite α] [Finite α'] (S : Group.Generators G α)
    (T : Group.Generators G α') : IsQuasiIsometricTo S.Space T.Space :=
  ⟨S.cast T, S.isQuasiIsometry_cast T⟩

end Group.Generators
