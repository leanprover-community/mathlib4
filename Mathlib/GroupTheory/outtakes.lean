/-
Copyright (c) 2026 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su
-/
module

public import Mathlib.Data.Set.Finite.List
public import Mathlib.GroupTheory.DehnFunction
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.Presentation

/-!
# Dehn functions: supporting theory

This file develops the theory of `Group.Presentation.dehn` and its auxiliary notions
`Group.Presentation.conjRelSet`, `Group.Presentation.IsAreaAtMost`, `Group.Presentation.area` and
`Group.Presentation.kerBall`, whose definitions live in `Mathlib.GroupTheory.DehnFunction`. It also
introduces the growth-type comparison `Nat.GrowthLE`/`Nat.GrowthEquiv` used to state the invariance
of the Dehn function.

## Main definitions

* `Nat.GrowthLE`, `Nat.GrowthEquiv`: the standard comparison of growth types,
  `f ≼ g ↔ ∃ C ≥ 1, ∀ n, f n ≤ C * g (C * n + C) + C * n + C`.

## Main results

* `Group.Presentation.mem_ker_iff_exists_isAreaAtMost`: a word has finite area exactly when it dies
  in `G`. This is the combinatorial content of `Group.Presentation.ker_eq_normalClosure`, and it is
  what makes `area` well behaved.
* `Group.Presentation.dehn_growthEquiv`: **any two finite presentations of the same group have
  equivalent Dehn functions.** So the growth type of the Dehn function is an invariant of the
  finitely presented group.

The Dehn function itself genuinely depends on the presentation: only its class under
`Nat.GrowthEquiv` is an invariant. That class is exactly the granularity at which the Dehn function
is a quasi-isometry invariant — the full statement, that quasi-isometric finitely presented groups
have `Nat.GrowthEquiv` Dehn functions, cannot yet be formulated here because Mathlib has no
quasi-isometries. `dehn_growthEquiv` is the special case of a change of presentation, which is what
makes "the Dehn function of a finitely presented group" well defined in the first place.

## Design notes

* `area` is defined by `sInf`, so `area w = 0` is a junk value when `w` does not die in `G`. Lemmas
  that genuinely need finiteness therefore carry a `w ∈ P.lift.ker` hypothesis; the ones that do
  not (`area_inv`, `area_conj`) are stated unconditionally.
* `dehn` is defined by `sSup`, and is junk unless `[Finite α]` makes the relevant set of words
  finite; again the lemmas carry the hypothesis.
* `FreeGroup.norm` needs `[DecidableEq α]`, so `kerBall` and `dehn` do too.
* `Nat.GrowthLE` is a preorder only on *monotone* functions, whence the `Monotone` hypotheses in
  `Nat.GrowthLE.rfl` and `Nat.GrowthLE.trans`. Dehn functions are monotone
  (`Group.Presentation.dehn_mono`), so this costs nothing here.

## References

* [D. F. Holt, S. Rees, C. E. Röver, *Groups, Languages and Automata*][HoltReesRover2017]
* <https://en.wikipedia.org/wiki/Dehn_function>

## Tags

Dehn function, isoperimetric function, area, van Kampen diagram, group presentation
-/

@[expose] public section

variable {G α α' ρ ρ' : Type*} [Group G]

/-! ### Comparison of growth types -/

namespace Nat

/-- `f` grows at most as fast as `g`, written `f ≼ g` in the literature: there is a `C ≥ 1` with
`f n ≤ C * g (C * n + C) + C * n + C` for all `n`.

This is the standard comparison used in geometric group theory: it is the coarsening under which
Dehn functions, growth functions and other filling invariants become quasi-isometry invariants. The
affine slack `C * n + C` on both the argument and the value is what absorbs a change of generating
set, so all functions bounded by a linear one become equivalent. -/
def GrowthLE (f g : ℕ → ℕ) : Prop :=
  ∃ C, 1 ≤ C ∧ ∀ n, f n ≤ C * g (C * n + C) + C * n + C

/-- `f` and `g` have the same growth type: each grows at most as fast as the other. -/
def GrowthEquiv (f g : ℕ → ℕ) : Prop :=
  GrowthLE f g ∧ GrowthLE g f

namespace GrowthLE

/-- A monotone function grows at most as fast as itself. -/
theorem rfl {f : ℕ → ℕ} (hf : Monotone f) : GrowthLE f f :=
  ⟨1, le_rfl, fun n => by have : f n ≤ f (1 * n + 1) := hf (by omega); omega⟩

/-- `GrowthLE` is transitive when the largest function is monotone. -/
theorem trans {f g h : ℕ → ℕ} (hh : Monotone h) (hfg : GrowthLE f g) (hgh : GrowthLE g h) :
    GrowthLE f h := by
  obtain ⟨C, hC, hf⟩ := hfg
  obtain ⟨D, hD, hg⟩ := hgh
  refine ⟨C * C * D + C * D + C + D, by omega, fun n => ?_⟩
  set E := C * C * D + C * D + C + D with hE
  have hstep : g (C * n + C) ≤ D * h (E * n + E) + D * (C * n + C) + D := by
    refine (hg _).trans ?_
    gcongr
    refine hh ?_
    calc D * (C * n + C) + D = C * D * n + (C * D + D) := by ring
      _ ≤ E * n + E :=
          Nat.add_le_add (Nat.mul_le_mul (show C * D ≤ E by omega) (le_refl n)) (by omega)
  calc f n ≤ C * g (C * n + C) + C * n + C := hf n
    _ ≤ C * (D * h (E * n + E) + D * (C * n + C) + D) + C * n + C := by gcongr
    _ = C * D * h (E * n + E) + (C * C * D + C) * n + (C * C * D + C * D + C) := by ring
    _ ≤ E * h (E * n + E) + E * n + E :=
        Nat.add_le_add (Nat.add_le_add
          (Nat.mul_le_mul (show C * D ≤ E by omega) (le_refl _))
          (Nat.mul_le_mul (show C * C * D + C ≤ E by omega) (le_refl n))) (by omega)

end GrowthLE

namespace GrowthEquiv

theorem rfl {f : ℕ → ℕ} (hf : Monotone f) : GrowthEquiv f f := ⟨GrowthLE.rfl hf, GrowthLE.rfl hf⟩

theorem symm {f g : ℕ → ℕ} (h : GrowthEquiv f g) : GrowthEquiv g f := ⟨h.2, h.1⟩

theorem trans {f g h : ℕ → ℕ} (hf : Monotone f) (hh : Monotone h)
    (h₁ : GrowthEquiv f g) (h₂ : GrowthEquiv g h) : GrowthEquiv f h :=
  ⟨h₁.1.trans hh h₂.1, h₂.2.trans hf h₁.2⟩

end GrowthEquiv

end Nat

namespace Group.Presentation

variable {P : Group.Presentation G α ρ}

/-! ### Conjugates of relators -/

theorem mul_inv_mem_conjRelSet {r : FreeGroup α} (hr : r ∈ P.relSet) (u : FreeGroup α) :
    u * r * u⁻¹ ∈ P.conjRelSet := ⟨u, r, hr, Or.inl rfl⟩

theorem rel_mem_conjRelSet (r : ρ) : P.rel r ∈ P.conjRelSet := by
  simpa using mul_inv_mem_conjRelSet (P.rel_mem_relSet r) 1

/-- `conjRelSet` is closed under conjugation. -/
theorem conj_mem_conjRelSet {x : FreeGroup α} (hx : x ∈ P.conjRelSet) (u : FreeGroup α) :
    u * x * u⁻¹ ∈ P.conjRelSet := by
  obtain ⟨v, r, hr, h | h⟩ := hx
  · exact ⟨u * v, r, hr, Or.inl (by rw [h]; group)⟩
  · exact ⟨u * v, r, hr, Or.inr (by rw [h]; group)⟩

/-- `conjRelSet` is closed under inversion. -/
theorem inv_mem_conjRelSet {x : FreeGroup α} (hx : x ∈ P.conjRelSet) : x⁻¹ ∈ P.conjRelSet := by
  obtain ⟨v, r, hr, h | h⟩ := hx
  · exact ⟨v, r, hr, Or.inr (by rw [h]; group)⟩
  · exact ⟨v, r, hr, Or.inl (by rw [h]; group)⟩

/-- Every conjugate of a relator dies in `G`. -/
theorem lift_eq_one_of_mem_conjRelSet {x : FreeGroup α} (hx : x ∈ P.conjRelSet) : P.lift x = 1 := by
  obtain ⟨u, r, hr, h | h⟩ := hx <;> simp [h, P.lift_eq_one_of_mem_relSet hr]

/-! ### Area -/

theorem IsAreaAtMost.mono {w : FreeGroup α} {m n : ℕ} (h : P.IsAreaAtMost w m) (hmn : m ≤ n) :
    P.IsAreaAtMost w n :=
  let ⟨l, hl, hmem, hprod⟩ := h; ⟨l, hl.trans hmn, hmem, hprod⟩

theorem isAreaAtMost_one : P.IsAreaAtMost 1 0 := ⟨[], le_rfl, by simp, rfl⟩

theorem isAreaAtMost_of_mem_conjRelSet {x : FreeGroup α} (hx : x ∈ P.conjRelSet) :
    P.IsAreaAtMost x 1 :=
  ⟨[x], le_rfl, by simpa using hx, by simp⟩

theorem IsAreaAtMost.mul {w v : FreeGroup α} {m n : ℕ} (hw : P.IsAreaAtMost w m)
    (hv : P.IsAreaAtMost v n) : P.IsAreaAtMost (w * v) (m + n) := by
  obtain ⟨l, hl, hlmem, rfl⟩ := hw
  obtain ⟨k, hk, hkmem, rfl⟩ := hv
  refine ⟨l ++ k, by simpa using Nat.add_le_add hl hk, ?_, by simp⟩
  simp only [List.mem_append]
  rintro x (hx | hx)
  exacts [hlmem x hx, hkmem x hx]

theorem IsAreaAtMost.inv {w : FreeGroup α} {n : ℕ} (hw : P.IsAreaAtMost w n) :
    P.IsAreaAtMost w⁻¹ n := by
  obtain ⟨l, hl, hmem, rfl⟩ := hw
  refine ⟨(l.map fun x => x⁻¹).reverse, by simpa using hl, ?_, (List.prod_inv_reverse l).symm⟩
  simp only [List.mem_reverse, List.mem_map]
  rintro x ⟨y, hy, rfl⟩
  exact inv_mem_conjRelSet (hmem y hy)

theorem IsAreaAtMost.conj {w : FreeGroup α} {n : ℕ} (hw : P.IsAreaAtMost w n) (u : FreeGroup α) :
    P.IsAreaAtMost (u * w * u⁻¹) n := by
  obtain ⟨l, hl, hmem, rfl⟩ := hw
  refine ⟨l.map (MulAut.conj u), by simpa using hl, ?_,
    by simpa using List.prod_hom l (MulAut.conj u)⟩
  simp only [List.mem_map]
  rintro x ⟨y, hy, rfl⟩
  exact conj_mem_conjRelSet (hmem y hy) u

theorem isAreaAtMost_inv_iff {w : FreeGroup α} {n : ℕ} :
    P.IsAreaAtMost w⁻¹ n ↔ P.IsAreaAtMost w n :=
  ⟨fun h => by simpa using h.inv, IsAreaAtMost.inv⟩

theorem isAreaAtMost_conj_iff {w : FreeGroup α} {n : ℕ} (u : FreeGroup α) :
    P.IsAreaAtMost (u * w * u⁻¹) n ↔ P.IsAreaAtMost w n := by
  refine ⟨fun h => ?_, fun h => h.conj u⟩
  have h' := h.conj u⁻¹
  rwa [show u⁻¹ * (u * w * u⁻¹) * u⁻¹⁻¹ = w by group] at h'

theorem IsAreaAtMost.lift_eq_one {w : FreeGroup α} {n : ℕ} (hw : P.IsAreaAtMost w n) :
    P.lift w = 1 := by
  obtain ⟨l, -, hmem, rfl⟩ := hw
  rw [← List.prod_hom l P.lift]
  refine List.prod_eq_one ?_
  simp only [List.mem_map]
  rintro x ⟨y, hy, rfl⟩
  exact lift_eq_one_of_mem_conjRelSet (hmem y hy)

variable (P) in
/-- A word dies in `G` if and only if it is a product of finitely many conjugates of relators and
inverse relators. This turns the defining condition `Group.Presentation.ker_eq_normalClosure` of a
presentation into the combinatorial statement that makes `Group.Presentation.area` meaningful. -/
theorem mem_ker_iff_exists_isAreaAtMost {w : FreeGroup α} :
    w ∈ P.lift.ker ↔ ∃ n, P.IsAreaAtMost w n := by
  refine ⟨fun hw => ?_, fun ⟨n, hn⟩ => hn.lift_eq_one⟩
  rw [P.ker_lift, Subgroup.normalClosure, ← Subgroup.mem_toSubmonoid,
    Subgroup.closure_toSubmonoid] at hw
  obtain ⟨l, hmem, rfl⟩ := Submonoid.exists_list_of_mem_closure hw
  refine ⟨l.length, l, le_rfl, fun x hx => ?_, rfl⟩
  rcases hmem x hx with h | h
  · rw [Group.mem_conjugatesOfSet_iff] at h
    obtain ⟨r, hr, hconj⟩ := h
    obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
    exact mul_inv_mem_conjRelSet hr c
  · rw [Set.mem_inv, Group.mem_conjugatesOfSet_iff] at h
    obtain ⟨r, hr, hconj⟩ := h
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    exact ⟨c, r, hr, Or.inr (by rw [← inv_inj, ← hc]; group)⟩

theorem area_le {w : FreeGroup α} {n : ℕ} (h : P.IsAreaAtMost w n) : P.area w ≤ n :=
  Nat.sInf_le h

theorem isAreaAtMost_area {w : FreeGroup α} (hw : w ∈ P.lift.ker) :
    P.IsAreaAtMost w (P.area w) :=
  Nat.sInf_mem ((P.mem_ker_iff_exists_isAreaAtMost).mp hw)

@[simp]
theorem area_one : P.area (1 : FreeGroup α) = 0 :=
  Nat.le_zero.mp (area_le isAreaAtMost_one)

theorem area_mul_le {w v : FreeGroup α} (hw : w ∈ P.lift.ker) (hv : v ∈ P.lift.ker) :
    P.area (w * v) ≤ P.area w + P.area v :=
  area_le ((isAreaAtMost_area hw).mul (isAreaAtMost_area hv))

@[simp]
theorem area_inv (w : FreeGroup α) : P.area w⁻¹ = P.area w := by
  simp only [area]
  exact congrArg _ (Set.ext fun _ => isAreaAtMost_inv_iff)

@[simp]
theorem area_conj (u w : FreeGroup α) : P.area (u * w * u⁻¹) = P.area w := by
  simp only [area]
  exact congrArg _ (Set.ext fun _ => isAreaAtMost_conj_iff u)

theorem area_le_one_of_mem_relSet {r : FreeGroup α} (hr : r ∈ P.relSet) : P.area r ≤ 1 := by
  simpa using area_le (isAreaAtMost_of_mem_conjRelSet (mul_inv_mem_conjRelSet hr 1))

theorem area_rel_le_one (r : ρ) : P.area (P.rel r) ≤ 1 :=
  area_le_one_of_mem_relSet (P.rel_mem_relSet r)

/-- A product of `l.length` words, each of area at most `A` and each dying in `G`, has area at most
`A * l.length`. -/
theorem area_list_prod_le {l : List (FreeGroup α)} {A : ℕ} (hker : ∀ x ∈ l, x ∈ P.lift.ker)
    (hA : ∀ x ∈ l, P.area x ≤ A) : P.area l.prod ≤ A * l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hxl : l.prod ∈ P.lift.ker := by
      rw [MonoidHom.mem_ker, ← List.prod_hom l P.lift]
      refine List.prod_eq_one ?_
      simp only [List.mem_map]
      rintro y ⟨z, hz, rfl⟩
      exact MonoidHom.mem_ker.mp (hker z (List.mem_cons_of_mem _ hz))
    calc P.area (x :: l).prod
        = P.area (x * l.prod) := by rw [List.prod_cons]
      _ ≤ P.area x + P.area l.prod := area_mul_le (hker x (List.mem_cons_self ..)) hxl
      _ ≤ A + A * l.length := Nat.add_le_add (hA x (List.mem_cons_self ..))
          (ih (fun y hy => hker y (List.mem_cons_of_mem _ hy))
            (fun y hy => hA y (List.mem_cons_of_mem _ hy)))
      _ = A * (x :: l).length := by rw [List.length_cons, Nat.mul_succ]; omega

/-! ### The Dehn function -/

section Dehn

variable (P) [DecidableEq α]

theorem one_mem_kerBall (n : ℕ) : (1 : FreeGroup α) ∈ P.kerBall n := by
  simp [kerBall]

theorem kerBall_mono : Monotone P.kerBall := fun _ _ h _ hw => ⟨hw.1, hw.2.trans h⟩

/-- The ball of radius `n` in a free group on finitely many generators is finite. -/
theorem finite_norm_le [Finite α] (n : ℕ) : {w : FreeGroup α | FreeGroup.norm w ≤ n}.Finite :=
  Set.Finite.preimage FreeGroup.toWord_injective.injOn (List.finite_length_le _ n)

theorem kerBall_finite [Finite α] (n : ℕ) : (P.kerBall n).Finite :=
  (finite_norm_le n).subset fun _ hw => hw.2

theorem bddAbove_area_image_kerBall [Finite α] (n : ℕ) : BddAbove (P.area '' P.kerBall n) :=
  ((P.kerBall_finite n).image _).bddAbove

theorem nonempty_area_image_kerBall (n : ℕ) : (P.area '' P.kerBall n).Nonempty :=
  ⟨0, 1, P.one_mem_kerBall n, by simp⟩

variable {P}

theorem area_le_dehn [Finite α] {w : FreeGroup α} (hw : w ∈ P.lift.ker) :
    P.area w ≤ P.dehn (FreeGroup.norm w) :=
  le_csSup (P.bddAbove_area_image_kerBall _) ⟨w, ⟨hw, le_rfl⟩, rfl⟩

theorem dehn_le {n B : ℕ} (h : ∀ w ∈ P.kerBall n, P.area w ≤ B) : P.dehn n ≤ B :=
  csSup_le (P.nonempty_area_image_kerBall n) (by rintro _ ⟨w, hw, rfl⟩; exact h w hw)

theorem dehn_mono [Finite α] : Monotone P.dehn := fun _ _ h =>
  csSup_le_csSup (P.bddAbove_area_image_kerBall _) (P.nonempty_area_image_kerBall _)
    (Set.image_mono (P.kerBall_mono h))

end Dehn

/-! ### Independence of the presentation

Given two presentations `P = ⟨α | rel⟩` and `Q = ⟨α' | rel'⟩` of the same group `G`, we choose for
each `P`-generator a `Q`-word representing the same element of `G`. This gives a homomorphism
`P.transfer Q : FreeGroup α →* FreeGroup α'` lying over the identity of `G`. It increases word
length by a bounded factor and area by a bounded factor, and composing it with the transfer in the
other direction changes a word by a boundedly small amount. Together these give
`Group.Presentation.dehn_growthEquiv`. -/

section Transfer

variable (P : Group.Presentation G α ρ) (Q : Group.Presentation G α' ρ')

/-- For each generator of `P`, a choice of word in the generators of `Q` representing the same
element of `G`. -/
noncomputable def transferWord (a : α) : FreeGroup α' := (Q.lift_surjective' (P.val a)).choose

@[simp]
theorem lift_transferWord (a : α) : Q.lift (P.transferWord Q a) = P.val a :=
  (Q.lift_surjective' (P.val a)).choose_spec

/-- Rewriting each `P`-generator as a chosen word in the `Q`-generators. This homomorphism lies over
the identity of `G`: see `Group.Presentation.lift_transfer`. -/
noncomputable def transfer : FreeGroup α →* FreeGroup α' := FreeGroup.lift (P.transferWord Q)

@[simp]
theorem transfer_of (a : α) : P.transfer Q (FreeGroup.of a) = P.transferWord Q a :=
  FreeGroup.lift_apply_of

@[simp]
theorem lift_transfer (w : FreeGroup α) : Q.lift (P.transfer Q w) = P.lift w := by
  have : Q.lift.comp (P.transfer Q) = P.lift :=
    FreeGroup.ext_hom _ _ fun a => by simp
  exact congrArg (fun f => f w) this

/-- Rewriting a `P`-word into the generators of `Q` and back again. This is generally not the
identity of `FreeGroup α`, but it does lie over the identity of `G`. -/
noncomputable def roundTrip : FreeGroup α →* FreeGroup α := (Q.transfer P).comp (P.transfer Q)

@[simp]
theorem lift_roundTrip (w : FreeGroup α) : P.lift (P.roundTrip Q w) = P.lift w := by
  rw [roundTrip, MonoidHom.comp_apply, lift_transfer, lift_transfer]

theorem mul_roundTrip_inv_mem_ker (w : FreeGroup α) : w * (P.roundTrip Q w)⁻¹ ∈ P.lift.ker := by
  simp [MonoidHom.mem_ker]

variable {P Q}

theorem conj_mem_ker {w : FreeGroup α} (hw : w ∈ P.lift.ker) (u : FreeGroup α) :
    u * w * u⁻¹ ∈ P.lift.ker := by
  simp [MonoidHom.mem_ker, MonoidHom.mem_ker.mp hw]

/-- `FreeGroup.mk [(a, true)]` is the generator `a`. -/
private theorem mk_singleton_true (a : α) : (FreeGroup.mk [(a, true)] : FreeGroup α) =
    FreeGroup.of a := rfl

/-- `FreeGroup.mk [(a, false)]` is the inverse of the generator `a`. -/
private theorem mk_singleton_false (a : α) : (FreeGroup.mk [(a, false)] : FreeGroup α) =
    (FreeGroup.of a)⁻¹ := by
  rw [show (FreeGroup.of a : FreeGroup α) = FreeGroup.mk [(a, true)] from rfl, FreeGroup.inv_mk]
  rfl

private theorem mk_nil : (FreeGroup.mk ([] : List (α × Bool)) : FreeGroup α) = 1 := rfl

private theorem mk_cons (x : α × Bool) (l : List (α × Bool)) :
    (FreeGroup.mk (x :: l) : FreeGroup α) = FreeGroup.mk [x] * FreeGroup.mk l := by
  rw [FreeGroup.mul_mk]; rfl

variable (P Q)

/-- The transfer homomorphism increases word length by at most a bounded factor. -/
theorem exists_norm_transfer_le [Finite α] [DecidableEq α] [DecidableEq α'] :
    ∃ M, ∀ w : FreeGroup α, FreeGroup.norm (P.transfer Q w) ≤ M * FreeGroup.norm w := by
  obtain ⟨M, hM⟩ :=
    (Set.finite_range fun a : α => FreeGroup.norm (P.transferWord Q a)).bddAbove
  have hgen : ∀ x : α × Bool, FreeGroup.norm (P.transfer Q (FreeGroup.mk [x])) ≤ M := by
    rintro ⟨a, b⟩
    cases b
    · rw [mk_singleton_false, map_inv, FreeGroup.norm_inv_eq, transfer_of]
      exact hM (Set.mem_range_self a)
    · rw [mk_singleton_true, transfer_of]
      exact hM (Set.mem_range_self a)
  have key : ∀ l : List (α × Bool),
      FreeGroup.norm (P.transfer Q (FreeGroup.mk l)) ≤ M * l.length := by
    intro l
    induction l with
    | nil => simp [mk_nil]
    | cons x l ih =>
      rw [mk_cons, map_mul]
      calc FreeGroup.norm (P.transfer Q (FreeGroup.mk [x]) * P.transfer Q (FreeGroup.mk l))
          ≤ FreeGroup.norm (P.transfer Q (FreeGroup.mk [x]))
              + FreeGroup.norm (P.transfer Q (FreeGroup.mk l)) := FreeGroup.norm_mul_le _ _
        _ ≤ M + M * l.length := Nat.add_le_add (hgen x) ih
        _ = M * (x :: l).length := by rw [List.length_cons, Nat.mul_succ]; omega
  refine ⟨M, fun w => ?_⟩
  have h := key w.toWord
  rwa [FreeGroup.mk_toWord] at h

variable {P Q}

/-- A conjugate of a `P`-relator is transferred to a word of boundedly small `Q`-area. -/
theorem area_transfer_le_of_mem_conjRelSet {A : ℕ}
    (hA : ∀ r : ρ, Q.area (P.transfer Q (P.rel r)) ≤ A)
    {x : FreeGroup α} (hx : x ∈ P.conjRelSet) : Q.area (P.transfer Q x) ≤ A := by
  obtain ⟨u, r, ⟨r₀, rfl⟩, hx | hx⟩ := hx
  · rw [hx, map_mul, map_mul, map_inv, area_conj]
    exact hA r₀
  · rw [hx, map_mul, map_mul, map_inv, map_inv, area_conj, area_inv]
    exact hA r₀

variable (P Q)

/-- The transfer homomorphism increases area by at most a bounded factor. -/
theorem exists_area_transfer_le [Finite ρ] :
    ∃ A, ∀ w ∈ P.lift.ker, Q.area (P.transfer Q w) ≤ A * P.area w := by
  obtain ⟨A, hA⟩ :=
    (Set.finite_range fun r : ρ => Q.area (P.transfer Q (P.rel r))).bddAbove
  have hA' : ∀ r : ρ, Q.area (P.transfer Q (P.rel r)) ≤ A := fun r => hA (Set.mem_range_self r)
  refine ⟨A, fun w hw => ?_⟩
  obtain ⟨l, hl, hmem, rfl⟩ := isAreaAtMost_area hw
  have hker : ∀ x ∈ l.map (P.transfer Q), x ∈ Q.lift.ker := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [MonoidHom.mem_ker, lift_transfer]
    exact lift_eq_one_of_mem_conjRelSet (hmem y hy)
  have harea : ∀ x ∈ l.map (P.transfer Q), Q.area x ≤ A := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact area_transfer_le_of_mem_conjRelSet hA' (hmem y hy)
  rw [← List.prod_hom l (P.transfer Q)]
  calc Q.area (l.map (P.transfer Q)).prod ≤ A * (l.map (P.transfer Q)).length :=
        area_list_prod_le hker harea
    _ = A * l.length := by rw [List.length_map]
    _ ≤ A * P.area l.prod := Nat.mul_le_mul (le_refl A) hl

/-- A word differs from its round trip by a word of area at most a bounded multiple of its length.
This is the estimate that lets one compare areas measured in two different presentations. -/
theorem exists_area_mul_roundTrip_inv_le [Finite α] [DecidableEq α] :
    ∃ B, ∀ w : FreeGroup α, P.area (w * (P.roundTrip Q w)⁻¹) ≤ B * FreeGroup.norm w := by
  obtain ⟨B, hB⟩ := (Set.finite_range fun a : α =>
    P.area (FreeGroup.of a * (P.roundTrip Q (FreeGroup.of a))⁻¹)).bddAbove
  have hgen : ∀ x : α × Bool,
      P.area (FreeGroup.mk [x] * (P.roundTrip Q (FreeGroup.mk [x]))⁻¹) ≤ B := by
    rintro ⟨a, b⟩
    cases b
    · rw [mk_singleton_false, map_inv, inv_inv,
        show (FreeGroup.of a)⁻¹ * P.roundTrip Q (FreeGroup.of a)
          = (FreeGroup.of a)⁻¹ * (FreeGroup.of a * (P.roundTrip Q (FreeGroup.of a))⁻¹)⁻¹
              * ((FreeGroup.of a)⁻¹)⁻¹ by group, area_conj, area_inv]
      exact hB (Set.mem_range_self a)
    · rw [mk_singleton_true]
      exact hB (Set.mem_range_self a)
  have step : ∀ s v : FreeGroup α, P.area (s * v * (P.roundTrip Q (s * v))⁻¹)
      ≤ P.area (s * (P.roundTrip Q s)⁻¹) + P.area (v * (P.roundTrip Q v)⁻¹) := by
    intro s v
    rw [show s * v * (P.roundTrip Q (s * v))⁻¹
        = s * (v * (P.roundTrip Q v)⁻¹) * s⁻¹ * (s * (P.roundTrip Q s)⁻¹) by
      rw [map_mul]; group]
    refine (area_mul_le (conj_mem_ker (P.mul_roundTrip_inv_mem_ker Q v) s)
      (P.mul_roundTrip_inv_mem_ker Q s)).trans ?_
    rw [area_conj]
    omega
  have key : ∀ l : List (α × Bool),
      P.area (FreeGroup.mk l * (P.roundTrip Q (FreeGroup.mk l))⁻¹) ≤ B * l.length := by
    intro l
    induction l with
    | nil => simp [mk_nil]
    | cons x l ih =>
      rw [mk_cons]
      calc P.area (FreeGroup.mk [x] * FreeGroup.mk l
            * (P.roundTrip Q (FreeGroup.mk [x] * FreeGroup.mk l))⁻¹)
          ≤ P.area (FreeGroup.mk [x] * (P.roundTrip Q (FreeGroup.mk [x]))⁻¹)
              + P.area (FreeGroup.mk l * (P.roundTrip Q (FreeGroup.mk l))⁻¹) := step _ _
        _ ≤ B + B * l.length := Nat.add_le_add (hgen x) ih
        _ = B * (x :: l).length := by rw [List.length_cons, Nat.mul_succ]; omega
  refine ⟨B, fun w => ?_⟩
  have h := key w.toWord
  rwa [FreeGroup.mk_toWord] at h

/-- **The Dehn function of a finite presentation is bounded by that of any other**, up to the
equivalence of growth types. -/
theorem dehn_growthLE [Finite α] [DecidableEq α] [Finite α'] [DecidableEq α'] [Finite ρ'] :
    Nat.GrowthLE P.dehn Q.dehn := by
  obtain ⟨M, hM⟩ := P.exists_norm_transfer_le Q
  obtain ⟨A, hA⟩ := Q.exists_area_transfer_le P
  obtain ⟨B, hB⟩ := P.exists_area_mul_roundTrip_inv_le Q
  refine ⟨max (max A B) (max M 1), le_max_of_le_right (le_max_right _ _), fun n => ?_⟩
  set C := max (max A B) (max M 1) with hC
  have hAC : A ≤ C := le_max_of_le_left (le_max_left _ _)
  have hBC : B ≤ C := le_max_of_le_left (le_max_right _ _)
  have hMC : M ≤ C := le_max_of_le_right (le_max_left _ _)
  have hbound : P.dehn n ≤ B * n + A * Q.dehn (M * n) := by
    refine dehn_le fun w hw => ?_
    obtain ⟨hwker, hwnorm⟩ := hw
    have hQker : P.transfer Q w ∈ Q.lift.ker := by
      rw [MonoidHom.mem_ker, lift_transfer]
      exact hwker
    calc P.area w
        = P.area (w * (P.roundTrip Q w)⁻¹ * P.roundTrip Q w) := by congr 1; group
      _ ≤ P.area (w * (P.roundTrip Q w)⁻¹) + P.area (P.roundTrip Q w) :=
          area_mul_le (P.mul_roundTrip_inv_mem_ker Q w)
            (by rw [MonoidHom.mem_ker, lift_roundTrip]; exact hwker)
      _ ≤ B * FreeGroup.norm w + A * Q.area (P.transfer Q w) :=
          Nat.add_le_add (hB w) (hA _ hQker)
      _ ≤ B * n + A * Q.dehn (M * n) := by
          refine Nat.add_le_add (Nat.mul_le_mul (le_refl B) hwnorm)
            (Nat.mul_le_mul (le_refl A) ((area_le_dehn hQker).trans (dehn_mono ?_)))
          exact (hM w).trans (Nat.mul_le_mul (le_refl M) hwnorm)
  calc P.dehn n ≤ B * n + A * Q.dehn (M * n) := hbound
    _ ≤ C * n + C * Q.dehn (C * n + C) :=
        Nat.add_le_add (Nat.mul_le_mul hBC (le_refl n))
          (Nat.mul_le_mul hAC (dehn_mono (by
            calc M * n ≤ C * n := Nat.mul_le_mul hMC (le_refl n)
              _ ≤ C * n + C := Nat.le_add_right _ _)))
    _ ≤ C * Q.dehn (C * n + C) + C * n + C := by omega

/-- **The Dehn function does not depend on the finite presentation**: any two finite presentations
of a group have Dehn functions of the same growth type. Hence the growth type of the Dehn function
is an invariant of the finitely presented group, and it is at this granularity that the Dehn
function is a quasi-isometry invariant. -/
theorem dehn_growthEquiv [Finite α] [DecidableEq α] [Finite ρ]
    [Finite α'] [DecidableEq α'] [Finite ρ'] :
    Nat.GrowthEquiv P.dehn Q.dehn :=
  ⟨P.dehn_growthLE Q, Q.dehn_growthLE P⟩

end Transfer

end Group.Presentation
