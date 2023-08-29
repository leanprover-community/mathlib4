/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Analysis.Normed.Field.Basic

#align_import number_theory.padics.padic_numbers from "leanprover-community/mathlib"@"b9b2114f7711fec1c1e055d507f082f8ceb2c3b7"

/-!
# p-adic numbers

This file defines the `p`-adic numbers (rationals) `ℚ_[p]` as
the completion of `ℚ` with respect to the `p`-adic norm.
We show that the `p`-adic norm on `ℚ` extends to `ℚ_[p]`, that `ℚ` is embedded in `ℚ_[p]`,
and that `ℚ_[p]` is Cauchy complete.

## Important definitions

* `Padic` : the type of `p`-adic numbers
* `padicNormE` : the rational valued `p`-adic norm on `ℚ_[p]`
* `Padic.addValuation` : the additive `p`-adic valuation on `ℚ_[p]`, with values in `WithTop ℤ`

## Notation

We introduce the notation `ℚ_[p]` for the `p`-adic numbers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

We use the same concrete Cauchy sequence construction that is used to construct `ℝ`.
`ℚ_[p]` inherits a field structure from this construction.
The extension of the norm on `ℚ` to `ℚ_[p]` is *not* analogous to extending the absolute value to
`ℝ` and hence the proof that `ℚ_[p]` is complete is different from the proof that ℝ is complete.

A small special-purpose simplification tactic, `padic_index_simp`, is used to manipulate sequence
indices in the proof that the norm extends.

`padicNormE` is the rational-valued `p`-adic norm on `ℚ_[p]`.
To instantiate `ℚ_[p]` as a normed field, we must cast this into an `ℝ`-valued norm.
The `ℝ`-valued norm, using notation `‖ ‖` from normed spaces,
is the canonical representation of this norm.

`simp` prefers `padicNorm` to `padicNormE` when possible.
Since `padicNormE` and `‖ ‖` have different types, `simp` does not rewrite one to the other.

Coercions from `ℚ` to `ℚ_[p]` are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation, cauchy, completion, p-adic completion
-/


noncomputable section

open Classical

open Nat multiplicity padicNorm CauSeq CauSeq.Completion Metric

/-- The type of Cauchy sequences of rationals with respect to the `p`-adic norm. -/
@[reducible]
def PadicSeq (p : ℕ) :=
  CauSeq _ (padicNorm p)
#align padic_seq PadicSeq

namespace PadicSeq

section

variable {p : ℕ} [Fact p.Prime]

/-- The `p`-adic norm of the entries of a nonzero Cauchy sequence of rationals is eventually
constant. -/
theorem stationary {f : CauSeq ℚ (padicNorm p)} (hf : ¬f ≈ 0) :
    ∃ N, ∀ m n, N ≤ m → N ≤ n → padicNorm p (f n) = padicNorm p (f m) :=
  have : ∃ ε > 0, ∃ N1, ∀ j ≥ N1, ε ≤ padicNorm p (f j) :=
    CauSeq.abv_pos_of_not_limZero <| not_limZero_of_not_congr_zero hf
  let ⟨ε, hε, N1, hN1⟩ := this
  let ⟨N2, hN2⟩ := CauSeq.cauchy₂ f hε
  ⟨max N1 N2, fun n m hn hm ↦ by
    have : padicNorm p (f n - f m) < ε := hN2 _ (max_le_iff.1 hn).2 _ (max_le_iff.1 hm).2
    -- ⊢ padicNorm p (↑f m) = padicNorm p (↑f n)
    have : padicNorm p (f n - f m) < padicNorm p (f n) :=
      lt_of_lt_of_le this <| hN1 _ (max_le_iff.1 hn).1
    have : padicNorm p (f n - f m) < max (padicNorm p (f n)) (padicNorm p (f m)) :=
      lt_max_iff.2 (Or.inl this)
    by_contra hne
    -- ⊢ False
    rw [← padicNorm.neg (f m)] at hne
    -- ⊢ False
    have hnam := add_eq_max_of_ne hne
    -- ⊢ False
    rw [padicNorm.neg, max_comm] at hnam
    -- ⊢ False
    rw [← hnam, sub_eq_add_neg, add_comm] at this
    -- ⊢ False
    apply _root_.lt_irrefl _ this⟩
    -- 🎉 no goals
#align padic_seq.stationary PadicSeq.stationary

/-- For all `n ≥ stationaryPoint f hf`, the `p`-adic norm of `f n` is the same. -/
def stationaryPoint {f : PadicSeq p} (hf : ¬f ≈ 0) : ℕ :=
  Classical.choose <| stationary hf
#align padic_seq.stationary_point PadicSeq.stationaryPoint

theorem stationaryPoint_spec {f : PadicSeq p} (hf : ¬f ≈ 0) :
    ∀ {m n},
      stationaryPoint hf ≤ m → stationaryPoint hf ≤ n → padicNorm p (f n) = padicNorm p (f m) :=
  @(Classical.choose_spec <| stationary hf)
#align padic_seq.stationary_point_spec PadicSeq.stationaryPoint_spec

/-- Since the norm of the entries of a Cauchy sequence is eventually stationary,
we can lift the norm to sequences. -/
def norm (f : PadicSeq p) : ℚ :=
  if hf : f ≈ 0 then 0 else padicNorm p (f (stationaryPoint hf))
#align padic_seq.norm PadicSeq.norm

theorem norm_zero_iff (f : PadicSeq p) : f.norm = 0 ↔ f ≈ 0 := by
  constructor
  -- ⊢ norm f = 0 → f ≈ 0
  · intro h
    -- ⊢ f ≈ 0
    by_contra hf
    -- ⊢ False
    unfold norm at h
    -- ⊢ False
    split_ifs at h; contradiction
    -- ⊢ False
                    -- ⊢ False
    apply hf
    -- ⊢ f ≈ 0
    intro ε hε
    -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → padicNorm p (↑(f - 0) j) < ε
    exists stationaryPoint hf
    -- ⊢ ∀ (j : ℕ), j ≥ stationaryPoint hf → padicNorm p (↑(f - 0) j) < ε
    intro j hj
    -- ⊢ padicNorm p (↑(f - 0) j) < ε
    have heq := stationaryPoint_spec hf le_rfl hj
    -- ⊢ padicNorm p (↑(f - 0) j) < ε
    simpa [h, heq]
    -- 🎉 no goals
  · intro h
    -- ⊢ norm f = 0
    simp [norm, h]
    -- 🎉 no goals
#align padic_seq.norm_zero_iff PadicSeq.norm_zero_iff

end

section Embedding

open CauSeq

variable {p : ℕ} [Fact p.Prime]

theorem equiv_zero_of_val_eq_of_equiv_zero {f g : PadicSeq p}
    (h : ∀ k, padicNorm p (f k) = padicNorm p (g k)) (hf : f ≈ 0) : g ≈ 0 := fun ε hε ↦
  let ⟨i, hi⟩ := hf _ hε
  ⟨i, fun j hj ↦ by simpa [h] using hi _ hj⟩
                    -- 🎉 no goals
#align padic_seq.equiv_zero_of_val_eq_of_equiv_zero PadicSeq.equiv_zero_of_val_eq_of_equiv_zero

theorem norm_nonzero_of_not_equiv_zero {f : PadicSeq p} (hf : ¬f ≈ 0) : f.norm ≠ 0 :=
  hf ∘ f.norm_zero_iff.1
#align padic_seq.norm_nonzero_of_not_equiv_zero PadicSeq.norm_nonzero_of_not_equiv_zero

theorem norm_eq_norm_app_of_nonzero {f : PadicSeq p} (hf : ¬f ≈ 0) :
    ∃ k, f.norm = padicNorm p k ∧ k ≠ 0 :=
  have heq : f.norm = padicNorm p (f <| stationaryPoint hf) := by simp [norm, hf]
                                                                  -- 🎉 no goals
  ⟨f <| stationaryPoint hf, heq, fun h ↦
    norm_nonzero_of_not_equiv_zero hf (by simpa [h] using heq)⟩
                                          -- 🎉 no goals
#align padic_seq.norm_eq_norm_app_of_nonzero PadicSeq.norm_eq_norm_app_of_nonzero

theorem not_limZero_const_of_nonzero {q : ℚ} (hq : q ≠ 0) : ¬LimZero (const (padicNorm p) q) :=
  fun h' ↦ hq <| const_limZero.1 h'
#align padic_seq.not_lim_zero_const_of_nonzero PadicSeq.not_limZero_const_of_nonzero

theorem not_equiv_zero_const_of_nonzero {q : ℚ} (hq : q ≠ 0) : ¬const (padicNorm p) q ≈ 0 :=
  fun h : LimZero (const (padicNorm p) q - 0) ↦ not_limZero_const_of_nonzero hq <| by simpa using h
                                                                                      -- 🎉 no goals
#align padic_seq.not_equiv_zero_const_of_nonzero PadicSeq.not_equiv_zero_const_of_nonzero

theorem norm_nonneg (f : PadicSeq p) : 0 ≤ f.norm :=
  if hf : f ≈ 0 then by simp [hf, norm] else by simp [norm, hf, padicNorm.nonneg]
                        -- 🎉 no goals
                                                -- 🎉 no goals
#align padic_seq.norm_nonneg PadicSeq.norm_nonneg

/-- An auxiliary lemma for manipulating sequence indices. -/
theorem lift_index_left_left {f : PadicSeq p} (hf : ¬f ≈ 0) (v2 v3 : ℕ) :
    padicNorm p (f (stationaryPoint hf)) =
    padicNorm p (f (max (stationaryPoint hf) (max v2 v3))) := by
  apply stationaryPoint_spec hf
  -- ⊢ stationaryPoint hf ≤ max (stationaryPoint hf) (max v2 v3)
  · apply le_max_left
    -- 🎉 no goals
  · exact le_rfl
    -- 🎉 no goals
#align padic_seq.lift_index_left_left PadicSeq.lift_index_left_left

/-- An auxiliary lemma for manipulating sequence indices. -/
theorem lift_index_left {f : PadicSeq p} (hf : ¬f ≈ 0) (v1 v3 : ℕ) :
    padicNorm p (f (stationaryPoint hf)) =
    padicNorm p (f (max v1 (max (stationaryPoint hf) v3))) := by
  apply stationaryPoint_spec hf
  -- ⊢ stationaryPoint hf ≤ max v1 (max (stationaryPoint hf) v3)
  · apply le_trans
    · apply le_max_left _ v3
      -- 🎉 no goals
    · apply le_max_right
      -- 🎉 no goals
  · exact le_rfl
    -- 🎉 no goals
#align padic_seq.lift_index_left PadicSeq.lift_index_left

/-- An auxiliary lemma for manipulating sequence indices. -/
theorem lift_index_right {f : PadicSeq p} (hf : ¬f ≈ 0) (v1 v2 : ℕ) :
    padicNorm p (f (stationaryPoint hf)) =
    padicNorm p (f (max v1 (max v2 (stationaryPoint hf)))) := by
  apply stationaryPoint_spec hf
  -- ⊢ stationaryPoint hf ≤ max v1 (max v2 (stationaryPoint hf))
  · apply le_trans
    · apply le_max_right v2
      -- 🎉 no goals
    · apply le_max_right
      -- 🎉 no goals
  · exact le_rfl
    -- 🎉 no goals
#align padic_seq.lift_index_right PadicSeq.lift_index_right

end Embedding

section Valuation

open CauSeq

variable {p : ℕ} [Fact p.Prime]

/-! ### Valuation on `PadicSeq` -/


/-- The `p`-adic valuation on `ℚ` lifts to `PadicSeq p`.
`Valuation f` is defined to be the valuation of the (`ℚ`-valued) stationary point of `f`. -/
def valuation (f : PadicSeq p) : ℤ :=
  if hf : f ≈ 0 then 0 else padicValRat p (f (stationaryPoint hf))
#align padic_seq.valuation PadicSeq.valuation

theorem norm_eq_pow_val {f : PadicSeq p} (hf : ¬f ≈ 0) : f.norm = (p : ℚ) ^ (-f.valuation : ℤ) := by
  rw [norm, valuation, dif_neg hf, dif_neg hf, padicNorm, if_neg]
  -- ⊢ ¬↑f (stationaryPoint hf) = 0
  intro H
  -- ⊢ False
  apply CauSeq.not_limZero_of_not_congr_zero hf
  -- ⊢ LimZero f
  intro ε hε
  -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → padicNorm p (↑f j) < ε
  use stationaryPoint hf
  -- ⊢ ∀ (j : ℕ), j ≥ stationaryPoint hf → padicNorm p (↑f j) < ε
  intro n hn
  -- ⊢ padicNorm p (↑f n) < ε
  rw [stationaryPoint_spec hf le_rfl hn]
  -- ⊢ padicNorm p (↑f (stationaryPoint hf)) < ε
  simpa [H] using hε
  -- 🎉 no goals
#align padic_seq.norm_eq_pow_val PadicSeq.norm_eq_pow_val

theorem val_eq_iff_norm_eq {f g : PadicSeq p} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) :
    f.valuation = g.valuation ↔ f.norm = g.norm := by
  rw [norm_eq_pow_val hf, norm_eq_pow_val hg, ← neg_inj, zpow_inj]
  -- ⊢ 0 < ↑p
  · exact_mod_cast (Fact.out : p.Prime).pos
    -- 🎉 no goals
  · exact_mod_cast (Fact.out : p.Prime).ne_one
    -- 🎉 no goals
#align padic_seq.val_eq_iff_norm_eq PadicSeq.val_eq_iff_norm_eq

end Valuation

end PadicSeq

section

open PadicSeq

-- Porting note: Commented out `padic_index_simp` tactic
/-
private unsafe def index_simp_core (hh hf hg : expr)
    (at_ : Interactive.Loc := Interactive.Loc.ns [none]) : tactic Unit := do
  let [v1, v2, v3] ← [hh, hf, hg].mapM fun n => tactic.mk_app `` stationary_point [n] <|> return n
  let e1 ← tactic.mk_app `` lift_index_left_left [hh, v2, v3] <|> return q(True)
  let e2 ← tactic.mk_app `` lift_index_left [hf, v1, v3] <|> return q(True)
  let e3 ← tactic.mk_app `` lift_index_right [hg, v1, v2] <|> return q(True)
  let sl ← [e1, e2, e3].foldlM (fun s e => simp_lemmas.add s e) simp_lemmas.mk
  when at_ (tactic.simp_target sl >> tactic.skip)
  let hs ← at_.get_locals
  hs (tactic.simp_hyp sl [])
#align index_simp_core index_simp_core

/-- This is a special-purpose tactic that lifts `padicNorm (f (stationary_point f))` to
`padicNorm (f (max _ _ _))`. -/
unsafe def tactic.interactive.padic_index_simp (l : interactive.parse interactive.types.pexpr_list)
    (at_ : interactive.parse interactive.types.location) : tactic Unit := do
  let [h, f, g] ← l.mapM tactic.i_to_expr
  index_simp_core h f g at_
#align tactic.interactive.padic_index_simp tactic.interactive.padic_index_simp
-/

end

namespace PadicSeq

section Embedding

open CauSeq

variable {p : ℕ} [hp : Fact p.Prime]

theorem norm_mul (f g : PadicSeq p) : (f * g).norm = f.norm * g.norm :=
  if hf : f ≈ 0 then by
    have hg : f * g ≈ 0 := mul_equiv_zero' _ hf
    -- ⊢ norm (f * g) = norm f * norm g
    simp only [hf, hg, norm, dif_pos, zero_mul]
    -- 🎉 no goals
  else
    if hg : g ≈ 0 then by
      have hf : f * g ≈ 0 := mul_equiv_zero _ hg
      -- ⊢ norm (f * g) = norm f * norm g
      simp only [hf, hg, norm, dif_pos, mul_zero]
      -- 🎉 no goals
    else by
      unfold norm
      -- ⊢ (if hf : f * g ≈ 0 then 0 else padicNorm p (↑(f * g) (stationaryPoint hf)))  …
      split_ifs with hfg
      -- ⊢ 0 = padicNorm p (↑f (stationaryPoint hf)) * padicNorm p (↑g (stationaryPoint …
      exact (mul_not_equiv_zero hf hg hfg).elim
      -- ⊢ padicNorm p (↑(f * g) (stationaryPoint hfg)) = padicNorm p (↑f (stationaryPo …
      -- Porting note: originally `padic_index_simp [hfg, hf, hg]`
      rw [lift_index_left_left hfg, lift_index_left hf, lift_index_right hg]
      apply padicNorm.mul
      -- 🎉 no goals
#align padic_seq.norm_mul PadicSeq.norm_mul

theorem eq_zero_iff_equiv_zero (f : PadicSeq p) : mk f = 0 ↔ f ≈ 0 :=
  mk_eq
#align padic_seq.eq_zero_iff_equiv_zero PadicSeq.eq_zero_iff_equiv_zero

theorem ne_zero_iff_nequiv_zero (f : PadicSeq p) : mk f ≠ 0 ↔ ¬f ≈ 0 :=
  not_iff_not.2 (eq_zero_iff_equiv_zero _)
#align padic_seq.ne_zero_iff_nequiv_zero PadicSeq.ne_zero_iff_nequiv_zero

theorem norm_const (q : ℚ) : norm (const (padicNorm p) q) = padicNorm p q :=
  if hq : q = 0 then by
    have : const (padicNorm p) q ≈ 0 := by simp [hq]; apply Setoid.refl (const (padicNorm p) 0)
    -- ⊢ norm (const (padicNorm p) q) = padicNorm p q
    subst hq; simp [norm, this]
    -- ⊢ norm (const (padicNorm p) 0) = padicNorm p 0
              -- 🎉 no goals
  else by
    have : ¬const (padicNorm p) q ≈ 0 := not_equiv_zero_const_of_nonzero hq
    -- ⊢ norm (const (padicNorm p) q) = padicNorm p q
    simp [norm, this]
    -- 🎉 no goals
#align padic_seq.norm_const PadicSeq.norm_const

theorem norm_values_discrete (a : PadicSeq p) (ha : ¬a ≈ 0) : ∃ z : ℤ, a.norm = (p : ℚ) ^ (-z) := by
  let ⟨k, hk, hk'⟩ := norm_eq_norm_app_of_nonzero ha
  -- ⊢ ∃ z, norm a = ↑p ^ (-z)
  simpa [hk] using padicNorm.values_discrete hk'
  -- 🎉 no goals
#align padic_seq.norm_values_discrete PadicSeq.norm_values_discrete

theorem norm_one : norm (1 : PadicSeq p) = 1 := by
  have h1 : ¬(1 : PadicSeq p) ≈ 0 := one_not_equiv_zero _
  -- ⊢ norm 1 = 1
  simp [h1, norm, hp.1.one_lt]
  -- 🎉 no goals
#align padic_seq.norm_one PadicSeq.norm_one

private theorem norm_eq_of_equiv_aux {f g : PadicSeq p} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) (hfg : f ≈ g)
    (h : padicNorm p (f (stationaryPoint hf)) ≠ padicNorm p (g (stationaryPoint hg)))
    (hlt : padicNorm p (g (stationaryPoint hg)) < padicNorm p (f (stationaryPoint hf))) :
    False := by
  have hpn : 0 < padicNorm p (f (stationaryPoint hf)) - padicNorm p (g (stationaryPoint hg)) :=
    sub_pos_of_lt hlt
  cases' hfg _ hpn with N hN
  -- ⊢ False
  let i := max N (max (stationaryPoint hf) (stationaryPoint hg))
  -- ⊢ False
  have hi : N ≤ i := le_max_left _ _
  -- ⊢ False
  have hN' := hN _ hi
  -- ⊢ False
  -- Porting note: originally `padic_index_simp [N, hf, hg] at hN' h hlt`
  rw [lift_index_left hf N (stationaryPoint hg), lift_index_right hg N (stationaryPoint hf)]
    at hN' h hlt
  have hpne : padicNorm p (f i) ≠ padicNorm p (-g i) := by rwa [← padicNorm.neg (g i)] at h
  -- ⊢ False
  rw [CauSeq.sub_apply, sub_eq_add_neg, add_eq_max_of_ne hpne, padicNorm.neg, max_eq_left_of_lt hlt]
    at hN'
  have : padicNorm p (f i) < padicNorm p (f i) := by
    apply lt_of_lt_of_le hN'
    apply sub_le_self
    apply padicNorm.nonneg
  exact lt_irrefl _ this
  -- 🎉 no goals

private theorem norm_eq_of_equiv {f g : PadicSeq p} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) (hfg : f ≈ g) :
    padicNorm p (f (stationaryPoint hf)) = padicNorm p (g (stationaryPoint hg)) := by
  by_contra h
  -- ⊢ False
  cases'
    Decidable.em
      (padicNorm p (g (stationaryPoint hg)) < padicNorm p (f (stationaryPoint hf))) with
    hlt hnlt
  · exact norm_eq_of_equiv_aux hf hg hfg h hlt
    -- 🎉 no goals
  · apply norm_eq_of_equiv_aux hg hf (Setoid.symm hfg) (Ne.symm h)
    -- ⊢ padicNorm p (↑f (stationaryPoint hf)) < padicNorm p (↑g (stationaryPoint hg))
    apply lt_of_le_of_ne
    -- ⊢ padicNorm p (↑f (stationaryPoint hf)) ≤ padicNorm p (↑g (stationaryPoint hg))
    apply le_of_not_gt hnlt
    -- ⊢ padicNorm p (↑f (stationaryPoint hf)) ≠ padicNorm p (↑g (stationaryPoint hg))
    apply h
    -- 🎉 no goals

theorem norm_equiv {f g : PadicSeq p} (hfg : f ≈ g) : f.norm = g.norm :=
  if hf : f ≈ 0 then by
    have hg : g ≈ 0 := Setoid.trans (Setoid.symm hfg) hf
    -- ⊢ norm f = norm g
    simp [norm, hf, hg]
    -- 🎉 no goals
  else by
    have hg : ¬g ≈ 0 := hf ∘ Setoid.trans hfg
    -- ⊢ norm f = norm g
    unfold norm; split_ifs; exact norm_eq_of_equiv hf hg hfg
    -- ⊢ (if hf : f ≈ 0 then 0 else padicNorm p (↑f (stationaryPoint hf))) = if hf :  …
                 -- ⊢ padicNorm p (↑f (stationaryPoint hf)) = padicNorm p (↑g (stationaryPoint hg))
                            -- 🎉 no goals
#align padic_seq.norm_equiv PadicSeq.norm_equiv

private theorem norm_nonarchimedean_aux {f g : PadicSeq p} (hfg : ¬f + g ≈ 0) (hf : ¬f ≈ 0)
    (hg : ¬g ≈ 0) : (f + g).norm ≤ max f.norm g.norm := by
  unfold norm; split_ifs
  -- ⊢ (if hf : f + g ≈ 0 then 0 else padicNorm p (↑(f + g) (stationaryPoint hf)))  …
               -- ⊢ padicNorm p (↑(f + g) (stationaryPoint hfg)) ≤ max (padicNorm p (↑f (station …
  -- Porting note: originally `padic_index_simp [hfg, hf, hg]`
  rw [lift_index_left_left hfg, lift_index_left hf, lift_index_right hg]
  apply padicNorm.nonarchimedean
  -- 🎉 no goals

theorem norm_nonarchimedean (f g : PadicSeq p) : (f + g).norm ≤ max f.norm g.norm :=
  if hfg : f + g ≈ 0 then by
    have : 0 ≤ max f.norm g.norm := le_max_of_le_left (norm_nonneg _)
    -- ⊢ norm (f + g) ≤ max (norm f) (norm g)
    simpa only [hfg, norm]
    -- 🎉 no goals
  else
    if hf : f ≈ 0 then by
      have hfg' : f + g ≈ g := by
        change LimZero (f - 0) at hf
        show LimZero (f + g - g); · simpa only [sub_zero, add_sub_cancel] using hf
      have hcfg : (f + g).norm = g.norm := norm_equiv hfg'
      -- ⊢ norm (f + g) ≤ max (norm f) (norm g)
      have hcl : f.norm = 0 := (norm_zero_iff f).2 hf
      -- ⊢ norm (f + g) ≤ max (norm f) (norm g)
      have : max f.norm g.norm = g.norm := by rw [hcl]; exact max_eq_right (norm_nonneg _)
      -- ⊢ norm (f + g) ≤ max (norm f) (norm g)
      rw [this, hcfg]
      -- 🎉 no goals
    else
      if hg : g ≈ 0 then by
        have hfg' : f + g ≈ f := by
          change LimZero (g - 0) at hg
          show LimZero (f + g - f); · simpa only [add_sub_cancel', sub_zero] using hg
        have hcfg : (f + g).norm = f.norm := norm_equiv hfg'
        -- ⊢ norm (f + g) ≤ max (norm f) (norm g)
        have hcl : g.norm = 0 := (norm_zero_iff g).2 hg
        -- ⊢ norm (f + g) ≤ max (norm f) (norm g)
        have : max f.norm g.norm = f.norm := by rw [hcl]; exact max_eq_left (norm_nonneg _)
        -- ⊢ norm (f + g) ≤ max (norm f) (norm g)
        rw [this, hcfg]
        -- 🎉 no goals
      else norm_nonarchimedean_aux hfg hf hg
#align padic_seq.norm_nonarchimedean PadicSeq.norm_nonarchimedean

theorem norm_eq {f g : PadicSeq p} (h : ∀ k, padicNorm p (f k) = padicNorm p (g k)) :
    f.norm = g.norm :=
  if hf : f ≈ 0 then by
    have hg : g ≈ 0 := equiv_zero_of_val_eq_of_equiv_zero h hf
    -- ⊢ norm f = norm g
    simp only [hf, hg, norm, dif_pos]
    -- 🎉 no goals
  else by
    have hg : ¬g ≈ 0 := fun hg ↦
      hf <| equiv_zero_of_val_eq_of_equiv_zero (by simp only [h, forall_const, eq_self_iff_true]) hg
    simp only [hg, hf, norm, dif_neg, not_false_iff]
    -- ⊢ padicNorm p (↑f (stationaryPoint (_ : ¬f ≈ 0))) = padicNorm p (↑g (stationar …
    let i := max (stationaryPoint hf) (stationaryPoint hg)
    -- ⊢ padicNorm p (↑f (stationaryPoint (_ : ¬f ≈ 0))) = padicNorm p (↑g (stationar …
    have hpf : padicNorm p (f (stationaryPoint hf)) = padicNorm p (f i) := by
      apply stationaryPoint_spec
      apply le_max_left
      exact le_rfl
    have hpg : padicNorm p (g (stationaryPoint hg)) = padicNorm p (g i) := by
      apply stationaryPoint_spec
      apply le_max_right
      exact le_rfl
    rw [hpf, hpg, h]
    -- 🎉 no goals
#align padic_seq.norm_eq PadicSeq.norm_eq

theorem norm_neg (a : PadicSeq p) : (-a).norm = a.norm :=
  norm_eq <| by simp
                -- 🎉 no goals
#align padic_seq.norm_neg PadicSeq.norm_neg

theorem norm_eq_of_add_equiv_zero {f g : PadicSeq p} (h : f + g ≈ 0) : f.norm = g.norm := by
  have : LimZero (f + g - 0) := h
  -- ⊢ norm f = norm g
  have : f ≈ -g := show LimZero (f - -g) by simpa only [sub_zero, sub_neg_eq_add]
  -- ⊢ norm f = norm g
  have : f.norm = (-g).norm := norm_equiv this
  -- ⊢ norm f = norm g
  simpa only [norm_neg] using this
  -- 🎉 no goals
#align padic_seq.norm_eq_of_add_equiv_zero PadicSeq.norm_eq_of_add_equiv_zero

theorem add_eq_max_of_ne {f g : PadicSeq p} (hfgne : f.norm ≠ g.norm) :
    (f + g).norm = max f.norm g.norm :=
  have hfg : ¬f + g ≈ 0 := mt norm_eq_of_add_equiv_zero hfgne
  if hf : f ≈ 0 then by
    have : LimZero (f - 0) := hf
    -- ⊢ norm (f + g) = max (norm f) (norm g)
    have : f + g ≈ g := show LimZero (f + g - g) by simpa only [sub_zero, add_sub_cancel]
    -- ⊢ norm (f + g) = max (norm f) (norm g)
    have h1 : (f + g).norm = g.norm := norm_equiv this
    -- ⊢ norm (f + g) = max (norm f) (norm g)
    have h2 : f.norm = 0 := (norm_zero_iff _).2 hf
    -- ⊢ norm (f + g) = max (norm f) (norm g)
    rw [h1, h2, max_eq_right (norm_nonneg _)]
    -- 🎉 no goals
  else
    if hg : g ≈ 0 then by
      have : LimZero (g - 0) := hg
      -- ⊢ norm (f + g) = max (norm f) (norm g)
      have : f + g ≈ f := show LimZero (f + g - f) by rw [add_sub_cancel']; simpa only [sub_zero]
      -- ⊢ norm (f + g) = max (norm f) (norm g)
      have h1 : (f + g).norm = f.norm := norm_equiv this
      -- ⊢ norm (f + g) = max (norm f) (norm g)
      have h2 : g.norm = 0 := (norm_zero_iff _).2 hg
      -- ⊢ norm (f + g) = max (norm f) (norm g)
      rw [h1, h2, max_eq_left (norm_nonneg _)]
      -- 🎉 no goals
    else by
      unfold norm at hfgne ⊢; split_ifs at hfgne ⊢
      -- ⊢ (if hf : f + g ≈ 0 then 0 else padicNorm p (↑(f + g) (stationaryPoint hf)))  …
                              -- ⊢ padicNorm p (↑(f + g) (stationaryPoint hfg)) = max (padicNorm p (↑f (station …
      -- Porting note: originally `padic_index_simp [hfg, hf, hg] at hfgne ⊢`
      rw [lift_index_left hf, lift_index_right hg] at hfgne
      rw [lift_index_left_left hfg, lift_index_left hf, lift_index_right hg]
      exact padicNorm.add_eq_max_of_ne hfgne
      -- 🎉 no goals
#align padic_seq.add_eq_max_of_ne PadicSeq.add_eq_max_of_ne

end Embedding

end PadicSeq

/-- The `p`-adic numbers `ℚ_[p]` are the Cauchy completion of `ℚ` with respect to the `p`-adic norm.
-/
def Padic (p : ℕ) [Fact p.Prime] :=
  CauSeq.Completion.Cauchy (padicNorm p)
#align padic Padic

-- mathport name: «exprℚ_[ ]»
/-- notation for p-padic rationals -/
notation "ℚ_[" p "]" => Padic p

namespace Padic

section Completion

variable {p : ℕ} [Fact p.Prime]

instance field : Field ℚ_[p] :=
  Cauchy.field

instance : Inhabited ℚ_[p] :=
  ⟨0⟩

-- short circuits
instance : CommRing ℚ_[p] :=
  Cauchy.commRing

instance : Ring ℚ_[p] :=
  Cauchy.ring

instance : Zero ℚ_[p] := by infer_instance
                            -- 🎉 no goals

instance : One ℚ_[p] := by infer_instance
                           -- 🎉 no goals

instance : Add ℚ_[p] := by infer_instance
                           -- 🎉 no goals

instance : Mul ℚ_[p] := by infer_instance
                           -- 🎉 no goals

instance : Sub ℚ_[p] := by infer_instance
                           -- 🎉 no goals

instance : Neg ℚ_[p] := by infer_instance
                           -- 🎉 no goals

instance : Div ℚ_[p] := by infer_instance
                           -- 🎉 no goals

instance : AddCommGroup ℚ_[p] := by infer_instance
                                    -- 🎉 no goals

/-- Builds the equivalence class of a Cauchy sequence of rationals. -/
def mk : PadicSeq p → ℚ_[p] :=
  Quotient.mk'
#align padic.mk Padic.mk

variable (p)

theorem zero_def : (0 : ℚ_[p]) = ⟦0⟧ := rfl
#align padic.zero_def Padic.zero_def

theorem mk_eq {f g : PadicSeq p} : mk f = mk g ↔ f ≈ g :=
  Quotient.eq'
#align padic.mk_eq Padic.mk_eq

theorem const_equiv {q r : ℚ} : const (padicNorm p) q ≈ const (padicNorm p) r ↔ q = r :=
  ⟨fun heq ↦ eq_of_sub_eq_zero <| const_limZero.1 heq, fun heq ↦ by
    rw [heq]⟩
    -- 🎉 no goals
#align padic.const_equiv Padic.const_equiv

@[norm_cast]
theorem coe_inj {q r : ℚ} : (↑q : ℚ_[p]) = ↑r ↔ q = r :=
  ⟨(const_equiv p).1 ∘ Quotient.eq'.1, fun h ↦ by rw [h]⟩
                                                  -- 🎉 no goals
#align padic.coe_inj Padic.coe_inj

instance : CharZero ℚ_[p] :=
  ⟨fun m n ↦ by
    rw [← Rat.cast_coe_nat]
    -- ⊢ ↑↑m = ↑n → m = n
    norm_cast
    -- ⊢ m = n → m = n
    exact id⟩
    -- 🎉 no goals

@[norm_cast]
theorem coe_add : ∀ {x y : ℚ}, (↑(x + y) : ℚ_[p]) = ↑x + ↑y :=
  Rat.cast_add _ _
#align padic.coe_add Padic.coe_add

@[norm_cast]
theorem coe_neg : ∀ {x : ℚ}, (↑(-x) : ℚ_[p]) = -↑x :=
  Rat.cast_neg _
#align padic.coe_neg Padic.coe_neg

@[norm_cast]
theorem coe_mul : ∀ {x y : ℚ}, (↑(x * y) : ℚ_[p]) = ↑x * ↑y :=
  Rat.cast_mul _ _
#align padic.coe_mul Padic.coe_mul

@[norm_cast]
theorem coe_sub : ∀ {x y : ℚ}, (↑(x - y) : ℚ_[p]) = ↑x - ↑y :=
  Rat.cast_sub _ _
#align padic.coe_sub Padic.coe_sub

@[norm_cast]
theorem coe_div : ∀ {x y : ℚ}, (↑(x / y) : ℚ_[p]) = ↑x / ↑y :=
  Rat.cast_div _ _
#align padic.coe_div Padic.coe_div

@[norm_cast]
theorem coe_one : (↑(1 : ℚ) : ℚ_[p]) = 1 := rfl
#align padic.coe_one Padic.coe_one

@[norm_cast]
theorem coe_zero : (↑(0 : ℚ) : ℚ_[p]) = 0 := rfl
#align padic.coe_zero Padic.coe_zero

end Completion

end Padic

/-- The rational-valued `p`-adic norm on `ℚ_[p]` is lifted from the norm on Cauchy sequences. The
canonical form of this function is the normed space instance, with notation `‖ ‖`. -/
def padicNormE {p : ℕ} [hp : Fact p.Prime] : AbsoluteValue ℚ_[p] ℚ where
  toFun := Quotient.lift PadicSeq.norm <| @PadicSeq.norm_equiv _ _
  map_mul' q r := Quotient.inductionOn₂ q r <| PadicSeq.norm_mul
  nonneg' q := Quotient.inductionOn q <| PadicSeq.norm_nonneg
  eq_zero' q := Quotient.inductionOn q <| fun r ↦ by
    rw [Padic.zero_def, Quotient.eq]
    -- ⊢ MulHom.toFun { toFun := Quotient.lift PadicSeq.norm (_ : ∀ {f g : PadicSeq p …
    exact PadicSeq.norm_zero_iff r
    -- 🎉 no goals
  add_le' q r := by
    trans
      max ((Quotient.lift PadicSeq.norm <| @PadicSeq.norm_equiv _ _) q)
        ((Quotient.lift PadicSeq.norm <| @PadicSeq.norm_equiv _ _) r)
    exact Quotient.inductionOn₂ q r <| PadicSeq.norm_nonarchimedean
    -- ⊢ max (Quotient.lift PadicSeq.norm (_ : ∀ {f g : PadicSeq p}, f ≈ g → PadicSeq …
    refine' max_le_add_of_nonneg (Quotient.inductionOn q <| PadicSeq.norm_nonneg) _
    -- ⊢ 0 ≤ Quotient.lift PadicSeq.norm (_ : ∀ {f g : PadicSeq p}, f ≈ g → PadicSeq. …
    exact Quotient.inductionOn r <| PadicSeq.norm_nonneg
    -- 🎉 no goals
#align padic_norm_e padicNormE

namespace padicNormE

section Embedding

open PadicSeq

variable {p : ℕ} [Fact p.Prime]

-- Porting note: Expanded `⟦f⟧` to `Padic.mk f`
theorem defn (f : PadicSeq p) {ε : ℚ} (hε : 0 < ε) :
    ∃ N, ∀ i ≥ N, padicNormE (Padic.mk f - f i : ℚ_[p]) < ε := by
  dsimp [padicNormE]
  -- ⊢ ∃ N, ∀ (i : ℕ), i ≥ N → Quotient.lift PadicSeq.norm (_ : ∀ {f g : PadicSeq p …
  change ∃ N, ∀ i ≥ N, (f - const _ (f i)).norm < ε
  -- ⊢ ∃ N, ∀ (i : ℕ), i ≥ N → PadicSeq.norm (f - const (padicNorm p) (↑f i)) < ε
  by_contra' h
  -- ⊢ False
  cases' cauchy₂ f hε with N hN
  -- ⊢ False
  rcases h N with ⟨i, hi, hge⟩
  -- ⊢ False
  have hne : ¬f - const (padicNorm p) (f i) ≈ 0 := by
    intro h
    unfold PadicSeq.norm at hge; split_ifs at hge
    exact not_lt_of_ge hge hε
  unfold PadicSeq.norm at hge; split_ifs at hge; exact not_le_of_gt hε hge
  -- ⊢ False
                               -- ⊢ False
                                                 -- ⊢ False
  apply not_le_of_gt _ hge
  -- ⊢ ε > padicNorm p (↑(f - const (padicNorm p) (↑f i)) (stationaryPoint h✝))
  cases' _root_.em (N ≤ stationaryPoint hne) with hgen hngen
  -- ⊢ ε > padicNorm p (↑(f - const (padicNorm p) (↑f i)) (stationaryPoint h✝))
  · apply hN _ hgen _ hi
    -- 🎉 no goals
  · have := stationaryPoint_spec hne le_rfl (le_of_not_le hngen)
    -- ⊢ ε > padicNorm p (↑(f - const (padicNorm p) (↑f i)) (stationaryPoint h✝))
    rw [← this]
    -- ⊢ ε > padicNorm p (↑(f - const (padicNorm p) (↑f i)) N)
    exact hN _ le_rfl _ hi
    -- 🎉 no goals
#align padic_norm_e.defn padicNormE.defn

/-- Theorems about `padicNormE` are named with a `'` so the names do not conflict with the
equivalent theorems about `norm` (`‖ ‖`). -/
theorem nonarchimedean' (q r : ℚ_[p]) :
    padicNormE (q + r : ℚ_[p]) ≤ max (padicNormE q) (padicNormE r) :=
  Quotient.inductionOn₂ q r <| norm_nonarchimedean
#align padic_norm_e.nonarchimedean' padicNormE.nonarchimedean'

/-- Theorems about `padicNormE` are named with a `'` so the names do not conflict with the
equivalent theorems about `norm` (`‖ ‖`). -/
theorem add_eq_max_of_ne' {q r : ℚ_[p]} :
    padicNormE q ≠ padicNormE r → padicNormE (q + r : ℚ_[p]) = max (padicNormE q) (padicNormE r) :=
  Quotient.inductionOn₂ q r fun _ _ ↦ PadicSeq.add_eq_max_of_ne
#align padic_norm_e.add_eq_max_of_ne' padicNormE.add_eq_max_of_ne'

@[simp]
theorem eq_padic_norm' (q : ℚ) : padicNormE (q : ℚ_[p]) = padicNorm p q :=
  norm_const _
#align padic_norm_e.eq_padic_norm' padicNormE.eq_padic_norm'

protected theorem image' {q : ℚ_[p]} : q ≠ 0 → ∃ n : ℤ, padicNormE q = (p : ℚ) ^ (-n) :=
  Quotient.inductionOn q fun f hf ↦
    have : ¬f ≈ 0 := (ne_zero_iff_nequiv_zero f).1 hf
    norm_values_discrete f this
#align padic_norm_e.image' padicNormE.image'

end Embedding

end padicNormE

namespace Padic

section Complete

open PadicSeq Padic

variable {p : ℕ} [Fact p.Prime] (f : CauSeq _ (@padicNormE p _))

theorem rat_dense' (q : ℚ_[p]) {ε : ℚ} (hε : 0 < ε) : ∃ r : ℚ, padicNormE (q - r : ℚ_[p]) < ε :=
  Quotient.inductionOn q fun q' ↦
    have : ∃ N, ∀ (m) (_ : m ≥ N) (n) (_ : n ≥ N), padicNorm p (q' m - q' n) < ε := cauchy₂ _ hε
    let ⟨N, hN⟩ := this
    ⟨q' N, by
      dsimp [padicNormE]
      -- ⊢ Quotient.lift PadicSeq.norm (_ : ∀ {f g : PadicSeq p}, f ≈ g → PadicSeq.norm …
      -- Porting note: `change` → `convert_to` (`change` times out!)
      -- and add `PadicSeq p` type annotation
      convert_to PadicSeq.norm (q' - const _ (q' N) : PadicSeq p) < ε
      -- ⊢ PadicSeq.norm (q' - const (padicNorm p) (↑q' N)) < ε
      cases' Decidable.em (q' - const (padicNorm p) (q' N) ≈ 0) with heq hne'
      -- ⊢ PadicSeq.norm (q' - const (padicNorm p) (↑q' N)) < ε
      · simpa only [heq, PadicSeq.norm, dif_pos]
        -- 🎉 no goals
      · simp only [PadicSeq.norm, dif_neg hne']
        -- ⊢ padicNorm p (↑(q' - const (padicNorm p) (↑q' N)) (stationaryPoint hne')) < ε
        change padicNorm p (q' _ - q' _) < ε
        -- ⊢ padicNorm p (↑q' (stationaryPoint hne') - ↑q' N) < ε
        cases' Decidable.em (stationaryPoint hne' ≤ N) with hle hle
        -- ⊢ padicNorm p (↑q' (stationaryPoint hne') - ↑q' N) < ε
        · -- Porting note: inlined `stationaryPoint_spec` invocation.
          have := (stationaryPoint_spec hne' le_rfl hle).symm
          -- ⊢ padicNorm p (↑q' (stationaryPoint hne') - ↑q' N) < ε
          simp only [const_apply, sub_apply, padicNorm.zero, sub_self] at this
          -- ⊢ padicNorm p (↑q' (stationaryPoint hne') - ↑q' N) < ε
          simpa only [this]
          -- 🎉 no goals
        · exact hN _ (lt_of_not_ge hle).le _ le_rfl⟩
          -- 🎉 no goals
#align padic.rat_dense' Padic.rat_dense'

open Classical

private theorem div_nat_pos (n : ℕ) : 0 < 1 / (n + 1 : ℚ) :=
  div_pos zero_lt_one (by exact_mod_cast succ_pos _)
                          -- 🎉 no goals

/-- `limSeq f`, for `f` a Cauchy sequence of `p`-adic numbers, is a sequence of rationals with the
same limit point as `f`. -/
def limSeq : ℕ → ℚ :=
  fun n ↦ Classical.choose (rat_dense' (f n) (div_nat_pos n))
#align padic.lim_seq Padic.limSeq

theorem exi_rat_seq_conv {ε : ℚ} (hε : 0 < ε) :
    ∃ N, ∀ i ≥ N, padicNormE (f i - (limSeq f i : ℚ_[p]) : ℚ_[p]) < ε := by
  refine' (exists_nat_gt (1 / ε)).imp fun N hN i hi ↦ _
  -- ⊢ ↑padicNormE (↑f i - ↑(limSeq f i)) < ε
  have h := Classical.choose_spec (rat_dense' (f i) (div_nat_pos i))
  -- ⊢ ↑padicNormE (↑f i - ↑(limSeq f i)) < ε
  refine' lt_of_lt_of_le h ((div_le_iff' <| by exact_mod_cast succ_pos _).mpr _)
  -- ⊢ 1 ≤ (↑i + 1) * ε
  rw [right_distrib]
  -- ⊢ 1 ≤ ↑i * ε + 1 * ε
  apply le_add_of_le_of_nonneg
  -- ⊢ 1 ≤ ↑i * ε
  · exact (div_le_iff hε).mp (le_trans (le_of_lt hN) (by exact_mod_cast hi))
    -- 🎉 no goals
  · apply le_of_lt
    -- ⊢ 0 < 1 * ε
    simpa
    -- 🎉 no goals
#align padic.exi_rat_seq_conv Padic.exi_rat_seq_conv

theorem exi_rat_seq_conv_cauchy : IsCauSeq (padicNorm p) (limSeq f) := fun ε hε ↦ by
  have hε3 : 0 < ε / 3 := div_pos hε (by norm_num)
  -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → padicNorm p (limSeq f j - limSeq f i) < ε
  let ⟨N, hN⟩ := exi_rat_seq_conv f hε3
  -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → padicNorm p (limSeq f j - limSeq f i) < ε
  let ⟨N2, hN2⟩ := f.cauchy₂ hε3
  -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → padicNorm p (limSeq f j - limSeq f i) < ε
  exists max N N2
  -- ⊢ ∀ (j : ℕ), j ≥ max N N2 → padicNorm p (limSeq f j - limSeq f (max N N2)) < ε
  intro j hj
  -- ⊢ padicNorm p (limSeq f j - limSeq f (max N N2)) < ε
  suffices
    padicNormE (limSeq f j - f (max N N2) + (f (max N N2) - limSeq f (max N N2)) : ℚ_[p]) < ε by
    ring_nf at this ⊢
    rw [← padicNormE.eq_padic_norm']
    exact_mod_cast this
  · apply lt_of_le_of_lt
    · apply padicNormE.add_le
      -- 🎉 no goals
    · rw [←add_thirds ε]
      -- ⊢ ↑padicNormE (↑(limSeq f j) - ↑f (max N N2)) + ↑padicNormE (↑f (max N N2) - ↑ …
      apply _root_.add_lt_add
      -- ⊢ ↑padicNormE (↑(limSeq f j) - ↑f (max N N2)) < ε / 3 + ε / 3
      · suffices padicNormE (limSeq f j - f j + (f j - f (max N N2)) : ℚ_[p]) < ε / 3 + ε / 3 by
          simpa only [sub_add_sub_cancel]
        apply lt_of_le_of_lt
        · apply padicNormE.add_le
          -- 🎉 no goals
        · apply _root_.add_lt_add
          -- ⊢ ↑padicNormE (↑(limSeq f j) - ↑f j) < ε / 3
          · rw [padicNormE.map_sub]
            -- ⊢ ↑padicNormE (↑f j - ↑(limSeq f j)) < ε / 3
            apply_mod_cast hN j
            -- ⊢ j ≥ N
            exact le_of_max_le_left hj
            -- 🎉 no goals
          · exact hN2 _ (le_of_max_le_right hj) _ (le_max_right _ _)
            -- 🎉 no goals
      · apply_mod_cast hN (max N N2)
        -- ⊢ max N N2 ≥ N
        apply le_max_left
        -- 🎉 no goals
#align padic.exi_rat_seq_conv_cauchy Padic.exi_rat_seq_conv_cauchy

private def lim' : PadicSeq p :=
  ⟨_, exi_rat_seq_conv_cauchy f⟩

private def lim : ℚ_[p] :=
  ⟦lim' f⟧

theorem complete' : ∃ q : ℚ_[p], ∀ ε > 0, ∃ N, ∀ i ≥ N, padicNormE (q - f i : ℚ_[p]) < ε :=
  ⟨lim f, fun ε hε ↦ by
    obtain ⟨N, hN⟩ := exi_rat_seq_conv f (half_pos hε)
    -- ⊢ ∃ N, ∀ (i : ℕ), i ≥ N → ↑padicNormE (Padic.lim f - ↑f i) < ε
    obtain ⟨N2, hN2⟩ := padicNormE.defn (lim' f) (half_pos hε)
    -- ⊢ ∃ N, ∀ (i : ℕ), i ≥ N → ↑padicNormE (Padic.lim f - ↑f i) < ε
    refine' ⟨max N N2, fun i hi ↦ _⟩
    -- ⊢ ↑padicNormE (Padic.lim f - ↑f i) < ε
    rw [← sub_add_sub_cancel _ (lim' f i : ℚ_[p]) _]
    -- ⊢ ↑padicNormE (Padic.lim f - ↑(↑(Padic.lim' f) i) + (↑(↑(Padic.lim' f) i) - ↑f …
    refine' (padicNormE.add_le _ _).trans_lt _
    -- ⊢ ↑padicNormE (Padic.lim f - ↑(↑(Padic.lim' f) i)) + ↑padicNormE (↑(↑(Padic.li …
    rw [← add_halves ε]
    -- ⊢ ↑padicNormE (Padic.lim f - ↑(↑(Padic.lim' f) i)) + ↑padicNormE (↑(↑(Padic.li …
    apply _root_.add_lt_add
    -- ⊢ ↑padicNormE (Padic.lim f - ↑(↑(Padic.lim' f) i)) < ε / 2
    · apply hN2 _ (le_of_max_le_right hi)
      -- 🎉 no goals
    · rw [padicNormE.map_sub]
      -- ⊢ ↑padicNormE (↑f i - ↑(↑(Padic.lim' f) i)) < ε / 2
      exact hN _ (le_of_max_le_left hi)⟩
      -- 🎉 no goals
#align padic.complete' Padic.complete'

theorem complete'' : ∃ q : ℚ_[p], ∀ ε > 0, ∃ N, ∀ i ≥ N, padicNormE (f i - q : ℚ_[p]) < ε := by
  obtain ⟨x, hx⟩ := complete' f
  -- ⊢ ∃ q, ∀ (ε : ℚ), ε > 0 → ∃ N, ∀ (i : ℕ), i ≥ N → ↑padicNormE (↑f i - q) < ε
  refine ⟨x, fun ε hε => ?_⟩
  -- ⊢ ∃ N, ∀ (i : ℕ), i ≥ N → ↑padicNormE (↑f i - x) < ε
  obtain ⟨N, hN⟩ := hx ε hε
  -- ⊢ ∃ N, ∀ (i : ℕ), i ≥ N → ↑padicNormE (↑f i - x) < ε
  refine ⟨N, fun i hi => ?_⟩
  -- ⊢ ↑padicNormE (↑f i - x) < ε
  rw [padicNormE.map_sub]
  -- ⊢ ↑padicNormE (x - ↑f i) < ε
  exact hN i hi
  -- 🎉 no goals
end Complete

section NormedSpace

variable (p : ℕ) [Fact p.Prime]

instance : Dist ℚ_[p] :=
  ⟨fun x y ↦ padicNormE (x - y : ℚ_[p])⟩

instance metricSpace : MetricSpace ℚ_[p] where
  dist_self := by simp [dist]
                  -- 🎉 no goals
  dist := dist
  dist_comm x y := by simp [dist, ← padicNormE.map_neg (x - y : ℚ_[p])]
                      -- 🎉 no goals
  dist_triangle x y z := by
    dsimp [dist]
    -- ⊢ ↑(↑padicNormE (x - z)) ≤ ↑(↑padicNormE (x - y)) + ↑(↑padicNormE (y - z))
    exact_mod_cast padicNormE.sub_le x y z
    -- 🎉 no goals
  eq_of_dist_eq_zero := by
    dsimp [dist]; intro _ _ h
    -- ⊢ ∀ {x y : ℚ_[p]}, ↑(↑padicNormE (x - y)) = 0 → x = y
                  -- ⊢ x✝ = y✝
    apply eq_of_sub_eq_zero
    -- ⊢ x✝ - y✝ = 0
    apply padicNormE.eq_zero.1
                   -- ⊢ (fun x y => ↑{ val := ↑(↑padicNormE (x - y)), property := (_ : 0 ≤ ↑(↑padicN …
                           -- 🎉 no goals
    -- ⊢ ↑padicNormE (x✝ - y✝) = 0
    exact_mod_cast h
    -- 🎉 no goals
  -- Porting note: added because autoparam was not ported
  edist_dist := by intros; exact (ENNReal.ofReal_eq_coe_nnreal _).symm

instance : Norm ℚ_[p] :=
  ⟨fun x ↦ padicNormE x⟩

instance normedField : NormedField ℚ_[p] :=
  { Padic.field,
    Padic.metricSpace p with
    dist_eq := fun _ _ ↦ rfl
    norm_mul' := by simp [Norm.norm, map_mul]
                    -- 🎉 no goals
    norm := norm }

instance isAbsoluteValue : IsAbsoluteValue fun a : ℚ_[p] ↦ ‖a‖ where
  abv_nonneg' := norm_nonneg
  abv_eq_zero' := norm_eq_zero
  abv_add' := norm_add_le
  abv_mul' := by simp [Norm.norm, map_mul]
                 -- 🎉 no goals
#align padic.is_absolute_value Padic.isAbsoluteValue

theorem rat_dense (q : ℚ_[p]) {ε : ℝ} (hε : 0 < ε) : ∃ r : ℚ, ‖q - r‖ < ε :=
  let ⟨ε', hε'l, hε'r⟩ := exists_rat_btwn hε
  let ⟨r, hr⟩ := rat_dense' q (ε := ε') (by simpa using hε'l)
                                            -- 🎉 no goals
  ⟨r, lt_trans (by simpa [Norm.norm] using hr) hε'r⟩
                   -- 🎉 no goals
#align padic.rat_dense Padic.rat_dense

end NormedSpace

end Padic

namespace padicNormE

section NormedSpace

variable {p : ℕ} [hp : Fact p.Prime]
-- Porting note : Linter thinks this is a duplicate simp lemma, so `priority` is assigned
@[simp (high)]
protected theorem mul (q r : ℚ_[p]) : ‖q * r‖ = ‖q‖ * ‖r‖ := by simp [Norm.norm, map_mul]
                                                                -- 🎉 no goals
#align padic_norm_e.mul padicNormE.mul

protected theorem is_norm (q : ℚ_[p]) : ↑(padicNormE q) = ‖q‖ := rfl
#align padic_norm_e.is_norm padicNormE.is_norm

theorem nonarchimedean (q r : ℚ_[p]) : ‖q + r‖ ≤ max ‖q‖ ‖r‖ := by
  dsimp [norm]
  -- ⊢ ↑(↑padicNormE (q + r)) ≤ max ↑(↑padicNormE q) ↑(↑padicNormE r)
  exact_mod_cast nonarchimedean' _ _
  -- 🎉 no goals
#align padic_norm_e.nonarchimedean padicNormE.nonarchimedean

theorem add_eq_max_of_ne {q r : ℚ_[p]} (h : ‖q‖ ≠ ‖r‖) : ‖q + r‖ = max ‖q‖ ‖r‖ := by
  dsimp [norm] at h ⊢
  -- ⊢ ↑(↑padicNormE (q + r)) = max ↑(↑padicNormE q) ↑(↑padicNormE r)
  have : padicNormE q ≠ padicNormE r := by exact_mod_cast h
  -- ⊢ ↑(↑padicNormE (q + r)) = max ↑(↑padicNormE q) ↑(↑padicNormE r)
  exact_mod_cast add_eq_max_of_ne' this
  -- 🎉 no goals
#align padic_norm_e.add_eq_max_of_ne padicNormE.add_eq_max_of_ne

@[simp]
theorem eq_padicNorm (q : ℚ) : ‖(q : ℚ_[p])‖ = padicNorm p q := by
  dsimp [norm]
  -- ⊢ ↑(↑padicNormE ↑q) = ↑(padicNorm p q)
  rw [← padicNormE.eq_padic_norm']
  -- 🎉 no goals
#align padic_norm_e.eq_padic_norm padicNormE.eq_padicNorm

@[simp]
theorem norm_p : ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [← @Rat.cast_coe_nat ℝ _ p]
  -- ⊢ ‖↑p‖ = (↑↑p)⁻¹
  rw [← @Rat.cast_coe_nat ℚ_[p] _ p]
  -- ⊢ ‖↑↑p‖ = (↑↑p)⁻¹
  simp [hp.1.ne_zero, hp.1.ne_one, norm, padicNorm, padicValRat, padicValInt, zpow_neg,
    -Rat.cast_coe_nat]
#align padic_norm_e.norm_p padicNormE.norm_p

theorem norm_p_lt_one : ‖(p : ℚ_[p])‖ < 1 := by
  rw [norm_p]
  -- ⊢ (↑p)⁻¹ < 1
  apply inv_lt_one
  -- ⊢ 1 < ↑p
  exact_mod_cast hp.1.one_lt
  -- 🎉 no goals
#align padic_norm_e.norm_p_lt_one padicNormE.norm_p_lt_one

-- Porting note : Linter thinks this is a duplicate simp lemma, so `priority` is assigned
@[simp (high)]
theorem norm_p_zpow (n : ℤ) : ‖(p : ℚ_[p]) ^ n‖ = (p : ℝ) ^ (-n) := by
  rw [norm_zpow, norm_p, zpow_neg, inv_zpow]
  -- 🎉 no goals
#align padic_norm_e.norm_p_zpow padicNormE.norm_p_zpow

-- Porting note : Linter thinks this is a duplicate simp lemma, so `priority` is assigned
@[simp (high)]
theorem norm_p_pow (n : ℕ) : ‖(p : ℚ_[p]) ^ n‖ = (p : ℝ) ^ (-n : ℤ) := by
  rw [← norm_p_zpow, zpow_ofNat]
  -- 🎉 no goals
#align padic_norm_e.norm_p_pow padicNormE.norm_p_pow

instance : NontriviallyNormedField ℚ_[p] :=
  { Padic.normedField p with
    non_trivial :=
      ⟨p⁻¹, by
        rw [norm_inv, norm_p, inv_inv]
        -- ⊢ 1 < ↑p
        exact_mod_cast hp.1.one_lt⟩ }
        -- 🎉 no goals

protected theorem image {q : ℚ_[p]} : q ≠ 0 → ∃ n : ℤ, ‖q‖ = ↑((p : ℚ) ^ (-n)) :=
  Quotient.inductionOn q fun f hf ↦
    have : ¬f ≈ 0 := (PadicSeq.ne_zero_iff_nequiv_zero f).1 hf
    let ⟨n, hn⟩ := PadicSeq.norm_values_discrete f this
    ⟨n, by rw [← hn]; rfl⟩
           -- ⊢ ‖Quotient.mk equiv f‖ = ↑(PadicSeq.norm f)
                      -- 🎉 no goals
#align padic_norm_e.image padicNormE.image

protected theorem is_rat (q : ℚ_[p]) : ∃ q' : ℚ, ‖q‖ = q' :=
  if h : q = 0 then ⟨0, by simp [h]⟩
                           -- 🎉 no goals
  else
    let ⟨n, hn⟩ := padicNormE.image h
    ⟨_, hn⟩
#align padic_norm_e.is_rat padicNormE.is_rat

/-- `ratNorm q`, for a `p`-adic number `q` is the `p`-adic norm of `q`, as rational number.

The lemma `padicNormE.eq_ratNorm` asserts `‖q‖ = ratNorm q`. -/
def ratNorm (q : ℚ_[p]) : ℚ :=
  Classical.choose (padicNormE.is_rat q)
#align padic_norm_e.rat_norm padicNormE.ratNorm

theorem eq_ratNorm (q : ℚ_[p]) : ‖q‖ = ratNorm q :=
  Classical.choose_spec (padicNormE.is_rat q)
#align padic_norm_e.eq_rat_norm padicNormE.eq_ratNorm

theorem norm_rat_le_one : ∀ {q : ℚ} (_ : ¬p ∣ q.den), ‖(q : ℚ_[p])‖ ≤ 1
  | ⟨n, d, hn, hd⟩ => fun hq : ¬p ∣ d ↦
    if hnz : n = 0 then by
      have : (⟨n, d, hn, hd⟩ : ℚ) = 0 := Rat.zero_iff_num_zero.mpr hnz
      -- ⊢ ‖↑(Rat.mk' n d)‖ ≤ 1
      norm_num [this]
      -- 🎉 no goals
    else by
      have hnz' : (⟨n, d, hn, hd⟩ : ℚ) ≠ 0 := mt Rat.zero_iff_num_zero.1 hnz
      -- ⊢ ‖↑(Rat.mk' n d)‖ ≤ 1
      rw [padicNormE.eq_padicNorm]
      -- ⊢ ↑(padicNorm p (Rat.mk' n d)) ≤ 1
      norm_cast
      -- ⊢ padicNorm p (Rat.mk' n d) ≤ 1
      -- Porting note: `Nat.cast_zero` instead of another `norm_cast` call
      rw [padicNorm.eq_zpow_of_nonzero hnz', padicValRat, neg_sub,
        padicValNat.eq_zero_of_not_dvd hq, Nat.cast_zero, zero_sub, zpow_neg, zpow_ofNat]
      apply inv_le_one
      -- ⊢ 1 ≤ ↑p ^ padicValInt p (Rat.mk' n d).num
      · norm_cast
        -- ⊢ 1 ≤ p ^ padicValInt p (Rat.mk' n d).num
        apply one_le_pow
        -- ⊢ 0 < p
        exact hp.1.pos
        -- 🎉 no goals
#align padic_norm_e.norm_rat_le_one padicNormE.norm_rat_le_one

theorem norm_int_le_one (z : ℤ) : ‖(z : ℚ_[p])‖ ≤ 1 :=
  suffices ‖((z : ℚ) : ℚ_[p])‖ ≤ 1 by simpa
                                      -- 🎉 no goals
                        -- 🎉 no goals
  norm_rat_le_one <| by simp [hp.1.ne_one]
#align padic_norm_e.norm_int_le_one padicNormE.norm_int_le_one

theorem norm_int_lt_one_iff_dvd (k : ℤ) : ‖(k : ℚ_[p])‖ < 1 ↔ ↑p ∣ k := by
  constructor
  -- ⊢ ‖↑k‖ < 1 → ↑p ∣ k
  · intro h
    -- ⊢ ↑p ∣ k
    contrapose! h
    -- ⊢ 1 ≤ ‖↑k‖
    apply le_of_eq
    -- ⊢ 1 = ‖↑k‖
    rw [eq_comm]
    -- ⊢ ‖↑k‖ = 1
    calc
      ‖(k : ℚ_[p])‖ = ‖((k : ℚ) : ℚ_[p])‖ := by norm_cast
      _ = padicNorm p k := (padicNormE.eq_padicNorm _)
      _ = 1 := by exact_mod_cast (int_eq_one_iff k).mpr h
  · rintro ⟨x, rfl⟩
    -- ⊢ ‖↑(↑p * x)‖ < 1
    push_cast
    -- ⊢ ‖↑p * ↑x‖ < 1
    rw [padicNormE.mul]
    -- ⊢ ‖↑p‖ * ‖↑x‖ < 1
    calc
      _ ≤ ‖(p : ℚ_[p])‖ * 1 :=
        mul_le_mul le_rfl (by simpa using norm_int_le_one _) (norm_nonneg _) (norm_nonneg _)
      _ < 1 := by
        rw [mul_one, padicNormE.norm_p]
        apply inv_lt_one
        exact_mod_cast hp.1.one_lt
#align padic_norm_e.norm_int_lt_one_iff_dvd padicNormE.norm_int_lt_one_iff_dvd

theorem norm_int_le_pow_iff_dvd (k : ℤ) (n : ℕ) :
    ‖(k : ℚ_[p])‖ ≤ (p : ℝ) ^ (-n : ℤ) ↔ (p ^ n : ℤ) ∣ k := by
  have : (p : ℝ) ^ (-n : ℤ) = (p : ℚ) ^ (-n : ℤ) := by simp
  -- ⊢ ‖↑k‖ ≤ ↑p ^ (-↑n) ↔ ↑(p ^ n) ∣ k
  rw [show (k : ℚ_[p]) = ((k : ℚ) : ℚ_[p]) by norm_cast, eq_padicNorm, this]
  -- ⊢ ↑(padicNorm p ↑k) ≤ ↑(↑p ^ (-↑n)) ↔ ↑(p ^ n) ∣ k
  norm_cast
  -- ⊢ padicNorm p ↑k ≤ ↑p ^ (-↑n) ↔ ↑(p ^ n) ∣ k
  rw [← padicNorm.dvd_iff_norm_le]
  -- 🎉 no goals
#align padic_norm_e.norm_int_le_pow_iff_dvd padicNormE.norm_int_le_pow_iff_dvd

theorem eq_of_norm_add_lt_right {z1 z2 : ℚ_[p]} (h : ‖z1 + z2‖ < ‖z2‖) : ‖z1‖ = ‖z2‖ :=
  _root_.by_contradiction fun hne ↦
    not_lt_of_ge (by rw [padicNormE.add_eq_max_of_ne hne]; apply le_max_right) h
                     -- ⊢ max ‖z1‖ ‖z2‖ ≥ ‖z2‖
                                                           -- 🎉 no goals
#align padic_norm_e.eq_of_norm_add_lt_right padicNormE.eq_of_norm_add_lt_right

theorem eq_of_norm_add_lt_left {z1 z2 : ℚ_[p]} (h : ‖z1 + z2‖ < ‖z1‖) : ‖z1‖ = ‖z2‖ :=
  _root_.by_contradiction fun hne ↦
    not_lt_of_ge (by rw [padicNormE.add_eq_max_of_ne hne]; apply le_max_left) h
                     -- ⊢ max ‖z1‖ ‖z2‖ ≥ ‖z1‖
                                                           -- 🎉 no goals
#align padic_norm_e.eq_of_norm_add_lt_left padicNormE.eq_of_norm_add_lt_left

end NormedSpace

end padicNormE

namespace Padic

variable {p : ℕ} [hp : Fact p.Prime]

-- Porting note : remove `set_option eqn_compiler.zeta true`

instance complete : CauSeq.IsComplete ℚ_[p] norm where
  isComplete := fun f => by
    have cau_seq_norm_e : IsCauSeq padicNormE f := fun ε hε => by
      have h := isCauSeq f ε (by exact_mod_cast hε)
      dsimp [norm] at h
      exact_mod_cast h
    -- Porting note: Padic.complete' works with `f i - q`, but the goal needs `q - f i`,
    -- using `rewrite [padicNormE.map_sub]` causes time out, so a separate lemma is created
    cases' Padic.complete'' ⟨f, cau_seq_norm_e⟩ with q hq
    -- ⊢ ∃ b, f ≈ const norm b
    exists q
    -- ⊢ f ≈ const norm q
    intro ε hε
    -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → ‖↑(f - const norm q) j‖ < ε
    cases' exists_rat_btwn hε with ε' hε'
    -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → ‖↑(f - const norm q) j‖ < ε
    norm_cast at hε'
    -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → ‖↑(f - const norm q) j‖ < ε
    cases' hq ε' hε'.1 with N hN
    -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → ‖↑(f - const norm q) j‖ < ε
    exists N
    -- ⊢ ∀ (j : ℕ), j ≥ N → ‖↑(f - const norm q) j‖ < ε
    intro i hi
    -- ⊢ ‖↑(f - const norm q) i‖ < ε
    have h := hN i hi
    -- ⊢ ‖↑(f - const norm q) i‖ < ε
    change norm (f i - q) < ε
    -- ⊢ ‖↑f i - q‖ < ε
    refine lt_trans ?_ hε'.2
    -- ⊢ ‖↑f i - q‖ < ↑ε'
    dsimp [norm]
    -- ⊢ ↑(↑padicNormE (↑f i - q)) < ↑ε'
    exact_mod_cast h
    -- 🎉 no goals
#align padic.complete Padic.complete

theorem padicNormE_lim_le {f : CauSeq ℚ_[p] norm} {a : ℝ} (ha : 0 < a) (hf : ∀ i, ‖f i‖ ≤ a) :
    ‖f.lim‖ ≤ a := by
  -- Porting note: `Setoid.symm` cannot work out which `Setoid` to use, so instead swap the order
  -- now, I use a rewrite to swap it later
  obtain ⟨N, hN⟩ := (CauSeq.equiv_lim f) _ ha
  -- ⊢ ‖CauSeq.lim f‖ ≤ a
  rw [←sub_add_cancel f.lim (f N)]
  -- ⊢ ‖CauSeq.lim f - ↑f N + ↑f N‖ ≤ a
  refine le_trans (padicNormE.nonarchimedean _ _) ?_
  -- ⊢ max ‖CauSeq.lim f - ↑f N‖ ‖↑f N‖ ≤ a
  rw [norm_sub_rev]
  -- ⊢ max ‖↑f N - CauSeq.lim f‖ ‖↑f N‖ ≤ a
  exact max_le (le_of_lt (hN _ le_rfl)) (hf _)
  -- 🎉 no goals
  -- Porting note: the following nice `calc` block does not work
  -- exact calc
  --   ‖f.lim‖ = ‖f.lim - f N + f N‖ := sorry
  --   ‖f.lim - f N + f N‖ ≤ max ‖f.lim - f N‖ ‖f N‖ := sorry -- (padicNormE.nonarchimedean _ _)
  --   max ‖f.lim - f N‖ ‖f N‖ = max ‖f N - f.lim‖ ‖f N‖ := sorry -- by congr; rw [norm_sub_rev]
  --   max ‖f N - f.lim‖ ‖f N‖ ≤ a := sorry -- max_le (le_of_lt (hN _ le_rfl)) (hf _)
#align padic.padic_norm_e_lim_le Padic.padicNormE_lim_le

open Filter Set

instance : CompleteSpace ℚ_[p] := by
  apply complete_of_cauchySeq_tendsto
  -- ⊢ ∀ (u : ℕ → ℚ_[p]), CauchySeq u → ∃ a, Tendsto u atTop (nhds a)
  intro u hu
  -- ⊢ ∃ a, Tendsto u atTop (nhds a)
  let c : CauSeq ℚ_[p] norm := ⟨u, Metric.cauchySeq_iff'.mp hu⟩
  -- ⊢ ∃ a, Tendsto u atTop (nhds a)
  refine' ⟨c.lim, fun s h ↦ _⟩
  -- ⊢ s ∈ map u atTop
  rcases Metric.mem_nhds_iff.1 h with ⟨ε, ε0, hε⟩
  -- ⊢ s ∈ map u atTop
  have := c.equiv_lim ε ε0
  -- ⊢ s ∈ map u atTop
  simp only [mem_map, mem_atTop_sets, mem_setOf_eq]
  -- ⊢ ∃ a, ∀ (b : ℕ), b ≥ a → b ∈ u ⁻¹' s
  exact this.imp fun N hN n hn ↦ hε (hN n hn)
  -- 🎉 no goals

/-! ### Valuation on `ℚ_[p]` -/


/-- `Padic.valuation` lifts the `p`-adic valuation on rationals to `ℚ_[p]`. -/
def valuation : ℚ_[p] → ℤ :=
  Quotient.lift (@PadicSeq.valuation p _) fun f g h ↦ by
    by_cases hf : f ≈ 0
    -- ⊢ PadicSeq.valuation f = PadicSeq.valuation g
    · have hg : g ≈ 0 := Setoid.trans (Setoid.symm h) hf
      -- ⊢ PadicSeq.valuation f = PadicSeq.valuation g
      simp [hf, hg, PadicSeq.valuation]
      -- 🎉 no goals
    · have hg : ¬g ≈ 0 := fun hg ↦ hf (Setoid.trans h hg)
      -- ⊢ PadicSeq.valuation f = PadicSeq.valuation g
      rw [PadicSeq.val_eq_iff_norm_eq hf hg]
      -- ⊢ PadicSeq.norm f = PadicSeq.norm g
      exact PadicSeq.norm_equiv h
      -- 🎉 no goals
#align padic.valuation Padic.valuation

@[simp]
theorem valuation_zero : valuation (0 : ℚ_[p]) = 0 :=
  dif_pos ((const_equiv p).2 rfl)
#align padic.valuation_zero Padic.valuation_zero

@[simp]
theorem valuation_one : valuation (1 : ℚ_[p]) = 0 := by
  change dite (CauSeq.const (padicNorm p) 1 ≈ _) _ _ = _
  -- ⊢ (if h : const (padicNorm p) 1 ≈ 0 then (fun hf => 0) h else (fun hf => padic …
  have h : ¬CauSeq.const (padicNorm p) 1 ≈ 0 := by
    intro H
    erw [const_equiv p] at H
    exact one_ne_zero H
  rw [dif_neg h]
  -- ⊢ (fun hf => padicValRat p (↑(const (padicNorm p) 1) (PadicSeq.stationaryPoint …
  simp
  -- 🎉 no goals
#align padic.valuation_one Padic.valuation_one

theorem norm_eq_pow_val {x : ℚ_[p]} : x ≠ 0 → ‖x‖ = (p : ℝ) ^ (-x.valuation) := by
  refine Quotient.inductionOn' x fun f hf => ?_
  -- ⊢ ‖Quotient.mk'' f‖ = ↑p ^ (-valuation (Quotient.mk'' f))
  change (PadicSeq.norm _ : ℝ) = (p : ℝ) ^ (-PadicSeq.valuation _)
  -- ⊢ ↑(PadicSeq.norm f) = ↑p ^ (-PadicSeq.valuation f)
  rw [PadicSeq.norm_eq_pow_val]
  -- ⊢ ↑(↑p ^ (-PadicSeq.valuation f)) = ↑p ^ (-PadicSeq.valuation f)
  change ↑((p : ℚ) ^ (-PadicSeq.valuation f)) = (p : ℝ) ^ (-PadicSeq.valuation f)
  -- ⊢ ↑(↑p ^ (-PadicSeq.valuation f)) = ↑p ^ (-PadicSeq.valuation f)
  · rw [Rat.cast_zpow, Rat.cast_coe_nat]
    -- 🎉 no goals
  · apply CauSeq.not_limZero_of_not_congr_zero
    -- ⊢ ¬f - 0 ≈ 0
    -- Porting note: was `contrapose! hf`
    intro hf'
    -- ⊢ False
    apply hf
    -- ⊢ Quotient.mk'' f = 0
    apply Quotient.sound
    -- ⊢ f ≈ const (padicNorm p) 0
    simpa using hf'
    -- 🎉 no goals
#align padic.norm_eq_pow_val Padic.norm_eq_pow_val

@[simp]
theorem valuation_p : valuation (p : ℚ_[p]) = 1 := by
  have h : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  -- ⊢ valuation ↑p = 1
  refine' neg_injective ((zpow_strictMono h).injective <| (norm_eq_pow_val _).symm.trans _)
  -- ⊢ ↑p ≠ 0
  · exact_mod_cast (Fact.out : p.Prime).ne_zero
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align padic.valuation_p Padic.valuation_p

theorem valuation_map_add {x y : ℚ_[p]} (hxy : x + y ≠ 0) :
    min (valuation x) (valuation y) ≤ valuation (x + y : ℚ_[p]) := by
  by_cases hx : x = 0
  -- ⊢ min (valuation x) (valuation y) ≤ valuation (x + y)
  · rw [hx, zero_add]
    -- ⊢ min (valuation 0) (valuation y) ≤ valuation y
    exact min_le_right _ _
    -- 🎉 no goals
  · by_cases hy : y = 0
    -- ⊢ min (valuation x) (valuation y) ≤ valuation (x + y)
    · rw [hy, add_zero]
      -- ⊢ min (valuation x) (valuation 0) ≤ valuation x
      exact min_le_left _ _
      -- 🎉 no goals
    · have h_norm : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := padicNormE.nonarchimedean x y
      -- ⊢ min (valuation x) (valuation y) ≤ valuation (x + y)
      have hp_one : (1 : ℝ) < p := by
        rw [← Nat.cast_one, Nat.cast_lt]
        exact Nat.Prime.one_lt hp.elim
      rwa [norm_eq_pow_val hx, norm_eq_pow_val hy, norm_eq_pow_val hxy,
        zpow_le_max_iff_min_le hp_one] at h_norm
#align padic.valuation_map_add Padic.valuation_map_add

@[simp]
theorem valuation_map_mul {x y : ℚ_[p]} (hx : x ≠ 0) (hy : y ≠ 0) :
    valuation (x * y : ℚ_[p]) = valuation x + valuation y := by
  have h_norm : ‖x * y‖ = ‖x‖ * ‖y‖ := norm_mul x y
  -- ⊢ valuation (x * y) = valuation x + valuation y
  have hp_ne_one : (p : ℝ) ≠ 1 := by
    rw [← Nat.cast_one, Ne.def, Nat.cast_inj]
    exact Nat.Prime.ne_one hp.elim
  have hp_pos : (0 : ℝ) < p := by
    rw [← Nat.cast_zero, Nat.cast_lt]
    exact Nat.Prime.pos hp.elim
  rw [norm_eq_pow_val hx, norm_eq_pow_val hy, norm_eq_pow_val (mul_ne_zero hx hy), ←
    zpow_add₀ (ne_of_gt hp_pos), zpow_inj hp_pos hp_ne_one, ← neg_add, neg_inj] at h_norm
  exact h_norm
  -- 🎉 no goals
#align padic.valuation_map_mul Padic.valuation_map_mul

/-- The additive `p`-adic valuation on `ℚ_[p]`, with values in `WithTop ℤ`. -/
def addValuationDef : ℚ_[p] → WithTop ℤ :=
  fun x ↦ if x = 0 then ⊤ else x.valuation
#align padic.add_valuation_def Padic.addValuationDef

@[simp]
theorem AddValuation.map_zero : addValuationDef (0 : ℚ_[p]) = ⊤ := by
  rw [addValuationDef, if_pos (Eq.refl _)]
  -- 🎉 no goals
#align padic.add_valuation.map_zero Padic.AddValuation.map_zero

@[simp]
theorem AddValuation.map_one : addValuationDef (1 : ℚ_[p]) = 0 := by
  rw [addValuationDef, if_neg one_ne_zero, valuation_one, WithTop.coe_zero]
  -- 🎉 no goals
#align padic.add_valuation.map_one Padic.AddValuation.map_one

theorem AddValuation.map_mul (x y : ℚ_[p]) :
    addValuationDef (x * y : ℚ_[p]) = addValuationDef x + addValuationDef y := by
  simp only [addValuationDef]
  -- ⊢ (if x * y = 0 then ⊤ else ↑(valuation (x * y))) = (if x = 0 then ⊤ else ↑(va …
  by_cases hx : x = 0
  -- ⊢ (if x * y = 0 then ⊤ else ↑(valuation (x * y))) = (if x = 0 then ⊤ else ↑(va …
  · rw [hx, if_pos (Eq.refl _), zero_mul, if_pos (Eq.refl _), WithTop.top_add]
    -- 🎉 no goals
  · by_cases hy : y = 0
    -- ⊢ (if x * y = 0 then ⊤ else ↑(valuation (x * y))) = (if x = 0 then ⊤ else ↑(va …
    · rw [hy, if_pos (Eq.refl _), mul_zero, if_pos (Eq.refl _), WithTop.add_top]
      -- 🎉 no goals
    · rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← WithTop.coe_add, WithTop.coe_eq_coe,
        valuation_map_mul hx hy]
#align padic.add_valuation.map_mul Padic.AddValuation.map_mul

theorem AddValuation.map_add (x y : ℚ_[p]) :
    min (addValuationDef x) (addValuationDef y) ≤ addValuationDef (x + y : ℚ_[p]) := by
  simp only [addValuationDef]
  -- ⊢ min (if x = 0 then ⊤ else ↑(valuation x)) (if y = 0 then ⊤ else ↑(valuation  …
  by_cases hxy : x + y = 0
  -- ⊢ min (if x = 0 then ⊤ else ↑(valuation x)) (if y = 0 then ⊤ else ↑(valuation  …
  · rw [hxy, if_pos (Eq.refl _)]
    -- ⊢ min (if x = 0 then ⊤ else ↑(valuation x)) (if y = 0 then ⊤ else ↑(valuation  …
    exact le_top
    -- 🎉 no goals
  · by_cases hx : x = 0
    -- ⊢ min (if x = 0 then ⊤ else ↑(valuation x)) (if y = 0 then ⊤ else ↑(valuation  …
    · rw [hx, if_pos (Eq.refl _), min_eq_right, zero_add]
      -- ⊢ (if y = 0 then ⊤ else ↑(valuation y)) ≤ ⊤
      exact le_top
      -- 🎉 no goals
    · by_cases hy : y = 0
      -- ⊢ min (if x = 0 then ⊤ else ↑(valuation x)) (if y = 0 then ⊤ else ↑(valuation  …
      · rw [hy, if_pos (Eq.refl _), min_eq_left, add_zero]
        -- ⊢ (if x = 0 then ⊤ else ↑(valuation x)) ≤ ⊤
        exact le_top
        -- 🎉 no goals
      · rw [if_neg hx, if_neg hy, if_neg hxy, ← WithTop.coe_min, WithTop.coe_le_coe]
        -- ⊢ min (valuation x) (valuation y) ≤ valuation (x + y)
        exact valuation_map_add hxy
        -- 🎉 no goals
#align padic.add_valuation.map_add Padic.AddValuation.map_add

/-- The additive `p`-adic valuation on `ℚ_[p]`, as an `addValuation`. -/
def addValuation : AddValuation ℚ_[p] (WithTop ℤ) :=
  AddValuation.of addValuationDef AddValuation.map_zero AddValuation.map_one AddValuation.map_add
    AddValuation.map_mul
#align padic.add_valuation Padic.addValuation

@[simp]
theorem addValuation.apply {x : ℚ_[p]} (hx : x ≠ 0) :
    Padic.addValuation x = (x.valuation : WithTop ℤ) := by
  simp only [Padic.addValuation, AddValuation.of_apply, addValuationDef, if_neg hx]
  -- 🎉 no goals
#align padic.add_valuation.apply Padic.addValuation.apply

section NormLEIff

/-! ### Various characterizations of open unit balls -/


theorem norm_le_pow_iff_norm_lt_pow_add_one (x : ℚ_[p]) (n : ℤ) :
    ‖x‖ ≤ (p : ℝ) ^ n ↔ ‖x‖ < (p : ℝ) ^ (n + 1) := by
  have aux : ∀ n : ℤ, 0 < ((p : ℝ) ^ n) := by
    apply Nat.zpow_pos_of_pos
    exact hp.1.pos
  by_cases hx0 : x = 0
  -- ⊢ ‖x‖ ≤ ↑p ^ n ↔ ‖x‖ < ↑p ^ (n + 1)
  · simp [hx0, norm_zero, aux, le_of_lt (aux _)]
    -- 🎉 no goals
  rw [norm_eq_pow_val hx0]
  -- ⊢ ↑p ^ (-valuation x) ≤ ↑p ^ n ↔ ↑p ^ (-valuation x) < ↑p ^ (n + 1)
  have h1p : 1 < (p : ℝ) := by exact_mod_cast hp.1.one_lt
  -- ⊢ ↑p ^ (-valuation x) ≤ ↑p ^ n ↔ ↑p ^ (-valuation x) < ↑p ^ (n + 1)
  have H := zpow_strictMono h1p
  -- ⊢ ↑p ^ (-valuation x) ≤ ↑p ^ n ↔ ↑p ^ (-valuation x) < ↑p ^ (n + 1)
  rw [H.le_iff_le, H.lt_iff_lt, Int.lt_add_one_iff]
  -- 🎉 no goals
#align padic.norm_le_pow_iff_norm_lt_pow_add_one Padic.norm_le_pow_iff_norm_lt_pow_add_one

theorem norm_lt_pow_iff_norm_le_pow_sub_one (x : ℚ_[p]) (n : ℤ) :
    ‖x‖ < (p : ℝ) ^ n ↔ ‖x‖ ≤ (p : ℝ) ^ (n - 1) := by
  rw [norm_le_pow_iff_norm_lt_pow_add_one, sub_add_cancel]
  -- 🎉 no goals
#align padic.norm_lt_pow_iff_norm_le_pow_sub_one Padic.norm_lt_pow_iff_norm_le_pow_sub_one

theorem norm_le_one_iff_val_nonneg (x : ℚ_[p]) : ‖x‖ ≤ 1 ↔ 0 ≤ x.valuation := by
  by_cases hx : x = 0
  -- ⊢ ‖x‖ ≤ 1 ↔ 0 ≤ valuation x
  · simp only [hx, norm_zero, valuation_zero, zero_le_one, le_refl]
    -- 🎉 no goals
  · rw [norm_eq_pow_val hx, ← zpow_zero (p : ℝ), zpow_le_iff_le, Right.neg_nonpos_iff]
    -- ⊢ 1 < ↑p
    exact Nat.one_lt_cast.2 (Nat.Prime.one_lt' p).1
    -- 🎉 no goals
#align padic.norm_le_one_iff_val_nonneg Padic.norm_le_one_iff_val_nonneg

end NormLEIff

end Padic
