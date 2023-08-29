/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot
-/
import Mathlib.LinearAlgebra.Basis
import Mathlib.Data.Fin.FlagRange

/-!
# Flag of submodules defined by a basis

In this file we define `Basis.flag b k`, where `b : Basis (Fin n) R M`, `k : Fin (n + 1)`,
to be the subspace spanned by the first `k` vectors of the basis `b`.

We also prove some lemmas about this definition.
-/

open Set Submodule

namespace Basis

section Semiring

variable {R M : Type _} [Semiring R] [AddCommMonoid M] [Module R M] {n : ℕ}

/-- The subspace spanned by the first `k` vectors of the basis `b`. -/
def flag (b : Basis (Fin n) R M) (k : Fin (n + 1)) : Submodule R M :=
  .span R <| b '' {i | i.castSucc < k}

@[simp]
theorem flag_zero (b : Basis (Fin n) R M) : b.flag 0 = ⊥ := by simp [flag]
                                                               -- 🎉 no goals

@[simp]
theorem flag_last (b : Basis (Fin n) R M) : b.flag (.last n) = ⊤ := by
  simp [flag, Fin.castSucc_lt_last]
  -- 🎉 no goals

theorem flag_le_iff (b : Basis (Fin n) R M) {k p} :
    b.flag k ≤ p ↔ ∀ i : Fin n, i.castSucc < k → b i ∈ p :=
  span_le.trans ball_image_iff

theorem flag_succ (b : Basis (Fin n) R M) (k : Fin n) :
    b.flag k.succ = (R ∙ b k) ⊔ b.flag k.castSucc := by
  simp only [flag, Fin.castSucc_lt_castSucc_iff]
  -- ⊢ span R ((fun a => ↑b a) '' {i | Fin.castSucc i < Fin.succ k}) = span R {↑b k …
  simp [Fin.castSucc_lt_iff_succ_le, le_iff_eq_or_lt, setOf_or, image_insert_eq, span_insert]
  -- 🎉 no goals

theorem self_mem_flag (b : Basis (Fin n) R M) {i : Fin n} {k : Fin (n + 1)} (h : i.castSucc < k) :
    b i ∈ b.flag k :=
  subset_span <| mem_image_of_mem _ h

@[simp]
theorem self_mem_flag_iff [Nontrivial R] (b : Basis (Fin n) R M) {i : Fin n} {k : Fin (n + 1)} :
    b i ∈ b.flag k ↔ i.castSucc < k :=
  b.self_mem_span_image

@[mono]
theorem flag_mono (b : Basis (Fin n) R M) : Monotone b.flag :=
  Fin.monotone_iff_le_succ.2 fun k ↦ by rw [flag_succ]; exact le_sup_right
                                        -- ⊢ flag b (Fin.castSucc k) ≤ span R {↑b k} ⊔ flag b (Fin.castSucc k)
                                                        -- 🎉 no goals

theorem isChain_range_flag (b : Basis (Fin n) R M) : IsChain (· ≤ ·) (range b.flag) :=
  b.flag_mono.isChain_range

@[mono]
theorem flag_strictMono [Nontrivial R] (b : Basis (Fin n) R M) : StrictMono b.flag :=
  Fin.strictMono_iff_lt_succ.2 fun _ ↦ by simp [flag_succ]
                                          -- 🎉 no goals

end Semiring

section CommRing

variable {R M : Type _} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

@[simp]
theorem flag_le_ker_coord_iff [Nontrivial R] (b : Basis (Fin n) R M) {k : Fin (n + 1)} {l : Fin n} :
    b.flag k ≤ LinearMap.ker (b.coord l) ↔ k ≤ l.castSucc := by
  simp [flag_le_iff, Finsupp.single_apply_eq_zero, imp_false, imp_not_comm]
  -- 🎉 no goals

theorem flag_le_ker_coord (b : Basis (Fin n) R M) {k : Fin (n + 1)} {l : Fin n}
    (h : k ≤ l.castSucc) : b.flag k ≤ LinearMap.ker (b.coord l) := by
  nontriviality R
  -- ⊢ flag b k ≤ LinearMap.ker (coord b l)
  exact b.flag_le_ker_coord_iff.2 h
  -- 🎉 no goals

end CommRing

section DivisionRing

variable {K V : Type _} [DivisionRing K] [AddCommGroup V] [Module K V] {n : ℕ}

theorem flag_covby (b : Basis (Fin n) K V) (i : Fin n) :
    b.flag i.castSucc ⋖ b.flag i.succ := by
  rw [flag_succ]
  -- ⊢ flag b (Fin.castSucc i) ⋖ span K {↑b i} ⊔ flag b (Fin.castSucc i)
  apply covby_span_singleton_sup
  -- ⊢ ¬↑b i ∈ flag b (Fin.castSucc i)
  simp
  -- 🎉 no goals

theorem flag_wcovby (b : Basis (Fin n) K V) (i : Fin n) :
    b.flag i.castSucc ⩿ b.flag i.succ :=
  (b.flag_covby i).wcovby

/-- Range of `Basis.flag` as a `Flag`. -/
@[simps!]
def toFlag (b : Basis (Fin n) K V) : Flag (Submodule K V) :=
  .rangeFin b.flag b.flag_zero b.flag_last b.flag_wcovby

@[simp]
theorem mem_toFlag (b : Basis (Fin n) K V) {p : Submodule K V} : p ∈ b.toFlag ↔ ∃ k, b.flag k = p :=
  Iff.rfl

theorem isMaxChain_range_flag (b : Basis (Fin n) K V) : IsMaxChain (· ≤ ·) (range b.flag) :=
  b.toFlag.maxChain

end DivisionRing
