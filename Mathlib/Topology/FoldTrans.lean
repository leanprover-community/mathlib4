/-
Copyright (c) 2026 Sebastian Kumar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Kumar
-/
module

public import Batteries.Data.Fin.Fold
public import Mathlib.Topology.Subpath

/-!
# Concatenating sequences of paths

This file introduces a way to concatenate sequences of paths with compatible endpoints,
which is useful when partitioning paths (such as in Lemma 1.15 from [hatcher02]).
The implementation is based on `Fin.dfoldl` from the Batteries library.

## Main results

- `foldTrans`: definition of path concatenation
- `foldTrans_refl`: generalizes `Path.refl_trans_refl`
- `foldHcomp`: generalizes `Path.Homotopy.hcomp`
- `foldTransSubpath`: homotopy between the concatenation of subpaths and a single subpath
-/

@[expose] public noncomputable section

open Fin Function unitInterval

universe u

variable {X : Type u} [TopologicalSpace X] {n : ℕ}

namespace Path

/-- Folds `Path.trans` across a sequence of paths with compatible endpoints. -/
def foldTrans (p : Fin (n + 1) → X) (F : ∀ k : Fin n, Path (p k.castSucc) (p k.succ)) :
    Path (p 0) (p (last n)) :=
  dfoldl n (fun i => Path (p 0) (p i)) (fun i ih => ih.trans (F i)) (refl (p 0))

/-- Folding zero paths gives the constant path (the identity of `Path.trans`). -/
@[simp]
lemma foldTrans_zero (p : Fin 1 → X) (F : ∀ k : Fin 0, Path (p k.castSucc) (p k.succ)) :
    foldTrans p F = refl (p 0) := by rw [foldTrans, dfoldl_zero]

/-- Folding `n + 1` paths corresponds to folding `n` paths and then concatenating the last path. -/
@[simp]
lemma foldTrans_succ (p : Fin (n + 2) → X)
    (F : ∀ k : Fin (n + 1), Path (p k.castSucc) (p k.succ)) : foldTrans p F =
      (foldTrans (p ∘ castSucc) (fun k ↦ (F k.castSucc))).trans (F (last n)) := by
  rw [foldTrans, dfoldl_succ_last]
  rfl

/-- Folding the constant path at `x` `n` times just yields the constant path at `x`. -/
@[simp]
theorem foldTrans_refl (n : ℕ) (x : X) :
    foldTrans (fun (_ : Fin (n + 1)) ↦ x) (fun _ ↦ Path.refl x) = Path.refl x := by
  induction n with
  | zero => rw [foldTrans_zero]
  | succ _ _ =>
    rw [foldTrans_succ]
    convert refl_trans_refl

namespace Homotopy

/-- Given two sequences of paths `F` and `G`, and a sequence `H` of homotopies between them,
there is a natural homotopy between `foldTrans _ F` and `foldTrans _ G`. -/
def foldHcomp (p : Fin (n + 1) → X) (F G : ∀ k : Fin n, Path (p k.castSucc) (p k.succ))
    (H : ∀ k, (F k).Homotopy (G k)) : Homotopy (foldTrans p F) (foldTrans p G) := by
  induction n with
  | zero =>
    rw [foldTrans_zero, foldTrans_zero]
    exact refl (Path.refl _)
  | succ n ih =>
    rw [foldTrans_succ, foldTrans_succ]
    exact hcomp (ih _ _ _ (fun k ↦ H k.castSucc)) (H (last n))

/-- Given a path `γ` and a sequence `p` of `n + 1` points in `[0, 1]`, there is a natural homotopy
between the concatenation of paths `γ.subpath (p k) (p (k + 1))`, and `γ.subpath (p 0) (p n)`. -/
def foldTransSubpath {a b : X} (γ : Path a b) (p : Fin (n + 1) → I) : Homotopy
    (foldTrans (γ ∘ p) (fun k ↦ γ.subpath (p k.castSucc) (p k.succ)))
    (γ.subpath (p 0) (p (last n))) := by
  induction n with
  | zero =>
    simp only [foldTrans_zero, reduceLast, subpath_self]
    exact refl _
  | succ n ih =>
    rw [foldTrans_succ]
    exact trans ((ih (p ∘ castSucc)).hcomp (refl _)) (subpathTransSubpath γ _ _ _)

end Homotopy

namespace Homotopic

/-- Alternative to `Path.Homotopy.foldHcomp` in terms of `Path.Homotopic`. -/
theorem fold_hcomp (p : Fin (n + 1) → X) (F G : ∀ k : Fin n, Path (p k.castSucc) (p k.succ))
    (h : ∀ k, (F k).Homotopic (G k)) : Homotopic (foldTrans p F) (foldTrans p G) :=
  ⟨Homotopy.foldHcomp p F G (fun k ↦ (h k).some)⟩

/-- Alternative to `Path.Homotopy.foldTransSubpath` in terms of `Path.Homotopic`. -/
@[simp]
theorem foldTrans_subpath {a b : X} (γ : Path a b) (p : Fin (n + 1) → I) : Homotopic
    (foldTrans (γ ∘ p) (fun k ↦ γ.subpath (p k.castSucc) (p k.succ)))
    (γ.subpath (p 0) (p (last n))) :=
  ⟨Homotopy.foldTransSubpath γ p⟩

end Path.Homotopic

end
