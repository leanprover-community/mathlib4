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

- `concatenate`: definition of path concatenation
- `concatenate_refl`: generalizes `Path.refl_trans_refl`
- `concatenateHcomp`: generalizes `Path.Homotopy.hcomp`
- `concatenateSubpath`: homotopy between the concatenation of subpaths and a single subpath
-/

@[expose] public noncomputable section

open Fin Function unitInterval

variable {X : Type*} [TopologicalSpace X] {n : ℕ}

namespace Path

/-- Concatenation of a sequence of paths with compatible endpoints. -/
def concatenate (p : Fin (n + 1) → X) (F : ∀ k : Fin n, Path (p k.castSucc) (p k.succ)) :
    Path (p 0) (p (last n)) :=
  dfoldl n (fun i => Path (p 0) (p i)) (fun i ih => ih.trans (F i)) (refl (p 0))

/-- Concatenating zero paths gives the constant path (the identity of `Path.trans`). -/
lemma concatenate_zero (p : Fin 1 → X) (F) :
    concatenate p F = refl (p 0) := by
  rw [concatenate, dfoldl_zero]

/-- Concatenating `n + 1` paths corresponds to concatenating `n` paths and then the last path. -/
lemma concatenate_succ (p : Fin (n + 2) → X) (F) :
    concatenate p F = (concatenate (p ∘ castSucc) (fun k ↦ (F k.castSucc))).trans (F (last n)) := by
  rw [concatenate, dfoldl_succ_last]
  rfl

/-- Concatenating the constant path at `x` with itself just yields the constant path at `x`. -/
@[simp]
theorem concatenate_refl (n : ℕ) (x : X) :
    concatenate (fun (_ : Fin (n + 1)) ↦ x) (fun _ ↦ Path.refl x) = Path.refl x := by
  induction n with
  | zero => rw [concatenate_zero]
  | succ _ _ =>
    rw [concatenate_succ]
    convert refl_trans_refl

namespace Homotopy

/-- Given two sequences of paths `F` and `G`, and a sequence `H` of homotopies between them,
there is a natural homotopy between `concatenate _ F` and `concatenate _ G`. -/
def concatenateHcomp (p : Fin (n + 1) → X) (F G : ∀ k : Fin n, Path (p k.castSucc) (p k.succ))
    (H : ∀ k, (F k).Homotopy (G k)) : Homotopy (concatenate p F) (concatenate p G) := by
  induction n with
  | zero =>
    rw [concatenate_zero, concatenate_zero]
    exact refl (Path.refl _)
  | succ n ih =>
    rw [concatenate_succ, concatenate_succ]
    exact hcomp (ih _ _ _ (fun k ↦ H k.castSucc)) (H (last n))

/-- Given a path `γ` and a sequence `p` of `n + 1` points in `[0, 1]`, there is a natural homotopy
between the concatenation of paths `γ.subpath (p k) (p (k + 1))`, and `γ.subpath (p 0) (p n)`. -/
def concatenateSubpath {a b : X} (γ : Path a b) (p : Fin (n + 1) → I) : Homotopy
    (concatenate (γ ∘ p) (fun k ↦ γ.subpath (p k.castSucc) (p k.succ)))
    (γ.subpath (p 0) (p (last n))) := by
  induction n with
  | zero =>
    simp only [concatenate_zero, reduceLast, subpath_self]
    exact refl _
  | succ n ih =>
    rw [concatenate_succ]
    exact trans ((ih (p ∘ castSucc)).hcomp (refl _)) (subpathTransSubpath γ _ _ _)

end Homotopy

namespace Homotopic

/-- Alternative to `Path.Homotopy.concatenateHcomp` in terms of `Path.Homotopic`. -/
theorem concatenate_hcomp (p : Fin (n + 1) → X) (F G : ∀ k : Fin n, Path (p k.castSucc) (p k.succ))
    (h : ∀ k, (F k).Homotopic (G k)) : Homotopic (concatenate p F) (concatenate p G) :=
  ⟨Homotopy.concatenateHcomp p F G (fun k ↦ (h k).some)⟩

/-- Alternative to `Path.Homotopy.concatenateSubpath` in terms of `Path.Homotopic`. -/
@[simp]
theorem concatenate_subpath {a b : X} (γ : Path a b) (p : Fin (n + 1) → I) : Homotopic
    (concatenate (γ ∘ p) (fun k ↦ γ.subpath (p k.castSucc) (p k.succ)))
    (γ.subpath (p 0) (p (last n))) :=
  ⟨Homotopy.concatenateSubpath γ p⟩

end Path.Homotopic

end
