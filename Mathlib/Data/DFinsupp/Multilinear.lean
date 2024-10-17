/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Data.DFinsupp.Basic

/-!
# Interactions between finitely-supported functions and multilinear maps
-/

universe uι uκ uR uM uN
variable {ι : Type uι} {κ : ι → Type uκ}
variable {R : Type uR} {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

variable [DecidableEq ι] [Fintype ι] [Semiring R]
variable [∀ i k, AddCommMonoid (M i k)] [∀ i k, Module R (M i k)]
variable [∀ p, AddCommMonoid (N p)] [∀ p, Module R (N p)]

namespace DFinsupp

/--
Given a family of indices `κ` and a multilinear map `f p` for each way `p` to select one index from
each family, map a family of finitely-supported functions `x` into a finitely-supported function
from each selection.

Strictly this doesn't need multilinearity, only the fact that `f p m = 0` whenever `m i = 0` for
some `i`.
-/
@[simps toFun]
def piMultilinear
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
    (x : ∀ i, Π₀ j : κ i, M i j) :
    Π₀ t : Π i, κ i, N t where
  toFun p := f p (fun i => x _ _)
  support' := (Quotient.finChoice (S := _) fun i => (x i).support').recOnSubsingleton fun s =>
    Trunc.mk ⟨
      Finset.univ.val.pi (fun i ↦ (s i).val) |>.map fun f i => f i (Finset.mem_univ _),
      fun p => by
        simp only [Multiset.mem_map, Multiset.mem_pi, Finset.mem_val,
          Finset.mem_univ, forall_true_left]
        simp_rw [or_iff_not_imp_right]
        intro h
        push_neg at h
        refine ⟨fun i _ => p i, fun i => (s i).prop _ |>.resolve_right ?_, rfl⟩
        exact mt ((f p).map_coord_zero (m := fun i => x i _) i) h⟩

theorem support_piMultilinear_subset
    [∀ i, DecidableEq (κ i)]
    [∀ i j, (x : M i j) → Decidable (x ≠ 0)] [∀ i, (x : N i) → Decidable (x ≠ 0)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
    (x : ∀ i, Π₀ j : κ i, M i j) :
    (piMultilinear f x).support ⊆ Fintype.piFinset fun i => (x i).support := by
  intro p hp
  simp only [mem_support_toFun, piMultilinear_toFun, ne_eq, Fintype.mem_piFinset] at hp ⊢
  intro i
  exact mt ((f p).map_coord_zero (m := fun i => x i _) i) hp

@[simp]
theorem piMultilinear_single
    [∀ i, DecidableEq (κ i)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
    (p : ∀ i, κ i) (m : ∀ i, M i (p i)) :
    piMultilinear f (fun i => .single (p i) (m i)) = single p (f p m) := by
  ext q
  simp [piMultilinear_toFun]
  obtain rfl | hpq := eq_or_ne p q
  · simp
  · rw [dif_neg hpq]
    rw [Function.ne_iff] at hpq
    obtain ⟨i, h⟩ := hpq
    apply (f q).map_coord_zero i
    rw [dif_neg h]

end DFinsupp
