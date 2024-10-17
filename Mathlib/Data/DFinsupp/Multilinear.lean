/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Sophie Morel
-/
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Data.DFinsupp.Basic

/-!
# Interactions between finitely-supported functions and multilinear maps

This file provides `DFinsupp.piMultilinear`.
-/

universe uι uκ uR uM uN
variable {ι : Type uι} {κ : ι → Type uκ}
variable {R : Type uR} {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

variable [DecidableEq ι] [Fintype ι] [Semiring R]
variable [∀ i k, AddCommMonoid (M i k)] [∀ i k, Module R (M i k)]
variable [∀ p, AddCommMonoid (N p)] [∀ p, Module R (N p)]

namespace DFinsupp

omit [Fintype ι] in
/-- This lemma is sufficiently impossible to name that it's easier to just keep it private. -/
private theorem update_aux (m : (i : ι) → Π₀ (j : κ i), M i j)
    (i : ι) (p : (i : ι) → κ i) (x : Π₀ (j : κ i), M i j) :
    (fun k ↦ Function.update m i x k (p k)) =
      Function.update (fun i ↦ (m i) (p i)) i (x (p i)) := by
  ext j
  obtain rfl | hij := eq_or_ne j i <;> simp [*]

/--
Given a family of indices `κ` and a multilinear map `f p` for each way `p` to select one index from
each family, map a family of finitely-supported functions `x` into a finitely-supported function
from each selection.

Strictly this doesn't need multilinearity, only the fact that `f p m = 0` whenever `m i = 0` for
some `i`.
-/
@[simps]
def piMultilinear
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    MultilinearMap R (fun i => Π₀ j : κ i, M i j) (Π₀ t : Π i, κ i, N t) where
  toFun x :=
  { toFun := fun p => f p (fun i => x _ _)
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
          exact mt ((f p).map_coord_zero (m := fun i => x i _) i) h⟩}
  map_add' {inst} m i x y := by
    cases Subsingleton.elim inst (by clear inst; assumption)
    ext p
    dsimp
    simp_rw [update_aux, DFinsupp.add_apply, (f p).map_add]
  map_smul' {inst} m i c x := by
    cases Subsingleton.elim inst (by clear inst; assumption)
    ext p
    dsimp
    simp_rw [update_aux, DFinsupp.smul_apply, (f p).map_smul]

theorem support_piMultilinear_subset
    [∀ i, DecidableEq (κ i)]
    [∀ i j, (x : M i j) → Decidable (x ≠ 0)] [∀ i, (x : N i) → Decidable (x ≠ 0)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
    (x : ∀ i, Π₀ j : κ i, M i j) :
    (piMultilinear f x).support ⊆ Fintype.piFinset fun i => (x i).support := by
  intro p hp
  simp only [mem_support_toFun, piMultilinear_apply_toFun, ne_eq, Fintype.mem_piFinset] at hp ⊢
  intro i
  exact mt ((f p).map_coord_zero (m := fun i => x i _) i) hp

/-- When applied to a family of finitely-supported functions each supported on a single element,
`piMultilinear` is itself supported on a single element, with value equal to the map `f` applied
at that point. -/
@[simp]
theorem piMultilinear_single
    [∀ i, DecidableEq (κ i)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
    (p : ∀ i, κ i) (m : ∀ i, M i (p i)) :
    piMultilinear f (fun i => .single (p i) (m i)) = single p (f p m) := by
  ext q
  obtain rfl | hpq := eq_or_ne p q
  · simp
  · rw [single_eq_of_ne hpq]
    rw [Function.ne_iff] at hpq
    obtain ⟨i, hpqi⟩ := hpq
    apply (f q).map_coord_zero i
    simp_rw [single_eq_of_ne hpqi]

end DFinsupp
