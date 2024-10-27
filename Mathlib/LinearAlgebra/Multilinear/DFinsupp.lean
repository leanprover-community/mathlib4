/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Sophie Morel
-/
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Interactions between finitely-supported functions and multilinear maps

This file provides `MultilinearMap.dfinsuppFamily`, which satisfies
`MultilinearMap.dfinsuppFamily f x p = f p (fun i => x i (p i))`.
This is the finitely-supported version of `MultilinearMap.piFamily`.

This is useful because all the intermediate results are bundled:

* `MultilinearMap.dfinsuppFamily f x` is a `DFinsupp` supported by families of indices `p`.
* `MultilinearMap.dfinsuppFamily f` is a `MultilinearMap` operating on finitely-supported functions
  `x`.
* `MultilinearMap.dfinsuppFamilyₗ` is a `LinearMap`, linear in the family of multilinear maps `f`.

-/

universe uι uκ uS uR uM uN
variable {ι : Type uι} {κ : ι → Type uκ}
variable {S : Type uS} {R : Type uR} {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

namespace MultilinearMap

section Semiring

variable [DecidableEq ι] [Fintype ι] [Semiring R]
variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]
variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

/--
Given a family of indices `κ` and a multilinear map `f p` for each way `p` to select one index from
each family, `dfinsuppFamily f` maps a family of finitely-supported functions (one for each domain
`κ i`) into a finitely-supported function from each selection of indices (with domain `Π i, κ i`).

Strictly this doesn't need multilinearity, only the fact that `f p m = 0` whenever `m i = 0` for
some `i`.

This is the `DFinsupp` version of `MultilinearMap.pi'`.
-/
@[simps]
def dfinsuppFamily
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    MultilinearMap R (fun i => Π₀ j : κ i, M i j) (Π₀ t : Π i, κ i, N t) where
  toFun x :=
  { toFun := fun p => f p (fun i => x i (p i))
    support' := (Trunc.finChoice fun i => (x i).support').map fun s => ⟨
      Finset.univ.val.pi (fun i ↦ (s i).val) |>.map fun f i => f i (Finset.mem_univ _),
      fun p => by
        simp only [Multiset.mem_map, Multiset.mem_pi, Finset.mem_val, Finset.mem_univ,
          forall_true_left]
        simp_rw [or_iff_not_imp_right]
        intro h
        push_neg at h
        refine ⟨fun i _ => p i, fun i => (s i).prop _ |>.resolve_right ?_, rfl⟩
        exact mt ((f p).map_coord_zero (m := fun i => x i _) i) h⟩}
  map_add' {dec} m i x y := DFinsupp.ext fun p => by
    cases Subsingleton.elim dec (by infer_instance)
    dsimp
    simp_rw [Function.apply_update (fun i m => m (p i)) m, DFinsupp.add_apply, (f p).map_add]
  map_smul' {dec} m i c x := DFinsupp.ext fun p => by
    cases Subsingleton.elim dec (by infer_instance)
    dsimp
    simp_rw [Function.apply_update (fun i m => m (p i)) m, DFinsupp.smul_apply, (f p).map_smul]

theorem support_dfinsuppFamily_subset
    [∀ i, DecidableEq (κ i)]
    [∀ i j, (x : M i j) → Decidable (x ≠ 0)] [∀ i, (x : N i) → Decidable (x ≠ 0)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
    (x : ∀ i, Π₀ j : κ i, M i j) :
    (dfinsuppFamily f x).support ⊆ Fintype.piFinset fun i => (x i).support := by
  intro p hp
  simp only [DFinsupp.mem_support_toFun, dfinsuppFamily_apply_toFun, ne_eq,
    Fintype.mem_piFinset] at hp ⊢
  intro i
  exact mt ((f p).map_coord_zero (m := fun i => x i _) i) hp

/-- When applied to a family of finitely-supported functions each supported on a single element,
`dfinsuppFamily` is itself supported on a single element, with value equal to the map `f` applied
at that point. -/
@[simp]
theorem dfinsuppFamily_single [∀ i, DecidableEq (κ i)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
    (p : ∀ i, κ i) (m : ∀ i, M i (p i)) :
    dfinsuppFamily f (fun i => .single (p i) (m i)) = DFinsupp.single p (f p m) := by
  ext q
  obtain rfl | hpq := eq_or_ne p q
  · simp
  · rw [DFinsupp.single_eq_of_ne hpq]
    rw [Function.ne_iff] at hpq
    obtain ⟨i, hpqi⟩ := hpq
    apply (f q).map_coord_zero i
    simp_rw [DFinsupp.single_eq_of_ne hpqi]

@[simp]
theorem dfinsuppFamily_compLinearMap_lsingle [∀ i, DecidableEq (κ i)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) (p : ∀ i, κ i) :
    (dfinsuppFamily f).compLinearMap (fun i => DFinsupp.lsingle (p i))
      = (DFinsupp.lsingle p).compMultilinearMap (f p) :=
  MultilinearMap.ext <| dfinsuppFamily_single f p

@[simp]
theorem dfinsuppFamily_zero :
    dfinsuppFamily (0 : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) = 0 := by
  ext; simp

@[simp]
theorem dfinsuppFamily_add (f g : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    dfinsuppFamily (f + g) = dfinsuppFamily f + dfinsuppFamily g := by
  ext; simp

@[simp]
theorem dfinsuppFamily_smul
    [Monoid S] [∀ p, DistribMulAction S (N p)] [∀ p, SMulCommClass R S (N p)]
    (s : S) (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    dfinsuppFamily (s • f) = s • dfinsuppFamily f := by
  ext; simp

end Semiring

section CommSemiring

variable [DecidableEq ι] [Fintype ι] [CommSemiring R]
variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]
variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

/-- `MultilinearMap.dfinsuppFamily` as a linear map. -/
@[simps]
def dfinsuppFamilyₗ :
    (Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
      →ₗ[R] MultilinearMap R (fun i => Π₀ j : κ i, M i j) (Π₀ t : Π i, κ i, N t) where
  toFun := dfinsuppFamily
  map_add' := dfinsuppFamily_add
  map_smul' := dfinsuppFamily_smul

end CommSemiring

end MultilinearMap
