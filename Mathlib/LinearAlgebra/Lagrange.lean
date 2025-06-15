/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Wrenna Robson
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Lagrange interpolation

## Main definitions
* In everything that follows, `s : Finset ι` is a finite set of indexes, with `v : ι → F` an
  indexing of the field over some type. We call the image of v on s the interpolation nodes,
  though strictly unique nodes are only defined when v is injective on s.
* `Lagrange.basisDivisor x y`, with `x y : F`. These are the normalised irreducible factors of
  the Lagrange basis polynomials. They evaluate to `1` at `x` and `0` at `y` when `x` and `y`
  are distinct.
* `Lagrange.basis v i` with `i : ι`: the Lagrange basis polynomial that evaluates to `1` at `v i`
  and `0` at `v j` for `i ≠ j`.
* `Lagrange.interpolate v r` where `r : ι → F` is a function from the fintype to the field: the
  Lagrange interpolant that evaluates to `r i` at `x i` for all `i : ι`. The `r i` are the _values_
  associated with the _nodes_`x i`.
-/


open Polynomial

section PolynomialDetermination

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] {f g : R[X]}

section Finset

open Function Fintype
open scoped Finset

variable (s : Finset R)

theorem eq_zero_of_degree_lt_of_eval_finset_eq_zero (degree_f_lt : f.degree < #s)
    (eval_f : ∀ x ∈ s, f.eval x = 0) : f = 0 := by
  rw [← mem_degreeLT] at degree_f_lt
  simp_rw [eval_eq_sum_degreeLTEquiv degree_f_lt] at eval_f
  rw [← degreeLTEquiv_eq_zero_iff_eq_zero degree_f_lt]
  exact
    Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
      (Injective.comp (Embedding.subtype _).inj' (equivFinOfCardEq (card_coe _)).symm.injective)
      fun _ => eval_f _ (Finset.coe_mem _)

theorem eq_of_degree_sub_lt_of_eval_finset_eq (degree_fg_lt : (f - g).degree < #s)
    (eval_fg : ∀ x ∈ s, f.eval x = g.eval x) : f = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_degree_lt_of_eval_finset_eq_zero _ degree_fg_lt ?_
  simp_rw [eval_sub, sub_eq_zero]
  exact eval_fg

theorem eq_of_degrees_lt_of_eval_finset_eq (degree_f_lt : f.degree < #s)
    (degree_g_lt : g.degree < #s) (eval_fg : ∀ x ∈ s, f.eval x = g.eval x) : f = g := by
  rw [← mem_degreeLT] at degree_f_lt degree_g_lt
  refine eq_of_degree_sub_lt_of_eval_finset_eq _ ?_ eval_fg
  rw [← mem_degreeLT]; exact Submodule.sub_mem _ degree_f_lt degree_g_lt

/--
Two polynomials, with the same degree and leading coefficient, which have the same evaluation
on a set of distinct values with cardinality equal to the degree, are equal.
-/
theorem eq_of_degree_le_of_eval_finset_eq
    (h_deg_le : f.degree ≤ #s)
    (h_deg_eq : f.degree = g.degree)
    (hlc : f.leadingCoeff = g.leadingCoeff)
    (h_eval : ∀ x ∈ s, f.eval x = g.eval x) :
    f = g := by
  rcases eq_or_ne f 0 with rfl | hf
  · rwa [degree_zero, eq_comm, degree_eq_bot, eq_comm] at h_deg_eq
  · exact eq_of_degree_sub_lt_of_eval_finset_eq s
      (lt_of_lt_of_le (degree_sub_lt h_deg_eq hf hlc) h_deg_le) h_eval

end Finset

section Indexed

open Finset

variable {ι : Type*} {v : ι → R} (s : Finset ι)

theorem eq_zero_of_degree_lt_of_eval_index_eq_zero (hvs : Set.InjOn v s)
    (degree_f_lt : f.degree < #s) (eval_f : ∀ i ∈ s, f.eval (v i) = 0) : f = 0 := by
  classical
    rw [← card_image_of_injOn hvs] at degree_f_lt
    refine eq_zero_of_degree_lt_of_eval_finset_eq_zero _ degree_f_lt ?_
    intro x hx
    rcases mem_image.mp hx with ⟨_, hj, rfl⟩
    exact eval_f _ hj

theorem eq_of_degree_sub_lt_of_eval_index_eq (hvs : Set.InjOn v s)
    (degree_fg_lt : (f - g).degree < #s) (eval_fg : ∀ i ∈ s, f.eval (v i) = g.eval (v i)) :
    f = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_degree_lt_of_eval_index_eq_zero _ hvs degree_fg_lt ?_
  simp_rw [eval_sub, sub_eq_zero]
  exact eval_fg

theorem eq_of_degrees_lt_of_eval_index_eq (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s)
    (degree_g_lt : g.degree < #s) (eval_fg : ∀ i ∈ s, f.eval (v i) = g.eval (v i)) : f = g := by
  refine eq_of_degree_sub_lt_of_eval_index_eq _ hvs ?_ eval_fg
  rw [← mem_degreeLT] at degree_f_lt degree_g_lt ⊢
  exact Submodule.sub_mem _ degree_f_lt degree_g_lt

theorem eq_of_degree_le_of_eval_index_eq (hvs : Set.InjOn v s)
    (h_deg_le : f.degree ≤ #s)
    (h_deg_eq : f.degree = g.degree)
    (hlc : f.leadingCoeff = g.leadingCoeff)
    (h_eval : ∀ i ∈ s, f.eval (v i) = g.eval (v i)) : f = g := by
  rcases eq_or_ne f 0 with rfl | hf
  · rwa [degree_zero, eq_comm, degree_eq_bot, eq_comm] at h_deg_eq
  · exact eq_of_degree_sub_lt_of_eval_index_eq s hvs
      (lt_of_lt_of_le (degree_sub_lt h_deg_eq hf hlc) h_deg_le)
      h_eval

end Indexed

end Polynomial

end PolynomialDetermination

noncomputable section

namespace Lagrange

open Polynomial

section BasisDivisor
variable {F : Type*} [Field F]
variable {x y : F}

/-- `basisDivisor x y` is the unique linear or constant polynomial such that
when evaluated at `x` it gives `1` and `y` it gives `0` (where when `x = y` it is identically `0`).
Such polynomials are the building blocks for the Lagrange interpolants. -/
def basisDivisor (x y : F) : F[X] :=
  C (x - y)⁻¹ * (X - C y)

theorem basisDivisor_self : basisDivisor x x = 0 := by
  simp only [basisDivisor, sub_self, inv_zero, map_zero, zero_mul]

theorem basisDivisor_inj (hxy : basisDivisor x y = 0) : x = y := by
  simp_rw [basisDivisor, mul_eq_zero, X_sub_C_ne_zero, or_false, C_eq_zero, inv_eq_zero,
    sub_eq_zero] at hxy
  exact hxy

@[simp]
theorem basisDivisor_eq_zero_iff : basisDivisor x y = 0 ↔ x = y :=
  ⟨basisDivisor_inj, fun H => H ▸ basisDivisor_self⟩

theorem basisDivisor_ne_zero_iff : basisDivisor x y ≠ 0 ↔ x ≠ y := by
  rw [Ne, basisDivisor_eq_zero_iff]

theorem degree_basisDivisor_of_ne (hxy : x ≠ y) : (basisDivisor x y).degree = 1 := by
  rw [basisDivisor, degree_mul, degree_X_sub_C, degree_C, zero_add]
  exact inv_ne_zero (sub_ne_zero_of_ne hxy)

@[simp]
theorem degree_basisDivisor_self : (basisDivisor x x).degree = ⊥ := by
  rw [basisDivisor_self, degree_zero]

theorem natDegree_basisDivisor_self : (basisDivisor x x).natDegree = 0 := by
  rw [basisDivisor_self, natDegree_zero]

theorem natDegree_basisDivisor_of_ne (hxy : x ≠ y) : (basisDivisor x y).natDegree = 1 :=
  natDegree_eq_of_degree_eq_some (degree_basisDivisor_of_ne hxy)

@[simp]
theorem eval_basisDivisor_right : eval y (basisDivisor x y) = 0 := by
  simp only [basisDivisor, eval_mul, eval_C, eval_sub, eval_X, sub_self, mul_zero]

theorem eval_basisDivisor_left_of_ne (hxy : x ≠ y) : eval x (basisDivisor x y) = 1 := by
  simp only [basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
  exact inv_mul_cancel₀ (sub_ne_zero_of_ne hxy)

end BasisDivisor

section Basis

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι → F} {i j : ι}

open Finset

/-- Lagrange basis polynomials indexed by `s : Finset ι`, defined at nodes `v i` for a
map `v : ι → F`. For `i, j ∈ s`, `basis s v i` evaluates to 0 at `v j` for `i ≠ j`. When
`v` is injective on `s`, `basis s v i` evaluates to 1 at `v i`. -/
protected def basis (s : Finset ι) (v : ι → F) (i : ι) : F[X] :=
  ∏ j ∈ s.erase i, basisDivisor (v i) (v j)

@[simp]
theorem basis_empty : Lagrange.basis ∅ v i = 1 :=
  rfl

@[simp]
theorem basis_singleton (i : ι) : Lagrange.basis {i} v i = 1 := by
  rw [Lagrange.basis, erase_singleton, prod_empty]

@[simp]
theorem basis_pair_left (hij : i ≠ j) : Lagrange.basis {i, j} v i = basisDivisor (v i) (v j) := by
  simp only [Lagrange.basis, hij, erase_insert_eq_erase, erase_eq_of_notMem, mem_singleton,
    not_false_iff, prod_singleton]

@[simp]
theorem basis_pair_right (hij : i ≠ j) : Lagrange.basis {i, j} v j = basisDivisor (v j) (v i) := by
  rw [pair_comm]
  exact basis_pair_left hij.symm

theorem basis_ne_zero (hvs : Set.InjOn v s) (hi : i ∈ s) : Lagrange.basis s v i ≠ 0 := by
  simp_rw [Lagrange.basis, prod_ne_zero_iff, Ne, mem_erase]
  rintro j ⟨hij, hj⟩
  rw [basisDivisor_eq_zero_iff, hvs.eq_iff hi hj]
  exact hij.symm

@[simp]
theorem eval_basis_self (hvs : Set.InjOn v s) (hi : i ∈ s) :
    (Lagrange.basis s v i).eval (v i) = 1 := by
  rw [Lagrange.basis, eval_prod]
  refine prod_eq_one fun j H => ?_
  rw [eval_basisDivisor_left_of_ne]
  rcases mem_erase.mp H with ⟨hij, hj⟩
  exact mt (hvs hi hj) hij.symm

@[simp]
theorem eval_basis_of_ne (hij : i ≠ j) (hj : j ∈ s) : (Lagrange.basis s v i).eval (v j) = 0 := by
  simp_rw [Lagrange.basis, eval_prod, prod_eq_zero_iff]
  exact ⟨j, ⟨mem_erase.mpr ⟨hij.symm, hj⟩, eval_basisDivisor_right⟩⟩

@[simp]
theorem natDegree_basis (hvs : Set.InjOn v s) (hi : i ∈ s) :
    (Lagrange.basis s v i).natDegree = #s - 1 := by
  have H : ∀ j, j ∈ s.erase i → basisDivisor (v i) (v j) ≠ 0 := by
    simp_rw [Ne, mem_erase, basisDivisor_eq_zero_iff]
    exact fun j ⟨hij₁, hj⟩ hij₂ => hij₁ (hvs hj hi hij₂.symm)
  rw [← card_erase_of_mem hi, card_eq_sum_ones]
  convert natDegree_prod _ _ H using 1
  refine sum_congr rfl fun j hj => (natDegree_basisDivisor_of_ne ?_).symm
  rw [Ne, ← basisDivisor_eq_zero_iff]
  exact H _ hj

theorem degree_basis (hvs : Set.InjOn v s) (hi : i ∈ s) :
    (Lagrange.basis s v i).degree = ↑(#s - 1) := by
  rw [degree_eq_natDegree (basis_ne_zero hvs hi), natDegree_basis hvs hi]

theorem sum_basis (hvs : Set.InjOn v s) (hs : s.Nonempty) :
    ∑ j ∈ s, Lagrange.basis s v j = 1 := by
  refine eq_of_degrees_lt_of_eval_index_eq s hvs (lt_of_le_of_lt (degree_sum_le _ _) ?_) ?_ ?_
  · rw [Nat.cast_withBot, Finset.sup_lt_iff (WithBot.bot_lt_coe #s)]
    intro i hi
    rw [degree_basis hvs hi, Nat.cast_withBot, WithBot.coe_lt_coe]
    exact Nat.pred_lt (card_ne_zero_of_mem hi)
  · rw [degree_one, ← WithBot.coe_zero, Nat.cast_withBot, WithBot.coe_lt_coe]
    exact Nonempty.card_pos hs
  · intro i hi
    rw [eval_finset_sum, eval_one, ← add_sum_erase _ _ hi, eval_basis_self hvs hi,
      add_eq_left]
    refine sum_eq_zero fun j hj => ?_
    rcases mem_erase.mp hj with ⟨hij, _⟩
    rw [eval_basis_of_ne hij hi]

theorem basisDivisor_add_symm {x y : F} (hxy : x ≠ y) :
    basisDivisor x y + basisDivisor y x = 1 := by
  classical
  rw [← sum_basis Function.injective_id.injOn ⟨x, mem_insert_self _ {y}⟩,
    sum_insert (notMem_singleton.mpr hxy), sum_singleton, basis_pair_left hxy,
    basis_pair_right hxy, id, id]

end Basis

section Interpolate

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s t : Finset ι} {i j : ι} {v : ι → F} (r r' : ι → F)

open Finset

/-- Lagrange interpolation: given a finset `s : Finset ι`, a nodal map `v : ι → F` injective on
`s` and a value function `r : ι → F`, `interpolate s v r` is the unique
polynomial of degree `< #s` that takes value `r i` on `v i` for all `i` in `s`. -/
@[simps]
def interpolate (s : Finset ι) (v : ι → F) : (ι → F) →ₗ[F] F[X] where
  toFun r := ∑ i ∈ s, C (r i) * Lagrange.basis s v i
  map_add' f g := by
    simp_rw [← Finset.sum_add_distrib]
    have h : (fun x => C (f x) * Lagrange.basis s v x + C (g x) * Lagrange.basis s v x) =
    (fun x => C ((f + g) x) * Lagrange.basis s v x) := by
      simp_rw [← add_mul, ← C_add, Pi.add_apply]
    rw [h]
  map_smul' c f := by
    simp_rw [Finset.smul_sum, C_mul', smul_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]

theorem interpolate_empty : interpolate ∅ v r = 0 := by rw [interpolate_apply, sum_empty]

theorem interpolate_singleton : interpolate {i} v r = C (r i) := by
  rw [interpolate_apply, sum_singleton, basis_singleton, mul_one]

theorem interpolate_one (hvs : Set.InjOn v s) (hs : s.Nonempty) : interpolate s v 1 = 1 := by
  simp_rw [interpolate_apply, Pi.one_apply, map_one, one_mul]
  exact sum_basis hvs hs

theorem eval_interpolate_at_node (hvs : Set.InjOn v s) (hi : i ∈ s) :
    eval (v i) (interpolate s v r) = r i := by
  rw [interpolate_apply, eval_finset_sum, ← add_sum_erase _ _ hi]
  simp_rw [eval_mul, eval_C, eval_basis_self hvs hi, mul_one, add_eq_left]
  refine sum_eq_zero fun j H => ?_
  rw [eval_basis_of_ne (mem_erase.mp H).1 hi, mul_zero]

theorem degree_interpolate_le (hvs : Set.InjOn v s) :
    (interpolate s v r).degree ≤ ↑(#s - 1) := by
  refine (degree_sum_le _ _).trans ?_
  rw [Finset.sup_le_iff]
  intro i hi
  rw [degree_mul, degree_basis hvs hi]
  by_cases hr : r i = 0
  · simpa only [hr, map_zero, degree_zero, WithBot.bot_add] using bot_le
  · rw [degree_C hr, zero_add]

theorem degree_interpolate_lt (hvs : Set.InjOn v s) : (interpolate s v r).degree < #s := by
  rw [Nat.cast_withBot]
  rcases eq_empty_or_nonempty s with (rfl | h)
  · rw [interpolate_empty, degree_zero, card_empty]
    exact WithBot.bot_lt_coe _
  · refine lt_of_le_of_lt (degree_interpolate_le _ hvs) ?_
    rw [Nat.cast_withBot, WithBot.coe_lt_coe]
    exact Nat.sub_lt (Nonempty.card_pos h) zero_lt_one

theorem degree_interpolate_erase_lt (hvs : Set.InjOn v s) (hi : i ∈ s) :
    (interpolate (s.erase i) v r).degree < ↑(#s - 1) := by
  rw [← Finset.card_erase_of_mem hi]
  exact degree_interpolate_lt _ (Set.InjOn.mono (coe_subset.mpr (erase_subset _ _)) hvs)

theorem values_eq_on_of_interpolate_eq (hvs : Set.InjOn v s)
    (hrr' : interpolate s v r = interpolate s v r') : ∀ i ∈ s, r i = r' i := fun _ hi => by
  rw [← eval_interpolate_at_node r hvs hi, hrr', eval_interpolate_at_node r' hvs hi]

theorem interpolate_eq_of_values_eq_on (hrr' : ∀ i ∈ s, r i = r' i) :
    interpolate s v r = interpolate s v r' :=
  sum_congr rfl fun i hi => by rw [hrr' _ hi]

theorem interpolate_eq_iff_values_eq_on (hvs : Set.InjOn v s) :
    interpolate s v r = interpolate s v r' ↔ ∀ i ∈ s, r i = r' i :=
  ⟨values_eq_on_of_interpolate_eq _ _ hvs, interpolate_eq_of_values_eq_on _ _⟩

theorem eq_interpolate {f : F[X]} (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s) :
    f = interpolate s v fun i => f.eval (v i) :=
  eq_of_degrees_lt_of_eval_index_eq _ hvs degree_f_lt (degree_interpolate_lt _ hvs) fun _ hi =>
    (eval_interpolate_at_node (fun x ↦ eval (v x) f) hvs hi).symm

theorem eq_interpolate_of_eval_eq {f : F[X]} (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s)
    (eval_f : ∀ i ∈ s, f.eval (v i) = r i) : f = interpolate s v r := by
  rw [eq_interpolate hvs degree_f_lt]
  exact interpolate_eq_of_values_eq_on _ _ eval_f

/-- This is the characteristic property of the interpolation: the interpolation is the
unique polynomial of `degree < Fintype.card ι` which takes the value of the `r i` on the `v i`.
-/
theorem eq_interpolate_iff {f : F[X]} (hvs : Set.InjOn v s) :
    (f.degree < #s ∧ ∀ i ∈ s, eval (v i) f = r i) ↔ f = interpolate s v r := by
  constructor <;> intro h
  · exact eq_interpolate_of_eval_eq _ hvs h.1 h.2
  · rw [h]
    exact ⟨degree_interpolate_lt _ hvs, fun _ hi => eval_interpolate_at_node _ hvs hi⟩

/-- Lagrange interpolation induces isomorphism between functions from `s`
and polynomials of degree less than `Fintype.card ι`. -/
def funEquivDegreeLT (hvs : Set.InjOn v s) : degreeLT F #s ≃ₗ[F] s → F where
  toFun f i := f.1.eval (v i)
  map_add' _ _ := funext fun _ => eval_add
  map_smul' c f := funext <| by simp
  invFun r :=
    ⟨interpolate s v fun x => if hx : x ∈ s then r ⟨x, hx⟩ else 0,
      mem_degreeLT.2 <| degree_interpolate_lt _ hvs⟩
  left_inv := by
    rintro ⟨f, hf⟩
    simp only [Subtype.mk_eq_mk, Subtype.coe_mk, dite_eq_ite]
    rw [mem_degreeLT] at hf
    conv => rhs; rw [eq_interpolate hvs hf]
    exact interpolate_eq_of_values_eq_on _ _ fun _ hi => if_pos hi
  right_inv := by
    intro f
    ext ⟨i, hi⟩
    simp only [Subtype.coe_mk, eval_interpolate_at_node _ hvs hi]
    exact dif_pos hi

theorem interpolate_eq_sum_interpolate_insert_sdiff (hvt : Set.InjOn v t) (hs : s.Nonempty)
    (hst : s ⊆ t) :
    interpolate t v r = ∑ i ∈ s, interpolate (insert i (t \ s)) v r * Lagrange.basis s v i := by
  symm
  refine eq_interpolate_of_eval_eq _ hvt (lt_of_le_of_lt (degree_sum_le _ _) ?_) fun i hi => ?_
  · simp_rw [Nat.cast_withBot, Finset.sup_lt_iff (WithBot.bot_lt_coe #t), degree_mul]
    intro i hi
    have hs : 1 ≤ #s := Nonempty.card_pos ⟨_, hi⟩
    have hst' : #s ≤ #t := card_le_card hst
    have H : #t = 1 + (#t - #s) + (#s - 1) := by
      rw [add_assoc, tsub_add_tsub_cancel hst' hs, ← add_tsub_assoc_of_le (hs.trans hst'),
        Nat.succ_add_sub_one, zero_add]
    rw [degree_basis (Set.InjOn.mono hst hvt) hi, H, WithBot.coe_add, Nat.cast_withBot,
      WithBot.add_lt_add_iff_right (@WithBot.coe_ne_bot _ (#s - 1))]
    convert degree_interpolate_lt _
        (hvt.mono (coe_subset.mpr (insert_subset_iff.mpr ⟨hst hi, sdiff_subset⟩)))
    rw [card_insert_of_notMem (notMem_sdiff_of_mem_right hi), card_sdiff hst, add_comm]
  · simp_rw [eval_finset_sum, eval_mul]
    by_cases hi' : i ∈ s
    · rw [← add_sum_erase _ _ hi', eval_basis_self (hvt.mono hst) hi',
        eval_interpolate_at_node _
          (hvt.mono (coe_subset.mpr (insert_subset_iff.mpr ⟨hi, sdiff_subset⟩)))
          (mem_insert_self _ _),
        mul_one, add_eq_left]
      refine sum_eq_zero fun j hj => ?_
      rcases mem_erase.mp hj with ⟨hij, _⟩
      rw [eval_basis_of_ne hij hi', mul_zero]
    · have H : (∑ j ∈ s, eval (v i) (Lagrange.basis s v j)) = 1 := by
        rw [← eval_finset_sum, sum_basis (hvt.mono hst) hs, eval_one]
      rw [← mul_one (r i), ← H, mul_sum]
      refine sum_congr rfl fun j hj => ?_
      congr
      exact
        eval_interpolate_at_node _ (hvt.mono (insert_subset_iff.mpr ⟨hst hj, sdiff_subset⟩))
          (mem_insert.mpr (Or.inr (mem_sdiff.mpr ⟨hi, hi'⟩)))

theorem interpolate_eq_add_interpolate_erase (hvs : Set.InjOn v s) (hi : i ∈ s) (hj : j ∈ s)
    (hij : i ≠ j) :
    interpolate s v r =
      interpolate (s.erase j) v r * basisDivisor (v i) (v j) +
        interpolate (s.erase i) v r * basisDivisor (v j) (v i) := by
  rw [interpolate_eq_sum_interpolate_insert_sdiff _ hvs ⟨i, mem_insert_self i {j}⟩ _,
    sum_insert (notMem_singleton.mpr hij), sum_singleton, basis_pair_left hij,
    basis_pair_right hij, sdiff_insert_insert_of_mem_of_notMem hi (notMem_singleton.mpr hij),
    sdiff_singleton_eq_erase, pair_comm,
    sdiff_insert_insert_of_mem_of_notMem hj (notMem_singleton.mpr hij.symm),
    sdiff_singleton_eq_erase]
  exact insert_subset_iff.mpr ⟨hi, singleton_subset_iff.mpr hj⟩

end Interpolate

section Nodal

variable {R : Type*} [CommRing R] {ι : Type*}
variable {s : Finset ι} {v : ι → R}

open Finset Polynomial

/-- `nodal s v` is the unique monic polynomial whose roots are the nodes defined by `v` and `s`.

That is, the roots of `nodal s v` are exactly the image of `v` on `s`,
with appropriate multiplicity.

We can use `nodal` to define the barycentric forms of the evaluated interpolant.
-/
def nodal (s : Finset ι) (v : ι → R) : R[X] :=
  ∏ i ∈ s, (X - C (v i))

theorem nodal_eq (s : Finset ι) (v : ι → R) : nodal s v = ∏ i ∈ s, (X - C (v i)) :=
  rfl

@[simp]
theorem nodal_empty : nodal ∅ v = 1 := by
  rfl

@[simp]
theorem natDegree_nodal [Nontrivial R] : (nodal s v).natDegree = #s := by
  simp_rw [nodal, natDegree_prod_of_monic (h := fun i _ => monic_X_sub_C (v i)),
    natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one]

theorem nodal_ne_zero [Nontrivial R] : nodal s v ≠ 0 := by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · exact one_ne_zero
  · apply ne_zero_of_natDegree_gt (n := 0)
    simp only [natDegree_nodal, h.card_pos]

@[simp]
theorem degree_nodal [Nontrivial R] : (nodal s v).degree = #s := by
  simp_rw [degree_eq_natDegree nodal_ne_zero, natDegree_nodal]

theorem nodal_monic : (nodal s v).Monic :=
  monic_prod_of_monic s (fun i ↦ X - C (v i)) fun i _ ↦ monic_X_sub_C (v i)

theorem eval_nodal {x : R} : (nodal s v).eval x = ∏ i ∈ s, (x - v i) := by
  simp_rw [nodal, eval_prod, eval_sub, eval_X, eval_C]

theorem eval_nodal_at_node {i : ι} (hi : i ∈ s) : eval (v i) (nodal s v) = 0 := by
  rw [eval_nodal]
  exact s.prod_eq_zero hi (sub_self (v i))

theorem eval_nodal_not_at_node [Nontrivial R] [NoZeroDivisors R] {x : R}
    (hx : ∀ i ∈ s, x ≠ v i) : eval x (nodal s v) ≠ 0 := by
  simp_rw [nodal, eval_prod, prod_ne_zero_iff, eval_sub, eval_X, eval_C, sub_ne_zero]
  exact hx

theorem nodal_eq_mul_nodal_erase [DecidableEq ι] {i : ι} (hi : i ∈ s) :
    nodal s v = (X - C (v i)) * nodal (s.erase i) v := by
    simp_rw [nodal, Finset.mul_prod_erase _ (fun x => X - C (v x)) hi]

theorem X_sub_C_dvd_nodal (v : ι → R) {i : ι} (hi : i ∈ s) : X - C (v i) ∣ nodal s v := by
  classical
  exact ⟨nodal (s.erase i) v, nodal_eq_mul_nodal_erase hi⟩

theorem nodal_insert_eq_nodal [DecidableEq ι] {i : ι} (hi : i ∉ s) :
    nodal (insert i s) v = (X - C (v i)) * nodal s v := by
  simp_rw [nodal, prod_insert hi]

theorem derivative_nodal [DecidableEq ι] :
    derivative (nodal s v) = ∑ i ∈ s, nodal (s.erase i) v := by
  refine s.induction_on ?_ fun i t hit IH => ?_
  · rw [nodal_empty, derivative_one, sum_empty]
  · rw [nodal_insert_eq_nodal hit, derivative_mul, IH, derivative_sub, derivative_X, derivative_C,
      sub_zero, one_mul, sum_insert hit, mul_sum, erase_insert hit, add_right_inj]
    refine sum_congr rfl fun j hjt => ?_
    rw [t.erase_insert_of_ne (ne_of_mem_of_not_mem hjt hit).symm,
      nodal_insert_eq_nodal (mem_of_mem_erase.mt hit)]

theorem eval_nodal_derivative_eval_node_eq [DecidableEq ι] {i : ι} (hi : i ∈ s) :
    eval (v i) (derivative (nodal s v)) = eval (v i) (nodal (s.erase i) v) := by
  rw [derivative_nodal, eval_finset_sum, ← add_sum_erase _ _ hi, add_eq_left]
  exact sum_eq_zero fun j hj => (eval_nodal_at_node (mem_erase.mpr ⟨(mem_erase.mp hj).1.symm, hi⟩))

/-- The vanishing polynomial on a multiplicative subgroup is of the form X ^ n - 1. -/
@[simp] theorem nodal_subgroup_eq_X_pow_card_sub_one [IsDomain R]
  (G : Subgroup Rˣ) [Fintype G] :
  nodal (G : Set Rˣ).toFinset ((↑) : Rˣ → R) = X ^ (Fintype.card G) - 1 := by
  have h : degree (1 : R[X]) < degree ((X : R[X]) ^ Fintype.card G) := by simp [Fintype.card_pos]
  apply eq_of_degree_le_of_eval_index_eq (v := ((↑) : Rˣ → R)) (G : Set Rˣ).toFinset
  · exact Set.injOn_of_injective Units.ext
  · simp
  · rw [degree_sub_eq_left_of_degree_lt h, degree_nodal, Set.toFinset_card, degree_pow, degree_X,
      nsmul_eq_mul, mul_one, Nat.cast_inj]
    exact rfl
  · rw [nodal_monic, leadingCoeff_sub_of_degree_lt h, monic_X_pow]
  · intros i hi
    rw [eval_nodal_at_node hi]
    replace hi : i ∈ G := by simpa using hi
    obtain ⟨g, rfl⟩ : ∃ g : G, g.val = i := ⟨⟨i, hi⟩, rfl⟩
    simp [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow G]

end Nodal

section NodalWeight

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι → F} {i : ι}

open Finset

/-- This defines the nodal weight for a given set of node indexes and node mapping function `v`. -/
def nodalWeight (s : Finset ι) (v : ι → F) (i : ι) :=
  ∏ j ∈ s.erase i, (v i - v j)⁻¹

theorem nodalWeight_eq_eval_nodal_erase_inv :
    nodalWeight s v i = (eval (v i) (nodal (s.erase i) v))⁻¹ := by
  rw [eval_nodal, nodalWeight, prod_inv_distrib]

theorem nodal_erase_eq_nodal_div (hi : i ∈ s) :
    nodal (s.erase i) v = nodal s v / (X - C (v i)) := by
  rw [nodal_eq_mul_nodal_erase hi, mul_div_cancel_left₀]
  exact X_sub_C_ne_zero _

theorem nodalWeight_eq_eval_nodal_derative (hi : i ∈ s) :
    nodalWeight s v i = (eval (v i) (Polynomial.derivative (nodal s v)))⁻¹ := by
  rw [eval_nodal_derivative_eval_node_eq hi, nodalWeight_eq_eval_nodal_erase_inv]

theorem nodalWeight_ne_zero (hvs : Set.InjOn v s) (hi : i ∈ s) : nodalWeight s v i ≠ 0 := by
  rw [nodalWeight, prod_ne_zero_iff]
  intro j hj
  rcases mem_erase.mp hj with ⟨hij, hj⟩
  exact inv_ne_zero (sub_ne_zero_of_ne (mt (hvs.eq_iff hi hj).mp hij.symm))

end NodalWeight

section LagrangeBarycentric

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι → F} (r : ι → F) {i : ι} {x : F}

open Finset

theorem basis_eq_prod_sub_inv_mul_nodal_div (hi : i ∈ s) :
    Lagrange.basis s v i = C (nodalWeight s v i) * (nodal s v / (X - C (v i))) := by
  simp_rw [Lagrange.basis, basisDivisor, nodalWeight, prod_mul_distrib, map_prod, ←
    nodal_erase_eq_nodal_div hi, nodal]

theorem eval_basis_not_at_node (hi : i ∈ s) (hxi : x ≠ v i) :
    eval x (Lagrange.basis s v i) = eval x (nodal s v) * (nodalWeight s v i * (x - v i)⁻¹) := by
  rw [mul_comm, basis_eq_prod_sub_inv_mul_nodal_div hi, eval_mul, eval_C, ←
    nodal_erase_eq_nodal_div hi, eval_nodal, eval_nodal, mul_assoc, ← mul_prod_erase _ _ hi, ←
    mul_assoc (x - v i)⁻¹, inv_mul_cancel₀ (sub_ne_zero_of_ne hxi), one_mul]

theorem interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C :
    interpolate s v r = ∑ i ∈ s, C (nodalWeight s v i) * (nodal s v / (X - C (v i))) * C (r i) :=
  sum_congr rfl fun j hj => by rw [mul_comm, basis_eq_prod_sub_inv_mul_nodal_div hj]

/-- This is the first barycentric form of the Lagrange interpolant. -/
theorem eval_interpolate_not_at_node (hx : ∀ i ∈ s, x ≠ v i) :
    eval x (interpolate s v r) =
      eval x (nodal s v) * ∑ i ∈ s, nodalWeight s v i * (x - v i)⁻¹ * r i := by
  simp_rw [interpolate_apply, mul_sum, eval_finset_sum, eval_mul, eval_C]
  refine sum_congr rfl fun i hi => ?_
  rw [← mul_assoc, mul_comm, eval_basis_not_at_node hi (hx _ hi)]

theorem sum_nodalWeight_mul_inv_sub_ne_zero (hvs : Set.InjOn v s) (hx : ∀ i ∈ s, x ≠ v i)
    (hs : s.Nonempty) : (∑ i ∈ s, nodalWeight s v i * (x - v i)⁻¹) ≠ 0 :=
  @right_ne_zero_of_mul_eq_one _ _ _ (eval x (nodal s v)) _ <| by
    simpa only [Pi.one_apply, interpolate_one hvs hs, eval_one, mul_one] using
      (eval_interpolate_not_at_node 1 hx).symm

/-- This is the second barycentric form of the Lagrange interpolant. -/
theorem eval_interpolate_not_at_node' (hvs : Set.InjOn v s) (hs : s.Nonempty)
    (hx : ∀ i ∈ s, x ≠ v i) :
    eval x (interpolate s v r) =
      (∑ i ∈ s, nodalWeight s v i * (x - v i)⁻¹ * r i) /
        ∑ i ∈ s, nodalWeight s v i * (x - v i)⁻¹ := by
  rw [← div_one (eval x (interpolate s v r)), ← @eval_one _ _ x, ← interpolate_one hvs hs,
    eval_interpolate_not_at_node r hx, eval_interpolate_not_at_node 1 hx]
  simp only [mul_div_mul_left _ _ (eval_nodal_not_at_node hx), Pi.one_apply, mul_one]

end LagrangeBarycentric

end Lagrange
