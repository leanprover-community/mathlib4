/-
Copyright (c) 2024 Thomas Lanard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Inna Capdeboscq, Johan Commelin, Thomas Lanard, Peiran Wu
-/
module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.RingTheory.ZMod.LocalRing
public import Mathlib.Data.ZMod.QuotientRing
/-!
# Cardinal of the general linear group over finite rings

This file computes the cardinal of the general linear group over finite rings.

## Main statements

* `card_linearIndependent` gives the cardinal of the set of linearly independent vectors over a
  finite-dimensional vector space over a finite field.
* `Matrix.card_GL_field` gives the cardinal of the general linear group over a finite field.
* `Matrix.card_GL_eq_of_isLocalHom`: for a surjective local ring hom `f : R →+* S`,
  `Nat.card (GL (Fin n) R) = Nat.card (RingHom.ker f) ^ (n ^ 2) * Nat.card (GL (Fin n) S)`.
* `Matrix.card_GL_zmod` gives the cardinal of the general linear group over `ZMod N`.
-/

@[expose] public section

open LinearMap Module

section LinearIndependent

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
variable [Fintype K] [Finite V]

local notation "q" => Fintype.card K
local notation "n" => Module.finrank K V

attribute [local instance] Fintype.ofFinite in
open Fintype in
/-- The cardinal of the set of linearly independent vectors over a finite-dimensional vector space
over a finite field. -/
theorem card_linearIndependent {k : ℕ} (hk : k ≤ n) :
    Nat.card { s : Fin k → V // LinearIndependent K s } =
      ∏ i : Fin k, (q ^ n - q ^ i.val) := by
  rw [Nat.card_eq_fintype_card]
  induction k with
  | zero =>
      have : Unique { s : Fin 0 → V // (⊤ : Submodule K (Fin 0 →₀ K)) = ⊥ } :=
        uniqueOfSubsingleton ⟨0, Subsingleton.elim ..⟩
      simp_rw [linearIndependent_iff_ker, Finsupp.linearCombination_fin_zero, ker_zero,
        Finset.univ_eq_empty, Finset.prod_empty, card_unique]
  | succ k ih =>
      have (s : { s : Fin k → V // LinearIndependent K s }) :
          card ((Submodule.span K (Set.range (s : Fin k → V)))ᶜ : Set (V)) =
          (q) ^ n - (q) ^ k := by
            rw [card_compl_set, Module.card_eq_pow_finrank (K := K)
            (V := ((Submodule.span K (Set.range (s : Fin k → V))) : Set (V)))]
            simp only [SetLike.coe_sort_coe, finrank_span_eq_card s.2, card_fin]
            rw [Module.card_eq_pow_finrank (K := K)]
      simp [card_congr (equiv_linearIndependent k), sum_congr _ _ this, ih (Nat.le_of_succ_le hk),
        mul_comm, Fin.prod_univ_succAbove _ (Fin.last k), -Set.fintypeCard_eq_ncard]

end LinearIndependent

namespace Matrix

section SpecialLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] {R : Type*} [CommRing R]

/-- The cardinal of the special linear group times the cardinal of the unit group is the
cardinal of the general linear group. -/
theorem card_SL_mul_card_units :
    Nat.card (SpecialLinearGroup n R) * Nat.card Rˣ = Nat.card (GL n R) := by
  simpa [Subgroup.index_ker, MonoidHom.range_eq_top.mpr GeneralLinearGroup.det_surjective,
    Subgroup.card_top, Nat.card_congr SpecialLinearGroup.toGLKerEquiv.toEquiv]
    using Subgroup.card_mul_index (GeneralLinearGroup.det : GL n R →* Rˣ).ker

/-- The cardinal of the special linear group over a commutative ring with finitely many
units. -/
theorem card_SL [Finite Rˣ] :
    Nat.card (SpecialLinearGroup n R) = Nat.card (GL n R) / Nat.card Rˣ :=
  Nat.eq_div_of_mul_eq_right Nat.card_pos.ne'
    (by simpa [mul_comm] using card_SL_mul_card_units)

end SpecialLinearGroup

/-- The cardinal of a matrix. -/
theorem card_matrix {m n α} [Finite m] [Finite n] :
    Nat.card (Matrix m n α) = Nat.card α ^ (Nat.card n * Nat.card m) := by
  simp [Matrix, Nat.card_fun, ← pow_mul]

theorem enatCard_matrix {m n α} :
    ENat.card (Matrix m n α) = ENat.card α ^ (ENat.card n * ENat.card m) := by
  simp [Matrix, ENat.card_fun, ←ENat.epow_mul]

section field

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]

local notation "q" => Fintype.card 𝔽

variable (n : ℕ)

/-- Equivalence between `GL n F` and `n` vectors of length `n` that are linearly independent. Given
by sending a matrix to its columns. -/
noncomputable def equiv_GL_linearindependent :
    GL (Fin n) 𝔽 ≃ { s : Fin n → Fin n → 𝔽 // LinearIndependent 𝔽 s } where
  toFun M := ⟨M.1.col, by
    apply linearIndependent_iff_card_eq_finrank_span.2
    rw [Set.finrank, ← rank_eq_finrank_span_cols, rank_unit]⟩
  invFun M := GeneralLinearGroup.mk'' (transpose (M.1)) <| by
    classical
    let b := basisOfPiSpaceOfLinearIndependent M.2
    have := (Pi.basisFun 𝔽 (Fin n)).invertibleToMatrix b
    rw [← Basis.coePiBasisFun.toMatrix_eq_transpose,
      ← coe_basisOfPiSpaceOfLinearIndependent M.2]
    exact isUnit_det_of_invertible _
  right_inv := by exact congrFun rfl

/-- The cardinal of the general linear group over a finite field. -/
theorem card_GL_field :
    Nat.card (GL (Fin n) 𝔽) = ∏ i : (Fin n), (q ^ n - q ^ (i : ℕ)) := by
  rw [Nat.card_congr (equiv_GL_linearindependent n), card_linearIndependent,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, le_refl]

/-- The cardinal of the special linear group over a finite field. -/
theorem card_SL_field [NeZero n] :
    Nat.card (SpecialLinearGroup (Fin n)  𝔽) = (∏ i : Fin n, (q ^ n - q ^ (i : ℕ))) / (q - 1) := by
  simp [card_SL, card_GL_field, Nat.card_units]

end field

section IsLocalHom

variable {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
  (f : R →+* S) [IsLocalHom f]

theorem GeneralLinearGroup.map_surjective (hf : Function.Surjective f) :
    Function.Surjective (GeneralLinearGroup.map f : GL n R → GL n S) := by
  intro g
  let M := (g : Matrix n n S).map (Function.surjInv hf)
  have hM : M.map f = g := by ext; simp [M, Function.surjInv_eq hf]
  exact ⟨GeneralLinearGroup.mk'' M ((isUnit_map_iff f _).mp (by simp [RingHom.map_det, hM])),
    Units.ext hM⟩

/-- For a local ring hom `f : R →+* S`, the kernel of `GL n R →* GL n S` is in bijection with the
matrices with entries in `RingHom.ker f`, via `g ↦ g - 1`. -/
noncomputable def GeneralLinearGroup.kerMapEquivMatrixKer :
    (map (n := n) f).ker ≃ Matrix n n (RingHom.ker f) where
  toFun g := .of fun i j ↦ ⟨(g.1 - 1 : Matrix n n R) i j, by
    simpa [RingHom.mem_ker, sub_eq_zero, one_apply, apply_ite f]
      using Matrix.ext_iff.mpr (Units.ext_iff.mp (MonoidHom.mem_ker.mp g.2)) i j⟩
  invFun A :=
    have hA : (1 + A.map (↑) : Matrix n n R).map f = 1 := by
      ext i j; simp [one_apply, apply_ite f, RingHom.mem_ker.mp (A i j).2]
    ⟨mk'' _ <| (isUnit_map_iff f _).mp <| by simp [RingHom.map_det, hA], Units.ext hA⟩
  left_inv g := by ext; simp
  right_inv A := by ext; simp

/-- If `f : R →+* S` is surjective and local, then
`Nat.card (GL n R) = Nat.card (RingHom.ker f) ^ (n ^ 2) *  Nat.card (GL n S)`. -/
theorem card_GL_eq_of_isLocalHom (n : ℕ) (hf : Function.Surjective f) :
    Nat.card (GL (Fin n) R) = Nat.card (RingHom.ker f) ^ (n ^ 2) *  Nat.card (GL (Fin n) S) := by
  rw [← Subgroup.card_ker_mul_card_of_surjective (GeneralLinearGroup.map_surjective _ hf),
    Nat.card_congr (GeneralLinearGroup.kerMapEquivMatrixKer _), card_matrix, Nat.card_fin, sq]

end IsLocalHom

section ZMod

/-- The cardinal of the general linear group over `ZMod (p ^ r)`, for `p` prime and `r ≠ 0`. -/
theorem card_GL_zmod_prime_pow {p r n : ℕ} [hp : Fact p.Prime] (hr : r ≠ 0) :
    Nat.card (GL (Fin n) (ZMod (p ^ r))) =
      (∏ i : Fin n, (p ^ n - p ^ (i : ℕ))) * (p ^ (r - 1)) ^ (n ^ 2) := by
  have := ZMod.isLocalHom_castHom_pow (n := p) hr
  let f := ZMod.castHom (dvd_pow_self p hr) (ZMod p)
  have hf : Function.Surjective f := ZMod.castHom_surjective _
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hr
  have hker : Nat.card (RingHom.ker f) = p ^ r := mul_right_cancel₀ hp.out.ne_zero <| by
    simpa [pow_succ] using AddSubgroup.card_ker_mul_card_of_surjective (f := f.toAddMonoidHom) hf
  rw [card_GL_eq_of_isLocalHom f n hf, card_GL_field, ZMod.card, hker, Nat.add_sub_cancel,
    mul_comm]

/-- The cardinal of the general linear group over `ZMod N`, for `N ≠ 0`. -/
theorem card_GL_zmod {N n : ℕ} (hN : N ≠ 0) :
    Nat.card (GL (Fin n) (ZMod N)) = ∏ p ∈ N.primeFactors,
      (∏ i : Fin n, (p ^ n - p ^ (i : ℕ))) * (p ^ (N.factorization p - 1)) ^ (n ^ 2) := by
  rw [Nat.card_congr ((GeneralLinearGroup.mapEquiv (ZMod.equivPi N hN)).trans
    (GeneralLinearGroup.piEquiv _)).toEquiv, Nat.card_pi, ← N.primeFactors.prod_coe_sort]
  exact Fintype.prod_congr _ _ fun ⟨p, hp⟩ ↦
    have := Fact.mk (Nat.prime_of_mem_primeFactors hp)
    card_GL_zmod_prime_pow (Finsupp.mem_support_iff.mp hp)

end ZMod

end Matrix
