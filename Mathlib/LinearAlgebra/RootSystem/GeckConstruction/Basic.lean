/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!
# Geck's construction of a Lie algebra associated to a root system

This file contains an implementation of Geck's construction of a semisimple Lie algebra from a
reduced crystallographic root system. It follows [Geck](Geck2017) quite closely.

## Main definitions:
* `RootPairing.GeckConstruction.lieAlgebra`: the Geck construction of the Lie algebra associated to
  a root system with distinguished base.
* `RootPairing.GeckConstruction.cartanSubalgebra`: a distinguished subalgebra corresponding to a
  Cartan subalgebra of the Geck construction.
* `RootPairing.GeckConstruction.cartanSubalgebra_le_lieAlgebra`: the distinguished subalgebra is
  contained in the Geck construction.

## Alternative approaches

The are at least three ways to construct a Lie algebra from a root system:
1. As a quotient of a free Lie algebra, using the Serre relations
2. Directly defining the Lie bracket on $H ⊕ K^∣Φ|$
3. The Geck construction

We comment on these as follows:
1. This construction takes just a matrix as input. It yields a semisimple Lie algebra iff the
   matrix is a Cartan matrix but it is quite a lot of work to prove this. On the other hand, it also
   allows construction of Kac-Moody Lie algebras. It has been implemented as `Matrix.ToLieAlgebra`
   but as of May 2025, almost nothing has been proved about it in Mathlib.
2. This construction takes a root system with base as input, together with sufficient additional
   data to determine a collection of extraspecial pairs of roots. The additional data for the
   extraspecial pairs is required to pin down certain signs when defining the Lie bracket. (These
   signs can be interpreted as a set-theoretic splitting of Tits's extension of the Weyl group by
   an elementary 2-group of order $2^l$ where $l$ is the rank.)
3. This construction takes a root system with base as input and is implemented here.

There seems to be no known construction of a Lie algebra from a root system without first choosing
a base: https://mathoverflow.net/questions/495434/

-/

noncomputable section

open Function Set Submodule
open scoped Matrix

attribute [local simp] Matrix.mul_apply Matrix.one_apply Matrix.diagonal_apply

namespace RootPairing.GeckConstruction

variable {ι R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] {b : P.Base}

/-- Part of an `sl₂` triple used in Geck's construction of a Lie algebra from a root system. -/
def h (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  open scoped Classical in
  .fromBlocks 0 0 0 (.diagonal (P.pairingIn ℤ · i))

lemma h_def [DecidableEq ι] (i : b.support) :
    h i = .fromBlocks 0 0 0 (.diagonal (P.pairingIn ℤ · i)) := by
  ext (j | j) (k | k) <;> simp [h, Matrix.diagonal_apply]

lemma h_eq_diagonal [DecidableEq ι] (i : b.support) :
    h i = .diagonal (Sum.elim 0 (P.pairingIn ℤ · i)) := by
  ext (j | j) (k | k) <;> simp [h, Matrix.diagonal_apply]

lemma span_range_h_le_range_diagonal [DecidableEq ι] :
    span R (range h) ≤ LinearMap.range (Matrix.diagonalLinearMap (b.support ⊕ ι) R R) := by
  rw [span_le]
  rintro - ⟨i, rfl⟩
  rw [h_eq_diagonal]
  exact LinearMap.mem_range_self _ _

open Matrix in
@[simp] lemma diagonal_elim_mem_span_h_iff [DecidableEq ι] {d : ι → R} :
    diagonal (Sum.elim 0 d) ∈ span R (range <| h (b := b)) ↔
      d ∈ span R (range <| fun (i : b.support) j ↦ (P.pairingIn ℤ j i : R)) := by
  let g : Matrix ι ι R →ₗ[R] Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
    { toFun := .fromBlocks 0 0 0
      map_add' x y := by ext (i | i) (j | j) <;> simp
      map_smul' t x := by ext (i | i) (j | j) <;> simp }
  have h₀ : Injective (g ∘ diagonalLinearMap ι R R) := fun _ _ hd ↦ funext <| by simpa [g] using hd
  have h₁ {d : ι → R} : diagonal (Sum.elim 0 d) = g (diagonalLinearMap ι R R d) := by
    ext (i | i) (j | j) <;> simp [g]
  have h₂ : range h = g '' (diagonalLinearMap ι R R ''
    (range <| fun (i : b.support) j ↦ (P.pairingIn ℤ j i : R))) := by ext; simp [g, h_def]
  simp_rw [h₁, h₂, span_image, ← map_comp, ← comp_apply (f := g), mem_map, LinearMap.coe_comp,
    h₀.eq_iff, exists_eq_right]

lemma apply_sum_inl_eq_zero_of_mem_span_h
    (i : b.support) (j : b.support ⊕ ι) {x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R}
    (hx : x ∈ span R (range h)) :
    x j (Sum.inl i) = 0 := by
  induction hx using span_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; cases j <;> simp [h]
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul t u _ hu => simp [hu]

lemma lie_h_h [Fintype ι] (i j : b.support) :
    ⁅h i, h j⁆ = 0 := by
  classical
  simpa only [h_eq_diagonal, ← commute_iff_lie_eq] using Matrix.commute_diagonal _ _

variable [Finite ι] [IsDomain R] [CharZero R]

/-- Part of an `sl₂` triple used in Geck's construction of a Lie algebra from a root system. -/
def e (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 0
    (.of fun i' j ↦ if i' = i ∧ j = -i then 1 else 0)
    (.of fun i' j ↦ if i' = i then ↑|b.cartanMatrix i j| else 0)
    (.of fun i' j ↦ if P.root i' = P.root i + P.root j then P.chainBotCoeff i j + 1 else 0)

/-- Part of an `sl₂` triple used in Geck's construction of a Lie algebra from a root system. -/
def f (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 0
    (.of fun i' j ↦ if i' = i ∧ j = i then 1 else 0)
    (.of fun i' j ↦ if i' = -i then ↑|b.cartanMatrix i j| else 0)
    (.of fun i' j ↦ if P.root i' = P.root j - P.root i then P.chainTopCoeff i j + 1 else 0)

variable (b)

/-- An involutive matrix which can transfer results between `RootPairing.GeckConstruction.e` and
`RootPairing.GeckConstruction.f`. -/
def ω :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 1 0 0 <| .of fun i j ↦ if i = -j then 1 else 0

/-- Geck's construction of the Lie algebra associated to a root system with distinguished base.

Note that it is convenient to include `range h` in the Lie span, to make it elementary that it
contains `RootPairing.GeckConstruction.cartanSubalgebra`, and not depend on
`RootPairing.GeckConstruction.lie_e_f_same`. -/
def lieAlgebra [Fintype ι] [DecidableEq ι] :
    LieSubalgebra R (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) :=
  LieSubalgebra.lieSpan R _ (range h ∪ range e ∪ range f)

/-- A distinguished subalgebra corresponding to a Cartan subalgebra of the Geck construction.

See also `RootPairing.GeckConstruction.cartanSubalgebra'`. -/
def cartanSubalgebra [Fintype ι] [DecidableEq ι] :
    LieSubalgebra R (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) where
  __ := Submodule.span R (range h)
  lie_mem' {x y} hx hy := by
    have aux : (∀ u ∈ range (h (b := b)), ∀ v ∈ range (h (b := b)), ⁅u, v⁆ = 0) := by
      rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩; exact lie_h_h i j
    simp only [Submodule.carrier_eq_coe, SetLike.mem_coe, LieSubalgebra.mem_toSubmodule,
      ← LieSubalgebra.coe_lieSpan_eq_span_of_forall_lie_eq_zero (R := R) aux] at hx hy ⊢
    exact LieSubalgebra.lie_mem _ hx hy

/-- A distinguished Cartan subalgebra of the Geck construction. -/
def cartanSubalgebra' [Fintype ι] [DecidableEq ι] :
    LieSubalgebra R (lieAlgebra b) :=
  (cartanSubalgebra b).comap (lieAlgebra b).incl

omit [Finite ι] [IsDomain R] [CharZero R] in
lemma cartanSubalgebra_eq_lieSpan [Fintype ι] [DecidableEq ι] :
    cartanSubalgebra b = LieSubalgebra.lieSpan R _ (range h) := by
  refine le_antisymm LieSubalgebra.submodule_span_le_lieSpan ?_
  rw [LieSubalgebra.lieSpan_le, cartanSubalgebra]
  exact Submodule.subset_span

variable {b}

omit [Finite ι] [IsDomain R] [CharZero R] in
@[simp] lemma h_mem_cartanSubalgebra [Fintype ι] [DecidableEq ι] (i : b.support) :
    h i ∈ cartanSubalgebra b :=
  Submodule.subset_span <| mem_range_self i

@[simp] lemma h_mem_cartanSubalgebra' [Fintype ι] [DecidableEq ι] (i : b.support) (hi) :
    ⟨h i, hi⟩ ∈ cartanSubalgebra' b := by
  simp [cartanSubalgebra']

lemma h_mem_lieAlgebra [Fintype ι] [DecidableEq ι] (i : b.support) :
    h i ∈ lieAlgebra b :=
  LieSubalgebra.subset_lieSpan <| by simp

lemma e_mem_lieAlgebra [Fintype ι] [DecidableEq ι] (i : b.support) :
    e i ∈ lieAlgebra b :=
  LieSubalgebra.subset_lieSpan <| by simp

lemma f_mem_lieAlgebra [Fintype ι] [DecidableEq ι] (i : b.support) :
    f i ∈ lieAlgebra b :=
  LieSubalgebra.subset_lieSpan <| by simp

/-- The element `h i`, as a term of the Cartan subalgebra `cartanSubalgebra' b`. -/
def h' [Fintype ι] [DecidableEq ι] (i : b.support) : cartanSubalgebra' b :=
  ⟨⟨h i, h_mem_lieAlgebra i⟩, h_mem_cartanSubalgebra' i (h_mem_lieAlgebra i)⟩

variable (b) in
@[simp]
lemma span_range_h'_eq_top [Fintype ι] [DecidableEq ι] :
    span R (range h') = (⊤ : Submodule R (cartanSubalgebra' b)) := by
  rw [eq_top_iff]
  rintro ⟨⟨x, -⟩, hx : x ∈ span R (range h)⟩ -
  let g : cartanSubalgebra' b →ₗ[R] Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
    (lieAlgebra b).subtype ∘ₗ (cartanSubalgebra' b).subtype
  suffices x ∈ (span R (range h')).map g by
    rwa [← SetLike.mem_coe, ← (injective_subtype _).mem_set_image,
        ← (injective_subtype _).mem_set_image, ← image_comp]
  rwa [map_span, ← range_comp]

omit [Finite ι] [IsDomain R] [CharZero R] [P.IsCrystallographic] in
@[simp] lemma ω_mul_ω [DecidableEq ι] [Fintype ι] :
    ω b * ω b = 1 := by
  ext (k | k) (l | l) <;>
  simp [ω, -indexNeg_neg]

omit [Finite ι] [IsDomain R] in
lemma ω_mul_h [Fintype ι] (i : b.support) :
    ω b * h i = -h i * ω b := by
  classical
  ext (k | k) (l | l)
  · simp [ω, h]
  · simp [ω, h]
  · simp [ω, h]
  · simp only [ω, h, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₂]
    aesop

lemma ω_mul_e [Fintype ι] (i : b.support) :
    ω b * e i = f i * ω b := by
  letI := P.indexNeg
  classical
  ext (k | k) (l | l)
  · simp [ω, e, f]
  · simp only [ω, e, f, mul_ite, mul_zero, Fintype.sum_sum_type, Matrix.mul_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Finset.sum_ite_eq']
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (by simp_all)]
    simp [← ite_and, and_comm, -indexNeg_neg, neg_eq_iff_eq_neg]
  · simp [ω, e, f]
  · simp only [ω, e, f, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.of_apply, mul_ite, ← neg_eq_iff_eq_neg (a := k)]
    rw [Finset.sum_eq_single_of_mem (-k) (Finset.mem_univ _) (by aesop)]
    simp [neg_eq_iff_eq_neg, sub_eq_add_neg]

lemma ω_mul_f [Fintype ι] (i : b.support) :
    ω b * f i = e i * ω b := by
  classical
  have := congr_arg (· * ω b) (congr_arg (ω b * ·) (ω_mul_e i))
  simp only [← mul_assoc, ω_mul_ω] at this
  simpa [mul_assoc, ω_mul_ω] using this.symm

lemma lie_e_f_mul_ω [Fintype ι] (i j : b.support) :
    ⁅e i, f j⁆ * ω b = -ω b * ⁅e j, f i⁆ := by
  classical
  calc ⁅e i, f j⁆ * ω b = e i * f j * ω b - f j * e i * ω b := by rw [Ring.lie_def, sub_mul]
                      _ = e i * (f j * ω b) - f j * (e i * ω b) := by rw [mul_assoc, mul_assoc]
                      _ = e i * (ω b * e j) - f j * (ω b * f i) := by rw [← ω_mul_e, ← ω_mul_f]
                      _ = (e i * ω b) * e j - (f j * ω b) * f i := by rw [← mul_assoc, ← mul_assoc]
                      _ = (ω b * f i) * e j - (ω b * e j) * f i := by rw [← ω_mul_e, ← ω_mul_f]
                      _ = ω b * (f i * e j) - ω b * (e j * f i) := by rw [mul_assoc, mul_assoc]
                      _ = -ω b * ⁅e j, f i⁆ := ?_
  rw [Ring.lie_def, mul_sub, neg_mul, neg_mul, sub_neg_eq_add]
  abel

variable [DecidableEq ι]

/-- Geck's name for the "left" basis elements of `b.support ⊕ ι`. -/
abbrev u (i : b.support) : b.support ⊕ ι → R := Pi.single (Sum.inl i) 1

variable (b) in
/-- Geck's name for the "right" basis elements of `b.support ⊕ ι`. -/
abbrev v (i : ι) : b.support ⊕ ι → R := Pi.single (Sum.inr i) 1

variable (b) in
omit [Finite ι] [IsDomain R] [CharZero R] [P.IsCrystallographic] in
lemma apply_inr_eq_zero_of_mem_span_range_u (j : ι) {x : b.support ⊕ ι → R}
    (hx : x ∈ span R (range u)) : x (Sum.inr j) = 0 := by
  induction hx using span_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; simp [u]
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul t u _ hu => simp [hu]

lemma lie_e_lie_f_apply [Fintype ι] (i j : b.support) :
    ⁅e i, ⁅f i, u j⁆⁆ = |b.cartanMatrix i j| • u i := by
  ext (k | k)
  · simp [e, f, Matrix.mulVec, dotProduct, Pi.single_apply]
  · simp [e, f, Matrix.mulVec, dotProduct, P.ne_zero]

variable [Fintype ι]

instance : IsLieAbelian (cartanSubalgebra b) := by
  rw [cartanSubalgebra_eq_lieSpan, LieSubalgebra.isLieAbelian_lieSpan_iff]
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  exact lie_h_h i j

instance : IsLieAbelian (cartanSubalgebra' b) := by
  refine ⟨fun ⟨⟨x, hx⟩, hx'⟩ ⟨⟨y, hy⟩, hy'⟩ ↦ ?_⟩
  let x' : cartanSubalgebra b := ⟨x, hx'⟩
  let y' : cartanSubalgebra b := ⟨y, hy'⟩
  suffices ⁅x', y'⁆ = 0 by simpa [x', y', Subtype.ext_iff, -trivial_lie_zero] using this
  simp

instance : LieModule.IsTriangularizable R (cartanSubalgebra' b) (b.support ⊕ ι → R) := by
  refine ⟨fun ⟨⟨x, hx'⟩, hx⟩ ↦ ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d : b.support ⊕ ι → R, Matrix.diagonal d = x :=
    span_range_h_le_range_diagonal <| by simpa using hx
  simp

lemma cartanSubalgebra_le_lieAlgebra :
    cartanSubalgebra b ≤ lieAlgebra b := by
  rw [cartanSubalgebra, lieAlgebra, ← LieSubalgebra.toSubmodule_le_toSubmodule, Submodule.span_le]
  rintro - ⟨i, rfl⟩
  exact LieSubalgebra.subset_lieSpan <| Or.inl <| Or.inl <| mem_range_self i

lemma e_lie_u (i j : b.support) :
    ⁅e i, u j⁆ = |b.cartanMatrix i j| • v b i := by
  ext (k | k) <;> simp [e, Pi.single_apply]

lemma e_lie_v_ne {i j : ι} {k : b.support} (h : P.root j = P.root k + P.root i) :
    ⁅e k, v b i⁆ = (P.chainBotCoeff k i + 1 : R) • v b j := by
  letI := P.indexNeg
  ext (l | l)
  · replace h : i ≠ -k := by rintro rfl; exact P.ne_zero j <| by simpa using h
    simp [e, h, -indexNeg_neg]
  · simp [e, ← h, Pi.single_apply]

lemma f_lie_v_same (i : b.support) :
    ⁅f i, v b i⁆ = u i := by
  ext (j | j)
  · simp [f, Pi.single_apply]
  · simp [f, P.ne_zero j]

lemma f_lie_v_ne {i j : ι} {k : b.support} (h : P.root i = P.root j + P.root k) :
    ⁅f k, v b i⁆ = (P.chainTopCoeff k i + 1 : R) • v b j := by
  ext (l | l)
  · replace h : i ≠ k := by rintro rfl; exact P.ne_zero j <| by simpa using h
    simp [f, h]
  · simp [f, h, Pi.single_apply]

section ωConj

variable (b) in
/-- The conjugation `x ↦ ωxω` as an equivalence of Lie algebras. -/
@[simps] def ωConj :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R ≃ₗ⁅R⁆ Matrix (b.support ⊕ ι) (b.support ⊕ ι) R where
  toFun x := ω b * x * ω b
  invFun x := ω b * x * ω b
  map_add' x y := by noncomm_ring
  map_smul' t x := by simp
  map_lie' {x y} := by
    simp only [Ring.lie_def]
    nth_rw 1 [← mul_one x]
    nth_rw 2 [← one_mul x]
    simp only [← ω_mul_ω (b := b)]
    noncomm_ring
  left_inv x := by
    simp only [← mul_assoc, ω_mul_ω, one_mul]
    simp [mul_assoc]
  right_inv x := by
    simp only [← mul_assoc, ω_mul_ω, one_mul]
    simp [mul_assoc]

lemma ωConj_mem_of_mem
    {x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R} (hx : x ∈ lieAlgebra b) :
    ωConj b x ∈ lieAlgebra b := by
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem u hu =>
    obtain (⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩) : (∃ j, h j = u) ∨ (∃ j, e j = u) ∨ (∃ j, f j = u) := by
      simpa only [mem_union, mem_range, or_assoc] using hu
    · rw [← neg_mem_iff]
      exact LieSubalgebra.subset_lieSpan <| by simp [ω_mul_h, mul_assoc]
    · exact LieSubalgebra.subset_lieSpan <| by simp [ω_mul_e, mul_assoc]
    · exact LieSubalgebra.subset_lieSpan <| by simp [ω_mul_f, mul_assoc]
  | zero => simp
  | add u v _ _ hu hv => simpa [mul_add, add_mul] using add_mem hu hv
  | smul t u _ hu => simpa using SMulMemClass.smul_mem _ hu
  | lie u v _ _ hu hv =>
    rw [LieEquiv.map_lie]
    exact (lieAlgebra b).lie_mem hu hv

variable (N : LieSubmodule R (lieAlgebra b) (b.support ⊕ ι → R))

/-- The equivalence `x ↦ ωxω` as an operation on Lie submodules of the Geck construction. -/
def ωConjLieSubmodule :
    LieSubmodule R (lieAlgebra b) (b.support ⊕ ι → R) where
  __ := N.toSubmodule.comap (ω b).toLin'
  lie_mem A {x} hx := by
    let A' : lieAlgebra b := ⟨ωConj b _, ωConj_mem_of_mem A.property⟩
    suffices ⁅A', ω b *ᵥ x⁆ ∈ N by simpa [A', mul_assoc] using this
    exact LieSubmodule.lie_mem _ hx

@[simp] lemma mem_ωConjLieSubmodule_iff {x : b.support ⊕ ι → R} :
    x ∈ ωConjLieSubmodule N ↔ (ω b) *ᵥ x ∈ N :=
  Iff.rfl

@[simp] lemma ωConjLieSubmodule_eq_top_iff : ωConjLieSubmodule N = ⊤ ↔ N = ⊤ := by
  rw [← LieSubmodule.toSubmodule_eq_top]
  let e : Submodule R (b.support ⊕ ι → R) ≃o Submodule R (b.support ⊕ ι → R) :=
    Submodule.orderIsoMapComapOfBijective (ω b).toLin' (Involutive.bijective fun x ↦ by simp)
  change e.symm N = ⊤ ↔ _
  simp

end ωConj

end RootPairing.GeckConstruction
