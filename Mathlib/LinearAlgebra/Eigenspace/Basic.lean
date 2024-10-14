/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathlib.Algebra.Algebra.Spectrum
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Eigenvectors and eigenvalues

This file defines eigenspaces, eigenvalues, and eigenvalues, as well as their generalized
counterparts. We follow Axler's approach [axler2015] because it allows us to derive many properties
without choosing a basis and without using matrices.

An eigenspace of a linear map `f` for a scalar `μ` is the kernel of the map `(f - μ • id)`. The
nonzero elements of an eigenspace are eigenvectors `x`. They have the property `f x = μ • x`. If
there are eigenvectors for a scalar `μ`, the scalar `μ` is called an eigenvalue.

There is no consensus in the literature whether `0` is an eigenvector. Our definition of
`HasEigenvector` permits only nonzero vectors. For an eigenvector `x` that may also be `0`, we
write `x ∈ f.eigenspace μ`.

A generalized eigenspace of a linear map `f` for a natural number `k` and a scalar `μ` is the kernel
of the map `(f - μ • id) ^ k`. The nonzero elements of a generalized eigenspace are generalized
eigenvectors `x`. If there are generalized eigenvectors for a natural number `k` and a scalar `μ`,
the scalar `μ` is called a generalized eigenvalue.

The fact that the eigenvalues are the roots of the minimal polynomial is proved in
`LinearAlgebra.Eigenspace.Minpoly`.

The existence of eigenvalues over an algebraically closed field
(and the fact that the generalized eigenspaces then span) is deferred to
`LinearAlgebra.Eigenspace.IsAlgClosed`.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2015]
* https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors

## Tags

eigenspace, eigenvector, eigenvalue, eigen
-/


universe u v w

namespace Module

namespace End

open Module Set

variable {K R : Type v} {V M : Type w} [CommRing R] [AddCommGroup M] [Module R M] [Field K]
  [AddCommGroup V] [Module K V]

/-- The submodule `unifEigenspace f μ k` for a linear map `f`, a scalar `μ`,
and a number `k : ℕ∞` is the kernel of `(f - μ • id) ^ k` if `k` is a natural number,
or the union of all these kernels if `k = ∞`. -/
def unifEigenspace (f : End R M) (μ : R) : ℕ∞ →o Submodule R M where
  toFun k := ⨆ l : ℕ, ⨆ _ : l ≤ k, LinearMap.ker ((f - μ • 1) ^ l)
  monotone' _ _ hkl := biSup_mono fun _ hi ↦ hi.trans hkl

lemma mem_unifEigenspace {f : End R M} {μ : R} {k : ℕ∞} {x : M} :
    x ∈ f.unifEigenspace μ k ↔ ∃ l : ℕ, l ≤ k ∧ x ∈ LinearMap.ker ((f - μ • 1) ^ l) := by
  have : Nonempty {l : ℕ // l ≤ k} := ⟨⟨0, zero_le _⟩⟩
  have : Directed (ι := { i : ℕ // i ≤ k }) (· ≤ ·) fun i ↦ LinearMap.ker ((f - μ • 1) ^ (i : ℕ)) :=
    Monotone.directed_le fun m n h ↦ by simpa using (f - μ • 1).iterateKer.monotone h
  simp_rw [unifEigenspace, OrderHom.coe_mk, LinearMap.mem_ker, iSup_subtype',
    Submodule.mem_iSup_of_directed _ this, LinearMap.mem_ker, Subtype.exists, exists_prop]

lemma unifEigenspace_directed {f : End R M} {μ : R} {k : ℕ∞} :
    Directed (· ≤ ·) (fun l : {l : ℕ // l ≤ k} ↦ f.unifEigenspace μ l) := by
  have aux : Monotone ((↑) : {l : ℕ // l ≤ k} → ℕ∞) := fun x y h ↦ by simpa using h
  exact ((unifEigenspace f μ).monotone.comp aux).directed_le

lemma mem_unifEigenspace_nat {f : End R M} {μ : R} {k : ℕ} {x : M} :
    x ∈ f.unifEigenspace μ k ↔ x ∈ LinearMap.ker ((f - μ • 1) ^ k) := by
  rw [mem_unifEigenspace]
  constructor
  · rintro ⟨l, hl, hx⟩
    simp only [Nat.cast_le] at hl
    exact (f - μ • 1).iterateKer.monotone hl hx
  · intro hx
    exact ⟨k, le_rfl, hx⟩

lemma mem_unifEigenspace_top {f : End R M} {μ : R} {x : M} :
    x ∈ f.unifEigenspace μ ⊤ ↔ ∃ k : ℕ, x ∈ LinearMap.ker ((f - μ • 1) ^ k) := by
  simp [mem_unifEigenspace]

lemma unifEigenspace_nat {f : End R M} {μ : R} {k : ℕ} :
    f.unifEigenspace μ k = LinearMap.ker ((f - μ • 1) ^ k) := by
  ext; simp [mem_unifEigenspace_nat]

lemma unifEigenspace_eq_iSup_unifEigenspace_nat (f : End R M) (μ : R) (k : ℕ∞) :
    f.unifEigenspace μ k = ⨆ l : {l : ℕ // l ≤ k}, f.unifEigenspace μ l := by
  simp_rw [unifEigenspace_nat, unifEigenspace, OrderHom.coe_mk, iSup_subtype]

lemma unifEigenspace_top (f : End R M) (μ : R) :
    f.unifEigenspace μ ⊤ = ⨆ k : ℕ, f.unifEigenspace μ k := by
  rw [unifEigenspace_eq_iSup_unifEigenspace_nat, iSup_subtype]
  simp only [le_top, iSup_pos, OrderHom.coe_mk]

lemma unifEigenspace_one {f : End R M} {μ : R} :
    f.unifEigenspace μ 1 = LinearMap.ker (f - μ • 1) := by
  rw [← Nat.cast_one, unifEigenspace_nat, pow_one]

@[simp]
lemma mem_unifEigenspace_one {f : End R M} {μ : R} {x : M} :
    x ∈ f.unifEigenspace μ 1 ↔ f x = μ • x := by
  rw [unifEigenspace_one, LinearMap.mem_ker, LinearMap.sub_apply,
    sub_eq_zero, LinearMap.smul_apply, LinearMap.one_apply]

-- `simp` can prove this using `unifEigenspace_zero`
lemma mem_unifEigenspace_zero {f : End R M} {μ : R} {x : M} :
    x ∈ f.unifEigenspace μ 0 ↔ x = 0 := by
  rw [← Nat.cast_zero, mem_unifEigenspace_nat, pow_zero, LinearMap.mem_ker, LinearMap.one_apply]

@[simp]
lemma unifEigenspace_zero {f : End R M} {μ : R} :
    f.unifEigenspace μ 0 = ⊥ := by
  ext; apply mem_unifEigenspace_zero

@[simp]
lemma unifEigenspace_zero_nat (f : End R M) (k : ℕ) :
    f.unifEigenspace 0 k = LinearMap.ker (f ^ k) := by
  ext; simp [mem_unifEigenspace_nat]

/-- Let `M` be an `R`-module, and `f` an `R`-linear endomorphism of `M`,
and let `μ : R` and `k : ℕ∞` be given.
Then `x : M` satisfies `HasUnifEigenvector f μ k x` if
`x ∈ f.unifEigenspace μ k` and `x ≠ 0`.

For `k = 1`, this means that `x` is an eigenvector of `f` with eigenvalue `μ`. -/
def HasUnifEigenvector (f : End R M) (μ : R) (k : ℕ∞) (x : M) : Prop :=
  x ∈ f.unifEigenspace μ k ∧ x ≠ 0

/-- Let `M` be an `R`-module, and `f` an `R`-linear endomorphism of `M`.
Then `μ : R` and `k : ℕ∞` satisfy `HasUnifEigenvalue f μ k` if
`f.unifEigenspace μ k ≠ ⊥`.

For `k = 1`, this means that `μ` is an eigenvalue of `f`. -/
def HasUnifEigenvalue (f : End R M) (μ : R) (k : ℕ∞) : Prop :=
  f.unifEigenspace μ k ≠ ⊥

/-- Let `M` be an `R`-module, and `f` an `R`-linear endomorphism of `M`.
For `k : ℕ∞`, we define `UnifEigenvalues f k` to be the type of all
`μ : R` that satisfy `f.HasUnifEigenvalue μ k`.

For `k = 1` this is the type of all eigenvalues of `f`. -/
def UnifEigenvalues (f : End R M) (k : ℕ∞) : Type _ :=
  { μ : R // f.HasUnifEigenvalue μ k }

/-- The underlying value of a bundled eigenvalue. -/
@[coe]
def UnifEigenvalues.val (f : Module.End R M) (k : ℕ∞) : UnifEigenvalues f k → R := Subtype.val

instance UnifEigenvalues.instCoeOut {f : Module.End R M} (k : ℕ∞) :
    CoeOut (UnifEigenvalues f k) R where
  coe := UnifEigenvalues.val f k

instance UnivEigenvalues.instDecidableEq [DecidableEq R] (f : Module.End R M) (k : ℕ∞) :
    DecidableEq (UnifEigenvalues f k) :=
  inferInstanceAs (DecidableEq (Subtype (fun x : R ↦ f.HasUnifEigenvalue x k)))

lemma HasUnifEigenvector.hasUnifEigenvalue {f : End R M} {μ : R} {k : ℕ∞} {x : M}
    (h : f.HasUnifEigenvector μ k x) : f.HasUnifEigenvalue μ k := by
  rw [HasUnifEigenvalue, Submodule.ne_bot_iff]
  use x; exact h

lemma HasUnifEigenvector.apply_eq_smul {f : End R M} {μ : R} {x : M}
    (hx : f.HasUnifEigenvector μ 1 x) : f x = μ • x :=
  mem_unifEigenspace_one.mp hx.1

lemma HasUnifEigenvector.pow_apply {f : End R M} {μ : R} {v : M} (hv : f.HasUnifEigenvector μ 1 v)
    (n : ℕ) : (f ^ n) v = μ ^ n • v := by
  induction n <;> simp [*, pow_succ f, hv.apply_eq_smul, smul_smul, pow_succ' μ]

theorem HasUnifEigenvalue.exists_hasUnifEigenvector
    {f : End R M} {μ : R} {k : ℕ∞} (hμ : f.HasUnifEigenvalue μ k) :
    ∃ v, f.HasUnifEigenvector μ k v :=
  Submodule.exists_mem_ne_zero_of_ne_bot hμ

lemma HasUnifEigenvalue.pow {f : End R M} {μ : R} (h : f.HasUnifEigenvalue μ 1) (n : ℕ) :
    (f ^ n).HasUnifEigenvalue (μ ^ n) 1 := by
  rw [HasUnifEigenvalue, Submodule.ne_bot_iff]
  obtain ⟨m : M, hm⟩ := h.exists_hasUnifEigenvector
  exact ⟨m, by simpa [mem_unifEigenspace_one] using hm.pow_apply n, hm.2⟩

/-- A nilpotent endomorphism has nilpotent eigenvalues.

See also `LinearMap.isNilpotent_trace_of_isNilpotent`. -/
lemma HasUnifEigenvalue.isNilpotent_of_isNilpotent [NoZeroSMulDivisors R M] {f : End R M}
    (hfn : IsNilpotent f) {μ : R} (hf : f.HasUnifEigenvalue μ 1) :
    IsNilpotent μ := by
  obtain ⟨m : M, hm⟩ := hf.exists_hasUnifEigenvector
  obtain ⟨n : ℕ, hn : f ^ n = 0⟩ := hfn
  exact ⟨n, by simpa [hn, hm.2, eq_comm (a := (0 : M))] using hm.pow_apply n⟩

lemma HasUnifEigenvalue.mem_spectrum {f : End R M} {μ : R} (hμ : HasUnifEigenvalue f μ 1) :
    μ ∈ spectrum R f := by
  refine spectrum.mem_iff.mpr fun h_unit ↦ ?_
  set f' := LinearMap.GeneralLinearGroup.toLinearEquiv h_unit.unit
  rcases hμ.exists_hasUnifEigenvector with ⟨v, hv⟩
  refine hv.2 ((LinearMap.ker_eq_bot'.mp f'.ker) v (?_ : μ • v - f v = 0))
  rw [hv.apply_eq_smul, sub_self]

lemma hasUnifEigenvalue_iff_mem_spectrum [FiniteDimensional K V] {f : End K V} {μ : K} :
    f.HasUnifEigenvalue μ 1 ↔ μ ∈ spectrum K f := by
  rw [spectrum.mem_iff, IsUnit.sub_iff, LinearMap.isUnit_iff_ker_eq_bot,
    HasUnifEigenvalue, unifEigenspace_one, ne_eq, not_iff_not]
  simp [Submodule.ext_iff, LinearMap.mem_ker]

alias ⟨_, HasUnifEigenvalue.of_mem_spectrum⟩ := hasUnifEigenvalue_iff_mem_spectrum

lemma unifEigenspace_div (f : End K V) (a b : K) (hb : b ≠ 0) :
    unifEigenspace f (a / b) 1 = LinearMap.ker (b • f - a • 1) :=
  calc
    unifEigenspace f (a / b) 1 = unifEigenspace f (b⁻¹ * a) 1 := by rw [div_eq_mul_inv, mul_comm]
    _ = LinearMap.ker (f - (b⁻¹ * a) • 1)     := by rw [unifEigenspace_one]
    _ = LinearMap.ker (f - b⁻¹ • a • 1)       := by rw [smul_smul]
    _ = LinearMap.ker (b • (f - b⁻¹ • a • 1)) := by rw [LinearMap.ker_smul _ b hb]
    _ = LinearMap.ker (b • f - a • 1)         := by rw [smul_sub, smul_inv_smul₀ hb]

/-- The generalized eigenrange for a linear map `f`, a scalar `μ`, and an exponent `k ∈ ℕ∞`
is the range of `(f - μ • id) ^ k` if `k` is a natural number,
or the infimum of these ranges if `k = ∞`. -/
def unifEigenrange (f : End R M) (μ : R) (k : ℕ∞) : Submodule R M :=
  ⨅ l : ℕ, ⨅ (_ : l ≤ k), LinearMap.range ((f - μ • 1) ^ l)

lemma unifEigenrange_nat {f : End R M} {μ : R} {k : ℕ} :
    f.unifEigenrange μ k = LinearMap.range ((f - μ • 1) ^ k) := by
  ext x
  simp only [unifEigenrange, Nat.cast_le, Submodule.mem_iInf, LinearMap.mem_range]
  constructor
  · intro h
    exact h _ le_rfl
  · rintro ⟨x, rfl⟩ i hi
    have : k = i + (k - i) := by omega
    rw [this, pow_add]
    exact ⟨_, rfl⟩

/-- The exponent of a generalized eigenvalue is never 0. -/
lemma HasUnifEigenvalue.exp_ne_zero {f : End R M} {μ : R} {k : ℕ}
    (h : f.HasUnifEigenvalue μ k) : k ≠ 0 := by
  rintro rfl
  simp [HasUnifEigenvalue, Nat.cast_zero, unifEigenspace_zero] at h

/-- If there exists a natural number `k` such that the kernel of `(f - μ • id) ^ k` is the
maximal generalized eigenspace, then this value is the least such `k`. If not, this value is not
meaningful. -/
noncomputable def maxUnifEigenspaceIndex (f : End R M) (μ : R) :=
  monotonicSequenceLimitIndex <| (f.unifEigenspace μ).comp <| WithTop.coeOrderHom.toOrderHom

/-- For an endomorphism of a Noetherian module, the maximal eigenspace is always of the form kernel
`(f - μ • id) ^ k` for some `k`. -/
lemma unifEigenspace_top_eq_maxUnifEigenspaceIndex [h : IsNoetherian R M] (f : End R M) (μ : R) :
    unifEigenspace f μ ⊤ = f.unifEigenspace μ (maxUnifEigenspaceIndex f μ) := by
  rw [isNoetherian_iff] at h
  have := WellFounded.iSup_eq_monotonicSequenceLimit h <|
    (f.unifEigenspace μ).comp <| WithTop.coeOrderHom.toOrderHom
  convert this using 1
  simp only [unifEigenspace, OrderHom.coe_mk, le_top, iSup_pos, OrderHom.comp_coe,
    Function.comp_def]
  rw [iSup_prod', iSup_subtype', ← sSup_range, ← sSup_range]
  congr
  aesop

lemma unifEigenspace_le_unifEigenspace_maxUnifEigenspaceIndex [IsNoetherian R M] (f : End R M)
    (μ : R) (k : ℕ∞) :
    f.unifEigenspace μ k ≤ f.unifEigenspace μ (maxUnifEigenspaceIndex f μ) := by
  rw [← unifEigenspace_top_eq_maxUnifEigenspaceIndex]
  exact (f.unifEigenspace μ).monotone le_top

/-- Generalized eigenspaces for exponents at least `finrank K V` are equal to each other. -/
theorem unifEigenspace_eq_unifEigenspace_maxUnifEigenspaceIndex_of_le [IsNoetherian R M]
    (f : End R M) (μ : R) {k : ℕ} (hk : maxUnifEigenspaceIndex f μ ≤ k) :
    f.unifEigenspace μ k = f.unifEigenspace μ (maxUnifEigenspaceIndex f μ) :=
  le_antisymm
    (unifEigenspace_le_unifEigenspace_maxUnifEigenspaceIndex _ _ _)
    ((f.unifEigenspace μ).monotone <| by simpa using hk)

/-- A generalized eigenvalue for some exponent `k` is also
    a generalized eigenvalue for exponents larger than `k`. -/
lemma HasUnifEigenvalue.le {f : End R M} {μ : R} {k m : ℕ∞}
    (hm : k ≤ m) (hk : f.HasUnifEigenvalue μ k) :
    f.HasUnifEigenvalue μ m := by
  unfold HasUnifEigenvalue at *
  contrapose! hk
  rw [← le_bot_iff, ← hk]
  exact (f.unifEigenspace _).monotone hm

/-- A generalized eigenvalue for some exponent `k` is also
    a generalized eigenvalue for positive exponents. -/
lemma HasUnifEigenvalue.lt {f : End R M} {μ : R} {k m : ℕ∞}
    (hm : 0 < m) (hk : f.HasUnifEigenvalue μ k) :
    f.HasUnifEigenvalue μ m := by
  apply HasUnifEigenvalue.le (k := 1) (Order.one_le_iff_pos.mpr hm)
  intro contra; apply hk
  rw [unifEigenspace_one, LinearMap.ker_eq_bot] at contra
  rw [eq_bot_iff]
  intro x hx
  rw [mem_unifEigenspace] at hx
  rcases hx with ⟨l, -, hx⟩
  rwa [LinearMap.ker_eq_bot.mpr] at hx
  rw [LinearMap.coe_pow (f - μ • 1) l]
  exact Function.Injective.iterate contra l

/-- Generalized eigenvalues are actually just eigenvalues. -/
@[simp]
lemma hasUnifEigenvalue_iff_hasUnifEigenvalue_one {f : End R M} {μ : R} {k : ℕ∞} (hk : 0 < k) :
    f.HasUnifEigenvalue μ k ↔ f.HasUnifEigenvalue μ 1 :=
  ⟨HasUnifEigenvalue.lt zero_lt_one, HasUnifEigenvalue.lt hk⟩

lemma maxUnifEigenspaceIndex_le_finrank [FiniteDimensional K V] (f : End K V) (μ : K) :
    maxUnifEigenspaceIndex f μ ≤ finrank K V := by
  apply Nat.sInf_le
  intro n hn
  apply le_antisymm
  · exact (f.unifEigenspace μ).monotone <| WithTop.coeOrderHom.monotone hn
  · show (f.unifEigenspace μ) n ≤ (f.unifEigenspace μ) (finrank K V)
    rw [unifEigenspace_nat, unifEigenspace_nat]
    apply ker_pow_le_ker_pow_finrank

/-- Every generalized eigenvector is a generalized eigenvector for exponent `finrank K V`.
    (Lemma 8.11 of [axler2015]) -/
lemma unifEigenspace_le_unifEigenspace_finrank [FiniteDimensional K V] (f : End K V)
    (μ : K) (k : ℕ∞) : f.unifEigenspace μ k ≤ f.unifEigenspace μ (finrank K V) := by
  calc f.unifEigenspace μ k
      ≤ f.unifEigenspace μ ⊤ := (f.unifEigenspace _).monotone le_top
    _ ≤ f.unifEigenspace μ (finrank K V) := by
      rw [unifEigenspace_top_eq_maxUnifEigenspaceIndex]
      exact (f.unifEigenspace _).monotone <| by simpa using maxUnifEigenspaceIndex_le_finrank f μ

/-- Generalized eigenspaces for exponents at least `finrank K V` are equal to each other. -/
theorem unifEigenspace_eq_unifEigenspace_finrank_of_le [FiniteDimensional K V]
    (f : End K V) (μ : K) {k : ℕ} (hk : finrank K V ≤ k) :
    f.unifEigenspace μ k = f.unifEigenspace μ (finrank K V) :=
  le_antisymm
    (unifEigenspace_le_unifEigenspace_finrank _ _ _)
    ((f.unifEigenspace μ).monotone <| by simpa using hk)

lemma mapsTo_unifEigenspace_of_comm {f g : End R M} (h : Commute f g) (μ : R) (k : ℕ∞) :
    MapsTo g (f.unifEigenspace μ k) (f.unifEigenspace μ k) := by
  intro x hx
  simp only [SetLike.mem_coe, mem_unifEigenspace, LinearMap.mem_ker] at hx ⊢
  rcases hx with ⟨l, hl, hx⟩
  replace h : Commute ((f - μ • (1 : End R M)) ^ l) g :=
    (h.sub_left <| Algebra.commute_algebraMap_left μ g).pow_left l
  use l, hl
  rw [← LinearMap.comp_apply, ← LinearMap.mul_eq_comp, h.eq, LinearMap.mul_eq_comp,
    LinearMap.comp_apply, hx, map_zero]

/-- The restriction of `f - μ • 1` to the `k`-fold generalized `μ`-eigenspace is nilpotent. -/
lemma isNilpotent_restrict_unifEigenspace_nat (f : End R M) (μ : R) (k : ℕ)
    (h : MapsTo (f - μ • (1 : End R M))
      (f.unifEigenspace μ k) (f.unifEigenspace μ k) :=
      mapsTo_unifEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ k) :
    IsNilpotent ((f - μ • 1).restrict h) := by
  use k
  ext ⟨x, hx⟩
  rw [mem_unifEigenspace_nat] at hx
  rw [LinearMap.zero_apply, ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero,
    LinearMap.pow_restrict, LinearMap.restrict_apply]
  ext
  simpa

/-- The restriction of `f - μ • 1` to the generalized `μ`-eigenspace is nilpotent. -/
lemma isNilpotent_restrict_unifEigenspace_top [IsNoetherian R M] (f : End R M) (μ : R)
    (h : MapsTo (f - μ • (1 : End R M))
      (f.unifEigenspace μ ⊤) (f.unifEigenspace μ ⊤) :=
      mapsTo_unifEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ _) :
    IsNilpotent ((f - μ • 1).restrict h) := by
  apply isNilpotent_restrict_of_le
  swap; apply isNilpotent_restrict_unifEigenspace_nat f μ (maxUnifEigenspaceIndex f μ)
  rw [unifEigenspace_top_eq_maxUnifEigenspaceIndex]

/-- The submodule `eigenspace f μ` for a linear map `f` and a scalar `μ` consists of all vectors `x`
    such that `f x = μ • x`. (Def 5.36 of [axler2015])-/
abbrev eigenspace (f : End R M) (μ : R) : Submodule R M :=
  f.unifEigenspace μ 1

lemma eigenspace_def {f : End R M} {μ : R} :
    f.eigenspace μ = LinearMap.ker (f - μ • 1) := by
  rw [eigenspace, unifEigenspace_one]

@[simp]
theorem eigenspace_zero (f : End R M) : f.eigenspace 0 = LinearMap.ker f := by
  simp only [eigenspace, ← Nat.cast_one (R := ℕ∞), unifEigenspace_zero_nat, pow_one]

/-- A nonzero element of an eigenspace is an eigenvector. (Def 5.7 of [axler2015]) -/
abbrev HasEigenvector (f : End R M) (μ : R) (x : M) : Prop :=
  HasUnifEigenvector f μ 1 x

lemma hasEigenvector_iff {f : End R M} {μ : R} {x : M} :
    f.HasEigenvector μ x ↔ x ∈ f.eigenspace μ ∧ x ≠ 0 := Iff.rfl

/-- A scalar `μ` is an eigenvalue for a linear map `f` if there are nonzero vectors `x`
    such that `f x = μ • x`. (Def 5.5 of [axler2015]) -/
abbrev HasEigenvalue (f : End R M) (a : R) : Prop :=
  HasUnifEigenvalue f a 1

lemma hasEigenvalue_iff {f : End R M} {μ : R} :
    f.HasEigenvalue μ ↔ f.eigenspace μ ≠ ⊥ := Iff.rfl

/-- The eigenvalues of the endomorphism `f`, as a subtype of `R`. -/
abbrev Eigenvalues (f : End R M) : Type _ :=
  UnifEigenvalues f 1

@[coe]
abbrev Eigenvalues.val (f : Module.End R M) : Eigenvalues f → R := UnifEigenvalues.val f 1

theorem hasEigenvalue_of_hasEigenvector {f : End R M} {μ : R} {x : M} (h : HasEigenvector f μ x) :
    HasEigenvalue f μ :=
  h.hasUnifEigenvalue

theorem mem_eigenspace_iff {f : End R M} {μ : R} {x : M} : x ∈ eigenspace f μ ↔ f x = μ • x :=
  mem_unifEigenspace_one

nonrec
theorem HasEigenvector.apply_eq_smul {f : End R M} {μ : R} {x : M} (hx : f.HasEigenvector μ x) :
    f x = μ • x :=
  hx.apply_eq_smul

nonrec
theorem HasEigenvector.pow_apply {f : End R M} {μ : R} {v : M} (hv : f.HasEigenvector μ v) (n : ℕ) :
    (f ^ n) v = μ ^ n • v :=
  hv.pow_apply n

theorem HasEigenvalue.exists_hasEigenvector {f : End R M} {μ : R} (hμ : f.HasEigenvalue μ) :
    ∃ v, f.HasEigenvector μ v :=
  Submodule.exists_mem_ne_zero_of_ne_bot hμ

nonrec
lemma HasEigenvalue.pow {f : End R M} {μ : R} (h : f.HasEigenvalue μ) (n : ℕ) :
    (f ^ n).HasEigenvalue (μ ^ n) :=
  h.pow n

/-- A nilpotent endomorphism has nilpotent eigenvalues.

See also `LinearMap.isNilpotent_trace_of_isNilpotent`. -/
nonrec
lemma HasEigenvalue.isNilpotent_of_isNilpotent [NoZeroSMulDivisors R M] {f : End R M}
    (hfn : IsNilpotent f) {μ : R} (hf : f.HasEigenvalue μ) :
    IsNilpotent μ :=
  hf.isNilpotent_of_isNilpotent hfn

nonrec
theorem HasEigenvalue.mem_spectrum {f : End R M} {μ : R} (hμ : HasEigenvalue f μ) :
    μ ∈ spectrum R f :=
  hμ.mem_spectrum

theorem hasEigenvalue_iff_mem_spectrum [FiniteDimensional K V] {f : End K V} {μ : K} :
    f.HasEigenvalue μ ↔ μ ∈ spectrum K f :=
  hasUnifEigenvalue_iff_mem_spectrum

alias ⟨_, HasEigenvalue.of_mem_spectrum⟩ := hasEigenvalue_iff_mem_spectrum

theorem eigenspace_div (f : End K V) (a b : K) (hb : b ≠ 0) :
    eigenspace f (a / b) = LinearMap.ker (b • f - algebraMap K (End K V) a) :=
  unifEigenspace_div f a b hb

/-- The generalized eigenspace for a linear map `f`, a scalar `μ`, and an exponent `k ∈ ℕ` is the
kernel of `(f - μ • id) ^ k`. (Def 8.10 of [axler2015]). Furthermore, a generalized eigenspace for
some exponent `k` is contained in the generalized eigenspace for exponents larger than `k`. -/
def genEigenspace (f : End R M) (μ : R) : ℕ →o Submodule R M where
  toFun k := f.unifEigenspace μ k
  monotone' k l hkl := (f.unifEigenspace μ).monotone <| by simpa

lemma genEigenspace_def (f : End R M) (μ : R) (k : ℕ) :
    f.genEigenspace μ k = LinearMap.ker ((f - μ • 1) ^ k) := by
  rw [genEigenspace, OrderHom.coe_mk, unifEigenspace_nat]

@[simp]
theorem mem_genEigenspace (f : End R M) (μ : R) (k : ℕ) (m : M) :
    m ∈ f.genEigenspace μ k ↔ ((f - μ • (1 : End R M)) ^ k) m = 0 :=
  mem_unifEigenspace_nat

@[simp]
theorem genEigenspace_zero (f : End R M) (k : ℕ) :
    f.genEigenspace 0 k = LinearMap.ker (f ^ k) :=
  unifEigenspace_zero_nat _ _

/-- A nonzero element of a generalized eigenspace is a generalized eigenvector.
    (Def 8.9 of [axler2015])-/
abbrev HasGenEigenvector (f : End R M) (μ : R) (k : ℕ) (x : M) : Prop :=
  HasUnifEigenvector f μ k x

lemma hasGenEigenvector_iff {f : End R M} {μ : R} {k : ℕ} {x : M} :
    f.HasGenEigenvector μ k x ↔ x ∈ f.genEigenspace μ k ∧ x ≠ 0 := Iff.rfl

/-- A scalar `μ` is a generalized eigenvalue for a linear map `f` and an exponent `k ∈ ℕ` if there
    are generalized eigenvectors for `f`, `k`, and `μ`. -/
abbrev HasGenEigenvalue (f : End R M) (μ : R) (k : ℕ) : Prop :=
  HasUnifEigenvalue f μ k

lemma hasGenEigenvalue_iff {f : End R M} {μ : R} {k : ℕ} :
    f.HasGenEigenvalue μ k ↔ f.genEigenspace μ k ≠ ⊥ := Iff.rfl

/-- The generalized eigenrange for a linear map `f`, a scalar `μ`, and an exponent `k ∈ ℕ` is the
    range of `(f - μ • id) ^ k`. -/
abbrev genEigenrange (f : End R M) (μ : R) (k : ℕ) : Submodule R M :=
  unifEigenrange f μ k

lemma genEigenrange_def {f : End R M} {μ : R} {k : ℕ} :
    f.genEigenrange μ k = LinearMap.range ((f - μ • 1) ^ k) := by
  rw [genEigenrange, unifEigenrange_nat]

/-- The exponent of a generalized eigenvalue is never 0. -/
theorem exp_ne_zero_of_hasGenEigenvalue {f : End R M} {μ : R} {k : ℕ}
    (h : f.HasGenEigenvalue μ k) : k ≠ 0 :=
  HasUnifEigenvalue.exp_ne_zero h

/-- The union of the kernels of `(f - μ • id) ^ k` over all `k`. -/
abbrev maxGenEigenspace (f : End R M) (μ : R) : Submodule R M :=
  unifEigenspace f μ ⊤

lemma maxGenEigenspace_def (f : End R M) (μ : R) :
    f.maxGenEigenspace μ = ⨆ k, f.genEigenspace μ k := by
  simp_rw [maxGenEigenspace, unifEigenspace_top, genEigenspace, OrderHom.coe_mk]

theorem genEigenspace_le_maximal (f : End R M) (μ : R) (k : ℕ) :
    f.genEigenspace μ k ≤ f.maxGenEigenspace μ :=
  (f.unifEigenspace μ).monotone le_top

@[simp]
theorem mem_maxGenEigenspace (f : End R M) (μ : R) (m : M) :
    m ∈ f.maxGenEigenspace μ ↔ ∃ k : ℕ, ((f - μ • (1 : End R M)) ^ k) m = 0 :=
  mem_unifEigenspace_top

/-- If there exists a natural number `k` such that the kernel of `(f - μ • id) ^ k` is the
maximal generalized eigenspace, then this value is the least such `k`. If not, this value is not
meaningful. -/
noncomputable abbrev maxGenEigenspaceIndex (f : End R M) (μ : R) :=
  maxUnifEigenspaceIndex f μ

/-- For an endomorphism of a Noetherian module, the maximal eigenspace is always of the form kernel
`(f - μ • id) ^ k` for some `k`. -/
theorem maxGenEigenspace_eq [IsNoetherian R M] (f : End R M) (μ : R) :
    maxGenEigenspace f μ = f.genEigenspace μ (maxGenEigenspaceIndex f μ) :=
  unifEigenspace_top_eq_maxUnifEigenspaceIndex _ _

/-- A generalized eigenvalue for some exponent `k` is also
    a generalized eigenvalue for exponents larger than `k`. -/
theorem hasGenEigenvalue_of_hasGenEigenvalue_of_le {f : End R M} {μ : R} {k : ℕ}
    {m : ℕ} (hm : k ≤ m) (hk : f.HasGenEigenvalue μ k) :
    f.HasGenEigenvalue μ m :=
  hk.le <| by simpa using hm

/-- The eigenspace is a subspace of the generalized eigenspace. -/
theorem eigenspace_le_genEigenspace {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k) :
    f.eigenspace μ ≤ f.genEigenspace μ k :=
  (f.unifEigenspace _).monotone <| by simpa using Nat.succ_le_of_lt hk

/-- All eigenvalues are generalized eigenvalues. -/
theorem hasGenEigenvalue_of_hasEigenvalue {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k)
    (hμ : f.HasEigenvalue μ) : f.HasGenEigenvalue μ k :=
  hμ.lt <| by simpa using hk

/-- All generalized eigenvalues are eigenvalues. -/
theorem hasEigenvalue_of_hasGenEigenvalue {f : End R M} {μ : R} {k : ℕ}
    (hμ : f.HasGenEigenvalue μ k) : f.HasEigenvalue μ :=
  hμ.lt zero_lt_one

/-- Generalized eigenvalues are actually just eigenvalues. -/
@[simp]
theorem hasGenEigenvalue_iff_hasEigenvalue {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k) :
    f.HasGenEigenvalue μ k ↔ f.HasEigenvalue μ :=
  hasUnifEigenvalue_iff_hasUnifEigenvalue_one <| by simpa using hk

/-- Every generalized eigenvector is a generalized eigenvector for exponent `finrank K V`.
    (Lemma 8.11 of [axler2015]) -/
theorem genEigenspace_le_genEigenspace_finrank [FiniteDimensional K V] (f : End K V)
    (μ : K) (k : ℕ) : f.genEigenspace μ k ≤ f.genEigenspace μ (finrank K V) :=
  unifEigenspace_le_unifEigenspace_finrank _ _ _

@[simp] theorem iSup_genEigenspace_eq_genEigenspace_finrank
    [FiniteDimensional K V] (f : End K V) (μ : K) :
    ⨆ k, f.genEigenspace μ k = f.genEigenspace μ (finrank K V) :=
  le_antisymm (iSup_le (genEigenspace_le_genEigenspace_finrank f μ)) (le_iSup _ _)

/-- Generalized eigenspaces for exponents at least `finrank K V` are equal to each other. -/
theorem genEigenspace_eq_genEigenspace_finrank_of_le [FiniteDimensional K V]
    (f : End K V) (μ : K) {k : ℕ} (hk : finrank K V ≤ k) :
    f.genEigenspace μ k = f.genEigenspace μ (finrank K V) :=
  unifEigenspace_eq_unifEigenspace_finrank_of_le f μ hk

lemma mapsTo_genEigenspace_of_comm {f g : End R M} (h : Commute f g) (μ : R) (k : ℕ) :
    MapsTo g (f.genEigenspace μ k) (f.genEigenspace μ k) := by
  replace h : Commute ((f - μ • (1 : End R M)) ^ k) g :=
    (h.sub_left <| Algebra.commute_algebraMap_left μ g).pow_left k
  intro x hx
  simp only [SetLike.mem_coe, mem_genEigenspace] at hx ⊢
  rw [← LinearMap.comp_apply, ← LinearMap.mul_eq_comp, h.eq, LinearMap.mul_eq_comp,
    LinearMap.comp_apply, hx, map_zero]

lemma iSup_genEigenspace_eq (f : End R M) (μ : R) :
    ⨆ k, (f.genEigenspace μ) k = f.unifEigenspace μ ⊤ := by
  rw [unifEigenspace_eq_iSup_unifEigenspace_nat]
  ext
  simp only [iSup_subtype, le_top, iSup_pos]
  rfl

lemma mapsTo_maxGenEigenspace_of_comm {f g : End R M} (h : Commute f g) (μ : R) :
    MapsTo g ↑(f.maxGenEigenspace μ) ↑(f.maxGenEigenspace μ) := by
  rw [maxGenEigenspace_def]
  simp only [MapsTo, Submodule.coe_iSup_of_chain, mem_iUnion, SetLike.mem_coe]
  rintro x ⟨k, hk⟩
  exact ⟨k, f.mapsTo_genEigenspace_of_comm h μ k hk⟩

lemma mapsTo_iSup_genEigenspace_of_comm {f g : End R M} (h : Commute f g) (μ : R) :
    MapsTo g ↑(⨆ k, f.genEigenspace μ k) ↑(⨆ k, f.genEigenspace μ k) := by
  rw [← maxGenEigenspace_def]
  apply mapsTo_maxGenEigenspace_of_comm h

/-- The restriction of `f - μ • 1` to the `k`-fold generalized `μ`-eigenspace is nilpotent. -/
lemma isNilpotent_restrict_sub_algebraMap (f : End R M) (μ : R) (k : ℕ)
    (h : MapsTo (f - algebraMap R (End R M) μ)
      (f.genEigenspace μ k) (f.genEigenspace μ k) :=
      mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ k) :
    IsNilpotent ((f - algebraMap R (End R M) μ).restrict h) :=
  isNilpotent_restrict_unifEigenspace_nat _ _ _

/-- The restriction of `f - μ • 1` to the generalized `μ`-eigenspace is nilpotent. -/
lemma isNilpotent_restrict_maxGenEigenspace_sub_algebraMap [IsNoetherian R M] (f : End R M) (μ : R)
    (h : MapsTo (f - algebraMap R (End R M) μ)
      ↑(f.maxGenEigenspace μ) ↑(f.maxGenEigenspace μ) :=
      mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ) :
    IsNilpotent ((f - algebraMap R (End R M) μ).restrict h) := by
  apply isNilpotent_restrict_of_le (q := f.unifEigenspace μ (maxUnifEigenspaceIndex f μ))
    _ (isNilpotent_restrict_unifEigenspace_nat f μ (maxUnifEigenspaceIndex f μ))
  rw [maxGenEigenspace_eq]
  exact le_rfl

/-- The restriction of `f - μ • 1` to the generalized `μ`-eigenspace is nilpotent. -/
lemma isNilpotent_restrict_iSup_sub_algebraMap [IsNoetherian R M] (f : End R M) (μ : R)
    (h : MapsTo (f - algebraMap R (End R M) μ)
      ↑(⨆ k, f.genEigenspace μ k) ↑(⨆ k, f.genEigenspace μ k) :=
      mapsTo_iSup_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ) :
    IsNilpotent ((f - algebraMap R (End R M) μ).restrict h) := by
  apply isNilpotent_restrict_of_le (q := f.unifEigenspace μ (maxUnifEigenspaceIndex f μ))
    _ (isNilpotent_restrict_unifEigenspace_nat f μ (maxUnifEigenspaceIndex f μ))
  apply iSup_le
  intro k
  apply unifEigenspace_le_unifEigenspace_maxUnifEigenspaceIndex

lemma disjoint_unifEigenspace [NoZeroSMulDivisors R M]
    (f : End R M) {μ₁ μ₂ : R} (hμ : μ₁ ≠ μ₂) (k l : ℕ∞) :
    Disjoint (f.unifEigenspace μ₁ k) (f.unifEigenspace μ₂ l) := by
  rw [unifEigenspace_eq_iSup_unifEigenspace_nat, unifEigenspace_eq_iSup_unifEigenspace_nat]
  simp_rw [unifEigenspace_directed.disjoint_iSup_left, unifEigenspace_directed.disjoint_iSup_right]
  rintro ⟨k, -⟩ ⟨l, -⟩
  nontriviality M
  have := NoZeroSMulDivisors.isReduced R M
  rw [disjoint_iff]
  set p := f.unifEigenspace μ₁ k ⊓ f.unifEigenspace μ₂ l
  by_contra hp
  replace hp : Nontrivial p := Submodule.nontrivial_iff_ne_bot.mpr hp
  let f₁ : End R p := (f - algebraMap R (End R M) μ₁).restrict <| MapsTo.inter_inter
    (mapsTo_unifEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₁) μ₁ k)
    (mapsTo_unifEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₁) μ₂ l)
  let f₂ : End R p := (f - algebraMap R (End R M) μ₂).restrict <| MapsTo.inter_inter
    (mapsTo_unifEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₂) μ₁ k)
    (mapsTo_unifEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₂) μ₂ l)
  have : IsNilpotent (f₂ - f₁) := by
    apply Commute.isNilpotent_sub (x := f₂) (y := f₁) _
      (isNilpotent_restrict_of_le inf_le_right _)
      (isNilpotent_restrict_of_le inf_le_left _)
    · ext; simp [f₁, f₂, smul_sub, sub_sub, smul_comm μ₁, add_sub_left_comm]
    apply mapsTo_unifEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f _)
    apply isNilpotent_restrict_unifEigenspace_nat
    apply mapsTo_unifEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f _)
    apply isNilpotent_restrict_unifEigenspace_nat
  have hf₁₂ : f₂ - f₁ = algebraMap R (End R p) (μ₁ - μ₂) := by ext; simp [f₁, f₂, sub_smul]
  rw [hf₁₂, IsNilpotent.map_iff (NoZeroSMulDivisors.algebraMap_injective R (End R p)),
    isNilpotent_iff_eq_zero, sub_eq_zero] at this
  contradiction

lemma disjoint_genEigenspace [NoZeroSMulDivisors R M]
    (f : End R M) {μ₁ μ₂ : R} (hμ : μ₁ ≠ μ₂) (k l : ℕ) :
    Disjoint (f.genEigenspace μ₁ k) (f.genEigenspace μ₂ l) :=
  disjoint_unifEigenspace f hμ k l

lemma disjoint_iSup_genEigenspace [NoZeroSMulDivisors R M]
    (f : End R M) {μ₁ μ₂ : R} (hμ : μ₁ ≠ μ₂) :
    Disjoint (⨆ k, f.genEigenspace μ₁ k) (⨆ k, f.genEigenspace μ₂ k) := by
  simpa only [iSup_genEigenspace_eq] using disjoint_unifEigenspace f hμ ⊤ ⊤

lemma injOn_genEigenspace [NoZeroSMulDivisors R M] (f : End R M) :
    InjOn (⨆ k, f.genEigenspace · k) {μ | ⨆ k, f.genEigenspace μ k ≠ ⊥} := by
  rintro μ₁ _ μ₂ hμ₂ (hμ₁₂ : ⨆ k, f.genEigenspace μ₁ k = ⨆ k, f.genEigenspace μ₂ k)
  by_contra contra
  apply hμ₂
  simpa only [hμ₁₂, disjoint_self] using f.disjoint_iSup_genEigenspace contra

theorem independent_maxGenEigenspace [NoZeroSMulDivisors R M] (f : End R M) :
    CompleteLattice.Independent f.maxGenEigenspace := by
  classical
  suffices ∀ μ (s : Finset R), μ ∉ s → Disjoint (⨆ k, f.genEigenspace μ k)
      (s.sup fun μ ↦ ⨆ k, f.genEigenspace μ k) by
    show CompleteLattice.Independent (f.maxGenEigenspace ·)
    simp_rw [maxGenEigenspace_def,
      CompleteLattice.independent_iff_supIndep_of_injOn f.injOn_genEigenspace,
      Finset.supIndep_iff_disjoint_erase]
    exact fun s μ _ ↦ this _ _ (s.not_mem_erase μ)
  intro μ₁ s
  induction' s using Finset.induction_on with μ₂ s _ ih
  · simp
  intro hμ₁₂
  obtain ⟨hμ₁₂ : μ₁ ≠ μ₂, hμ₁ : μ₁ ∉ s⟩ := by rwa [Finset.mem_insert, not_or] at hμ₁₂
  specialize ih hμ₁
  rw [Finset.sup_insert, disjoint_iff, Submodule.eq_bot_iff]
  rintro x ⟨hx, hx'⟩
  simp only [SetLike.mem_coe] at hx hx'
  suffices x ∈ ⨆ k, genEigenspace f μ₂ k by
    rw [← Submodule.mem_bot (R := R), ← (f.disjoint_iSup_genEigenspace hμ₁₂).eq_bot]
    exact ⟨hx, this⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'; clear hx'
  let g := f - algebraMap R (End R M) μ₂
  obtain ⟨k : ℕ, hk : (g ^ k) y = 0⟩ := by simpa using hy
  have hyz : (g ^ k) (y + z) ∈
      (⨆ k, genEigenspace f μ₁ k) ⊓ s.sup fun μ ↦ ⨆ k, f.genEigenspace μ k := by
    refine ⟨f.mapsTo_iSup_genEigenspace_of_comm ?_ μ₁ hx, ?_⟩
    · exact Algebra.mul_sub_algebraMap_pow_commutes f μ₂ k
    · rw [SetLike.mem_coe, map_add, hk, zero_add]
      suffices (s.sup fun μ ↦ ⨆ k, f.genEigenspace μ k).map (g ^ k) ≤
          s.sup fun μ ↦ ⨆ k, f.genEigenspace μ k by exact this (Submodule.mem_map_of_mem hz)
      simp_rw [Finset.sup_eq_iSup, Submodule.map_iSup (ι := R), Submodule.map_iSup (ι := _ ∈ s)]
      refine iSup₂_mono fun μ _ ↦ ?_
      rintro - ⟨u, hu, rfl⟩
      refine f.mapsTo_iSup_genEigenspace_of_comm ?_ μ hu
      exact Algebra.mul_sub_algebraMap_pow_commutes f μ₂ k
  rw [ih.eq_bot, Submodule.mem_bot] at hyz
  simp_rw [Submodule.mem_iSup_of_chain, mem_genEigenspace]
  exact ⟨k, hyz⟩

theorem independent_genEigenspace [NoZeroSMulDivisors R M] (f : End R M) :
    CompleteLattice.Independent (fun μ ↦ ⨆ k, f.genEigenspace μ k) := by
  simp_rw [← maxGenEigenspace_def]
  apply independent_maxGenEigenspace

/-- The eigenspaces of a linear operator form an independent family of subspaces of `M`.  That is,
any eigenspace has trivial intersection with the span of all the other eigenspaces. -/
theorem eigenspaces_independent [NoZeroSMulDivisors R M] (f : End R M) :
    CompleteLattice.Independent f.eigenspace :=
  f.independent_genEigenspace.mono fun μ ↦ le_iSup (genEigenspace f μ) 1

/-- Eigenvectors corresponding to distinct eigenvalues of a linear operator are linearly
    independent. -/
theorem eigenvectors_linearIndependent' {ι : Type*} [NoZeroSMulDivisors R M]
    (f : End R M) (μ : ι → R) (hμ : Function.Injective μ) (v : ι → M)
    (h_eigenvec : ∀ i, f.HasEigenvector (μ i) (v i)) : LinearIndependent R v :=
  f.eigenspaces_independent.comp hμ |>.linearIndependent _
    (fun i ↦ h_eigenvec i |>.left) (fun i ↦ h_eigenvec i |>.right)

/-- Eigenvectors corresponding to distinct eigenvalues of a linear operator are linearly
    independent. (Lemma 5.10 of [axler2015])

    We use the eigenvalues as indexing set to ensure that there is only one eigenvector for each
    eigenvalue in the image of `xs`.
    See `Module.End.eigenvectors_linearIndependent'` for an indexed variant. -/
theorem eigenvectors_linearIndependent [NoZeroSMulDivisors R M]
    (f : End R M) (μs : Set R) (xs : μs → M)
    (h_eigenvec : ∀ μ : μs, f.HasEigenvector μ (xs μ)) : LinearIndependent R xs :=
  f.eigenvectors_linearIndependent' (fun μ : μs ↦ μ) Subtype.coe_injective _ h_eigenvec

/-- If `f` maps a subspace `p` into itself, then the generalized eigenspace of the restriction
    of `f` to `p` is the part of the generalized eigenspace of `f` that lies in `p`. -/
theorem genEigenspace_restrict (f : End R M) (p : Submodule R M) (k : ℕ) (μ : R)
    (hfp : ∀ x : M, x ∈ p → f x ∈ p) :
    genEigenspace (LinearMap.restrict f hfp) μ k =
      Submodule.comap p.subtype (f.genEigenspace μ k) := by
  simp only [genEigenspace_def, OrderHom.coe_mk, ← LinearMap.ker_comp]
  induction' k with k ih
  · rw [pow_zero, pow_zero, LinearMap.one_eq_id]
    apply (Submodule.ker_subtype _).symm
  · erw [pow_succ, pow_succ, LinearMap.ker_comp, LinearMap.ker_comp, ih, ← LinearMap.ker_comp,
      LinearMap.comp_assoc]

lemma _root_.Submodule.inf_genEigenspace (f : End R M) (p : Submodule R M) {k : ℕ} {μ : R}
    (hfp : ∀ x : M, x ∈ p → f x ∈ p) :
    p ⊓ f.genEigenspace μ k =
      (genEigenspace (LinearMap.restrict f hfp) μ k).map p.subtype := by
  rw [f.genEigenspace_restrict _ _ _ hfp, Submodule.map_comap_eq, Submodule.range_subtype]

/-- Given a family of endomorphisms `i ↦ f i`, a family of candidate eigenvalues `i ↦ μ i`, and a
submodule `p` which is invariant wrt every `f i`, the intersection of `p` with the simultaneous
maximal generalised eigenspace (taken over all `i`), is the same as the simultaneous maximal
generalised eigenspace of the `f i` restricted to `p`. -/
lemma _root_.Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo {ι : Type*} {μ : ι → R}
    (f : ι → End R M) (p : Submodule R M) (hfp : ∀ i, MapsTo (f i) p p) :
    p ⊓ ⨅ i, (f i).maxGenEigenspace (μ i) =
      (⨅ i, maxGenEigenspace ((f i).restrict (hfp i)) (μ i)).map p.subtype := by
  cases isEmpty_or_nonempty ι
  · simp [iInf_of_isEmpty]
  · simp_rw [inf_iInf, maxGenEigenspace_def, ((f _).genEigenspace _).mono.directed_le.inf_iSup_eq,
      p.inf_genEigenspace _ (hfp _), ← Submodule.map_iSup, Submodule.map_iInf _ p.injective_subtype]

/-- Given a family of endomorphisms `i ↦ f i`, a family of candidate eigenvalues `i ↦ μ i`, and a
distinguished index `i` whose maximal generalised `μ i`-eigenspace is invariant wrt every `f j`,
taking simultaneous maximal generalised eigenspaces is unaffected by first restricting to the
distinguished generalised `μ i`-eigenspace. -/
lemma iInf_maxGenEigenspace_restrict_map_subtype_eq
    {ι : Type*} {μ : ι → R} (i : ι) (f : ι → End R M)
    (h : ∀ j, MapsTo (f j) ((f i).maxGenEigenspace (μ i)) ((f i).maxGenEigenspace (μ i))) :
    letI p := (f i).maxGenEigenspace (μ i)
    letI q (j : ι) := maxGenEigenspace ((f j).restrict (h j)) (μ j)
    (⨅ j, q j).map p.subtype = ⨅ j, (f j).maxGenEigenspace (μ j) := by
  have : Nonempty ι := ⟨i⟩
  set p := (f i).maxGenEigenspace (μ i)
  have : ⨅ j, (f j).maxGenEigenspace (μ j) = p ⊓ ⨅ j, (f j).maxGenEigenspace (μ j) := by
    refine le_antisymm ?_ inf_le_right
    simpa only [le_inf_iff, le_refl, and_true] using iInf_le _ _
  rw [Submodule.map_iInf _ p.injective_subtype, this, Submodule.inf_iInf]
  simp_rw [maxGenEigenspace_def, Submodule.map_iSup,
    ((f _).genEigenspace _).mono.directed_le.inf_iSup_eq, p.inf_genEigenspace (f _) (h _)]

lemma mapsTo_restrict_maxGenEigenspace_restrict_of_mapsTo
    {p : Submodule R M} (f g : End R M) (hf : MapsTo f p p) (hg : MapsTo g p p) {μ₁ μ₂ : R}
    (h : MapsTo f (g.maxGenEigenspace μ₁) (g.maxGenEigenspace μ₂)) :
    MapsTo (f.restrict hf)
      (maxGenEigenspace (g.restrict hg) μ₁)
      (maxGenEigenspace (g.restrict hg) μ₂) := by
  intro x hx
  simp_rw [SetLike.mem_coe, mem_maxGenEigenspace, ← LinearMap.restrict_smul_one _,
    LinearMap.restrict_sub _, LinearMap.pow_restrict _, LinearMap.restrict_apply,
    Submodule.mk_eq_zero, ← mem_maxGenEigenspace] at hx ⊢
  exact h hx

/-- If `p` is an invariant submodule of an endomorphism `f`, then the `μ`-eigenspace of the
restriction of `f` to `p` is a submodule of the `μ`-eigenspace of `f`. -/
theorem eigenspace_restrict_le_eigenspace (f : End R M) {p : Submodule R M} (hfp : ∀ x ∈ p, f x ∈ p)
    (μ : R) : (eigenspace (f.restrict hfp) μ).map p.subtype ≤ f.eigenspace μ := by
  rintro a ⟨x, hx, rfl⟩
  simp only [SetLike.mem_coe, mem_eigenspace_iff, LinearMap.restrict_apply] at hx ⊢
  exact congr_arg Subtype.val hx

/-- Generalized eigenrange and generalized eigenspace for exponent `finrank K V` are disjoint. -/
theorem generalized_eigenvec_disjoint_range_ker [FiniteDimensional K V] (f : End K V) (μ : K) :
    Disjoint (f.genEigenrange μ (finrank K V))
      (f.genEigenspace μ (finrank K V)) := by
  have h :=
    calc
      Submodule.comap ((f - μ • 1) ^ finrank K V)
        (f.genEigenspace μ (finrank K V)) =
          LinearMap.ker ((f - algebraMap _ _ μ) ^ finrank K V *
            (f - algebraMap K (End K V) μ) ^ finrank K V) := by
              rw [genEigenspace, OrderHom.coe_mk, unifEigenspace_nat, ← LinearMap.ker_comp]; rfl
      _ = f.genEigenspace μ (finrank K V + finrank K V) := by
              rw [← pow_add, genEigenspace, OrderHom.coe_mk, unifEigenspace_nat]; rfl
      _ = f.genEigenspace μ (finrank K V) := by
              rw [genEigenspace_eq_genEigenspace_finrank_of_le]; omega
  rw [disjoint_iff_inf_le, genEigenrange, unifEigenrange_nat, LinearMap.range_eq_map,
    Submodule.map_inf_eq_map_inf_comap, top_inf_eq, h,
    genEigenspace, OrderHom.coe_mk, unifEigenspace_nat]
  apply Submodule.map_comap_le

/-- If an invariant subspace `p` of an endomorphism `f` is disjoint from the `μ`-eigenspace of `f`,
then the restriction of `f` to `p` has trivial `μ`-eigenspace. -/
theorem eigenspace_restrict_eq_bot {f : End R M} {p : Submodule R M} (hfp : ∀ x ∈ p, f x ∈ p)
    {μ : R} (hμp : Disjoint (f.eigenspace μ) p) : eigenspace (f.restrict hfp) μ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  simpa using hμp.le_bot ⟨eigenspace_restrict_le_eigenspace f hfp μ ⟨x, hx, rfl⟩, x.prop⟩

/-- The generalized eigenspace of an eigenvalue has positive dimension for positive exponents. -/
theorem pos_finrank_genEigenspace_of_hasEigenvalue [FiniteDimensional K V] {f : End K V}
    {k : ℕ} {μ : K} (hx : f.HasEigenvalue μ) (hk : 0 < k) :
    0 < finrank K (f.genEigenspace μ k) :=
  calc
    0 = finrank K (⊥ : Submodule K V) := by rw [finrank_bot]
    _ < finrank K (f.eigenspace μ) := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.2 hx)
    _ ≤ finrank K (f.genEigenspace μ k) :=
      Submodule.finrank_mono ((f.genEigenspace μ).monotone (Nat.succ_le_of_lt hk))

/-- A linear map maps a generalized eigenrange into itself. -/
theorem map_genEigenrange_le {f : End K V} {μ : K} {n : ℕ} :
    Submodule.map f (f.genEigenrange μ n) ≤ f.genEigenrange μ n :=
  calc
    Submodule.map f (f.genEigenrange μ n) =
      LinearMap.range (f * (f - algebraMap _ _ μ) ^ n) := by
        rw [genEigenrange, unifEigenrange_nat]; exact (LinearMap.range_comp _ _).symm
    _ = LinearMap.range ((f - algebraMap _ _ μ) ^ n * f) := by
        rw [Algebra.mul_sub_algebraMap_pow_commutes]
    _ = Submodule.map ((f - algebraMap _ _ μ) ^ n) (LinearMap.range f) := LinearMap.range_comp _ _
    _ ≤ f.genEigenrange μ n := by
      rw [genEigenrange, unifEigenrange_nat]
      apply LinearMap.map_le_range

lemma iSup_genEigenspace_le_smul (f : Module.End R M) (μ t : R) :
    (⨆ k, f.genEigenspace μ k) ≤ ⨆ k, (t • f).genEigenspace (t * μ) k := by
  intro m hm
  simp only [Submodule.mem_iSup_of_chain, mem_genEigenspace] at hm ⊢
  refine Exists.imp (fun k hk ↦ ?_) hm
  rw [mul_smul, ← smul_sub, smul_pow, LinearMap.smul_apply, hk, smul_zero]

lemma iSup_genEigenspace_inf_le_add
    (f₁ f₂ : End R M) (μ₁ μ₂ : R) (h : Commute f₁ f₂) :
    (⨆ k, f₁.genEigenspace μ₁ k) ⊓ (⨆ k, f₂.genEigenspace μ₂ k) ≤
    ⨆ k, (f₁ + f₂).genEigenspace (μ₁ + μ₂) k := by
  intro m hm
  simp only [iSup_le_iff, Submodule.mem_inf, Submodule.mem_iSup_of_chain,
    mem_genEigenspace] at hm ⊢
  obtain ⟨⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩⟩ := hm
  use k₁ + k₂ - 1
  have : f₁ + f₂ - (μ₁ + μ₂) • 1 = (f₁ - μ₁ • 1) + (f₂ - μ₂ • 1) := by
    rw [add_smul]; exact add_sub_add_comm f₁ f₂ (μ₁ • 1) (μ₂ • 1)
  replace h : Commute (f₁ - μ₁ • 1) (f₂ - μ₂ • 1) :=
    (h.sub_right <| Algebra.commute_algebraMap_right μ₂ f₁).sub_left
      (Algebra.commute_algebraMap_left μ₁ _)
  rw [this, h.add_pow', LinearMap.coeFn_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun ⟨i, j⟩ hij ↦ ?_
  suffices (((f₁ - μ₁ • 1) ^ i) * ((f₂ - μ₂ • 1) ^ j)) m = 0 by
    rw [LinearMap.smul_apply, this, smul_zero]
  cases' Nat.le_or_le_of_add_eq_add_pred (Finset.mem_antidiagonal.mp hij) with hi hj
  · rw [(h.pow_pow i j).eq, LinearMap.mul_apply, LinearMap.pow_map_zero_of_le hi hk₁,
      LinearMap.map_zero]
  · rw [LinearMap.mul_apply, LinearMap.pow_map_zero_of_le hj hk₂, LinearMap.map_zero]

lemma map_smul_of_iInf_genEigenspace_ne_bot [NoZeroSMulDivisors R M]
    {L F : Type*} [SMul R L] [FunLike F L (End R M)] [MulActionHomClass F R L (End R M)] (f : F)
    (μ : L → R) (h_ne : ⨅ x, ⨆ k, (f x).genEigenspace (μ x) k ≠ ⊥)
    (t : R) (x : L) :
    μ (t • x) = t • μ x := by
  by_contra contra
  let g : L → Submodule R M := fun x ↦ ⨆ k, (f x).genEigenspace (μ x) k
  have : ⨅ x, g x ≤ g x ⊓ g (t • x) := le_inf_iff.mpr ⟨iInf_le g x, iInf_le g (t • x)⟩
  refine h_ne <| eq_bot_iff.mpr (le_trans this (disjoint_iff_inf_le.mp ?_))
  apply Disjoint.mono_left (iSup_genEigenspace_le_smul (f x) (μ x) t)
  simp only [g, map_smul]
  exact disjoint_iSup_genEigenspace (t • f x) (Ne.symm contra)

lemma map_add_of_iInf_genEigenspace_ne_bot_of_commute [NoZeroSMulDivisors R M]
    {L F : Type*} [Add L] [FunLike F L (End R M)] [AddHomClass F L (End R M)] (f : F)
    (μ : L → R) (h_ne : ⨅ x, ⨆ k, (f x).genEigenspace (μ x) k ≠ ⊥)
    (h : ∀ x y, Commute (f x) (f y)) (x y : L) :
    μ (x + y) = μ x + μ y := by
  by_contra contra
  let g : L → Submodule R M := fun x ↦ ⨆ k, (f x).genEigenspace (μ x) k
  have : ⨅ x, g x ≤ (g x ⊓ g y) ⊓ g (x + y) :=
    le_inf_iff.mpr ⟨le_inf_iff.mpr ⟨iInf_le g x, iInf_le g y⟩, iInf_le g (x + y)⟩
  refine h_ne <| eq_bot_iff.mpr (le_trans this (disjoint_iff_inf_le.mp ?_))
  apply Disjoint.mono_left (iSup_genEigenspace_inf_le_add (f x) (f y) (μ x) (μ y) (h x y))
  simp only [g, map_add]
  exact disjoint_iSup_genEigenspace (f x + f y) (Ne.symm contra)

end End

end Module
