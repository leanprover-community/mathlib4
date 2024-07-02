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

#align_import linear_algebra.eigenspace.basic from "leanprover-community/mathlib"@"6b0169218d01f2837d79ea2784882009a0da1aa1"

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

open FiniteDimensional Set

variable {K R : Type v} {V M : Type w} [CommRing R] [AddCommGroup M] [Module R M] [Field K]
  [AddCommGroup V] [Module K V]

/-- The submodule `eigenspace f μ` for a linear map `f` and a scalar `μ` consists of all vectors `x`
    such that `f x = μ • x`. (Def 5.36 of [axler2015])-/
def eigenspace (f : End R M) (μ : R) : Submodule R M :=
  LinearMap.ker (f - algebraMap R (End R M) μ)
#align module.End.eigenspace Module.End.eigenspace

@[simp]
theorem eigenspace_zero (f : End R M) : f.eigenspace 0 = LinearMap.ker f := by simp [eigenspace]
#align module.End.eigenspace_zero Module.End.eigenspace_zero

/-- A nonzero element of an eigenspace is an eigenvector. (Def 5.7 of [axler2015]) -/
def HasEigenvector (f : End R M) (μ : R) (x : M) : Prop :=
  x ∈ eigenspace f μ ∧ x ≠ 0
#align module.End.has_eigenvector Module.End.HasEigenvector

/-- A scalar `μ` is an eigenvalue for a linear map `f` if there are nonzero vectors `x`
    such that `f x = μ • x`. (Def 5.5 of [axler2015]) -/
def HasEigenvalue (f : End R M) (a : R) : Prop :=
  eigenspace f a ≠ ⊥
#align module.End.has_eigenvalue Module.End.HasEigenvalue

/-- The eigenvalues of the endomorphism `f`, as a subtype of `R`. -/
def Eigenvalues (f : End R M) : Type _ :=
  { μ : R // f.HasEigenvalue μ }
#align module.End.eigenvalues Module.End.Eigenvalues

@[coe]
def Eigenvalues.val (f : Module.End R M) : Eigenvalues f → R := Subtype.val

instance Eigenvalues.instCoeOut {f : Module.End R M} : CoeOut (Eigenvalues f) R where
  coe := Eigenvalues.val f

instance Eigenvalues.instDecidableEq [DecidableEq R] (f : Module.End R M) :
    DecidableEq (Eigenvalues f) :=
  inferInstanceAs (DecidableEq (Subtype (fun x : R => HasEigenvalue f x)))

theorem hasEigenvalue_of_hasEigenvector {f : End R M} {μ : R} {x : M} (h : HasEigenvector f μ x) :
    HasEigenvalue f μ := by
  rw [HasEigenvalue, Submodule.ne_bot_iff]
  use x; exact h
#align module.End.has_eigenvalue_of_has_eigenvector Module.End.hasEigenvalue_of_hasEigenvector

theorem mem_eigenspace_iff {f : End R M} {μ : R} {x : M} : x ∈ eigenspace f μ ↔ f x = μ • x := by
  rw [eigenspace, LinearMap.mem_ker, LinearMap.sub_apply, algebraMap_end_apply, sub_eq_zero]
#align module.End.mem_eigenspace_iff Module.End.mem_eigenspace_iff

theorem HasEigenvector.apply_eq_smul {f : End R M} {μ : R} {x : M} (hx : f.HasEigenvector μ x) :
    f x = μ • x :=
  mem_eigenspace_iff.mp hx.1
#align module.End.has_eigenvector.apply_eq_smul Module.End.HasEigenvector.apply_eq_smul

theorem HasEigenvector.pow_apply {f : End R M} {μ : R} {v : M} (hv : f.HasEigenvector μ v) (n : ℕ) :
    (f ^ n) v = μ ^ n • v := by
  induction n <;> simp [*, pow_succ f, hv.apply_eq_smul, smul_smul, pow_succ' μ]

theorem HasEigenvalue.exists_hasEigenvector {f : End R M} {μ : R} (hμ : f.HasEigenvalue μ) :
    ∃ v, f.HasEigenvector μ v :=
  Submodule.exists_mem_ne_zero_of_ne_bot hμ
#align module.End.has_eigenvalue.exists_has_eigenvector Module.End.HasEigenvalue.exists_hasEigenvector

lemma HasEigenvalue.pow {f : End R M} {μ : R} (h : f.HasEigenvalue μ) (n : ℕ) :
    (f ^ n).HasEigenvalue (μ ^ n) := by
  rw [HasEigenvalue, Submodule.ne_bot_iff]
  obtain ⟨m : M, hm⟩ := h.exists_hasEigenvector
  exact ⟨m, by simpa [mem_eigenspace_iff] using hm.pow_apply n, hm.2⟩

/-- A nilpotent endomorphism has nilpotent eigenvalues.

See also `LinearMap.isNilpotent_trace_of_isNilpotent`. -/
lemma HasEigenvalue.isNilpotent_of_isNilpotent [NoZeroSMulDivisors R M] {f : End R M}
    (hfn : IsNilpotent f) {μ : R} (hf : f.HasEigenvalue μ) :
    IsNilpotent μ := by
  obtain ⟨m : M, hm⟩ := hf.exists_hasEigenvector
  obtain ⟨n : ℕ, hn : f ^ n = 0⟩ := hfn
  exact ⟨n, by simpa [hn, hm.2, eq_comm (a := (0 : M))] using hm.pow_apply n⟩

theorem HasEigenvalue.mem_spectrum {f : End R M} {μ : R} (hμ : HasEigenvalue f μ) :
    μ ∈ spectrum R f := by
  refine spectrum.mem_iff.mpr fun h_unit => ?_
  set f' := LinearMap.GeneralLinearGroup.toLinearEquiv h_unit.unit
  rcases hμ.exists_hasEigenvector with ⟨v, hv⟩
  refine hv.2 ((LinearMap.ker_eq_bot'.mp f'.ker) v (?_ : μ • v - f v = 0))
  rw [hv.apply_eq_smul, sub_self]
#align module.End.mem_spectrum_of_has_eigenvalue Module.End.HasEigenvalue.mem_spectrum

theorem hasEigenvalue_iff_mem_spectrum [FiniteDimensional K V] {f : End K V} {μ : K} :
    f.HasEigenvalue μ ↔ μ ∈ spectrum K f := by
  rw [spectrum.mem_iff, IsUnit.sub_iff, LinearMap.isUnit_iff_ker_eq_bot, HasEigenvalue, eigenspace]
#align module.End.has_eigenvalue_iff_mem_spectrum Module.End.hasEigenvalue_iff_mem_spectrum

alias ⟨_, HasEigenvalue.of_mem_spectrum⟩ := hasEigenvalue_iff_mem_spectrum

theorem eigenspace_div (f : End K V) (a b : K) (hb : b ≠ 0) :
    eigenspace f (a / b) = LinearMap.ker (b • f - algebraMap K (End K V) a) :=
  calc
    eigenspace f (a / b) = eigenspace f (b⁻¹ * a) := by rw [div_eq_mul_inv, mul_comm]
    _ = LinearMap.ker (f - (b⁻¹ * a) • LinearMap.id) := by rw [eigenspace]; rfl
    _ = LinearMap.ker (f - b⁻¹ • a • LinearMap.id) := by rw [smul_smul]
    _ = LinearMap.ker (f - b⁻¹ • algebraMap K (End K V) a) := rfl
    _ = LinearMap.ker (b • (f - b⁻¹ • algebraMap K (End K V) a)) := by
        rw [LinearMap.ker_smul _ b hb]
    _ = LinearMap.ker (b • f - algebraMap K (End K V) a) := by rw [smul_sub, smul_inv_smul₀ hb]
#align module.End.eigenspace_div Module.End.eigenspace_div

/-- The generalized eigenspace for a linear map `f`, a scalar `μ`, and an exponent `k ∈ ℕ` is the
kernel of `(f - μ • id) ^ k`. (Def 8.10 of [axler2015]). Furthermore, a generalized eigenspace for
some exponent `k` is contained in the generalized eigenspace for exponents larger than `k`. -/
def genEigenspace (f : End R M) (μ : R) : ℕ →o Submodule R M where
  toFun k := LinearMap.ker ((f - algebraMap R (End R M) μ) ^ k)
  monotone' k m hm := by
    simp only [← pow_sub_mul_pow _ hm]
    exact
      LinearMap.ker_le_ker_comp ((f - algebraMap R (End R M) μ) ^ k)
        ((f - algebraMap R (End R M) μ) ^ (m - k))
#align module.End.generalized_eigenspace Module.End.genEigenspace

@[simp]
theorem mem_genEigenspace (f : End R M) (μ : R) (k : ℕ) (m : M) :
    m ∈ f.genEigenspace μ k ↔ ((f - μ • (1 : End R M)) ^ k) m = 0 := Iff.rfl
#align module.End.mem_generalized_eigenspace Module.End.mem_genEigenspace

@[simp]
theorem genEigenspace_zero (f : End R M) (k : ℕ) :
    f.genEigenspace 0 k = LinearMap.ker (f ^ k) := by
  simp [Module.End.genEigenspace]
#align module.End.generalized_eigenspace_zero Module.End.genEigenspace_zero

/-- A nonzero element of a generalized eigenspace is a generalized eigenvector.
    (Def 8.9 of [axler2015])-/
def HasGenEigenvector (f : End R M) (μ : R) (k : ℕ) (x : M) : Prop :=
  x ≠ 0 ∧ x ∈ genEigenspace f μ k
#align module.End.has_generalized_eigenvector Module.End.HasGenEigenvector

/-- A scalar `μ` is a generalized eigenvalue for a linear map `f` and an exponent `k ∈ ℕ` if there
    are generalized eigenvectors for `f`, `k`, and `μ`. -/
def HasGenEigenvalue (f : End R M) (μ : R) (k : ℕ) : Prop :=
  genEigenspace f μ k ≠ ⊥
#align module.End.has_generalized_eigenvalue Module.End.HasGenEigenvalue

/-- The generalized eigenrange for a linear map `f`, a scalar `μ`, and an exponent `k ∈ ℕ` is the
    range of `(f - μ • id) ^ k`. -/
def genEigenrange (f : End R M) (μ : R) (k : ℕ) : Submodule R M :=
  LinearMap.range ((f - algebraMap R (End R M) μ) ^ k)
#align module.End.generalized_eigenrange Module.End.genEigenrange

/-- The exponent of a generalized eigenvalue is never 0. -/
theorem exp_ne_zero_of_hasGenEigenvalue {f : End R M} {μ : R} {k : ℕ}
    (h : f.HasGenEigenvalue μ k) : k ≠ 0 := by
  rintro rfl
  exact h LinearMap.ker_id
#align module.End.exp_ne_zero_of_has_generalized_eigenvalue Module.End.exp_ne_zero_of_hasGenEigenvalue

/-- The union of the kernels of `(f - μ • id) ^ k` over all `k`. -/
def maxGenEigenspace (f : End R M) (μ : R) : Submodule R M :=
  ⨆ k, f.genEigenspace μ k
#align module.End.maximal_generalized_eigenspace Module.End.maxGenEigenspace

theorem genEigenspace_le_maximal (f : End R M) (μ : R) (k : ℕ) :
    f.genEigenspace μ k ≤ f.maxGenEigenspace μ :=
  le_iSup _ _
#align module.End.generalized_eigenspace_le_maximal Module.End.genEigenspace_le_maximal

@[simp]
theorem mem_maxGenEigenspace (f : End R M) (μ : R) (m : M) :
    m ∈ f.maxGenEigenspace μ ↔ ∃ k : ℕ, ((f - μ • (1 : End R M)) ^ k) m = 0 := by
  simp only [maxGenEigenspace, ← mem_genEigenspace, Submodule.mem_iSup_of_chain]
#align module.End.mem_maximal_generalized_eigenspace Module.End.mem_maxGenEigenspace

/-- If there exists a natural number `k` such that the kernel of `(f - μ • id) ^ k` is the
maximal generalized eigenspace, then this value is the least such `k`. If not, this value is not
meaningful. -/
noncomputable def maxGenEigenspaceIndex (f : End R M) (μ : R) :=
  monotonicSequenceLimitIndex (f.genEigenspace μ)
#align module.End.maximal_generalized_eigenspace_index Module.End.maxGenEigenspaceIndex

/-- For an endomorphism of a Noetherian module, the maximal eigenspace is always of the form kernel
`(f - μ • id) ^ k` for some `k`. -/
theorem maxGenEigenspace_eq [h : IsNoetherian R M] (f : End R M) (μ : R) :
    maxGenEigenspace f μ =
      f.genEigenspace μ (maxGenEigenspaceIndex f μ) := by
  rw [isNoetherian_iff_wellFounded] at h
  exact (WellFounded.iSup_eq_monotonicSequenceLimit h (f.genEigenspace μ) : _)
#align module.End.maximal_generalized_eigenspace_eq Module.End.maxGenEigenspace_eq

/-- A generalized eigenvalue for some exponent `k` is also
    a generalized eigenvalue for exponents larger than `k`. -/
theorem hasGenEigenvalue_of_hasGenEigenvalue_of_le {f : End R M} {μ : R} {k : ℕ}
    {m : ℕ} (hm : k ≤ m) (hk : f.HasGenEigenvalue μ k) :
    f.HasGenEigenvalue μ m := by
  unfold HasGenEigenvalue at *
  contrapose! hk
  rw [← le_bot_iff, ← hk]
  exact (f.genEigenspace μ).monotone hm
#align module.End.has_generalized_eigenvalue_of_has_generalized_eigenvalue_of_le Module.End.hasGenEigenvalue_of_hasGenEigenvalue_of_le

/-- The eigenspace is a subspace of the generalized eigenspace. -/
theorem eigenspace_le_genEigenspace {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k) :
    f.eigenspace μ ≤ f.genEigenspace μ k :=
  (f.genEigenspace μ).monotone (Nat.succ_le_of_lt hk)
#align module.End.eigenspace_le_generalized_eigenspace Module.End.eigenspace_le_genEigenspace

/-- All eigenvalues are generalized eigenvalues. -/
theorem hasGenEigenvalue_of_hasEigenvalue {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k)
    (hμ : f.HasEigenvalue μ) : f.HasGenEigenvalue μ k := by
  apply hasGenEigenvalue_of_hasGenEigenvalue_of_le hk
  rw [HasGenEigenvalue, genEigenspace, OrderHom.coe_mk, pow_one]
  exact hμ
#align module.End.has_generalized_eigenvalue_of_has_eigenvalue Module.End.hasGenEigenvalue_of_hasEigenvalue

/-- All generalized eigenvalues are eigenvalues. -/
theorem hasEigenvalue_of_hasGenEigenvalue {f : End R M} {μ : R} {k : ℕ}
    (hμ : f.HasGenEigenvalue μ k) : f.HasEigenvalue μ := by
  intro contra; apply hμ
  erw [LinearMap.ker_eq_bot] at contra ⊢; rw [LinearMap.coe_pow]
  exact Function.Injective.iterate contra k
#align module.End.has_eigenvalue_of_has_generalized_eigenvalue Module.End.hasEigenvalue_of_hasGenEigenvalue

/-- Generalized eigenvalues are actually just eigenvalues. -/
@[simp]
theorem hasGenEigenvalue_iff_hasEigenvalue {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k) :
    f.HasGenEigenvalue μ k ↔ f.HasEigenvalue μ :=
  ⟨hasEigenvalue_of_hasGenEigenvalue, hasGenEigenvalue_of_hasEigenvalue hk⟩
#align module.End.has_generalized_eigenvalue_iff_has_eigenvalue Module.End.hasGenEigenvalue_iff_hasEigenvalue

/-- Every generalized eigenvector is a generalized eigenvector for exponent `finrank K V`.
    (Lemma 8.11 of [axler2015]) -/
theorem genEigenspace_le_genEigenspace_finrank [FiniteDimensional K V] (f : End K V)
    (μ : K) (k : ℕ) : f.genEigenspace μ k ≤ f.genEigenspace μ (finrank K V) :=
  ker_pow_le_ker_pow_finrank _ _
#align module.End.generalized_eigenspace_le_generalized_eigenspace_finrank Module.End.genEigenspace_le_genEigenspace_finrank

@[simp] theorem iSup_genEigenspace_eq_genEigenspace_finrank
    [FiniteDimensional K V] (f : End K V) (μ : K) :
    ⨆ k, f.genEigenspace μ k = f.genEigenspace μ (finrank K V) :=
  le_antisymm (iSup_le (genEigenspace_le_genEigenspace_finrank f μ)) (le_iSup _ _)

/-- Generalized eigenspaces for exponents at least `finrank K V` are equal to each other. -/
theorem genEigenspace_eq_genEigenspace_finrank_of_le [FiniteDimensional K V]
    (f : End K V) (μ : K) {k : ℕ} (hk : finrank K V ≤ k) :
    f.genEigenspace μ k = f.genEigenspace μ (finrank K V) :=
  ker_pow_eq_ker_pow_finrank_of_le hk
#align module.End.generalized_eigenspace_eq_generalized_eigenspace_finrank_of_le Module.End.genEigenspace_eq_genEigenspace_finrank_of_le

lemma mapsTo_genEigenspace_of_comm {f g : End R M} (h : Commute f g) (μ : R) (k : ℕ) :
    MapsTo g (f.genEigenspace μ k) (f.genEigenspace μ k) := by
  replace h : Commute ((f - μ • (1 : End R M)) ^ k) g :=
    (h.sub_left <| Algebra.commute_algebraMap_left μ g).pow_left k
  intro x hx
  simp only [SetLike.mem_coe, mem_genEigenspace] at hx ⊢
  rw [← LinearMap.comp_apply, ← LinearMap.mul_eq_comp, h.eq, LinearMap.mul_eq_comp,
    LinearMap.comp_apply, hx, map_zero]

lemma mapsTo_iSup_genEigenspace_of_comm {f g : End R M} (h : Commute f g) (μ : R) :
    MapsTo g ↑(⨆ k, f.genEigenspace μ k) ↑(⨆ k, f.genEigenspace μ k) := by
  simp only [MapsTo, Submodule.coe_iSup_of_chain, mem_iUnion, SetLike.mem_coe]
  rintro x ⟨k, hk⟩
  exact ⟨k, f.mapsTo_genEigenspace_of_comm h μ k hk⟩

/-- The restriction of `f - μ • 1` to the `k`-fold generalized `μ`-eigenspace is nilpotent. -/
lemma isNilpotent_restrict_sub_algebraMap (f : End R M) (μ : R) (k : ℕ)
    (h : MapsTo (f - algebraMap R (End R M) μ)
      (f.genEigenspace μ k) (f.genEigenspace μ k) :=
      mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ k) :
    IsNilpotent ((f - algebraMap R (End R M) μ).restrict h) := by
  use k
  ext
  simp [LinearMap.restrict_apply, LinearMap.pow_restrict _]

/-- The restriction of `f - μ • 1` to the generalized `μ`-eigenspace is nilpotent. -/
lemma isNilpotent_restrict_iSup_sub_algebraMap [IsNoetherian R M] (f : End R M) (μ : R)
    (h : MapsTo (f - algebraMap R (End R M) μ)
      ↑(⨆ k, f.genEigenspace μ k) ↑(⨆ k, f.genEigenspace μ k) :=
      mapsTo_iSup_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ) :
    IsNilpotent ((f - algebraMap R (End R M) μ).restrict h) := by
  obtain ⟨l, hl⟩ : ∃ l, ⨆ k, f.genEigenspace μ k = f.genEigenspace μ l :=
    ⟨_, maxGenEigenspace_eq f μ⟩
  use l
  ext ⟨x, hx⟩
  simpa [hl, LinearMap.restrict_apply, LinearMap.pow_restrict _] using hx

lemma disjoint_genEigenspace [NoZeroSMulDivisors R M]
    (f : End R M) {μ₁ μ₂ : R} (hμ : μ₁ ≠ μ₂) (k l : ℕ) :
    Disjoint (f.genEigenspace μ₁ k) (f.genEigenspace μ₂ l) := by
  nontriviality M
  have := NoZeroSMulDivisors.isReduced R M
  rw [disjoint_iff]
  set p := f.genEigenspace μ₁ k ⊓ f.genEigenspace μ₂ l
  by_contra hp
  replace hp : Nontrivial p := Submodule.nontrivial_iff_ne_bot.mpr hp
  let f₁ : End R p := (f - algebraMap R (End R M) μ₁).restrict <| MapsTo.inter_inter
    (mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₁) μ₁ k)
    (mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₁) μ₂ l)
  let f₂ : End R p := (f - algebraMap R (End R M) μ₂).restrict <| MapsTo.inter_inter
    (mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₂) μ₁ k)
    (mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₂) μ₂ l)
  have : IsNilpotent (f₂ - f₁) := by
    apply Commute.isNilpotent_sub (x := f₂) (y := f₁) _ ⟨l, ?_⟩ ⟨k, ?_⟩
    · ext; simp [f₁, f₂, smul_sub, sub_sub, smul_comm μ₁, add_sub_left_comm]
    all_goals ext ⟨x, _, _⟩; simpa [LinearMap.restrict_apply, LinearMap.pow_restrict _] using ‹_›
  have hf₁₂ : f₂ - f₁ = algebraMap R (End R p) (μ₁ - μ₂) := by ext; simp [f₁, f₂, sub_smul]
  rw [hf₁₂, IsNilpotent.map_iff (NoZeroSMulDivisors.algebraMap_injective R (End R p)),
    isNilpotent_iff_eq_zero, sub_eq_zero] at this
  contradiction

lemma disjoint_iSup_genEigenspace [NoZeroSMulDivisors R M]
    (f : End R M) {μ₁ μ₂ : R} (hμ : μ₁ ≠ μ₂) :
    Disjoint (⨆ k, f.genEigenspace μ₁ k) (⨆ k, f.genEigenspace μ₂ k) := by
  simp_rw [(f.genEigenspace μ₁).mono.directed_le.disjoint_iSup_left,
    (f.genEigenspace μ₂).mono.directed_le.disjoint_iSup_right]
  exact disjoint_genEigenspace f hμ

lemma injOn_genEigenspace [NoZeroSMulDivisors R M] (f : End R M) :
    InjOn (⨆ k, f.genEigenspace · k) {μ | ⨆ k, f.genEigenspace μ k ≠ ⊥} := by
  rintro μ₁ _ μ₂ hμ₂ (hμ₁₂ : ⨆ k, f.genEigenspace μ₁ k = ⨆ k, f.genEigenspace μ₂ k)
  by_contra contra
  apply hμ₂
  simpa only [hμ₁₂, disjoint_self] using f.disjoint_iSup_genEigenspace contra

theorem independent_genEigenspace [NoZeroSMulDivisors R M] (f : End R M) :
    CompleteLattice.Independent (fun μ ↦ ⨆ k, f.genEigenspace μ k) := by
  classical
  suffices ∀ μ (s : Finset R), μ ∉ s → Disjoint (⨆ k, f.genEigenspace μ k)
      (s.sup fun μ ↦ ⨆ k, f.genEigenspace μ k) by
    simp_rw [CompleteLattice.independent_iff_supIndep_of_injOn f.injOn_genEigenspace,
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

/-- The eigenspaces of a linear operator form an independent family of subspaces of `M`.  That is,
any eigenspace has trivial intersection with the span of all the other eigenspaces. -/
theorem eigenspaces_independent [NoZeroSMulDivisors R M] (f : End R M) :
    CompleteLattice.Independent f.eigenspace :=
  f.independent_genEigenspace.mono fun μ ↦ le_iSup (genEigenspace f μ) 1

/-- Eigenvectors corresponding to distinct eigenvalues of a linear operator are linearly
    independent. (Lemma 5.10 of [axler2015])

    We use the eigenvalues as indexing set to ensure that there is only one eigenvector for each
    eigenvalue in the image of `xs`. -/
theorem eigenvectors_linearIndependent [NoZeroSMulDivisors R M]
    (f : End R M) (μs : Set R) (xs : μs → M)
    (h_eigenvec : ∀ μ : μs, f.HasEigenvector μ (xs μ)) : LinearIndependent R xs :=
  CompleteLattice.Independent.linearIndependent _
    (f.eigenspaces_independent.comp Subtype.coe_injective) (fun μ => (h_eigenvec μ).1) fun μ =>
    (h_eigenvec μ).2
#align module.End.eigenvectors_linear_independent Module.End.eigenvectors_linearIndependent

/-- If `f` maps a subspace `p` into itself, then the generalized eigenspace of the restriction
    of `f` to `p` is the part of the generalized eigenspace of `f` that lies in `p`. -/
theorem genEigenspace_restrict (f : End R M) (p : Submodule R M) (k : ℕ) (μ : R)
    (hfp : ∀ x : M, x ∈ p → f x ∈ p) :
    genEigenspace (LinearMap.restrict f hfp) μ k =
      Submodule.comap p.subtype (f.genEigenspace μ k) := by
  simp only [genEigenspace, OrderHom.coe_mk, ← LinearMap.ker_comp]
  induction' k with k ih
  · rw [pow_zero, pow_zero, LinearMap.one_eq_id]
    apply (Submodule.ker_subtype _).symm
  · erw [pow_succ, pow_succ, LinearMap.ker_comp, LinearMap.ker_comp, ih, ← LinearMap.ker_comp,
      LinearMap.comp_assoc]
#align module.End.generalized_eigenspace_restrict Module.End.genEigenspace_restrict

lemma _root_.Submodule.inf_genEigenspace (f : End R M) (p : Submodule R M) {k : ℕ} {μ : R}
    (hfp : ∀ x : M, x ∈ p → f x ∈ p) :
    p ⊓ f.genEigenspace μ k =
      (genEigenspace (LinearMap.restrict f hfp) μ k).map p.subtype := by
  rw [f.genEigenspace_restrict _ _ _ hfp, Submodule.map_comap_eq, Submodule.range_subtype]

/-- If `p` is an invariant submodule of an endomorphism `f`, then the `μ`-eigenspace of the
restriction of `f` to `p` is a submodule of the `μ`-eigenspace of `f`. -/
theorem eigenspace_restrict_le_eigenspace (f : End R M) {p : Submodule R M} (hfp : ∀ x ∈ p, f x ∈ p)
    (μ : R) : (eigenspace (f.restrict hfp) μ).map p.subtype ≤ f.eigenspace μ := by
  rintro a ⟨x, hx, rfl⟩
  simp only [SetLike.mem_coe, mem_eigenspace_iff, LinearMap.restrict_apply] at hx ⊢
  exact congr_arg Subtype.val hx
#align module.End.eigenspace_restrict_le_eigenspace Module.End.eigenspace_restrict_le_eigenspace

/-- Generalized eigenrange and generalized eigenspace for exponent `finrank K V` are disjoint. -/
theorem generalized_eigenvec_disjoint_range_ker [FiniteDimensional K V] (f : End K V) (μ : K) :
    Disjoint (f.genEigenrange μ (finrank K V))
      (f.genEigenspace μ (finrank K V)) := by
  have h :=
    calc
      Submodule.comap ((f - algebraMap _ _ μ) ^ finrank K V)
        (f.genEigenspace μ (finrank K V)) =
          LinearMap.ker ((f - algebraMap _ _ μ) ^ finrank K V *
            (f - algebraMap K (End K V) μ) ^ finrank K V) := by
              rw [genEigenspace, OrderHom.coe_mk, ← LinearMap.ker_comp]; rfl
      _ = f.genEigenspace μ (finrank K V + finrank K V) := by rw [← pow_add]; rfl
      _ = f.genEigenspace μ (finrank K V) := by
        rw [genEigenspace_eq_genEigenspace_finrank_of_le]; omega
  rw [disjoint_iff_inf_le, genEigenrange, LinearMap.range_eq_map,
    Submodule.map_inf_eq_map_inf_comap, top_inf_eq, h]
  apply Submodule.map_comap_le
#align module.End.generalized_eigenvec_disjoint_range_ker Module.End.generalized_eigenvec_disjoint_range_ker

/-- If an invariant subspace `p` of an endomorphism `f` is disjoint from the `μ`-eigenspace of `f`,
then the restriction of `f` to `p` has trivial `μ`-eigenspace. -/
theorem eigenspace_restrict_eq_bot {f : End R M} {p : Submodule R M} (hfp : ∀ x ∈ p, f x ∈ p)
    {μ : R} (hμp : Disjoint (f.eigenspace μ) p) : eigenspace (f.restrict hfp) μ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  simpa using hμp.le_bot ⟨eigenspace_restrict_le_eigenspace f hfp μ ⟨x, hx, rfl⟩, x.prop⟩
#align module.End.eigenspace_restrict_eq_bot Module.End.eigenspace_restrict_eq_bot

/-- The generalized eigenspace of an eigenvalue has positive dimension for positive exponents. -/
theorem pos_finrank_genEigenspace_of_hasEigenvalue [FiniteDimensional K V] {f : End K V}
    {k : ℕ} {μ : K} (hx : f.HasEigenvalue μ) (hk : 0 < k) :
    0 < finrank K (f.genEigenspace μ k) :=
  calc
    0 = finrank K (⊥ : Submodule K V) := by rw [finrank_bot]
    _ < finrank K (f.eigenspace μ) := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.2 hx)
    _ ≤ finrank K (f.genEigenspace μ k) :=
      Submodule.finrank_mono ((f.genEigenspace μ).monotone (Nat.succ_le_of_lt hk))

#align module.End.pos_finrank_generalized_eigenspace_of_has_eigenvalue Module.End.pos_finrank_genEigenspace_of_hasEigenvalue

/-- A linear map maps a generalized eigenrange into itself. -/
theorem map_genEigenrange_le {f : End K V} {μ : K} {n : ℕ} :
    Submodule.map f (f.genEigenrange μ n) ≤ f.genEigenrange μ n :=
  calc
    Submodule.map f (f.genEigenrange μ n) =
      LinearMap.range (f * (f - algebraMap _ _ μ) ^ n) := by
        rw [genEigenrange]; exact (LinearMap.range_comp _ _).symm
    _ = LinearMap.range ((f - algebraMap _ _ μ) ^ n * f) := by
        rw [Algebra.mul_sub_algebraMap_pow_commutes]
    _ = Submodule.map ((f - algebraMap _ _ μ) ^ n) (LinearMap.range f) := LinearMap.range_comp _ _
    _ ≤ f.genEigenrange μ n := LinearMap.map_le_range

#align module.End.map_generalized_eigenrange_le Module.End.map_genEigenrange_le

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
