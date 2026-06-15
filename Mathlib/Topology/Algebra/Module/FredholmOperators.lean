/-
Copyright (c) 2026 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Anatole Dedecker, Patrick Massot, Aaron Liu, Oliver Nash, Filippo A. E. Nuccio
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Perturbation.StrictByFinite
public import Mathlib.RingTheory.Finiteness.Cofinite
public import Mathlib.Topology.Algebra.Module.Complement
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.LinearMap
public import Mathlib.Topology.Maps.Strict.Basic
public import Mathlib.Topology.Homeomorph.Defs

section FindHome

lemma sum_neg_one_pow_eq_zero_of_telescope {n : ℕ} (d : Fin (n + 2) → ℤ) (r : Fin (n + 1) → ℤ)
    (h_first : d 0 = r 0)
    (h_mid : ∀ i : Fin n, d i.succ.castSucc = r i.castSucc + r i.succ)
    (h_last : d (Fin.last _) = r (Fin.last _)) :
    ∑ i, (-1) ^ i.val * d i = 0 := by
  have h_spl1 : ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i.val) * (d i) = (-1 : ℤ) ^ 0 * (d 0) +
    ∑ i : Fin n, (-1 : ℤ) ^ (i.val + 1) * (d (Fin.succ (Fin.castSucc i))) +
      (-1 : ℤ) ^ (n + 1) * (d (Fin.last (n + 1))) := by
    have h_spl2 : ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i.val) * (d i) = (-1 : ℤ) ^ 0 * (d 0) +
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i.val + 1) * (d (Fin.succ i)) := by
        rw [Fin.sum_univ_succ]
        aesop
    simp only [h_spl2, Int.reduceNeg, pow_zero, one_mul, Fin.sum_univ_castSucc, Fin.val_castSucc,
      Fin.val_last, Fin.succ_last, Nat.succ_eq_add_one]
    ring
  have h_middle : ∑ i : Fin n, (-1 : ℤ) ^ (i.val + 1) * ((r (Fin.castSucc i)) +
    (r (Fin.succ i))) = ∑ i : Fin n, (-1 : ℤ) ^ (i.val + 1) * (r (Fin.castSucc i)) +
      ∑ i : Fin n, (-1 : ℤ) ^ (i.val + 1) * (r (Fin.succ i)) := by
    simp only [mul_add, Finset.sum_add_distrib]
  have := Fin.sum_univ_castSucc fun i ↦ (-1 : ℤ) ^ (i : ℕ) * r i
  have := Fin.sum_univ_succ fun i ↦ (-1 : ℤ) ^ (i : ℕ) * r i
  simp_all [Fin.sum_univ_succ, pow_succ']
  grind

open Function Module

lemma Module.sum_neg_one_pow_finrank_eq_zero_of_exact {n : ℕ} {k : Type*} (V : Fin (n + 2) → Type*)
    [Field k] [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)]
    (f : (i : Fin (n + 1)) → V i.castSucc →ₗ[k] V i.succ)
    (inj : Injective (f 0))
    (h_exact : ∀ i : Fin n, Exact (f i.castSucc) (f i.succ))
    (surj : Surjective (f (Fin.last _))) :
    ∑ i, (-1) ^ i.val * (finrank k (V i) : ℤ) = 0 := by
  apply sum_neg_one_pow_eq_zero_of_telescope _ _ _ _ _
  · use fun i ↦ finrank k <| LinearMap.range (f i)
  · exact ((fun {m n} ↦ Int.ofNat_inj.mpr) <| LinearMap.finrank_range_of_inj inj).symm
  · intro i
    grind [(h_exact i).linearMap_ker_eq, (f i.succ).finrank_range_add_finrank_ker]
  · rw [LinearMap.range_eq_top.mpr surj, finrank_top]
    rfl

universe u

-- Still not universe polymorphic; exposes some annoying typeclass wrangling.
lemma Module.sum_neg_one_pow_finrank_eq_zero_of_exact_six' {k : Type*} [Field k]
    {V₀ V₁ V₂ V₃ V₄ V₅ : Type u}
    [AddCommGroup V₀] [Module k V₀] [FiniteDimensional k V₀]
    [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
    [AddCommGroup V₃] [Module k V₃] [FiniteDimensional k V₃]
    [AddCommGroup V₄] [Module k V₄] [FiniteDimensional k V₄]
    [AddCommGroup V₅] [Module k V₅] [FiniteDimensional k V₅]
    (f₀ : V₀ →ₗ[k] V₁) (f₁ : V₁ →ₗ[k] V₂) (f₂ : V₂ →ₗ[k] V₃) (f₃ : V₃ →ₗ[k] V₄) (f₄ : V₄ →ₗ[k] V₅)
    (inj : Injective f₀)
    (exact₁ : Exact f₀ f₁)
    (exact₂ : Exact f₁ f₂)
    (exact₃ : Exact f₂ f₃)
    (exact₄ : Exact f₃ f₄)
    (surj : Surjective f₄) :
    (finrank k V₀ : ℤ) - finrank k V₁ + finrank k V₂ -
      finrank k V₃ + finrank k V₄ - finrank k V₅ = 0 := by
  letI Vs := ![V₀, V₁, V₂, V₃, V₄, V₅]
  letI _i1 (i : Fin 6) : AddCommGroup (Vs i) := by unfold Vs; exact match i with
  | 0 => inferInstanceAs (AddCommGroup V₀)
  | 1 => inferInstanceAs (AddCommGroup V₁)
  | 2 => inferInstanceAs (AddCommGroup V₂)
  | 3 => inferInstanceAs (AddCommGroup V₃)
  | 4 => inferInstanceAs (AddCommGroup V₄)
  | 5 => inferInstanceAs (AddCommGroup V₅)
  letI _i2 (i : Fin 6) : Module k (Vs i) := by unfold _i1; exact match i with
  | 0 => inferInstanceAs (Module k V₀)
  | 1 => inferInstanceAs (Module k V₁)
  | 2 => inferInstanceAs (Module k V₂)
  | 3 => inferInstanceAs (Module k V₃)
  | 4 => inferInstanceAs (Module k V₄)
  | 5 => inferInstanceAs (Module k V₅)
  have (i : Fin 6) : FiniteDimensional k (Vs i) := match i with
  | 0 => inferInstanceAs (FiniteDimensional k V₀)
  | 1 => inferInstanceAs (FiniteDimensional k V₁)
  | 2 => inferInstanceAs (FiniteDimensional k V₂)
  | 3 => inferInstanceAs (FiniteDimensional k V₃)
  | 4 => inferInstanceAs (FiniteDimensional k V₄)
  | 5 => inferInstanceAs (FiniteDimensional k V₅)
  letI fs (i : Fin 5) : Vs i.castSucc →ₗ[k] Vs i.succ := match i with
  | 0 => f₀
  | 1 => f₁
  | 2 => f₂
  | 3 => f₃
  | 4 => f₄
  simpa [Fin.sum_univ_six] using Module.sum_neg_one_pow_finrank_eq_zero_of_exact
    ![V₀, V₁, V₂, V₃, V₄, V₅] fs inj
    (fun i ↦ by fin_cases i; exacts [exact₁, exact₂, exact₃, exact₄]) surj

-- Would be nice to obtain via a `simproc`.
universe u₀ u₁ u₂ u₃ u₄ u₅
lemma Module.sum_neg_one_pow_finrank_eq_zero_of_exact_six {k : Type*} [Field k]
    {V₀ : Type u₀} [AddCommGroup V₀] [Module k V₀] [FiniteDimensional k V₀]
    {V₁ : Type u₁} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    {V₂ : Type u₂} [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
    {V₃ : Type u₃} [AddCommGroup V₃] [Module k V₃] [FiniteDimensional k V₃]
    {V₄ : Type u₄} [AddCommGroup V₄] [Module k V₄] [FiniteDimensional k V₄]
    {V₅ : Type u₅} [AddCommGroup V₅] [Module k V₅] [FiniteDimensional k V₅]
    (f₀ : V₀ →ₗ[k] V₁) (f₁ : V₁ →ₗ[k] V₂) (f₂ : V₂ →ₗ[k] V₃) (f₃ : V₃ →ₗ[k] V₄) (f₄ : V₄ →ₗ[k] V₅)
    (inj : Injective f₀)
    (exact₁ : Exact f₀ f₁)
    (exact₂ : Exact f₁ f₂)
    (exact₃ : Exact f₂ f₃)
    (exact₄ : Exact f₃ f₄)
    (surj : Surjective f₄) :
    (finrank k V₀ : ℤ) - finrank k V₁ + finrank k V₂ -
      finrank k V₃ + finrank k V₄ - finrank k V₅ = 0 := by
  let W₀ := ULift.{max u₀ u₁ u₂ u₃ u₄ u₅} V₀
  let W₁ := ULift.{max u₀ u₁ u₂ u₃ u₄ u₅} V₁
  let W₂ := ULift.{max u₀ u₁ u₂ u₃ u₄ u₅} V₂
  let W₃ := ULift.{max u₀ u₁ u₂ u₃ u₄ u₅} V₃
  let W₄ := ULift.{max u₀ u₁ u₂ u₃ u₄ u₅} V₄
  let W₅ := ULift.{max u₀ u₁ u₂ u₃ u₄ u₅} V₅
  let g₀ : W₀ →ₗ[k] W₁ := ULift.moduleEquiv.symm.toLinearMap ∘ₗ f₀ ∘ₗ ULift.moduleEquiv.toLinearMap
  let g₁ : W₁ →ₗ[k] W₂ := ULift.moduleEquiv.symm.toLinearMap ∘ₗ f₁ ∘ₗ ULift.moduleEquiv.toLinearMap
  let g₂ : W₂ →ₗ[k] W₃ := ULift.moduleEquiv.symm.toLinearMap ∘ₗ f₂ ∘ₗ ULift.moduleEquiv.toLinearMap
  let g₃ : W₃ →ₗ[k] W₄ := ULift.moduleEquiv.symm.toLinearMap ∘ₗ f₃ ∘ₗ ULift.moduleEquiv.toLinearMap
  let g₄ : W₄ →ₗ[k] W₅ := ULift.moduleEquiv.symm.toLinearMap ∘ₗ f₄ ∘ₗ ULift.moduleEquiv.toLinearMap
  have := sum_neg_one_pow_finrank_eq_zero_of_exact_six' g₀ g₁ g₂ g₃ g₄
    (inj := by simpa [g₀]) (surj := by simpa [g₄])
  simp only [W₀, W₁, W₂, W₃, W₄, W₅, finrank_ulift] at this
  apply this <;>
  simpa only [g₀, g₁, g₂, g₃, g₄, LinearEquiv.postcomp_exact_iff_exact,
    LinearEquiv.conj_symm_exact_iff_exact, LinearEquiv.precomp_exact_iff_exact]

end FindHome

public noncomputable section FredholmOperators

variable {𝕜 : Type*} [NormedField 𝕜]
variable {E F : Type*} [AddCommGroup E] [AddCommGroup F] [TopologicalSpace E] [TopologicalSpace F]
  [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
variable [Module 𝕜 E] [Module 𝕜 F]
variable {f : E →L[𝕜] F}


-- TODO: MOVE
@[simp]
lemma FiniteDimensional.range_zero {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} [Semiring R]
  [DivisionRing R₂] [AddCommMonoid M] [AddCommGroup M₂] [Module R M] [Module R₂ M₂] {τ₁₂ : R →+* R₂}
  [RingHomSurjective τ₁₂] : FiniteDimensional R₂ (0 : M →ₛₗ[τ₁₂] M₂).range := by
  rw [← Submodule.fg_iff_finiteDimensional, LinearMap.range_zero]
  exact Submodule.fg_bot

-- TODO: MOVE next to LinearMap.range_smul
lemma LinearMap.range_smul_le {K : Type*} {V : Type*} {V₂ : Type*} [Semifield K] [AddCommMonoid V]
    [Module K V] [AddCommMonoid V₂] [Module K V₂] (f : V →ₗ[K] V₂) (a : K) :
    (a • f).range ≤ f.range := by
  by_cases ha : a = 0
  · simp_all
  · exact f.range_smul a ha |>.le

section
variable {K : Type*} {V : Type*} {V₂ : Type*} [Field K] [AddCommMonoid V]
    [Module K V] [AddCommGroup V₂] [Module K V₂]

def LinearMap.HasFiniteRank (f : V →ₗ[K] V₂) := FiniteDimensional K f.range

@[simp] def LinearMap.HasFiniteRank.smul {f : V →ₗ[K] V₂}
    (hf : f.HasFiniteRank) (c : K) : (c • f).HasFiniteRank := by
  unfold LinearMap.HasFiniteRank at *
  rw [← Submodule.fg_iff_finiteDimensional] at *
  exact hf.of_le <| LinearMap.range_smul_le _ c

@[simp] def LinearMap.HasFiniteRank.zero : (0 : V →ₗ[K] V₂).HasFiniteRank := by
  unfold LinearMap.HasFiniteRank
  simp

@[simp] def LinearMap.HasFiniteRank.neg {f : V →ₗ[K] V₂}
    (hf : f.HasFiniteRank) : (-f).HasFiniteRank := by
  rw [show -f = (-1 : K) • f by module]
  apply hf.smul

@[simp] lemma LinearMap.HasFiniteRank.add {f g : V →ₗ[K] V₂}
    (hf : f.HasFiniteRank) (hg : g.HasFiniteRank) : (f + g).HasFiniteRank := by
  unfold LinearMap.HasFiniteRank at *
  exact Submodule.finiteDimensional_of_le <| LinearMap.range_add_le f g

@[simp] def LinearMap.HasFiniteRank.sub {f g : V →ₗ[K] V₂}
    (hf : f.HasFiniteRank) (hg : g.HasFiniteRank) : (f - g).HasFiniteRank := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

variable {V₃ : Type*} [AddCommGroup V₃] [Module K V₃]

lemma LinearMap.HasFiniteRank.comp_right {u : V →ₗ[K] V₂} (h : u.HasFiniteRank)
    (v : V₂ →ₗ[K] V₃) : (v ∘ₗ u).HasFiniteRank := by
  unfold LinearMap.HasFiniteRank at *
  rw [← Submodule.fg_iff_finiteDimensional, LinearMap.range_comp] at *
  exact Submodule.FG.map v h

lemma LinearMap.HasFiniteRank.comp_left {v : V₂ →ₗ[K] V₃} (h : v.HasFiniteRank)
    (u : V →ₗ[K] V₂) : (v ∘ₗ u).HasFiniteRank := by
  unfold LinearMap.HasFiniteRank at *
  rw [← Submodule.fg_iff_finiteDimensional] at *
  exact h.of_le <| u.range_comp_le_range v

lemma LinearMap.HasFiniteRank.comp_sub_comp {u v : V →ₗ[K] V₂} {u' v' : V₂ →ₗ[K] V₃}
    (h : (u - v).HasFiniteRank) (h' : (u' - v').HasFiniteRank) :
    (u' ∘ₗ u - v' ∘ₗ v).HasFiniteRank := by
  rw [show u' ∘ₗ u - v' ∘ₗ v = (u' - v') ∘ₗ u + v' ∘ₗ (u - v) by ext; simp]
  exact (h'.comp_left u).add <| h.comp_right v'

variable (K V V₂) in
def LinearMap.FiniteRank : Submodule K (V →ₗ[K] V₂) where
  carrier := {u | u.HasFiniteRank}
  add_mem' hu hv := by simp_all
  zero_mem' := by simp
  smul_mem' c hu := by simp_all

namespace LinearMap.FiniteRankSetoid

scoped instance setoid : Setoid (V →ₗ[K] V₂) := (LinearMap.FiniteRank K V V₂).quotientRel

lemma equiv_iff {u v : V →ₗ[K] V₂} : u ≈ v ↔ (u - v).HasFiniteRank := by
  erw [← @Quotient.eq_iff_equiv, Submodule.Quotient.eq]
  rfl

lemma equiv_comp {u v : V →ₗ[K] V₂} {u' v' : V₂ →ₗ[K] V₃} (h : u ≈ v) (h' : u' ≈ v') :
    u' ∘ₗ u ≈ v' ∘ₗ v := by
  rw [equiv_iff] at *
  exact h.comp_sub_comp h'

@[gcongr]
lemma equiv_comp_right {u : V →ₗ[K] V₂} {u' v' : V₂ →ₗ[K] V₃} (h' : u' ≈ v') :
    u' ∘ₗ u ≈ v' ∘ₗ u :=
  equiv_comp (Quotient.exact rfl) h'

@[gcongr]
lemma equiv_comp_left {u v : V →ₗ[K] V₂} {u' : V₂ →ₗ[K] V₃} (h : u ≈ v) :
    u' ∘ₗ u ≈ u' ∘ₗ v :=
  equiv_comp h (Quotient.exact rfl)

end LinearMap.FiniteRankSetoid

section
open scoped LinearMap.FiniteRankSetoid

def LinearMap.LeftQuasiInverse (u : V →ₗ[K] V₂) (v : V₂ →ₗ[K] V) := u ∘ₗ v ≈ .id

def LinearMap.RightQuasiInverse (u : V₃ →ₗ[K] V₂) (v : V₂ →ₗ[K] V₃) := v ∘ₗ u ≈ .id

def LinearMap.QuasiInverse (u : V₃ →ₗ[K] V₂) (v : V₂ →ₗ[K] V₃) :=
  u.LeftQuasiInverse v ∧ u.RightQuasiInverse v

@[symm]
lemma LinearMap.QuasiInverse.symm {u : V₃ →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    (h : u.QuasiInverse v) : v.QuasiInverse u :=
  And.symm h

lemma LinearMap.QuasiInverse.congr {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (h : u.QuasiInverse v) (hu : u' ≈ u) (hv : v' ≈ v) :
    u'.QuasiInverse v' := by
  simp only [QuasiInverse, LeftQuasiInverse, RightQuasiInverse, FiniteRankSetoid.equiv_iff] at *
  constructor
  · rw [show u' ∘ₗ v' - id = (u' ∘ₗ v' - u ∘ₗ v) + (u ∘ₗ v - id) by simp]
    exact (hv.comp_sub_comp hu).add h.1
  · rw [show v' ∘ₗ u' - id = (v' ∘ₗ u' - v ∘ₗ u) + (v ∘ₗ u - id) by simp]
    exact (hu.comp_sub_comp  hv).add h.2

lemma LinearMap.equiv_of_quasiInverse {u : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (h : u.QuasiInverse v) (h' : u.QuasiInverse v') :
    v ≈ v' :=
  calc
    v = v ∘ₗ .id := by simp
    _ ≈ v ∘ₗ (u ∘ₗ v') := by apply FiniteRankSetoid.equiv_comp_left; symm; exact h'.1
    _ = (v ∘ₗ u) ∘ₗ v' := by rw [comp_assoc]
    _ ≈ (.id) ∘ₗ v' := by apply FiniteRankSetoid.equiv_comp_right; exact h.2
    _ = v' := by simp

lemma LinearMap.equiv_of_quasiInverse' {u u' : V₃ →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    (h : u.QuasiInverse v) (h' : u'.QuasiInverse v) :
    u ≈ u' := by
  symm at h h'
  exact equiv_of_quasiInverse h h'

/-- Left quasi-inverses compose in the opposite order. -/
lemma LinearMap.LeftQuasiInverse.comp {V : Type*} [AddCommGroup V] [Module K V]
     {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    {u' : V₂ →ₗ[K] V}
    {v' : V₃ →ₗ[K] V₂} (hu : u'.LeftQuasiInverse u) (hv : v'.LeftQuasiInverse v) :
    (u' ∘ₗ v').LeftQuasiInverse (v ∘ₗ u) :=
  calc
    _ = u' ∘ₗ (v' ∘ₗ v) ∘ₗ u := rfl
    _ ≈ u' ∘ₗ .id ∘ₗ u := by gcongr; exact hv
    _ ≈ .id := hu

/-- Right quasi-inverses compose in the opposite order. -/
lemma LinearMap.RightQuasiInverse.comp {V : Type*} [AddCommGroup V] [Module K V] {u : V →ₗ[K] V₂}
    {v : V₂ →ₗ[K] V₃} {u' : V₂ →ₗ[K] V}
    {v' : V₃ →ₗ[K] V₂} (hu : u'.RightQuasiInverse u) (hv : v'.RightQuasiInverse v) :
    (u' ∘ₗ v').RightQuasiInverse (v ∘ₗ u) :=
  calc
    _ = v ∘ₗ (u ∘ₗ u') ∘ₗ v' := rfl
    _ ≈ v ∘ₗ .id ∘ₗ v' := by gcongr; exact hu
    _ ≈ .id := hv

/-- Quasi-inverses compose in the opposite order. -/
lemma LinearMap.QuasiInverse.comp {V : Type*} [AddCommGroup V] [Module K V] {u : V →ₗ[K] V₂}
    {v : V₂ →ₗ[K] V₃} {u' : V₂ →ₗ[K] V}
    {v' : V₃ →ₗ[K] V₂} (hu : u'.QuasiInverse u) (hv : v'.QuasiInverse v) :
    (u' ∘ₗ v').QuasiInverse (v ∘ₗ u) :=
  ⟨hu.1.comp hv.1, hu.2.comp hv.2⟩

/-- If `u'` is a right quasi-inverse of `u` and `w` is a left quasi-inverse of `v ∘ₗ u`,
then `u ∘ₗ w` is a left quasi-inverse of `v`. -/
lemma LinearMap.LeftQuasiInverse.of_comp_left {V : Type*} [AddCommGroup V] [Module K V]
    {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    {u' : V₂ →ₗ[K] V} {w : V₃ →ₗ[K] V} (hu : u'.RightQuasiInverse u)
    (hw : w.LeftQuasiInverse (v ∘ₗ u)) :
    (u ∘ₗ w).LeftQuasiInverse v := by
  calc
    _ = ((u ∘ₗ w) ∘ₗ v) ∘ₗ .id := rfl
    _ ≈ ((u ∘ₗ w) ∘ₗ v) ∘ₗ (u ∘ₗ u') := by gcongr; symm; exact hu
    _ = u ∘ₗ (w ∘ₗ (v ∘ₗ u)) ∘ₗ u' := rfl
    _ ≈ u ∘ₗ .id ∘ₗ u' := by gcongr; exact hw
    _ ≈ .id := hu

/-- If `u'` is a quasi-inverse of `u` and `w` is a quasi-inverse of `v ∘ₗ u`, then
`u ∘ₗ w` is a quasi-inverse of `v`. -/
lemma LinearMap.QuasiInverse.of_comp_left {V : Type*} [AddCommGroup V] [Module K V]
    {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    {u' : V₂ →ₗ[K] V} {w : V₃ →ₗ[K] V} (hu : u'.QuasiInverse u)
    (hw : w.QuasiInverse (v ∘ₗ u)) :
    (u ∘ₗ w).QuasiInverse v :=
  ⟨LinearMap.LeftQuasiInverse.of_comp_left hu.2 hw.1, hw.2⟩

/-- If `v'` is a left quasi-inverse of `v` and `w` is a right quasi-inverse of `v ∘ₗ u`,
then `w ∘ₗ v` is a right quasi-inverse of `u`. -/
lemma LinearMap.RightQuasiInverse.of_comp_right {V : Type*} [AddCommGroup V] [Module K V]
    {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    {v' : V₃ →ₗ[K] V₂} {w : V₃ →ₗ[K] V} (hv : v'.LeftQuasiInverse v)
    (hw : w.RightQuasiInverse (v ∘ₗ u)) :
    (w ∘ₗ v).RightQuasiInverse u := by
  calc
    _ = .id ∘ₗ (u ∘ₗ (w ∘ₗ v)) := rfl
    _ ≈ (v' ∘ₗ v) ∘ₗ (u ∘ₗ (w ∘ₗ v)) := by gcongr; symm; exact hv
    _ = v' ∘ₗ ((v ∘ₗ u) ∘ₗ w) ∘ₗ v := rfl
    _ ≈ v' ∘ₗ .id ∘ₗ v := by gcongr; exact hw
    _ ≈ .id := hv

/-- If `v'` is a quasi-inverse of `v` and `w` is a quasi-inverse of `v ∘ₗ u`, then
`w ∘ₗ v` is a quasi-inverse of `u`. -/
lemma LinearMap.QuasiInverse.of_comp_right {V : Type*} [AddCommGroup V] [Module K V]
    {u : V →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    {v' : V₃ →ₗ[K] V₂} {w : V₃ →ₗ[K] V} (hv : v'.QuasiInverse v)
    (hw : w.QuasiInverse (v ∘ₗ u)) :
    (w ∘ₗ v).QuasiInverse u :=
  ⟨hw.1, LinearMap.RightQuasiInverse.of_comp_right hv.1 hw.2⟩

end
end

open Topology ContinuousLinearMap Submodule Set

variable (f)

-- **FAE** I'd rather call this `Prop`-like structure `HasFredholmStructure` rather than `Is...`
structure IsFredholmStruct : Prop where
  isStrict : IsStrictMap f
  isClosed_range : IsClosed (f.range : Set F)
  kerFG : FiniteDimensional 𝕜 f.ker
  cokerFG : FiniteDimensional 𝕜 (F ⧸ f.range)
  closedComplemented_ker : f.ker.ClosedComplemented

variable [ContinuousConstSMul 𝕜 E] [ContinuousConstSMul 𝕜 F]

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [Module 𝕜 G] [ContinuousConstSMul 𝕜 G] [ContinuousAdd G]

variable (𝕜 E F) in
def ContinuousLinearMap.FiniteRank : Submodule 𝕜 (E →L[𝕜] F) :=
  Submodule.comap (coeLM 𝕜) (LinearMap.FiniteRank 𝕜 E F)

namespace ContinuousLinearMap.FiniteRankSetoid

scoped instance setoid : Setoid (E →L[𝕜] F) :=
  Setoid.comap ContinuousLinearMap.toLinearMap LinearMap.FiniteRankSetoid.setoid

omit [IsTopologicalAddGroup E] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 E]
  [ContinuousConstSMul 𝕜 F] in
open scoped LinearMap.FiniteRankSetoid in
lemma equiv_iff {u v : E →L[𝕜] F} : (u ≈ v) ↔ u.toLinearMap ≈ v.toLinearMap :=
  Iff.rfl

omit [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
    [ContinuousConstSMul 𝕜 E] [ContinuousConstSMul 𝕜 F] [IsTopologicalAddGroup G]
    [ContinuousConstSMul 𝕜 G] [ContinuousAdd G] in
lemma equiv_comp {u v : E →L[𝕜] F} {u' v' : F →L[𝕜] G} (h : u ≈ v) (h' : u' ≈ v') :
    u' ∘L u ≈ v' ∘L v := by
  rw [equiv_iff] at *
  push_cast
  exact LinearMap.FiniteRankSetoid.equiv_comp h h'

end ContinuousLinearMap.FiniteRankSetoid

section IsFredholmQuot

open scoped ContinuousLinearMap.FiniteRankSetoid

/-FAE: I don't like this definition that seems to fix `g` (making it a structure would be even more
  disgusting). -/
def IsFredholmQuot : Prop := ∃ g : F →L[𝕜] E,
  (f ∘L g ≈ .id 𝕜 F) ∧ (g ∘L f ≈ .id 𝕜 E)

omit [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
  [ContinuousConstSMul 𝕜 E] [ContinuousConstSMul 𝕜 F] in
lemma IsFredholmQuot.iff_toLinearMap :
    IsFredholmQuot f ↔ ∃ g : F →L[𝕜] E, LinearMap.QuasiInverse f.toLinearMap g.toLinearMap := by
  rfl

theorem AnatoleDream (hf : IsFredholmStruct f) : IsFredholmQuot f:= sorry

def AnatoleDream_symm (hf : IsFredholmQuot f) : IsFredholmStruct f := sorry

/- ## API -/

namespace LinearMap

open Module

variable {k : Type*} [Field k] [Module k E] [Module k F] (f : E →ₗ[k] F)

/-- The index of a linear map.

In the case that either the kernel or cokernel is not finite-dimensional, the value is junk. -/
def index : ℤ := finrank k f.ker - finrank k (F ⧸ f.range)

@[simp] lemma index_id :
    (id : E →ₗ[k] E).index = 0 := by
  have : Subsingleton (E ⧸ (⊤ : Submodule k E)) := Submodule.Quotient.subsingleton_iff.mpr rfl
  simp [index, finrank_eq_zero_of_subsingleton]

@[simp] lemma index_zero :
    (0 : E →ₗ[k] F).index = finrank k E - finrank k F := by
  rw [index, ker_zero, range_zero]
  simpa using (Submodule.quotEquivOfEqBot _ rfl).finrank_eq

lemma index_injective {f : E →ₗ[k] F} (hf : Function.Injective f) :
    f.index = - finrank k (F ⧸ f.range) := by
  simpa [LinearMap.index] using LinearMap.ker_eq_bot.2 hf ▸ finrank_bot _ _

lemma index_surjective {f : E →ₗ[k] F} (hf : Function.Surjective f) :
    f.index = finrank k f.ker := by
  rw [LinearMap.index, LinearMap.range_eq_top.mpr hf]
  simp [finrank_eq_zero_of_subsingleton]

lemma index_smul (t : k) (ht : t ≠ 0) :
    (t • f).index = f.index := by
  rw [index, index, ker_smul _ _ ht, range_smul _ _ ht]

@[simp] lemma index_neg :
    (-f).index = f.index := by
  rw [index, index, ker_neg, range_neg]

open Function in
lemma index_comp {G : Type*} [AddCommGroup G] [Module k G] (g : F →ₗ[k] G)
    [FiniteDimensional k f.ker] [FiniteDimensional k g.ker]
    [FiniteDimensional k (F ⧸ f.range)] [FiniteDimensional k (G ⧸ g.range)] :
    (g ∘ₗ f).index = g.index + f.index := by
  -- 0 → f.ker → (g ∘ₗ f).ker → g.ker → f.coker → (g ∘ₗ f).coker → g.coker → 0
  have : FiniteDimensional k (g ∘ₗ f).ker := by rw [ker_comp]; infer_instance
  have : FiniteDimensional k (G ⧸ (g ∘ₗ f).range) := by rw [range_comp]; infer_instance
  let f₀ : f.ker →ₗ[k] (g ∘ₗ f).ker := Submodule.inclusion <| ker_le_ker_comp f g
  let f₁ : (g ∘ₗ f).ker →ₗ[k] g.ker := f.restrict <| by simp
  let f₂ : g.ker →ₗ[k] F ⧸ f.range := f.range.mkQ ∘ₗ g.ker.subtype
  let f₃ : (F ⧸ f.range) →ₗ[k] G ⧸ (g ∘ₗ f).range :=
    f.range.mapQ (g ∘ₗ f).range g <| by rw [← map_le_iff_le_comap, range_comp]
  let f₄ : (G ⧸ (g ∘ₗ f).range) →ₗ[k] G ⧸ g.range := factor <| range_comp_le_range f g
  have h₀ : Injective f₀ := Submodule.inclusion_injective _
  have h₁ : Exact f₀ f₁ := fun ⟨x, hx⟩ ↦ by simp [f₀, f₁, restrict_apply, Submodule.inclusion_apply]
  have h₂ : Exact f₁ f₂ := fun ⟨x, hx⟩ ↦ by aesop (add simp restrict_apply)
  have h₃ : Exact f₂ f₃ := by rw [exact_iff]; simp [f₂, f₃, range_comp, ker_mapQ, comap_map_eq]
  have h₄ : Exact f₃ f₄ := by rw [exact_iff]; simp [f₃, f₄, factor, ker_mapQ, range_mapQ]
  have h₅ : Surjective f₄ := factor_surjective _
  grind [index, sum_neg_one_pow_finrank_eq_zero_of_exact_six f₀ f₁ f₂ f₃ f₄ h₀ h₁ h₂ h₃ h₄ h₅]

lemma index_eq_of_finiteDimensional [FiniteDimensional k E] [FiniteDimensional k F] :
    f.index = finrank k E - finrank k F := by
  -- 0 → f.ker → E → F → f.coker → 0
  rw [index]
  have h₁ := f.range.finrank_quotient_add_finrank
  have h₂ := f.quotKerEquivRange.finrank_eq
  have h₃ := f.ker.finrank_quotient_add_finrank
  grind

end LinearMap

/- ## Kernel -/
variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

variable {u : M →ₗ[R] N}

variable (u) in
def IsFredholm_existsₗ : Prop := ∃ v : N →ₗ[R] M,
  ((u ∘ₗ v - 1).range).FG ∧ ((v ∘ₗ u - 1).range).FG

lemma KernelFG_of_isFredholmₗ (hu : IsFredholm_existsₗ u) : u.ker.FG := by
  obtain ⟨v, -, hv_left⟩ := hu
  have : u.ker ≤ (v.comp u - 1).range := by
    intro x hx
    use -x
    simp only [LinearMap.mem_ker] at hx
    simp
    simp [hx]
  apply Submodule.FG.of_le _ this
  exact hv_left

/- ## Cokernel -/

lemma CokernelFG_of_isFredholm' (hu : IsFredholm_existsₗ u) : (u.range).CoFG := by
  obtain ⟨v, hv, -⟩ := hu
  have : (u ∘ₗ v - (1 : N →ₗ[R] N)).ker ≤ Submodule.comap (1 : N →ₗ[R] N) u.range :=
    fun x hx ↦ by
      use v x
      rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
        Module.End.one_apply, sub_eq_zero] at hx
  exact CoFG.of_le this <| range_fg_iff_ker_cofg.mp hv

/- ## GoodRelation -/

/- ## IsStrict Using Technical Lemma -/

/- ## Fredholm operator is an isomorphism on a finite codim space -/

open ContinuousLinearMap.FiniteRankSetoid

section

variable {u : E →L[𝕜] F} {v : F →L[𝕜] E}

variable [ContinuousConstSMul 𝕜 E]

omit [IsTopologicalAddGroup F] in
theorem ContinuousLinearMap.coFG_eqLocus (hgf : v ∘L u ≈ .id 𝕜 E) :
    (LinearMap.eqLocus (.id 𝕜 E) (v ∘L u)).CoFG := by
  change (LinearMap.eqLocus (LinearMap.id) (v ∘L u).toLinearMap).CoFG
  rw [LinearMap.eqLocus_eq_ker_sub, ← range_fg_iff_ker_cofg, Submodule.fg_iff_finiteDimensional]
  simpa [equiv_iff, LinearMap.FiniteRankSetoid.equiv_iff] using Setoid.symm hgf

omit [IsTopologicalAddGroup F] in
theorem ContinuousLinearMap.id_sub_comp_ker_coFG (hgf : v ∘L u ≈ .id 𝕜 E) :
    (.id 𝕜 E - v ∘L u).ker.CoFG := by
  rw [← range_fg_iff_ker_cofg, Submodule.fg_iff_finiteDimensional]
  simp [equiv_iff, LinearMap.FiniteRankSetoid.equiv_iff] using Setoid.symm hgf

variable [T1Space E] [T1Space F] [ContinuousConstSMul 𝕜 F]

/-- Need rename. -/
theorem aaron (hr : IsFredholmQuot u) :
    ∃ (E₁ : Submodule 𝕜 E) (F₁ : Submodule 𝕜 F), IsClosed E₁.carrier ∧ E₁.CoFG ∧
      IsClosed F₁.carrier ∧ F₁.CoFG ∧ ∃ h : MapsTo u E₁ F₁,
        (u.restrict h).IsInvertible := by
  obtain ⟨v, huv, hvu⟩ := hr
  set E₁ := LinearMap.eqLocus (.id 𝕜 E) (v ∘L u)
  set F₁ := LinearMap.eqLocus (.id 𝕜 F) (u ∘L v)
  have u_mapsto : MapsTo u E₁ F₁ := fun x hx ↦ congr(u $hx)
  have v_mapsto : MapsTo v F₁ E₁ := fun x hx ↦ congr(v $hx)
  refine ⟨E₁, F₁, isClosed_eqLocus _ _, ContinuousLinearMap.coFG_eqLocus hvu, isClosed_eqLocus _ _,
    ContinuousLinearMap.coFG_eqLocus huv, u_mapsto, ?_⟩
  refine .of_inverse (g := v.restrict v_mapsto) ?_ ?_
  · ext ⟨x, hx : x = u (v x)⟩; simp [← hx]
  · ext ⟨x, hx : x = v (u x)⟩; simp [← hx]

end

/- ## Inclusions from closed finite codimension subspaces are Fredholm (Aaron)

Easy for every definition.
The index is the codimension of the range.

(The same is true for quotient by finite dimensional complemented subspaces)
-/

omit [IsTopologicalAddGroup E] [IsTopologicalAddGroup F] in
theorem Topology.IsClosedEmbedding.isFredholmStruct {f : E →L[𝕜] F} [CompleteSpace 𝕜]
    [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] (hf : IsClosedEmbedding f) (hc : f.range.CoFG) :
    IsFredholmStruct f := by
  constructor
  · exact hf.isStrictMap
  · simp
    exact hf.isClosed_range
  · rw [LinearMap.ker_eq_bot.2 hf.injective]
    exact Module.Finite.bot 𝕜 E
  · simp [hc]
  · rw [LinearMap.ker_eq_bot.2 hf.injective]
    exact closedComplemented_bot

omit [IsTopologicalAddGroup E] in
theorem Submodule.isFredholmStruct [CompleteSpace 𝕜] [ContinuousSMul 𝕜 E] {p : Submodule 𝕜 E}
    (hp : IsClosed p.carrier) (hc : p.CoFG) :
    IsFredholmStruct p.subtypeL := by
  refine (IsClosedEmbedding.subtypeVal hp).isFredholmStruct ?_
  simpa using hc

omit [IsTopologicalAddGroup E] [IsTopologicalAddGroup F] in
theorem Topology.IsQuotientMap.isFredholmStruct {f : E →L[𝕜] F} (hq : IsQuotientMap f)
    (hfg : FiniteDimensional 𝕜 f.ker) (hcompl : f.ker.ClosedComplemented) :
    IsFredholmStruct f := by
  constructor
  · exact hq.isStrictMap
  · rw [LinearMap.range_eq_top.2 hq.surjective]
    exact isClosed_univ
  · exact hfg
  · rw [LinearMap.range_eq_top.2 hq.surjective]
    exact Submodule.CoFG.top
  · exact hcompl

--ToDO :move
theorem Submodule.ker_mkQL {p : Submodule 𝕜 E} : p.mkQL.ker = p := by ext; simp

variable [ContinuousSMul 𝕜 E]
theorem Submodule.mkQL_isFredholmStruct {p : Submodule 𝕜 E} (hc : FiniteDimensional 𝕜 p)
    (hcompl : p.ClosedComplemented) :
    IsFredholmStruct p.mkQL :=
  p.isQuotientMap_mkQL.isFredholmStruct (by rwa [p.ker_mkQL]) (by simpa)

/- ## Composition of Fredholm (with the inverse definition) (Aaron)

Consider the three CLMs `u`, `v` and `v ∘L u`. If two of them are Fredholm,
the third one is.

I'm not sure what the set of statements should look like, but I imagine the following :
1. If `u` and `v` are Fredholm, `v ∘L u` is
2. If `u` is Fredholm, then `v` Fredholm ↔ `v ∘ u` Fredholm
3. If `v` is Fredholm, then `u` Fredholm ↔ `v ∘ u` Fredholm
-/

lemma IsFredholmQuot.comp {f : E →L[𝕜] F} {f' : F →L[𝕜] G} (hf : IsFredholmQuot f)
    (hf' : IsFredholmQuot f') : IsFredholmQuot (f' ∘L f) := by
  rw [IsFredholmQuot.iff_toLinearMap] at *
  rcases hf with ⟨g, hg⟩
  rcases hf' with ⟨g', hg'⟩
  exact ⟨g ∘L g', hg'.comp hg⟩

lemma IsFredholmQuot.of_equiv {f f' : E →L[𝕜] F} (h : f ≈ f') (hu : IsFredholmQuot f) :
    IsFredholmQuot f' := by
  rw [IsFredholmQuot.iff_toLinearMap] at *
  obtain ⟨g, hg⟩ := hu
  exact ⟨g, hg.congr (symm h) (Setoid.refl g)⟩

lemma IsFredholmQuot.congr {f f' : E →L[𝕜] F} (h : f ≈ f') :
    IsFredholmQuot f ↔ IsFredholmQuot f' :=
  ⟨fun hu => hu.of_equiv h, fun hv => hv.of_equiv (symm h)⟩

lemma IsFredholmQuot.of_left_of_comp {f : F →L[𝕜] G} {f' : E →L[𝕜] F}
    (hf : IsFredholmQuot f) (hcomp : IsFredholmQuot (f ∘L f')) :
    IsFredholmQuot f' := by
  rw [IsFredholmQuot.iff_toLinearMap] at *
  obtain ⟨g, hg⟩ := hf
  obtain ⟨w, hw⟩ := hcomp
  exact ⟨w ∘L f, (hg.symm.of_comp_right hw.symm).symm⟩

lemma IsFredholmQuot.of_right_of_comp [ContinuousSMul 𝕜 F] {f : F →L[𝕜] G}
    {f' : E →L[𝕜] F}
    (hf' : IsFredholmQuot f') (hcomp : IsFredholmQuot (f ∘L f')) :
    IsFredholmQuot f := by
  rw [IsFredholmQuot.iff_toLinearMap] at *
  obtain ⟨g, hg⟩ := hf'
  obtain ⟨w, hw⟩ := hcomp
  exact ⟨f' ∘L w, (hg.symm.of_comp_left hw.symm).symm⟩

/- ## Fredholm_struct ==> good decomposition (Filippo)

If `u` satisfies `Fredholm_struct`, then there are decompositions `E = E₁ ⊕ E₂`,
`F = F₁ ⊕ F₂` such that `E₂` and `F₂` are FG and, in this decomposition, u is of the form

Φ 0
0 0

with Φ an isomorphism.

E₂ = u.ker
F₁ = u.range
The others are arbitrary complements

-/
end IsFredholmQuot

end FredholmOperators

public noncomputable section Filippo

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E]
   [TopologicalSpace E] [Module 𝕜 E]
variable [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [Module 𝕜 F] [ContinuousSMul 𝕜 F]
variable {u : E →L[𝕜] F}

open Submodule Function

variable (𝕜 E) in
structure preFredholmDecomposition where
  X₁ : Submodule 𝕜 E
  X₂ : Submodule 𝕜 E
  topCompl : IsTopCompl X₁ X₂
  fin_dim : FiniteDimensional 𝕜 X₂

open Submodule.ClosedComplemented in
private lemma injectiveOn_complement (huF : IsFredholmStruct u) :
    letI compl := (of_finiteDimensional_quotient huF.isClosed_range (hq := huF.cokerFG)).complement
    Injective (u.range.mkQ.domRestrict compl) := by
  let compl := (of_finiteDimensional_quotient huF.isClosed_range (hq := huF.cokerFG)).complement
  set f := u.range.mkQ with hf
  set g := (f.domRestrict compl) with hg_def
  rw [← g.ker_eq_bot]
  ext ⟨x, hx'⟩
  refine ⟨fun hx ↦ ?_ , fun hx ↦ by simp_all⟩
  rw [hg_def] at hx
  simp only [hf, LinearMap.mem_ker, LinearMap.domRestrict_apply, mkQ_apply,
    Quotient.mk_eq_zero] at hx
  have := (of_finiteDimensional_quotient huF.isClosed_range
    (hq := huF.cokerFG)).isTopCompl_complement.isCompl.disjoint
  rw [Submodule.disjoint_def] at this
  simpa only [mem_bot, mk_eq_zero] using this _ hx hx'

variable [IsTopologicalAddGroup E]

open Submodule.ClosedComplemented in
def FredholmDecomposition (huF : IsFredholmStruct u) :
    preFredholmDecomposition 𝕜 E × preFredholmDecomposition 𝕜 F :=
  ⟨⟨(exists_isTopCompl huF.5).choose, u.ker, (exists_isTopCompl huF.5).choose_spec.symm,
      huF.3⟩,
    ⟨u.range, (of_finiteDimensional_quotient huF.isClosed_range
      (hq := huF.cokerFG)).complement, (of_finiteDimensional_quotient huF.isClosed_range
      (hq := huF.cokerFG)).isTopCompl_complement,
      huF.cokerFG.of_injective _ (injectiveOn_complement huF)⟩⟩

variable (𝕜 u) in
structure FredholmDecomposition' where
  dec_left : preFredholmDecomposition 𝕜 E
  dec_right : preFredholmDecomposition 𝕜 F
  ker : u.domRestrict (dec_left).X₂ = 0
  mapsto : ∀ a ∈ (dec_left).X₁, u a ∈ (dec_right).X₁
  invertible₁ : (u.restrict mapsto).IsInvertible

variable (huF : IsFredholmStruct u)

@[simp]
theorem FredholmDecomposition_dom₂ : (FredholmDecomposition huF).1.X₂ = u.ker := by rfl

-- FAE : Perhaps we want the version with `restrict` rather than `domRestrict`
theorem FredholmDecomposition_InjectiveOn₁' :
    Injective (u.domRestrict (FredholmDecomposition huF).1.X₁).toLinearMap := by
  rw [← LinearMap.ker_eq_bot, ContinuousLinearMap.toLinearMap_domRestrict,
    LinearMap.ker_domRestrict, ← Submodule.disjoint_iff_comap_eq_bot]
  exact (FredholmDecomposition huF).1.3.isCompl.disjoint


@[simp]
theorem FredholmDecomposition_codom₁ : (FredholmDecomposition huF).2.X₁ = u.range := by rfl

theorem FredholmDecomposition_mapsTo₁ (x : _) (_ : x ∈ (FredholmDecomposition huF).1.X₁) :
    u x ∈ (FredholmDecomposition huF).2.X₁ := by simp

theorem FredholmDecomposition_InjectiveOn₁ :
    Injective (u.restrict (FredholmDecomposition_mapsTo₁ huF)).toLinearMap := by
  rw [ContinuousLinearMap.restrict_eq_domRestrict_codRestrict (by simp)]
  simp only [ContinuousLinearMap.toLinearMap_domRestrict, LinearMap.injective_domRestrict_iff,
    ContinuousLinearMap.ker_codRestrict, ← disjoint_iff]
  exact (FredholmDecomposition huF).1.3.isCompl.disjoint


theorem FredholmDecomposition_mapsTo₂ (huF : IsFredholmStruct u) :
    ∀ x ∈ (FredholmDecomposition huF).1.X₂, u x ∈ (FredholmDecomposition huF).2.X₂ := by
  intro x hx
  simp only [FredholmDecomposition, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
  exact hx ▸ Submodule.zero_mem ..

-- FAE: Perhaps we want (also?) the version with `restrict` instead of `domRestrict`
theorem FredholmDecomposition_ZeroOn₂ (huF : IsFredholmStruct u) :
    (u.domRestrict (FredholmDecomposition huF).1.X₂) = 0 := by sorry

namespace LinearMap
section IsCompl

variable {R : Type u_1} [Ring R] {M : Type u_2} [AddCommGroup M] [Module R M] {N : Type u_3}
  [AddCommGroup N] [Module R N]

-- lemma _root_.Submodule.isCompl_eq_add {p q : Submodule R M} (h : IsCompl p q) (x : M) :
--     ∃ (a : p), ∃ (b : q), (a : M) + b = x := by
--   obtain ⟨⟨a, b⟩, ⟨h_exists, h_unique⟩⟩ := Submodule.existsUnique_add_of_isCompl_prod h x
--   refine ⟨a, b, h_exists⟩


lemma Submodule.isCompl_projection_sub_mem {p q : Submodule R M} (h : IsCompl p q) (x : M) :
    (p.projection q h) x - x ∈ q := by
  simp [Submodule.projection_eq_self_sub_projection h.symm x]

@[simp]
lemma domRestrict_range_eq {f : M →ₗ[R] N} {p : Submodule R M} (h : IsCompl p f.ker) :
    (f.domRestrict p).range = f.range := by
  let π := p.projectionOnto _ h
  ext x
  refine ⟨fun ⟨⟨a, _⟩, _⟩ ↦ ⟨a, by simpa⟩, fun ⟨a, hxa⟩ ↦ ?_⟩
  simp only [LinearMap.range_domRestrict, mem_map]
  refine ⟨π a, coe_mem _, ?_⟩
  rw [← hxa, eq_of_sub_eq_zero (a := f (π a)) (b := f a)] --improve
  rw [← f.map_sub, Submodule.coe_projectionOnto_apply, ← LinearMap.mem_ker]
  apply Submodule.isCompl_projection_sub_mem

@[simp]
lemma subtype_codRestrict_range {f : M →ₗ[R] N} {p : Submodule R N}
    (h : ∀ x : M, f x ∈ p) : (map p.subtype (f.codRestrict p h).range) = f.range := by
  ext x
  refine ⟨fun hx ↦ ?_, fun ⟨y, hxy⟩ ↦ ?_⟩
  · simp only [mem_map, LinearMap.mem_range, subtype_apply, exists_exists_eq_and,
    LinearMap.codRestrict_apply] at hx
    exact LinearMap.mem_range.mpr hx
  · simp only [mem_map, LinearMap.mem_range, subtype_apply, exists_exists_eq_and,
    LinearMap.codRestrict_apply]
    use y

@[simp]
lemma codRestrict_range_subtype {f : M →ₗ[R] N} {p : Submodule R N}
    (h : ∀ x : M, f x ∈ p) : (f.codRestrict p h).range = comap p.subtype f.range := by
  rw [← comap_map_eq_of_injective (injective_subtype p) (codRestrict p f h).range,
    LinearMap.subtype_codRestrict_range]

end IsCompl

-- section domRestrict
--
-- variable {R R₂ M M₂ : Type*} [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]
--   [Module R M] [Module R₂ M₂] {σ₁₂ : R →+* R₂} (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M)
--
-- lemma subtype_domRestrict_ker : map p.subtype (f.domRestrict p).ker ≤ f.ker :=
--    fun _ ↦ by simp_all
--
-- lemma domRestrict_ker_subtype : (f.domRestrict p).ker ≤ comap p.subtype f.ker := by
--   rw [← comap_map_eq_of_injective (injective_subtype p) (f.domRestrict p).ker]
--   exact comap_mono <| subtype_domRestrict_ker ..
--
-- lemma domRestrict_ker_eq_zero {x : f.ker} : f.domRestrict f.ker = 0 := by
--   sorry
-- end domRestrict

end LinearMap

theorem FredholmDecomposition_SurjectiveOn₁ :
    Surjective (u.restrict (FredholmDecomposition_mapsTo₁ huF)).toLinearMap := by
  simp only [FredholmDecomposition_codom₁, LinearMap.mem_range, ContinuousLinearMap.coe_coe,
    exists_apply_eq_apply, implies_true, ContinuousLinearMap.restrict_eq_domRestrict_codRestrict,
    ContinuousLinearMap.toLinearMap_domRestrict, ContinuousLinearMap.toLinearMap_codRestrict]
  rw [← LinearMap.range_eq_top, LinearMap.domRestrict_range_eq]
  · simp
  simpa! [LinearMap.ker_codRestrict] using ((FredholmDecomposition huF).1.topCompl).isCompl


namespace ContinuousLinearEquiv
variable {R S M M₂ : Type*} [Semiring R] [Semiring S] {σ : R →+* S} {σ' : S →+* R}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] [TopologicalSpace M] [AddCommMonoid M]
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M] [Module S M₂]

-- **FAE** Open PR [#39473](https://github.com/leanprover-community/mathlib4/pull/39473)
-- open ContinuousLinearEquiv in
-- lemma IsHomeomorph.coe {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X ≃ Y}
--     (hf : IsHomeomorph f) : hf.homeomorph = f := by
--   simp

-- **FAE** Open PR [#39473](https://github.com/leanprover-community/mathlib4/pull/39473)
lemma IsHomeomorph.inv_coe {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X ≃ Y}
    (hf : IsHomeomorph f) : hf.homeomorph.invFun = f.invFun := by
  simp

-- **FAE** MOVE ME
open ContinuousLinearEquiv in
def ofIsHomeomorph (f : M ≃ₛₗ[σ] M₂) (hf : IsHomeomorph f.toEquiv) : M ≃SL[σ] M₂ where
  __ := f
  continuous_toFun := hf.continuous
  continuous_invFun := by
    rw [Equiv.isHomeomorph_iff] at hf
    exact hf.2 -- nice?

@[simp]
lemma ofIsHomeomorph_coe {f : M ≃ₛₗ[σ] M₂} (hf : IsHomeomorph f) :
    (ContinuousLinearEquiv.ofIsHomeomorph f hf).toLinearEquiv = f := by dsimp only [ofIsHomeomorph]

@[simp]
lemma ofIsHomeomorph_apply {f : M ≃ₛₗ[σ] M₂} (hf : IsHomeomorph f) (x : M) :
    (ContinuousLinearEquiv.ofIsHomeomorph f hf) x = f x := by dsimp [ofIsHomeomorph]

end ContinuousLinearEquiv

private def FredholmDecomposition_LinearEquiv₁ :
    (FredholmDecomposition huF).1.X₁ ≃ₗ[𝕜] (FredholmDecomposition huF).2.X₁ :=
  .ofBijective _ ⟨FredholmDecomposition_InjectiveOn₁ huF, FredholmDecomposition_SurjectiveOn₁ huF⟩

private lemma FredholmDecomposition_LinearEquiv₁_coe :
    ((FredholmDecomposition_LinearEquiv₁ huF) : _ → _)  =
      u.restrict (FredholmDecomposition_mapsTo₁ huF) := rfl

def FredholmDecomposition_ContinuousLinearEquiv₁ :
  (FredholmDecomposition huF).1.X₁ ≃L[𝕜] (FredholmDecomposition huF).2.X₁ := by
  apply ContinuousLinearEquiv.ofIsHomeomorph (FredholmDecomposition_LinearEquiv₁ huF)
  simp [FredholmDecomposition_LinearEquiv₁_coe huF]
  sorry


theorem FredholmDecomposition_isInvertibleOn₁ :
    (u.restrict (FredholmDecomposition_mapsTo₁ huF)).IsInvertible :=
  ⟨FredholmDecomposition_ContinuousLinearEquiv₁ huF, by rfl⟩

open Submodule.ClosedComplemented in
def NiceFD : FredholmDecomposition' 𝕜 u where
  dec_left := ⟨(exists_isTopCompl huF.5).choose, u.ker, (exists_isTopCompl huF.5).choose_spec.symm,
      huF.3⟩
  dec_right := ⟨u.range, (of_finiteDimensional_quotient huF.isClosed_range
      (hq := huF.cokerFG)).complement, (of_finiteDimensional_quotient huF.isClosed_range
      (hq := huF.cokerFG)).isTopCompl_complement,
      huF.cokerFG.of_injective _ (injectiveOn_complement huF)⟩
  ker := by -- u.domRestrict_ker_zero
    ext; simp
  mapsto := by simp
  invertible₁ := FredholmDecomposition_isInvertibleOn₁ huF

end Filippo

open Submodule

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E]
   [TopologicalSpace E] [Module 𝕜 E] [ContinuousSMul 𝕜 E] [IsTopologicalAddGroup E] [T2Space E]

/-- This has a PR now. -/
lemma Submodule.ClosedComplemented_of_finiteDimensional_closedComplemented (A B : Submodule 𝕜 E)
    (hA : FiniteDimensional 𝕜 A) (hA1 : A.ClosedComplemented)
    (hB : B ≤ A) : B.ClosedComplemented := by
  obtain ⟨p, hp⟩ := hA1
  obtain ⟨q, hq⟩ := B.exists_isCompl
  refine ⟨((projectionOnto B q hq).domRestrict A).toContinuousLinearMap ∘SL p, fun x ↦ ?_⟩
  simp [hp ⟨x, hB x.2⟩]

variable [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module 𝕜 F]
variable [ContinuousSMul 𝕜 F] [T1Space F]

-- Irrelevant, but : I should update this in Mathlib, where it only is stated for self maps.
open Function LinearMap in
theorem LinearMap.injective_restrict_iff_disjoint' {R M N : Type*}
   [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    {p : Submodule R M} {q : Submodule R N} {f : M →ₗ[R] N} (hf : ∀ x ∈ p, f x ∈ q) :
    Injective (f.restrict hf) ↔ Disjoint p (ker f) := by
  rw [← ker_eq_bot, ker_restrict hf, ← ker_domRestrict, ker_eq_bot, injective_domRestrict_iff,
    disjoint_iff]

namespace ContinuousLinearMap
-- some helper lemmas about the range of ContinuousLinearMap.restrict

lemma map_eq_of_surjective_restrict {𝕜 E F : Type*} [Semiring 𝕜] [AddCommMonoid E]
    [AddCommMonoid F] [TopologicalSpace E] [TopologicalSpace F] [Module 𝕜 E]
    [Module 𝕜 F] {u : E →L[𝕜] F} {E₁ : Submodule 𝕜 E}
    {F₁ : Submodule 𝕜 F} (h_mapsto : Set.MapsTo u E₁ F₁)
    (h_surj : Function.Surjective (u.restrict h_mapsto)) :
    E₁.map u.toLinearMap = F₁ :=
  calc
    E₁.map u.toLinearMap = (u.toLinearMap.domRestrict E₁).range := by
      rw [LinearMap.range_domRestrict]
    _ = (F₁.subtype.comp (u.restrict h_mapsto).toLinearMap).range := by
      rw [ContinuousLinearMap.toLinearMap_restrict, LinearMap.subtype_comp_restrict]
    _ = F₁ := by
      rw [LinearMap.range_comp, LinearMap.range_eq_top.2 h_surj, Submodule.map_top,
        Submodule.range_subtype]

lemma image_eq_of_surjective_restrict {𝕜 E F : Type*} [Semiring 𝕜] [AddCommMonoid E]
    [AddCommMonoid F] [TopologicalSpace E] [TopologicalSpace F] [Module 𝕜 E]
    [Module 𝕜 F] {u : E →L[𝕜] F} {E₁ : Submodule 𝕜 E}
    {F₁ : Submodule 𝕜 F} (h_mapsto : Set.MapsTo u E₁ F₁)
    (h_surj : Function.Surjective (u.restrict h_mapsto)) :
    u '' E₁ = F₁ := by
  simpa [Submodule.map_coe] using
    congr_arg (fun S => S.carrier) (u.map_eq_of_surjective_restrict h_mapsto h_surj)

end ContinuousLinearMap

open Set in
lemma ContinuousLinearMap.ker_closedComplemented_of_isInvertible_restrict
    {u : E →L[𝕜] F} (E₁ : Submodule 𝕜 E) (F₁ : Submodule 𝕜 F)
    (E₁_closed : IsClosed (E₁ : Set E)) (E₁_coFG : E₁.CoFG) (h_mapsto : MapsTo u E₁ F₁)
    (h_inv : (u.restrict h_mapsto).IsInvertible) : u.ker.ClosedComplemented := by
  obtain ⟨C, hC1, hC2⟩ := Disjoint.exists_isCompl <|
    (LinearMap.injective_restrict_iff_disjoint' h_mapsto).mp
      <| ContinuousLinearMap.IsInvertible.injective h_inv
  have hJ:= CoFG.of_le hC1 E₁_coFG
  have hI := Module.Finite.iff_fg.mpr <| Submodule.CoFG.fg_of_isCompl hC2 (CoFG.of_le hC1 E₁_coFG)
  apply Submodule.ClosedComplemented_of_finiteDimensional_closedComplemented u.ker
  · exact finiteDimensional_of_le fun ⦃x⦄ a ↦ a
  · exact IsTopCompl.closedComplemented <| IsTopCompl.symm
         <| Submodule.IsCompl.isTopCompl_of_finiteDimensional_quotient hC2
           (isClosed_mono_of_finiteDimensional_quotient E₁_closed hC1)
  · exact toAddSubmonoid_le.mp fun ⦃x⦄ a ↦ a

open Set in
lemma fooo {u : E →L[𝕜] F} (E₁ : Submodule 𝕜 E) (F₁ : Submodule 𝕜 F)
    (E₁_closed : IsClosed (E₁ : Set E)) (F₁_closed : IsClosed (F₁ : Set F))
    (E₁_coFG : E₁.CoFG) (F₁_coFG : F₁.CoFG) (h_mapsto : MapsTo u E₁ F₁)
    (h_inv : (u.restrict h_mapsto).IsInvertible) :
    u.ker.ClosedComplemented := by
  sorry

open Set in
lemma bar [ContinuousSMul 𝕜 F] {u : E →L[𝕜] F} (E₁ : Submodule 𝕜 E) (F₁ : Submodule 𝕜 F)
    (E₁_closed : IsClosed (E₁ : Set E)) (F₁_closed : IsClosed (F₁ : Set F))
    (E₁_coFG : E₁.CoFG) (F₁_coFG : F₁.CoFG) (h_mapsto : MapsTo u E₁ F₁)
    (h_inv : (u.restrict h_mapsto).IsInvertible) :
    IsFredholmStruct u := by
  have h : Topology.IsStrictMap u ∧ IsClosed (range u) := by
    refine u.isStrictMap_isClosed_range_iff_restrict E₁ E₁_closed |>.2 ⟨?_, ?_⟩
    · obtain ⟨e, he⟩ := h_inv
      have h_emb : Topology.IsEmbedding (Subtype.val ∘ (u.restrict h_mapsto)) :=
        Topology.IsEmbedding.subtypeVal.comp <| he ▸ e.toHomeomorph.isEmbedding
      simpa using h_emb.isStrictMap
    · exact (u.image_eq_of_surjective_restrict h_mapsto h_inv.surjective) ▸ F₁_closed
  constructor
  · exact h.1
  · exact h.2
  · obtain ⟨G, hc⟩ := E₁.exists_isCompl
    have : FiniteDimensional 𝕜 G := G.fg_iff_finiteDimensional.1 (E₁_coFG.fg_of_isCompl hc)
    refine FiniteDimensional.of_injective
      ((G.projectionOnto E₁ hc.symm).domRestrict u.ker) (LinearMap.ker_eq_bot.1 ?_)
    ext z
    -- The following argument can probably be simplified
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, projectionOnto_apply_eq_zero_iff,
      mem_bot]
    refine ⟨fun h => ?_, fun h => by simp_all⟩
    have : (u.restrict h_mapsto) ⟨z, h⟩ = (u.restrict h_mapsto) 0 := by
      simp [ContinuousLinearMap.restrict_apply]
    simpa using h_inv.injective this
  · refine F₁_coFG.of_le fun x hx => ⟨(u.restrict h_mapsto).inverse ⟨x, hx⟩, ?_⟩
    rw [ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.coe_restrict_apply
      h_mapsto ((u.restrict h_mapsto).inverse ⟨x, hx⟩), h_inv.self_apply_inverse]
  · exact ContinuousLinearMap.ker_closedComplemented_of_isInvertible_restrict
      E₁ F₁ E₁_closed E₁_coFG h_mapsto h_inv

/- ## Glue together the equivalence (Anatole) -/

open Set

open ContinuousLinearMap in
theorem isFredholmTFAE (u : E →L[𝕜] F) : List.TFAE
    [
      IsFredholmQuot u,
      IsFredholmStruct u,
      ∃ (E₁ : Submodule 𝕜 E) (F₁ : Submodule 𝕜 F), IsClosed E₁.carrier ∧ E₁.CoFG ∧
        IsClosed F₁.carrier ∧ F₁.CoFG ∧ ∃ h : MapsTo u E₁ F₁,
          (u.restrict h).IsInvertible, Nonempty (FredholmDecomposition' 𝕜 u)] := by
  tfae_have 1 → 3 := aaron
  tfae_have 3 → 2 := by
    rintro ⟨E₁, F₁, E₁_closed, E₁_coFG, F₁_closed, F₁_coFG, u_mapsto, u_invertible⟩
    exact bar E₁ F₁ E₁_closed F₁_closed E₁_coFG F₁_coFG u_mapsto u_invertible
  tfae_have 2 → 4 := fun huF ↦ ⟨NiceFD huF⟩
  tfae_have 4 → 1 := by
    rintro ⟨FD⟩
    have hcompl_left := FD.1.topCompl
    have hcompl_right := FD.2.topCompl
    obtain ⟨φ, hφ⟩ := FD.5
    set v' := subtypeL _ ∘L ContinuousLinearMap.ofIsTopCompl hcompl_right
      φ.symm.toContinuousLinearMap 0 with hv'_def
    refine ⟨v', ?_, ?_⟩
    · rw [FiniteRankSetoid.equiv_iff, LinearMap.FiniteRankSetoid.equiv_iff]
      have := FD.dec_right.fin_dim
      suffices ((u.toLinearMap ∘ₗ v'.toLinearMap - LinearMap.id).range : Submodule 𝕜 F)
        ≤ FD.dec_right.X₂ by apply finiteDimensional_of_le this
      rintro x ⟨y, rfl⟩
      obtain ⟨⟨a, _⟩, ⟨rfl, -⟩⟩ := Submodule.existsUnique_add_of_isCompl_prod hcompl_right.isCompl y
      have h_uva : u (v' a) = a := by
        rw [hv'_def, coe_comp, coe_subtypeL, coe_subtype, Function.comp_apply,
          ofIsTopCompl_apply, ContinuousLinearMap.toLinearMap_zero, LinearMap.ofIsCompl_apply_left,
          coe_coe, ContinuousLinearEquiv.coe_coe]
        simp [show u (φ.symm a) = u.restrict FD.4 (φ.symm a) from coe_restrict_apply FD.4 _, ← hφ]
      simp_all
    · rw [FiniteRankSetoid.equiv_iff, LinearMap.FiniteRankSetoid.equiv_iff]
      have := FD.dec_left.fin_dim
      suffices ((v'.toLinearMap ∘ₗ u.toLinearMap - LinearMap.id).range : Submodule 𝕜 E)
        ≤ FD.dec_left.X₂ by apply finiteDimensional_of_le this
      rintro x ⟨y, rfl⟩
      obtain ⟨⟨a, b⟩, ⟨rfl, -⟩⟩ := Submodule.existsUnique_add_of_isCompl_prod hcompl_left.isCompl y
      have h_uva : v' (u a) = a := by
        rw [hv'_def, coe_comp, coe_subtypeL, coe_subtype, Function.comp_apply,
          ofIsTopCompl_apply, ContinuousLinearMap.toLinearMap_zero]
        have := @LinearMap.ofIsCompl_apply_left
          (φ := φ.symm.toLinearMap) (h := hcompl_right.isCompl) (ψ := 0) (u := ⟨u a, FD.4 a a.2⟩)
        simp only [ContinuousLinearEquiv.toLinearEquiv_symm, LinearEquiv.coe_coe,
          ContinuousLinearEquiv.coe_symm_toLinearEquiv] at this
        erw [this, SetLike.coe_eq_coe]
        apply_fun φ using φ.injective
        simp only [ContinuousLinearEquiv.apply_symm_apply]
        change _ = φ.toContinuousLinearMap a
        simp_rw [hφ, ← coe_restrict_apply FD.4 a]
      have hub : u b = 0 := by
        simp [← domRestrict_apply (f := u) (p := FD.dec_left.X₂) b, FD.3]
      simp_all
  tfae_finish

#print axioms isFredholmTFAE

/- ## Simpler criterion for `IsFredholmStruct` between RCLike Banach spaces

Notes :
* this is not needed for "index locally constant"
* everything below works for Fréchet spaces (where Fréchet => loc convex),
  but we don't have the prerequisites for it.
* here we really need to know that finite dimensional spaces are complemented.
  I propose to restrict to `RCLike` for now.

Lemma : Assume that `E` and `F` are Banach space, and that `u : E →L[𝕜] F`
has coFG range. Then `u` is strict and has closed range.

Proof : pick `G` an algebraic complement of `u.range`. It's finite dimensional,
hence closed and complemented, and `F ⧸ G` is Banach. Denote by `π : F → F ⧸ G` the quotient map.
`π ∘L u` is a surjective CLM between Banach spaces, so it's open,
hence a strict map with closed range. The result now follows from
`ContinuousLinearMap.isStrictMap_isClosed_range_iff_quotient`
(a consequence of the technical proposition)

Prop : In this setting, `IsFredholmStruct` ↔ finite dimensional kernel and cokernel

-/

lemma Submodule.Quotient.mk_image_IsCompl {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {p q : Submodule R M} (hc : IsCompl q p) :
    (Submodule.mkQ (p := p)) '' q = Set.univ := by
  rw [← Submodule.map_coe]
  exact congr_arg (fun s => s.carrier) ((Submodule.map_mkQ_eq_top p q).2 hc.symm.sup_eq_top)

theorem ContinuousLinearMap.isStrictMap_isClosed_range_of_coFG_range
    {𝕜 E F : Type*} [NormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (u : E →L[𝕜] F) (hu : u.range.CoFG) :
    Topology.IsStrictMap u ∧ IsClosed (u.range : Set F) := by
  let := IsRCLikeNormedField.rclike 𝕜
  obtain ⟨G, hG⟩ := u.range.exists_isCompl
  have hf : FiniteDimensional 𝕜 G := G.fg_iff_finiteDimensional.1 (hu.fg_of_isCompl hG)
  have hr : Set.range (G.mkQL ∘L u) = Set.univ := by
    simpa [Set.range_comp] using Submodule.Quotient.mk_image_IsCompl hG
  have ho : IsOpenMap (G.mkQL ∘L u) := by
    have : IsClosed (G : Set F) := G.closed_of_finiteDimensional
    exact ContinuousLinearMap.isOpenMap _ <| Set.range_eq_univ.1 hr
  exact (u.isStrictMap_isClosed_range_iff_quotient G
    (Submodule.ClosedComplemented.of_finiteDimensional G)).2
    ⟨Topology.IsOpenMap.isStrictMap ho (by fun_prop), hr ▸ isClosed_univ⟩

theorem IsFredholmStruct_iff {𝕜 E F : Type*} [NormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] (u : E →L[𝕜] F) :
    IsFredholmStruct (u : E →L[𝕜] F) ↔
      FiniteDimensional 𝕜 u.ker ∧ FiniteDimensional 𝕜 (F ⧸ u.range) where
  mp h := ⟨h.kerFG, h.cokerFG⟩
  mpr h := by
    constructor
    · exact u.isStrictMap_isClosed_range_of_coFG_range h.2 |>.1
    · exact u.isStrictMap_isClosed_range_of_coFG_range h.2 |>.2
    · exact h.1
    · exact h.2
    · let := IsRCLikeNormedField.rclike 𝕜
      have := h.1
      exact Submodule.ClosedComplemented.of_finiteDimensional _

/- ## A topological lemma

**Note** : this will be useful a bit later (to prove that Fredholm operators are
stable under compact perturbation) so this is not a priority.

Lemma : let `E`, `F` be (Hausdorff) TVSs, `u : E →L[𝕜] F`,
and `A` a neighborhood of `0` in `E`. If `restrict A u` is a
closed embedding, then `u` is a closed embedding.

This is TS III, § 5, p 71, lemme 1
-/

/-
## Index locally constant
-/

section NormPerturbation

open Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E]
  [CompleteSpace F]

-- We can add that `φ` is analytic on a neighborhood of `u₀`.
theorem key_fact {u₀ : E →L[𝕜] F} {v₀ : F →L[𝕜] E} (h : u₀.QuasiInverse v₀) :
    ∃ φ : (E →L[𝕜] F) → (F →L[𝕜] E), φ u₀ = v₀ ∧
      ∀ᶠ u in 𝓝 u₀, u.QuasiInverse (φ u) ∧
      ∀ᶠ u in 𝓝 u₀, u.index = u₀.index := by
  sorry

end NormPerturbation
