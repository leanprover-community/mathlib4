/-
Copyright (c) 2026 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ...
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Perturbation.StrictByFinite
public import Mathlib.RingTheory.Finiteness.Cofinite
public import Mathlib.Topology.Algebra.Module.Complement
public import Mathlib.Topology.Algebra.Module.FiniteDimension

section FindHome

open Function Module in
lemma Module.sum_neg_one_pow_finrank_eq_zero_of_exact {n : ℕ} {k : Type*} (V : Fin (n + 2) → Type*)
    [Field k] [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)]
    (f : (i : Fin (n + 1)) → V i.castSucc →ₗ[k] V i.succ)
    (inj : Injective (f 0))
    (exact : ∀ i : Fin n, Exact (f i.castSucc) (f i.succ))
    (surj : Surjective (f (Fin.last _))) :
    ∑ i, (-1) ^ i.val • (finrank k (V i) : ℤ) = 0 := by
  sorry

-- Can we have a simproc write this using `Module.sum_neg_one_pow_finrank_eq_zero_of_exact`
-- Note the key point that the universes of the `Vᵢ` are allowed be different here.
open Function Module in
lemma Module.sum_neg_one_pow_finrank_eq_zero_of_exact_six {k V₀ V₁ V₂ V₃ V₄ V₅ : Type*} [Field k]
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
  sorry

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

variable {V₄ : Type*} [AddCommGroup V₄] [Module K V₄]
lemma LinearMap.QuasiInverse_comp {u : V₂ →ₗ[K] V₃} {v : V₃ →ₗ[K] V₂} {u' : V₃ →ₗ[K] V₄}
    {v' : V₄ →ₗ[K] V₃}
    (h : u.QuasiInverse v) (h' : u'.QuasiInverse v') :
    (u' ∘ₗ u).QuasiInverse (v ∘ₗ v') := by
  rcases h with ⟨h₁, h₂⟩
  rcases h' with ⟨h'₁, h'₂⟩
  constructor
  · calc
      (u' ∘ₗ u) ∘ₗ (v ∘ₗ v') = u' ∘ₗ (u ∘ₗ v) ∘ₗ v' := comp_assoc ..
      _ ≈  u' ∘ₗ .id ∘ₗ v' := by gcongr ; exact h₁
      _ =  u' ∘ₗ v' := by simp
      _ ≈  .id := h'₁
  · calc
      (v ∘ₗ v') ∘ₗ (u' ∘ₗ u) = v ∘ₗ (v' ∘ₗ u') ∘ₗ u := comp_assoc ..
      _ ≈  v ∘ₗ .id ∘ₗ u := by gcongr ; exact h'₂
      _ =  v ∘ₗ u := by simp
      _ ≈  .id := h₂
end
end

open Topology ContinuousLinearMap Submodule Set

variable (f)

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
def ContinuouisLinearMap.FiniteRank : Submodule 𝕜 (E →L[𝕜] F) :=
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

lemma IsFredholmQuot.comp {f : E →L[𝕜] F} {f' : F →L[𝕜] G} (hf : IsFredholmQuot f)
    (hf' : IsFredholmQuot f') : IsFredholmQuot (f' ∘L f) := by
  rw [IsFredholmQuot.iff_toLinearMap] at *
  rcases hf with ⟨g, hg⟩
  rcases hf' with ⟨g', hg'⟩
  use g ∘L g'
  push_cast
  exact LinearMap.QuasiInverse_comp hg hg'

theorem AnatoleDream (hf : IsFredholmStruct f) : IsFredholmQuot f:= sorry

def AnatoleDream_symm (hf : IsFredholmQuot f) : IsFredholmStruct f := sorry

/- ## API -/

namespace LinearMap

open Module

variable (k : Type*) [Field k] [Module k E] [Module k F] (f : E →ₗ[k] F)

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
  have : FiniteDimensional k (g ∘ₗ f).ker := by sorry
  have : FiniteDimensional k (G ⧸ (g ∘ₗ f).range) := by sorry
  let f₀ : f.ker →ₗ[k] (g ∘ₗ f).ker := Submodule.inclusion <| ker_le_ker_comp f g
  let f₁ : (g ∘ₗ f).ker →ₗ[k] g.ker := f.restrict <| by simp
  let f₂ : g.ker →ₗ[k] F ⧸ f.range := f.range.mkQ ∘ₗ g.ker.subtype
  let f₃ : (F ⧸ f.range) →ₗ[k] G ⧸ (g ∘ₗ f).range :=
    f.range.mapQ (g ∘ₗ f).range g <| by rw [← map_le_iff_le_comap, range_comp]
  let f₄ : (G ⧸ (g ∘ₗ f).range) →ₗ[k] G ⧸ g.range := factor <| range_comp_le_range f g
  have h₀ : Injective f₀ := Submodule.inclusion_injective _
  have h₁ : Exact f₀ f₁ := fun ⟨x, hx⟩ ↦ by simp [f₀, f₁, restrict_apply, Submodule.inclusion_apply]
  have h₂ : Exact f₁ f₂ := fun ⟨x, hx⟩ ↦ by aesop (add simp restrict_apply)
  have h₃ : Exact f₂ f₃ := by
    rw [LinearMap.exact_iff]
    simp [f₂, f₃, range_comp, ker_mapQ, comap_map_eq]
  have h₄ : Exact f₃ f₄ := by
    rw [LinearMap.exact_iff]
    simp [f₃, f₄, factor, ker_mapQ, range_mapQ]
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
  simpa [equiv_iff, LinearMap.FiniteRankSetoid.equiv_iff] using Setoid.symm hgf

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
  · simpa using hf.isClosed_range
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
@[simp]
theorem Submodule.ker_mkQL {p : Submodule 𝕜 E} : p.mkQL.ker = p := by ext; simp

variable [ContinuousSMul 𝕜 E]
theorem Submodule.mkQL_isFredholmStruct {p : Submodule 𝕜 E} (hc : FiniteDimensional 𝕜 p)
    (hcompl : p.ClosedComplemented) :
    IsFredholmStruct p.mkQL :=
  p.isQuotientMap_mkQL.isFredholmStruct (by rwa [p.ker_mkQL]) (by simpa)

/- ## Composition of Fredholm (with the inverse definition) (Patrick)

Consider the three CLMs `u`, `v` and `v ∘L u`. If two of them are Fredholm,
the third one is.

I'm not sure what the set of statements should look like, but I imagine the following :
1. If `u` and `v` are Fredholm, `v ∘L u` is
2. If `u` is Fredholm, then `v` Fredholm ↔ `v ∘ u` Fredholm
3. If `v` is Fredholm, then `u` Fredholm ↔ `v ∘ u` Fredholm
-/

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
   [TopologicalSpace E] [Module 𝕜 E] [IsTopologicalAddGroup E]-- [T2Space E] [ContinuousSMul 𝕜 E]
variable [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [Module 𝕜 F] [ContinuousSMul 𝕜 F]
variable {u : E →L[𝕜] F}

open Submodule

variable (𝕜 E) in
structure preFredholmDecomposition where
  X₁ : Submodule 𝕜 E
  X₂ : Submodule 𝕜 E
  compl : IsTopCompl X₁ X₂
  fin_dim : FiniteDimensional 𝕜 X₂

-- variable (𝕜 E) in
open Submodule.ClosedComplemented in
def FredholmDecomposition (huF : IsFredholmStruct u) (huk : u.ker.ClosedComplemented) :
    preFredholmDecomposition 𝕜 E × preFredholmDecomposition 𝕜 F := by
  constructor
  · exact ⟨(exists_isTopCompl huk).choose, u.ker, (exists_isTopCompl huk).choose_spec.symm,
      huF.3⟩
  · have one := of_finiteDimensional_quotient huF.isClosed_range (hq := huF.cokerFG)
    refine ⟨u.range, one.complement, one.isTopCompl_complement, ?_⟩
    set f := u.range.mkQ with hf
    set g := f.domRestrict one.complement with hg_def
    have hg : Function.Injective g := by
      rw [← g.ker_eq_bot]
      ext x
      refine ⟨fun hx ↦ ?_ , fun hx ↦ ?_⟩
      · rw [hg_def] at hx
        simp only [hf, LinearMap.mem_ker, LinearMap.domRestrict_apply, mkQ_apply,
          Quotient.mk_eq_zero] at hx
        rcases x with ⟨x, hx'⟩
        simp only at hx
        have := one.isTopCompl_complement.isCompl.disjoint
        rw [Submodule.disjoint_def] at this
        simp only [mem_bot, mk_eq_zero]
        apply this _ hx hx'
      simp_all
    exact huF.cokerFG.of_injective g hg


theorem FredholmDecomposition_restrict (huF : IsFredholmStruct u)
    (huk : u.ker.ClosedComplemented) : (FredholmDecomposition huF huk).1.X₂ = u.ker := by rfl


theorem FredholmDecomposition_mapsTo (huF : IsFredholmStruct u) (huk : u.ker.ClosedComplemented) :
    ∀ x ∈ (FredholmDecomposition huF huk).1.X₂, u x ∈ (FredholmDecomposition huF huk).2.X₂ := by
  intro x hx
  simp only [FredholmDecomposition, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
  exact hx ▸ Submodule.zero_mem ..




-- **Waiting for *Anatole* to create the `ContinuousLinearMap.restrict` so that the code below type-check
-- theorem FredholmDecomposition_embedding (hu : IsFredholm_struc u)
--     (h_kerCompl : u.ker.ClosedComplemented) :
--     IsInvertible (u.restrict (FredholmDecomposition_mapsTo hu h_kerCompl)) := sorry

/- ## FredholmQuot ==> complemented kernel (Jon)

Lemma : if `A` is finite dimensional is complemented and if `B ≤ A` then `B` is complemented.

Proof: project onto `A`, then the projection from `A` to `B` is continuous because findim.

Assume we have a finite codim subspace `E₁` on which `u` is injective.
Pick `S` a complement of `E₁` containing `u.ker`. Then `S` is complemented and finite dimensional,
so `u.ker` is complemented.

-/

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

theorem isFredholmTFAE (u : E →L[𝕜] F) : List.TFAE
    [
      IsFredholmQuot u,
      IsFredholmStruct u,
      ∃ (E₁ : Submodule 𝕜 E) (F₁ : Submodule 𝕜 F), IsClosed E₁.carrier ∧ E₁.CoFG ∧
        IsClosed F₁.carrier ∧ F₁.CoFG ∧ ∃ h : MapsTo u E₁ F₁,
          (u.restrict h).IsInvertible,
      -- TODO: Filippo, quel est l'énoncé ci-dessous ?
      ∃ (E₁ E₂ : Submodule 𝕜 E) (F₁ F₂ : Submodule 𝕜 F), E₂.FG ∧ F₂.FG ∧
        ∃ E_compl : IsTopCompl E₁ E₂, ∃ F_compl : IsTopCompl F₁ F₂,
        ∃ u' : E₁ ≃L[𝕜] F₁, u = F₁.subtypeL ∘L u' ∘L E₁.projectionOntoL E₂ E_compl
    ] := by
  tfae_have 1 → 3 := aaron
  tfae_have 3 → 2 := by
    rintro ⟨E₁, F₁, E₁_closed, E₁_coFG, F₁_closed, F₁_coFG, u_mapsto, u_invertible⟩
    exact bar E₁ F₁ E₁_closed F₁_closed E₁_coFG F₁_coFG u_mapsto u_invertible
  tfae_have 2 → 4 := by
    sorry -- Filippo
  tfae_have 4 → 1 := by
    sorry -- should be easy
  tfae_finish

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
      ∀ᶠ u in 𝓝 u₀, u.index 𝕜 = u₀.index 𝕜 := by
  sorry

end NormPerturbation
