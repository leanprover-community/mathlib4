/-
Copyright (c) 2026 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ...
-/
module

public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.RingTheory.Finiteness.Cofinite
public import Mathlib.Topology.Maps.Strict.Basic
public import Mathlib.Topology.Algebra.Module.LinearMap
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.LinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [AddCommGroup E] [AddCommGroup F] [TopologicalSpace E] [TopologicalSpace F]
  [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
variable [Module 𝕜 E] [Module 𝕜 F]
variable {f : E →L[𝕜] F}

public noncomputable section FredholmOperators

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

def LinearMap.hasFiniteRank (f : V →ₗ[K] V₂) := FiniteDimensional K f.range

@[simp] def LinearMap.hasFiniteRank.smul {f : V →ₗ[K] V₂}
    (hf : f.hasFiniteRank) (c : K) : (c • f).hasFiniteRank := by
  unfold LinearMap.hasFiniteRank at *
  rw [← Submodule.fg_iff_finiteDimensional] at *
  exact hf.of_le <| LinearMap.range_smul_le _ c

@[simp] def LinearMap.hasFiniteRank.zero : (0 : V →ₗ[K] V₂).hasFiniteRank := by
  unfold LinearMap.hasFiniteRank
  simp

@[simp] def LinearMap.hasFiniteRank.neg {f : V →ₗ[K] V₂}
    (hf : f.hasFiniteRank) : (-f).hasFiniteRank := by
  rw [show -f = (-1 : K) • f by module]
  apply hf.smul

@[simp] lemma LinearMap.hasFiniteRank.add {f g : V →ₗ[K] V₂}
    (hf : f.hasFiniteRank) (hg : g.hasFiniteRank) : (f + g).hasFiniteRank := by
  unfold LinearMap.hasFiniteRank at *
  exact Submodule.finiteDimensional_of_le <| LinearMap.range_add_le f g

@[simp] def LinearMap.hasFiniteRank.sub {f g : V →ₗ[K] V₂}
    (hf : f.hasFiniteRank) (hg : g.hasFiniteRank) : (f - g).hasFiniteRank := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

variable {V₃ : Type*} [AddCommGroup V₃] [Module K V₃]

lemma LinearMap.hasFiniteRank.comp_right {u : V →ₗ[K] V₂} (h : u.hasFiniteRank)
    (v : V₂ →ₗ[K] V₃) : (v ∘ₗ u).hasFiniteRank := by
  unfold LinearMap.hasFiniteRank at *
  rw [← Submodule.fg_iff_finiteDimensional, LinearMap.range_comp] at *
  exact Submodule.FG.map v h

lemma LinearMap.hasFiniteRank.comp_left {v : V₂ →ₗ[K] V₃} (h : v.hasFiniteRank)
    (u : V →ₗ[K] V₂) : (v ∘ₗ u).hasFiniteRank := by
  unfold LinearMap.hasFiniteRank at *
  rw [← Submodule.fg_iff_finiteDimensional] at *
  exact h.of_le <| u.range_comp_le_range v

lemma LinearMap.hasFiniteRank.comp_sub_comp {u v : V →ₗ[K] V₂} {u' v' : V₂ →ₗ[K] V₃}
    (h : (u - v).hasFiniteRank) (h' : (u' - v').hasFiniteRank) :
    (u' ∘ₗ u - v' ∘ₗ v).hasFiniteRank := by
  rw [show u' ∘ₗ u - v' ∘ₗ v = (u' - v') ∘ₗ u + v' ∘ₗ (u - v) by ext; simp]
  exact (h'.comp_left u).add <| h.comp_right v'

variable (K V V₂) in
def LinearMap.FiniteRank : Submodule K (V →ₗ[K] V₂) where
  carrier := {u | u.hasFiniteRank}
  add_mem' hu hv := by simp_all
  zero_mem' := by simp
  smul_mem' c hu := by simp_all

namespace QuotFiniteRank
scoped instance : Setoid (V →ₗ[K] V₂) := (LinearMap.FiniteRank K V V₂).quotientRel

lemma eqv_iff {u v : V →ₗ[K] V₂} : u ≈ v ↔ (u - v).hasFiniteRank := by
  erw [← @Quotient.eq_iff_equiv, Submodule.Quotient.eq]
  rfl

lemma rel_comp {u v : V →ₗ[K] V₂} {u' v' : V₂ →ₗ[K] V₃} (h : u ≈ v) (h' : u' ≈ v') :
    u' ∘ₗ u ≈ v' ∘ₗ v := by
  rw [eqv_iff] at *
  exact h.comp_sub_comp h'

lemma rel_comp_right {u : V →ₗ[K] V₂} {u' v' : V₂ →ₗ[K] V₃} (h' : u' ≈ v') :
    u' ∘ₗ u ≈ v' ∘ₗ u :=
  rel_comp (Quotient.exact rfl) h'

lemma rel_comp_left {u v : V →ₗ[K] V₂} {u' : V₂ →ₗ[K] V₃} (h : u ≈ v) :
    u' ∘ₗ u ≈ u' ∘ₗ v :=
  rel_comp h (Quotient.exact rfl)
end QuotFiniteRank

section
open scoped QuotFiniteRank

def LinearMap.LeftQuasiInverse (u : V →ₗ[K] V₂) (v : V₂ →ₗ[K] V) := u ∘ₗ v ≈ .id

def LinearMap.RightQuasiInverse (u : V₃ →ₗ[K] V₂) (v : V₂ →ₗ[K] V₃) := v ∘ₗ u ≈ .id

def LinearMap.QuasiInverse (u : V₃ →ₗ[K] V₂) (v : V₂ →ₗ[K] V₃) :=
  u.LeftQuasiInverse v ∧ u.RightQuasiInverse v

@[symm]
lemma LinearMap.QuasiInverse.symm {u : V₃ →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    (h : u.QuasiInverse v) : v.QuasiInverse u :=
  And.symm h

lemma LinearMap.QuasiInverse_congr {u u' : V₃ →ₗ[K] V₂} {v v' : V₂ →ₗ[K] V₃}
    (h : u.QuasiInverse v) (hu : u' ≈ u) (hv : v' ≈ v) :
    u'.QuasiInverse v' := by
  simp only [QuasiInverse, LeftQuasiInverse, RightQuasiInverse, QuotFiniteRank.eqv_iff] at *
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
    _ ≈ v ∘ₗ (u ∘ₗ v') := by apply QuotFiniteRank.rel_comp_left; symm; exact h'.1
    _ = (v ∘ₗ u) ∘ₗ v' := by rw [comp_assoc]
    _ ≈ (.id) ∘ₗ v' := by apply QuotFiniteRank.rel_comp_right; exact h.2
    _ = v' := by simp

lemma LinearMap.equiv_of_quasiInverse' {u u' : V₃ →ₗ[K] V₂} {v : V₂ →ₗ[K] V₃}
    (h : u.QuasiInverse v) (h' : u'.QuasiInverse v) :
    u ≈ u' := by
  symm at h h'
  exact equiv_of_quasiInverse h h'
end
end

open Topology ContinuousLinearMap Submodule Set

variable (f)

structure IsFredholm_struc : Prop where
  isStrict : IsStrictMap f
  isClosed_range : IsClosed (f.range : Set F)
  kerFG : FiniteDimensional 𝕜 f.toLinearMap.ker
  cokerFG : FiniteDimensional 𝕜 (F ⧸ f.range)

/-FAE: I don't like this definition that seems to fix `g` (making it a structure would be even more
  disgusting). -/
def IsFredholm_exists : Prop := ∃ g : F →L[𝕜] E,
  FiniteDimensional 𝕜 (f ∘L g - .id 𝕜 F).range  ∧ FiniteDimensional 𝕜 (g ∘L f - .id 𝕜 E).range

namespace QuotFiniteSubmodules
variable [ContinuousConstSMul 𝕜 E] [ContinuousConstSMul 𝕜 F]

variable (𝕜 E F) in
def FiniteRank : Submodule 𝕜 (E →L[𝕜] F) where
  carrier := {u | u.toLinearMap.hasFiniteRank}
  add_mem' hu hv := by simp_all
  zero_mem' := by simp
  smul_mem' c hu := by simp_all

scoped instance : Setoid (E →L[𝕜] F) := (FiniteRank 𝕜 E F).quotientRel

lemma eqv_iff {u v : E →L[𝕜] F} : u ≈ v ↔ (u - v).toLinearMap.hasFiniteRank := by
  erw [← @Quotient.eq_iff_equiv, Submodule.Quotient.eq]
  rfl

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]  [Module 𝕜 G]
  [ContinuousConstSMul 𝕜 G] [ContinuousAdd G]

lemma rel_comp {u v : E →L[𝕜] F} {u' v' : F →L[𝕜] G} (h : u ≈ v) (h' : u' ≈ v') :
    u' ∘L u ≈ v' ∘L v := by
  rw [eqv_iff] at *
  exact h.comp_sub_comp h'

def IsFredholm_quot : Prop := ∃ g : F →L[𝕜] E,
  (f ∘L g ≈ .id 𝕜 F) ∧ (g ∘L f ≈ .id 𝕜 E)

end QuotFiniteSubmodules

theorem AnatoleDream_1 (hf : IsFredholm_struc f) : IsFredholm_exists f:= sorry

def AnatoleDream_1_symm (hf : IsFredholm_exists f) : IsFredholm_struc f := sorry

open QuotFiniteSubmodules in
theorem AnatoleDream_2 [ContinuousConstSMul 𝕜 E] [ContinuousConstSMul 𝕜 F] [ContinuousAdd E]
    [ContinuousAdd F] (hf : IsFredholm_struc f) : IsFredholm_quot f := sorry

open QuotFiniteSubmodules in
def AnatoleDream_2_symm [ContinuousConstSMul 𝕜 E] [ContinuousConstSMul 𝕜 F] [ContinuousAdd E]
    [ContinuousAdd F] (hf : IsFredholm_quot f) : (IsFredholm_struc f) := sorry

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

lemma index_smul (t : k) (ht : t ≠ 0) :
    (t • f).index = f.index := by
  rw [index, index, ker_smul _ _ ht, range_smul _ _ ht]

@[simp] lemma index_neg :
    (-f).index = f.index := by
  rw [index, index, ker_neg, range_neg]

lemma index_comp {G : Type*} [AddCommGroup G] [Module k G] (g : F →ₗ[k] G)
    /- TODO required assumptions. -/ :
    (g ∘ₗ f).index = g.index + f.index := by
  -- 0 → f.ker → (g ∘ₗ f).ker → g.ker → f.coker → (g ∘ₗ f).coker → g.coker → 0
  sorry

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

lemma CokernelFG_of_isFredholmₗ (hu : IsFredholm_existsₗ u) [Module.Free R (N ⧸ u.range)] :
    Module.Finite R (N ⧸ u.range) := by
  obtain ⟨v, hv_right, hv_left⟩ := hu
  let φ := u.dualMap
  have : IsFredholm_existsₗ φ := by
    unfold IsFredholm_existsₗ
    use v.dualMap
    sorry
    -- constructor
    -- · rw [LinearMap.dualMap_comp_dualMap]
    --   sorry
  have FG_ker_dual : φ.ker.FG := KernelFG_of_isFredholmₗ this
  have one := u.ker_dualMap_eq_dualAnnihilator_range
  rw [one] at FG_ker_dual
  let two := (u.range).dualQuotEquivDualAnnihilator
  rw [← Module.finite_dual_iff, Module.Finite.equiv_iff two]
  exact Module.Finite.iff_fg.mpr FG_ker_dual

lemma CokernelFG_of_isFredholm' (hu : IsFredholm_existsₗ u) : Module.Finite R (N ⧸ u.range) := by
  let q := u.range.mkQ
  obtain ⟨v, hv, -⟩ := hu
  let Q := (u ∘ₗ v - (1 : N →ₗ[R] N)).range.mkQ
  have crux : (u ∘ₗ v - (1 : N →ₗ[R] N)).ker ≤ Submodule.comap (1 : N →ₗ[R] N) u.range := by
    erw [comap_id]
    intro x hx
    use v x
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
      Module.End.one_apply, sub_eq_zero] at hx
  have hmap := Submodule.mapQ (u ∘ₗ v - (1 : N →ₗ[R] N)).ker u.range (1 : N →ₗ[R] N) crux
  have hpre := (u ∘ₗ v - (1 : N →ₗ[R] N)).quotKerEquivRange.symm.toLinearMap
  have hfin := hmap.comp hpre
  have h2 : -q ∘ (u ∘ₗ v - (1 : N →ₗ[R] N)) = q := by aesop
  have h3 := Set.rangeFactorization (u ∘ₗ v - (1 : N →ₗ[R] N)).toFun
  have K : Module.Finite R (u ∘ₗ v - 1).range := sorry
  apply Module.Finite.of_surjective (R := R) (M := (u ∘ₗ v - 1).range) hfin

  sorry

-- Quot.surjective_lift




/- In case Fredholm folks can't sleep, here's the right way to go about the above. The idea is
to look at the quotient via maps. Let `q : E → E⧸ImT`. This is characterized by (see one of the
annihilator results above) the equation `q ∘ T = 0`. This implies `q ∘ (T ∘ u - id_F)= -q` and so
`q` factors as `-q ∘ (T ∘ u - id_F)`. Since `q` is surjective, so is `-q|(T ∘ u - id_F).range` (onto
`E/Im T`). Since that range is assumed finite dimensional, and a surjective linear map from a finite
dimensional space has finite dimensional range, it follows that `E/Im T` must be finite dimensional.
Sorry for the deviation from notation...I'm writing a note for tomorrow! -/

/- ## GoodRelation -/

/- ## IsStrict Using Technical Lemma -/

/- ## Fredholm operator is an isomorphism on a finite codim space -/

open QuotFiniteSubmodules

variable {u : E →L[𝕜] F} {v : F →L[𝕜] E}

variable [ContinuousConstSMul 𝕜 E]

omit [IsTopologicalAddGroup F] in
theorem ContinuousLinearMap.id_sub_comp_ker_coFG (hgf : v ∘L u ≈ .id 𝕜 E) :
    (.id 𝕜 E - v ∘L u).ker.CoFG := by
  rw [← range_fg_iff_ker_cofg, Submodule.fg_iff_finiteDimensional]
  exact eqv_iff.1 (Setoid.symm hgf)

variable [T1Space E] [T1Space F] [ContinuousConstSMul 𝕜 F]

#check InvOn

/-- Need rename and more convenient statement. -/
theorem aaron' (huv : u ∘L v ≈ .id 𝕜 F) (hvu : v ∘L u ≈ .id 𝕜 E) :
    ∃ (E₁ : Submodule 𝕜 E) (F₁ : Submodule 𝕜 F), IsClosed E₁.carrier ∧ E₁.CoFG ∧
      IsClosed F₁.carrier ∧ F₁.CoFG ∧ InvOn v u (E₁ : Set E) (F₁ : Set F) ∧
        MapsTo u E₁ F₁ ∧ MapsTo v F₁ E₁ := by
  refine ⟨(.id 𝕜 E - v ∘L u).ker, (.id 𝕜 F - u ∘L v).ker, (.id 𝕜 E - v ∘L u).isClosed_ker,
    ContinuousLinearMap.id_sub_comp_ker_coFG hvu, (.id 𝕜 F - u ∘L v).isClosed_ker,
    ContinuousLinearMap.id_sub_comp_ker_coFG huv,
    ⟨fun _ hx => (sub_eq_zero.mp hx).symm, fun _ hx => (sub_eq_zero.mp hx).symm⟩, ?_, ?_⟩
  <;> intro x hx
  <;> simp_all [← map_sub]

/-- Need rename. -/
theorem aaron (hr : IsFredholm_quot u) :
    ∃ (E₁ : Submodule 𝕜 E) (F₁ : Submodule 𝕜 F), IsClosed E₁.carrier ∧ E₁.CoFG ∧
      IsClosed F₁.carrier ∧ F₁.CoFG ∧ BijOn u E₁ F₁ := by
  obtain ⟨v, huv, hvu⟩ := hr
  refine ⟨(.id 𝕜 E - v ∘L u).ker, (.id 𝕜 F - u ∘L v).ker, (.id 𝕜 E - v ∘L u).isClosed_ker,
    ContinuousLinearMap.id_sub_comp_ker_coFG hvu, (.id 𝕜 F - u ∘L v).isClosed_ker,
    ContinuousLinearMap.id_sub_comp_ker_coFG huv,
    InvOn.bijOn ⟨fun _ hx => (sub_eq_zero.mp hx).symm, fun _ hx => (sub_eq_zero.mp hx).symm⟩ ?_ ?_⟩
  <;> intro x hx
  <;> simp_all [← map_sub]

/- ## Injections from closed finite codimension subspaces are Fredholm

Easy for every definition.
The index is the codimension of the range.

(The same is true for quotient by finite dimensional complemented subspaces)
-/

/- ## Composition of Fredholm (with the inverse definition)

Consider the three CLMs `u`, `v` and `v ∘L u`. If two of them are Fredholm,
the third one is.

I'm not sure what the set of statements should look like, but I imagine the following :
1. If `u` and `v` are Fredholm, `v ∘L u` is
2. If `u` is Fredholm, then `v` Fredholm ↔ `v ∘ u` Fredholm
3. If `v` is Fredholm, then `u` Fredholm ↔ `v ∘ u` Fredholm
-/

/- ## ContinuousLinearEquiv is open in ContinuousLinearMap for Banach spaces

For `E = F` this follows from `Units.isOpen`. Then for the general case either
`E ≃L F` is empty or you reduce to the `E = F` case.
-/

/- ## Fredholm_struct ==> good decomposition

If `u` satisfies `Fredholm_struct`, then there are decompositions `E = E₁ ⊕ E₂`,
`F = F₁ ⊕ F₂` such that `E₂` and `F₂` are FG and, in this decomposition, u is of the form

Φ 0
0 0

with Φ an isomorphism.

E₂ = u.ker
F₁ = u.range
The others are arbitrary complements
-/

/- ## FredholmQuot ==> complemented kernel

Lemma : if `A` is finite dimensional is complemented and if `B ≤ A` then `B` is complemented.

Proof: project onto `A`, then the projection from `A` to `B` is continuous because findim.

If `u` is Fredholm, by `aaron`, we have a finite codim subspace `E₁` on which `u` is injective.
Pick `S` a complement of `E₁` containing `u.ker`. Then `S` is complemented and finite dimensional,
so `u.ker` is complemented.

-/

end FredholmOperators
