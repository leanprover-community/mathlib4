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
public import Mathlib.Topology.Maps.Strict.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Algebra.Module.LinearMap.Index
public import Mathlib.Algebra.Module.LinearMap.FiniteRange

@[expose] public section
noncomputable section FredholmOperators

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
  [Module 𝕜 G] [ContinuousConstSMul 𝕜 G]

variable (𝕜 E F) in
def ContinuousLinearMap.FiniteRank : Submodule 𝕜 (E →L[𝕜] F) :=
  Submodule.comap (coeLM 𝕜) (LinearMap.finiteRange 𝕜 E F)

namespace ContinuousLinearMap.FiniteRangeSetoid

open scoped LinearMap.FiniteRangeSetoid

scoped instance setoid : Setoid (E →L[𝕜] F) :=
  Setoid.comap ContinuousLinearMap.toLinearMap inferInstance

omit [IsTopologicalAddGroup E] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 E]
  [ContinuousConstSMul 𝕜 F] in
lemma equiv_iff {u v : E →L[𝕜] F} : (u ≈ v) ↔ u.toLinearMap ≈ v.toLinearMap :=
  Iff.rfl

omit [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
    [ContinuousConstSMul 𝕜 E] [ContinuousConstSMul 𝕜 F] [IsTopologicalAddGroup G]
    [ContinuousConstSMul 𝕜 G] in
lemma equiv_comp {u v : E →L[𝕜] F} {u' v' : F →L[𝕜] G} (h : u ≈ v) (h' : u' ≈ v') :
    u' ∘L u ≈ v' ∘L v := by
  rw [equiv_iff] at *
  push_cast
  exact LinearMap.FiniteRangeSetoid.equiv_comp h h'

end ContinuousLinearMap.FiniteRangeSetoid

section IsFredholmQuot

open scoped ContinuousLinearMap.FiniteRangeSetoid

/-FAE: I don't like this definition that seems to fix `g` (making it a structure would be even more
  disgusting). -/
def IsFredholmQuot : Prop := ∃ g : F →L[𝕜] E,
  (f ∘L g ≈ .id 𝕜 F) ∧ (g ∘L f ≈ .id 𝕜 E)

omit [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
  [ContinuousConstSMul 𝕜 E] [ContinuousConstSMul 𝕜 F] in
lemma IsFredholmQuot.iff_toLinearMap :
    IsFredholmQuot f ↔ ∃ g : F →L[𝕜] E, LinearMap.IsQuasiInverse f.toLinearMap g.toLinearMap := by
  rfl

theorem AnatoleDream (hf : IsFredholmStruct f) : IsFredholmQuot f:= sorry

def AnatoleDream_symm (hf : IsFredholmQuot f) : IsFredholmStruct f := sorry

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

open ContinuousLinearMap.FiniteRangeSetoid

section

variable {u : E →L[𝕜] F} {v : F →L[𝕜] E}

omit [IsTopologicalAddGroup F] in
theorem ContinuousLinearMap.coFG_eqLocus (hgf : v ∘L u ≈ .id 𝕜 E) :
    ((ContinuousLinearMap.id 𝕜 E).eqLocus (v ∘L u)).CoFG := by
  simpa [equiv_iff, LinearMap.FiniteRangeSetoid.equiv_iff_eqLocus_coFG] using Setoid.symm hgf

omit [IsTopologicalAddGroup F] in
theorem ContinuousLinearMap.id_sub_comp_ker_coFG (hgf : v ∘L u ≈ .id 𝕜 E) :
    (.id 𝕜 E - v ∘L u).ker.CoFG := by
  simpa [equiv_iff, LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange] using Setoid.symm hgf

variable [ContinuousConstSMul 𝕜 E]
variable [T1Space E] [T1Space F] [ContinuousConstSMul 𝕜 F]

/-- Need rename. -/
theorem aaron (hr : IsFredholmQuot u) :
    ∃ (E₁ : Submodule 𝕜 E) (F₁ : Submodule 𝕜 F), IsClosed E₁.carrier ∧ E₁.CoFG ∧
      IsClosed F₁.carrier ∧ F₁.CoFG ∧ ∃ h : MapsTo u E₁ F₁,
        (u.restrict h).IsInvertible := by
  obtain ⟨v, huv, hvu⟩ := hr
  set E₁ := (ContinuousLinearMap.id 𝕜 E).eqLocus (v ∘L u)
  set F₁ := (ContinuousLinearMap.id 𝕜 F).eqLocus (u ∘L v)
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
  · exact hf.isClosed_range
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
--private
lemma injectiveOn_complement (huF : IsFredholmStruct u) :
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

@[simp]
lemma ofIsHomeomorph_coe {f : M ≃ₛₗ[σ] M₂} (hf : IsHomeomorph f) :
    (ContinuousLinearEquiv.ofIsHomeomorph f hf).toLinearEquiv = f := by dsimp only [ofIsHomeomorph]

@[simp]
lemma ofIsHomeomorph_apply {f : M ≃ₛₗ[σ] M₂} (hf : IsHomeomorph f) (x : M) :
    (ContinuousLinearEquiv.ofIsHomeomorph f hf) x = f x := by dsimp [ofIsHomeomorph]

end ContinuousLinearEquiv

-- private
def FredholmDecomposition_LinearEquiv₁ :
    (FredholmDecomposition huF).1.X₁ ≃ₗ[𝕜] (FredholmDecomposition huF).2.X₁ :=
  .ofBijective _ ⟨FredholmDecomposition_InjectiveOn₁ huF, FredholmDecomposition_SurjectiveOn₁ huF⟩

-- private
lemma FredholmDecomposition_LinearEquiv₁_coe :
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
  obtain ⟨e, he⟩ := h_inv
  have eqL : u.domRestrict E₁ = F₁.subtypeL ∘L e := congr(F₁.subtypeL ∘L $he).symm
  have eqₗ : u.toLinearMap.domRestrict E₁ = F₁.subtype ∘ₗ e := congr(($eqL).toLinearMap)
  have h : Topology.IsStrictMap u ∧ IsClosed (u.range : Set F) := by
    rw [u.isStrictMap_isClosed_range_iff_restrict E₁ E₁_closed, ← LinearMap.range_domRestrict,
      eqₗ, eqL]
    exact ⟨F₁.isEmbedding_subtype.comp e.toHomeomorph.isEmbedding |>.isStrictMap, by simpa⟩
  have disj : Disjoint E₁ u.ker := by
    rw [disjoint_iff_comap_eq_bot, ← LinearMap.ker_domRestrict, eqₗ,
      LinearMap.ker_comp, ker_subtype, comap_bot, LinearEquiv.ker]
  constructor
  · exact h.1
  · exact h.2
  · rw [← Submodule.fg_iff_finiteDimensional]
    exact E₁_coFG.fg_of_disjoint disj.symm
  · refine F₁_coFG.of_le (le_trans ?_ (u.range_domRestrict_le_range E₁))
    rw [eqₗ, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, range_subtype]
  · exact ContinuousLinearMap.ker_closedComplemented_of_isInvertible_restrict
      E₁ F₁ E₁_closed E₁_coFG h_mapsto ⟨e, he⟩

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
    · rw [FiniteRangeSetoid.equiv_iff, LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange,
        LinearMap.hasFiniteRange_iff_range, Submodule.fg_iff_finiteDimensional]
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
    · rw [FiniteRangeSetoid.equiv_iff, LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange,
        LinearMap.hasFiniteRange_iff_range, Submodule.fg_iff_finiteDimensional]
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
  have hr : (G.mkQL ∘L u).range = ⊤ := by
    simp [LinearMap.range_comp, hG.symm.sup_eq_top]
  have ho : IsOpenMap (G.mkQL ∘L u) := by
    have : IsClosed (G : Set F) := G.closed_of_finiteDimensional
    exact ContinuousLinearMap.isOpenMap _ <| LinearMap.range_eq_top.mp hr
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
theorem key_fact {u₀ : E →L[𝕜] F} {v₀ : F →L[𝕜] E} (h : u₀.IsQuasiInverse v₀) :
    ∃ φ : (E →L[𝕜] F) → (F →L[𝕜] E), φ u₀ = v₀ ∧
      ∀ᶠ u in 𝓝 u₀, u.IsQuasiInverse (φ u) ∧
      ∀ᶠ u in 𝓝 u₀, u.index = u₀.index := by
  sorry

end NormPerturbation
