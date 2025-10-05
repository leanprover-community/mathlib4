/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Submodule.Order
import Mathlib.Algebra.Order.Module.Archimedean
import Mathlib.Algebra.Order.Module.Equiv
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.RingTheory.HahnSeries.Lex

/-!
# Hahn embedding theorem on ordered modules

This file proves a variant of the Hahn embedding theorem:

For a linearly ordered module `M` over an Archimedean division ring `K`,
there exists a strictly monotone linear map to lexicographically ordered
`HahnSeries (FiniteArchimedeanClass M) R` with an archimedean `K`-module `R`,
as long as there are embeddings from a certain family of Archimedean submodules to `R`.

The family of Archimedean submodules `HahnEmbedding.ArchimedeanStrata K M` is indexed by
`(c : ArchimedeanClass M)`, and each submodule is a complement of `ArchimedeanClass.ball K c`
under `ArchimedeanClass.closedBall K c`. The embeddings from these submodules are specified by
`HahnEmbedding.Seed K M R`.

By setting `K = ℚ` and `R = ℝ`, the condition can be trivially satisfied, leading
to a proof of the classic Hahn embedding theorem. (TODO: implement this)

## Main theorem

* `hahnEmbedding_isOrderedModule`:
  there exists a strictly monotone `M →ₗ[K] Lex (HahnSeries (FiniteArchimedeanClass M) R)` that maps
  `ArchimedeanClass M` to `HahnSeries.orderTop` in the expected way, as long as
  `HahnEmbedding.Seed K M R` is nonempty.

## References

* [M. Hausner, J.G. Wendel, *Ordered vector spaces*][hausnerwendel1952]
-/

/-! ### Step 1: base embedding

We start with `HahnEmbedding.ArchimedeanStrata` that gives a family of Archimedean submodules,
and a "seed" `HahnEmbedding.Seed` that specifies how to embed each
`HahnEmbedding.ArchimedeanStrata.stratum` into `R`.

From these, we create a partial map from the direct sum of all `stratum` to `HahnSeries Γ R`.
If `ArchimedeanClass M` is finite, the direct sum is the entire `M` and we are done
(though we don't handle this case separately). Otherwise, we will extend the map to `M` in the
following steps.
-/

open ArchimedeanClass DirectSum

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]
variable [Module K M] [IsOrderedModule K M]
variable {R : Type*} [AddCommGroup R] [LinearOrder R]
variable [Module K R]

namespace HahnEmbedding

variable (K M) in
/-- A family of submodules indexed by `ArchimedeanClass M` that
are complements between `ArchimedeanClass.ball` and `ArchimedeanClass.closedBall`. -/
structure ArchimedeanStrata where
  /-- For each `ArchimedeanClass`, specify a corresponding submodule. -/
  stratum : ArchimedeanClass M → Submodule K M
  /-- `stratum` and `ArchimedeanClass.ball` are disjoint. -/
  disjoint_ball_stratum (c : ArchimedeanClass M) : Disjoint (ball K c) (stratum c)
  /-- `stratum` and `ArchimedeanClass.ball` are codisjoint under `ArchimedeanClass.closedBall`. -/
  ball_sup_stratum_eq (c : ArchimedeanClass M) : ball K c ⊔ stratum c = closedBall K c

namespace ArchimedeanStrata
variable (u : ArchimedeanStrata K M) {c : ArchimedeanClass M}

@[simp] lemma ball_eq_closedBall : ball K c = closedBall K c ↔ c = ⊤ where
  mp h := by
    induction c using ind with | mk a
    contrapose! h
    rw [Ne, Submodule.ext_iff, not_forall]
    exact ⟨a, by simp [h]⟩
  mpr := by rintro rfl; simp

@[simp] lemma stratum_top : u.stratum (⊤ : ArchimedeanClass M) = ⊥ := by
  simpa using u.ball_sup_stratum_eq ⊤

theorem stratum_eq_bot_iff : u.stratum c = ⊥ ↔ c = ⊤ where
  mp h := by simpa [h] using u.ball_sup_stratum_eq c
  mpr := by rintro rfl; simp

theorem nontrivial_stratum (h : c ≠ ⊤) :
    Nontrivial (u.stratum c) :=
  (Submodule.nontrivial_iff_ne_bot).mpr (u.stratum_eq_bot_iff.ne.mpr h)

theorem archimedeanClassMk_of_mem_stratum {a : M}
    (ha : a ∈ u.stratum c) (h0 : a ≠ 0) : ArchimedeanClass.mk a = c := by
  apply le_antisymm
  · have hc : c ≠ ⊤ := by
      contrapose! h0
      rw [u.stratum_eq_bot_iff.mpr h0] at ha
      simpa using ha
    contrapose! h0 with hlt
    have ha' : a ∈ ball K c := (mem_ball_iff K hc).mpr hlt
    exact (Submodule.disjoint_def.mp (u.disjoint_ball_stratum _)) _ ha' ha
  · apply (mem_closedBall_iff K).mp
    rw [← u.ball_sup_stratum_eq c]
    exact Submodule.mem_sup_right ha

instance archimedean_stratum : Archimedean (u.stratum c) := by
  apply archimedean_of_mk_eq_mk
  intro a ha b hb
  suffices ArchimedeanClass.mk a.val = ArchimedeanClass.mk b.val by
    rw [mk_eq_mk] at this ⊢
    exact this
  rw [u.archimedeanClassMk_of_mem_stratum a.prop (by simpa using ha)]
  rw [u.archimedeanClassMk_of_mem_stratum b.prop (by simpa using hb)]

theorem iSupIndep_stratum : iSupIndep u.stratum := by
  intro c
  rw [Submodule.disjoint_def']
  intro a ha b hb hab
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ b).mp hb
  obtain hf' := congrArg ArchimedeanClass.mk hf
  contrapose! hf' with h0
  rw [← hab, DFinsupp.sum]
  by_cases hnonempty : f.support.Nonempty
  · have hmem (x : ArchimedeanClass M) : (f x).val ∈ u.stratum x :=
      Set.mem_of_mem_of_subset (f x).prop (by simp)
    have hmono : StrictMonoOn (fun i ↦ ArchimedeanClass.mk (f i).val) f.support := by
      intro x hx y hy hxy
      change ArchimedeanClass.mk (f x).val < ArchimedeanClass.mk (f y).val
      rw [u.archimedeanClassMk_of_mem_stratum (hmem x) (by simpa using hx)]
      rw [u.archimedeanClassMk_of_mem_stratum (hmem y) (by simpa using hy)]
      exact hxy
    rw [mk_sum hnonempty hmono]
    rw [u.archimedeanClassMk_of_mem_stratum (hmem _)
      (by simpa using Finset.min'_mem f.support hnonempty)]
    by_contra!
    obtain h := this ▸ Finset.min'_mem f.support hnonempty
    contrapose! h
    rw [DFinsupp.notMem_support_iff, u.archimedeanClassMk_of_mem_stratum ha h0]
    simpa using (f c).prop
  · rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty]
    symm
    simpa using h0

/-- The minimal submodule that contains all strata.

This is the domain of our "base" embedding into Hahn series, which we will extend into a full
embedding. -/
def baseDomain := ⨆ c, u.stratum c

/-- `ArchimedeanStrata.stratum` as a submodule of
`ArchimedeanStrata.baseDomain`. -/
abbrev stratum' (c : ArchimedeanClass M) : Submodule K (baseDomain u) :=
  (u.stratum c).comap u.baseDomain.subtype

theorem iSupIndep_stratum' : iSupIndep u.stratum' := by
  apply (iSupIndep_map_orderIso_iff (Submodule.mapIic u.baseDomain)).mp
  apply iSupIndep.of_coe_Iic_comp
  convert u.iSupIndep_stratum
  ext1 c
  simpa using le_iSup _ _

theorem isInternal_stratum' : DirectSum.IsInternal u.stratum' := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top u.iSupIndep_stratum'
  apply Submodule.map_injective_of_injective u.baseDomain.subtype_injective
  suffices ⨆ i, u.baseDomain ⊓ u.stratum i = u.baseDomain by simpa using this
  apply iSup_congr
  intro c
  simpa using le_iSup _ _

noncomputable
instance : DirectSum.Decomposition u.stratum' := (u.isInternal_stratum').chooseDecomposition _

end ArchimedeanStrata

variable (K M R) in
/-- `HahnEmbedding.Seed` extends `HahnEmbedding.ArchimedeanStrata` by specifying strictly monotone
linear maps from each `stratum` to module `R`. -/
structure Seed extends ArchimedeanStrata K M where
  /-- For each stratum, specify a linear map to `R` as the Hahn series coefficient. -/
  coeff (c : ArchimedeanClass M) : stratum c →ₗ[K] R
  /-- `coeff` is strictly monotone. -/
  strictMono_coeff (c : ArchimedeanClass M) : StrictMono (coeff c)

variable (seed : Seed K M R)

namespace Seed

/-- `HahnEmbedding.Seed.coeff` with `ArchimedeanStrata.stratum'` as domain. -/
def coeff' (c : ArchimedeanClass M) : seed.stratum' c →ₗ[K] R :=
  (seed.coeff c).comp (LinearMap.submoduleComap _ _)

/-- Coefficients of Hahn series for each `baseDomain` element. -/
noncomputable
def hahnCoeff : seed.baseDomain →ₗ[K] (⨁ _ : ArchimedeanClass M, R) :=
  (DirectSum.lmap seed.coeff') ∘ₗ (DirectSum.decomposeLinearEquiv _).toLinearMap

theorem hahnCoeff_apply {x : seed.baseDomain} {f : Π₀ c, seed.stratum c}
    (h : x.val = f.sum fun c ↦ (seed.stratum c).subtype) (c : ArchimedeanClass M) :
    seed.hahnCoeff x c = seed.coeff c (f c) := by
  suffices seed.baseDomain.subtype.submoduleComap
      (seed.stratum c) (DirectSum.decompose seed.stratum' x c) = f c by
    simp [Seed.hahnCoeff, coeff', this]
  have hxm {c : ArchimedeanClass M} (x : seed.stratum c) : x.val ∈ seed.baseDomain := by
    apply Set.mem_of_mem_of_subset x.prop
    simpa using le_iSup _ _
  let f' : ⨁ c, seed.stratum' c :=
    f.mapRange (fun c x ↦ (⟨⟨x.val, hxm x⟩, by simp⟩ : seed.stratum' c)) (by simp)
  have hf : f c = (seed.baseDomain.subtype.submoduleComap (seed.stratum c)) (f' c) := by
    apply Subtype.eq
    simp [f']
  have hx : x = (decompose seed.stratum').symm f' := by
    change x = f'.coeAddMonoidHom _
    apply Submodule.subtype_injective
    rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.sum_mapRange_index (by simp)]
    simp [h]
  simp [hf, hx]

/-- Combining all `HahnEmbedding.Seed.coeff` as
a partial linear map from `HahnEmbedding.Seed.baseDomain` to `HahnSeries`. -/
noncomputable
def baseEmbedding : M →ₗ.[K] Lex (HahnSeries (FiniteArchimedeanClass M) R) where
  domain := seed.baseDomain
  toFun := (toLexLinearEquiv _ _).toLinearMap ∘ₗ (HahnSeries.ofFinsuppLinearMap _) ∘ₗ
    (Finsupp.lcomapDomain _ Subtype.val_injective) ∘ₗ
    (finsuppLequivDFinsupp K).symm.toLinearMap ∘ₗ seed.hahnCoeff

theorem domain_baseEmbedding : seed.baseEmbedding.domain = seed.baseDomain := rfl

theorem coeff_baseEmbedding {x : seed.baseEmbedding.domain} {f : Π₀ c, seed.stratum c}
    (h : x.val = f.sum fun c ↦ (seed.stratum c).subtype) (c : FiniteArchimedeanClass M) :
    (ofLex ((baseEmbedding seed) x)).coeff c = seed.coeff c (f c) := by
  simpa [baseEmbedding] using seed.hahnCoeff_apply h c.val

theorem mem_domain_baseEmbedding {x : M} {c : ArchimedeanClass M} (h : x ∈ seed.stratum c) :
    x ∈ seed.baseEmbedding.domain := by
  apply Set.mem_of_mem_of_subset h
  rw [domain_baseEmbedding]
  simpa using le_iSup_iff.mpr fun _ h ↦ h c

end Seed

/-! ### Step 2: characterize partial embedding

We characterize the base embedding as a member of a class of partial linear embeddings
`HahnEmbedding.Partial`. These embeddings share nice properties, including being strictly monotone,
transferring `ArchimedeanClass` to `HahnEmbedding.orderTop`, and being "truncation-closed"
(see `HahnEmbedding.IsPartial.truncLT_mem_range`).
-/

/-- A partial linear map is called a "partial Hahn embedding" if it extends
`HahnEmbedding.Seed.baseEmbedding`, is strictly monotone, and is truncation-closed. -/
structure IsPartial (f : M →ₗ.[K] Lex (HahnSeries (FiniteArchimedeanClass M) R)) : Prop where
  /-- A partial Hahn embedding is strictly monotone. -/
  strictMono : StrictMono f
  /-- A partial Hahn embedding always extends `baseEmbedding`. -/
  baseEmbedding_le : seed.baseEmbedding ≤ f
  /-- If a Hahn series $f$ is in the range, then any truncation of $f$ is also in the range. -/
  truncLT_mem_range : ∀ x, ∀ c,
    toLex (HahnSeries.truncLTLinearMap K c (ofLex (f x))) ∈ LinearMap.range f.toFun

namespace Seed

theorem baseEmbedding_pos {x : seed.baseEmbedding.domain} (hx : 0 < x) :
    0 < seed.baseEmbedding x := by
  -- decompose `x` to sum of `stratum`
  have hmem : x.val ∈ seed.baseEmbedding.domain := x.prop
  simp_rw [seed.domain_baseEmbedding] at hmem
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ _).mp hmem
  have hfpos : 0 < (f.sum fun _ x ↦ x.val) := by
    rw [hf]
    simpa using hx
  have hsupport : f.support.Nonempty := by
    obtain hne := hfpos.ne.symm
    contrapose! hne with hempty
    apply DFinsupp.sum_eq_zero
    intro c
    simpa using DFinsupp.notMem_support_iff.mp (forall_not_of_not_exists hempty c)
  have htop : f.support.min' hsupport ≠ ⊤ := by
    by_contra! h
    have h : ⊤ ∈ f.support := h ▸ f.support.min'_mem hsupport
    rw [DFinsupp.mem_support_iff] at h
    contrapose! h
    rw [← Submodule.coe_eq_zero, ← Submodule.mem_bot K]
    convert ← (f ⊤).prop
    simp
  -- The dictating term for `HahnSeries` < is at the lowest archimedean class of `f.support`
  refine (HahnSeries.lt_iff _ _).mpr ⟨⟨f.support.min' hsupport, htop⟩, ?_, ?_⟩
  · intro j hj
    rw [seed.coeff_baseEmbedding hf.symm]
    rw [DFinsupp.notMem_support_iff.mp ?_]
    · simp
    contrapose! hj
    rw [← Subtype.coe_le_coe, Subtype.coe_mk]
    exact Finset.min'_le f.support _ hj
  -- Show that `f`'s value at dominating archimedean class is positive
  rw [seed.coeff_baseEmbedding hf.symm]
  suffices (seed.coeff (f.support.min' hsupport)) 0 <
      (seed.coeff (f.support.min' hsupport)) (f (f.support.min' hsupport)) by
    simpa using this
  suffices 0 < (f (f.support.min' hsupport)).val by
    apply (seed.strictMono_coeff (f.support.min' hsupport))
    simpa using this
  -- using the fact that `f.sum` is positive, we only needs to show that
  -- the remaining terms of f after removing the dominating class is of higher class
  apply pos_of_pos_of_mk_lt hfpos
  rw [mk_sub_comm]
  have hferase : (f.sum fun _ x ↦ x.val) - (f (f.support.min' hsupport)).val =
      ∑ x ∈ f.support.erase (f.support.min' hsupport), (f x).val :=
    sub_eq_of_eq_add (Finset.sum_erase_add _ _ (Finset.min'_mem _ hsupport)).symm
  rw [hferase]
  -- Now both sides are `mk (∑ ...)`
  -- We rewrite them to `mk (dominating term)`
  have hmono : StrictMonoOn (fun x ↦ ArchimedeanClass.mk (f x).val) f.support := by
    intro c hc d hd h
    simp only
    rw [seed.archimedeanClassMk_of_mem_stratum (f c).prop (by simpa using hc)]
    rw [seed.archimedeanClassMk_of_mem_stratum (f d).prop (by simpa using hd)]
    exact h
  rw [DFinsupp.sum, mk_sum hsupport hmono]
  rw [seed.archimedeanClassMk_of_mem_stratum (f _).prop
    (by simpa using f.support.min'_mem hsupport)]
  by_cases hsupport' : (f.support.erase (f.support.min' hsupport)).Nonempty
  · rw [mk_sum hsupport' (hmono.mono (by simp))]
    rw [seed.archimedeanClassMk_of_mem_stratum (f _).prop (by
      simpa using (Finset.mem_erase.mp <| (f.support.erase _).min'_mem hsupport').2)]
    apply Finset.min'_lt_of_mem_erase_min'
    apply Finset.min'_mem _ _
  · -- special case: `f` has a single term, and becomes 0 after removing it
    have : f.support.erase (f.support.min' hsupport) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hsupport'
    simpa [this] using lt_top_iff_ne_top.mpr htop

theorem baseEmbedding_strictMono [IsOrderedAddMonoid R] : StrictMono seed.baseEmbedding := by
  intro x y h
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
  exact baseEmbedding_pos _ <| by simpa using h

theorem truncLT_mem_range_baseEmbedding (x : seed.baseEmbedding.domain)
    (c : FiniteArchimedeanClass M) :
    toLex (HahnSeries.truncLTLinearMap K c (ofLex (seed.baseEmbedding x))) ∈
    LinearMap.range seed.baseEmbedding.toFun := by
  -- decompose `x` to `stratum`
  have hmem : x.val ∈ seed.baseEmbedding.domain := x.prop
  simp_rw [seed.domain_baseEmbedding] at hmem
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ _).mp hmem
  -- Truncating in the codomain is the same as truncating away some submodule
  let f' : Π₀ (i : ArchimedeanClass M), seed.stratum i :=
    DFinsupp.mk f.support fun d ↦ if c.val ≤ d.val then 0 else f d.val
  refine ⟨⟨f'.sum fun d x ↦ x.val, ?_⟩, ?_⟩
  · rw [seed.domain_baseEmbedding, ArchimedeanStrata.baseDomain,
      Submodule.mem_iSup_iff_exists_dfinsupp']
    use f'
  apply_fun ofLex
  rw [ofLex_toLex, LinearPMap.toFun_eq_coe]
  ext d
  rw [seed.coeff_baseEmbedding rfl]
  unfold f'
  obtain hdc | hdc := lt_or_ge d c
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_lt hdc,
      seed.coeff_baseEmbedding hf.symm]
    apply congrArg
    have hcd : ¬ c.val ≤ d.val := not_le_of_gt hdc
    simp only [DFinsupp.mk_apply, hcd, ↓reduceIte]
    aesop
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_le hdc]
    have hcd : c.val ≤ d.val := hdc
    simp only [DFinsupp.mk_apply, hcd, ↓reduceIte]
    convert LinearMap.map_zero _
    simp

/-- `HahnEmbedding.Seed.baseEmbedding` is a partial Hahn embedding. -/
theorem isPartial_baseEmbedding [IsOrderedAddMonoid R] : IsPartial seed seed.baseEmbedding where
  strictMono := seed.baseEmbedding_strictMono
  baseEmbedding_le := le_refl _
  truncLT_mem_range := seed.truncLT_mem_range_baseEmbedding

end Seed

/-- The type of all partial Hahn embeddings. -/
abbrev Partial := {f : M →ₗ.[K] Lex (HahnSeries (FiniteArchimedeanClass M) R) // IsPartial seed f}

namespace Partial
variable {seed} (f : Partial seed)

noncomputable
instance [IsOrderedAddMonoid R] : Inhabited (Partial seed) where
  default := ⟨seed.baseEmbedding, seed.isPartial_baseEmbedding⟩

/-- `HahnEmbedding.Partial` as an `OrderedAddMonoidHom`. -/
def toOrderAddMonoidHom : f.val.domain →+o Lex (HahnSeries (FiniteArchimedeanClass M) R) where
  __ := f.val.toFun
  map_zero' := by simp
  monotone' := f.prop.strictMono.monotone

theorem toOrderAddMonoidHom_apply (x : f.val.domain) : f.toOrderAddMonoidHom x = f.val x := rfl

theorem toOrderAddMonoidHom_injective : Function.Injective f.toOrderAddMonoidHom :=
  f.prop.strictMono.injective

theorem mem_domain {x : M} {c : ArchimedeanClass M} (hx : x ∈ seed.stratum c) :
    x ∈ f.val.domain := by
  apply Set.mem_of_subset_of_mem f.prop.baseEmbedding_le.1
  apply seed.mem_domain_baseEmbedding hx

theorem apply_of_mem_stratum {x : f.val.domain} {c : FiniteArchimedeanClass M}
    (hx : x.val ∈ seed.stratum c.val) :
    f.val x = toLex (HahnSeries.single c (seed.coeff c.val ⟨x.val, hx⟩)) := by
  have hx' : x.val ∈ seed.baseEmbedding.domain := seed.mem_domain_baseEmbedding hx
  have heq : (⟨x.val, hx'⟩ : seed.baseEmbedding.domain).val = x.val := rfl
  rw [← f.prop.baseEmbedding_le.2 heq]
  let fx : Π₀ c, seed.stratum c := DFinsupp.single c ⟨x.val, hx⟩
  have hfx : x.val = fx.sum fun c ↦ (seed.stratum c).subtype := by
    simp [fx, DFinsupp.sum_single_index]
  apply_fun ofLex
  rw [ofLex_toLex]
  ext d
  rw [seed.coeff_baseEmbedding hfx]
  unfold fx
  obtain rfl | hdc := eq_or_ne d c
  · simp
  have hcd : c.val ≠ d.val := Subtype.ext_iff.ne.mp hdc.symm
  simp [HahnSeries.coeff_single_of_ne hdc, hcd]

/-- Archimedean equivalence is preserved by `f`. -/
theorem archimedeanClassMk_eq_iff [IsOrderedAddMonoid R] (x y : f.val.domain) :
    mk (f.val x) = mk (f.val y) ↔ mk x.val = mk y.val := by
  simp_rw [← toOrderAddMonoidHom_apply, ← orderHom_mk]
  trans mk x = mk y
  · exact Function.Injective.eq_iff <| orderHom_injective <| toOrderAddMonoidHom_injective _
  · simp_rw [mk_eq_mk]
    aesop

/-- Archimedean equivalence of input is transferred to `HahnSeries.orderTop` equality. -/
theorem orderTop_eq_iff [IsOrderedAddMonoid R] [Archimedean R] (x y : f.val.domain) :
    (ofLex (f.val x)).orderTop = (ofLex (f.val y)).orderTop ↔ mk x.val = mk y.val := by
  obtain hsubsingleton | hnontrivial := subsingleton_or_nontrivial M
  · have : y = x := Subtype.eq <| hsubsingleton.allEq _ _
    simp [this]
  have hnonempty : Nonempty (FiniteArchimedeanClass M) := inferInstance
  obtain c := hnonempty.some
  have hnontrivial' : Nontrivial (seed.stratum c) := seed.nontrivial_stratum c.prop
  have : Nontrivial R := (seed.strictMono_coeff c).injective.nontrivial
  rw [← archimedeanClassMk_eq_iff]
  simp_rw [← HahnSeries.archimedeanClassOrderIsoWithTop_apply]
  rw [(HahnSeries.archimedeanClassOrderIsoWithTop (FiniteArchimedeanClass M) R).injective.eq_iff]

/-- Archimedean class of the input is transferred to `HahnSeries.orderTop`. -/
theorem orderTop_eq_archimedeanClassMk [IsOrderedAddMonoid R] [Archimedean R] (x : f.val.domain) :
    FiniteArchimedeanClass.withTopOrderIso M (ofLex (f.val x)).orderTop = mk x.val := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx0' : x.val ≠ 0 := by simpa using hx0
  have : Nontrivial (seed.stratum (mk x)) := by
    apply seed.nontrivial_stratum
    simpa using hx0
  -- Pick a representative `x'` from `stratum` with the same class as `x`.
  -- `f.val x'` is a `HahnSeries.single` whose `orderTop` is known
  obtain ⟨⟨x', hx'mem⟩, hx'0⟩ := exists_ne (0 : seed.stratum (mk x))
  have heq : mk x' = mk x.val := by
    apply seed.archimedeanClassMk_of_mem_stratum hx'mem
    simpa using hx'0
  let x'' : f.val.domain := ⟨x', mem_domain f hx'mem⟩
  have hx''mem : x''.val ∈ seed.stratum (FiniteArchimedeanClass.mk x.val hx0').val := hx'mem
  have h0 : (seed.coeff (FiniteArchimedeanClass.mk x.val hx0').val) ⟨x''.val, hx''mem⟩ ≠ 0 := by
    rw [(LinearMap.map_eq_zero_iff _ (seed.strictMono_coeff _).injective).ne]
    unfold x''
    simpa using hx'0
  have heq' : mk x''.val = mk x.val := heq
  rw [← orderTop_eq_iff, apply_of_mem_stratum f hx''mem, ofLex_toLex,
    HahnSeries.orderTop_single h0] at heq'
  simp [← heq']

theorem orderTop_eq_finiteArchimedeanClassMk [IsOrderedAddMonoid R] [Archimedean R]
    {x : f.val.domain} (hx0 : x.val ≠ 0) :
    (ofLex (f.val x)).orderTop = FiniteArchimedeanClass.mk x.val hx0 := by
  apply_fun FiniteArchimedeanClass.withTopOrderIso M
  simp [orderTop_eq_archimedeanClassMk]

/-- For `x` within a ball of Archimedean class `c`, `f.val x`'coefficient at `d` vanishes
for `d ≤ c`. -/
theorem coeff_eq_zero_of_mem [IsOrderedAddMonoid R] [Archimedean R]
    {c : ArchimedeanClass M} {x : f.val.domain} (hx : x.val ∈ ball K c)
    {d : FiniteArchimedeanClass M} (hd : d.val ≤ c) : (ofLex (f.val x)).coeff d = 0 := by
  by_cases hc : c = ⊤
  · rw [hc] at hx
    have hx : x = 0 := by simpa using hx
    simp [hx]
  apply HahnSeries.coeff_eq_zero_of_lt_orderTop
  apply_fun FiniteArchimedeanClass.withTopOrderIso _
  rw [orderTop_eq_archimedeanClassMk, FiniteArchimedeanClass.withTopOrderIso_apply_coe]
  apply lt_of_le_of_lt hd
  simpa [hc] using hx

/-- `f.val x` has a non-zero coefficient at the position of the Archimedean class of `x`. -/
theorem coeff_ne_zero [IsOrderedAddMonoid R] [Archimedean R] {x : f.val.domain} (hx0 : x.val ≠ 0) :
    (ofLex (f.val x)).coeff (FiniteArchimedeanClass.mk x.val hx0) ≠ 0 :=
  HahnSeries.coeff_orderTop_ne <| f.orderTop_eq_finiteArchimedeanClassMk hx0

/-- When `y` and `z` are both near `x` (the difference is in a ball),
initial coefficients of `f.val y` and `f.val z` agree. -/
theorem coeff_eq_of_mem [IsOrderedAddMonoid R] [Archimedean R] (x : M) {y z : f.val.domain}
    {c : ArchimedeanClass M} (hy : y.val - x ∈ ball K c) (hz : z.val - x ∈ ball K c)
    {d : FiniteArchimedeanClass M} (hd : d ≤ c) :
    (ofLex (f.val y)).coeff d = (ofLex (f.val z)).coeff d := by
  apply eq_of_sub_eq_zero
  rw [← HahnSeries.coeff_sub, ← ofLex_sub, ← LinearPMap.map_sub]
  refine coeff_eq_zero_of_mem f ?_ hd
  have : (y - z).val = (y.val - x) - (z.val - x) := by
    push_cast
    simp
  rw [this]
  exact Submodule.sub_mem _ hy hz

/-! ### Step 3: extend the embedding

We create a larger `HahnEmbedding.Partial` from an existing one by adding a new element to the
domain and assigning an appropriate output that preserves all `HahnEmbedding.Partial`'s properties.
-/

/-- Evaluate coefficients of the `HahnSeries` given an arbitrary input that's not necessarily in
`f`'s domain. The coefficient is picked from `y` that is "close enough" to `x` (their difference
is in a higher `ArchimedeanClass`). If no such `y` exists (in other words, x is "isolated"), set the
coefficient to 0.

This doesn't immediately extend `f`'s domain to the entire module in a consistent way. Such
extension isn't necessarily linear.
-/
noncomputable
def evalCoeff (x : M) (c : FiniteArchimedeanClass M) : R :=
  open Classical in
  if h : ∃ y : f.val.domain, y.val - x ∈ ball K c then
    (ofLex (f.val h.choose)).coeff c
  else
    0

/-- The coefficient is well-defined regardless of which `y` we pick in `evalCoeff`. -/
theorem evalCoeff_eq [IsOrderedAddMonoid R] [Archimedean R] {x : M} {c : FiniteArchimedeanClass M}
    {y : f.val.domain} (hy : y.val - x ∈ ball K c) :
    evalCoeff f x c = (ofLex (f.val y)).coeff c := by
  have hnonempty : ∃ y : f.val.domain, y.val - x ∈ ball K c := ⟨y, hy⟩
  simpa [evalCoeff, hnonempty] using coeff_eq_of_mem f x hnonempty.choose_spec hy (le_refl _)

theorem evalCoeff_eq_zero {x : M} {c : FiniteArchimedeanClass M}
    (h : ¬∃ y : f.val.domain, y.val - x ∈ ball K c) :
    f.evalCoeff x c = 0 := by
  simp [evalCoeff, h]

theorem isWF_support_evalCoeff [IsOrderedAddMonoid R] [Archimedean R] (x : M) :
    (evalCoeff f x).support.IsWF := by
  rw [Set.isWF_iff_no_descending_seq]
  by_contra!
  obtain ⟨seq, ⟨hanti, hmem⟩⟩ := this
  have hnonempty : ∃ y : f.val.domain, y.val - x ∈ ball K (seq 0) := by
    specialize hmem 0
    contrapose hmem with hempty
    simp [evalCoeff, hempty]
  obtain ⟨y, hy⟩ := hnonempty
  have hmem' (n : ℕ) : seq n ∈ (ofLex (f.val y)).coeff.support := by
    specialize hmem n
    rw [Function.mem_support] at ⊢ hmem
    convert hmem using 1
    refine (f.evalCoeff_eq (ball_antitone K ?_ hy)).symm
    simpa using hanti.antitone (show 0 ≤ n by simp)
  obtain hwf := (ofLex (f.val y)).isWF_support
  contrapose! hwf
  rw [Set.isWF_iff_no_descending_seq]
  simpa using ⟨seq, hanti, hmem'⟩

/-- Promote `HahnEmbedding.Partial.evalCoeff`'s output to a new `HahnSeries`. -/
noncomputable
def eval [IsOrderedAddMonoid R] [Archimedean R] (x : M) :
    Lex (HahnSeries (FiniteArchimedeanClass M) R) :=
  toLex { coeff := f.evalCoeff x
          isPWO_support' := (f.isWF_support_evalCoeff x).isPWO }

@[simp]
theorem eval_zero [IsOrderedAddMonoid R] [Archimedean R] : f.eval 0 = 0 := by
  unfold eval
  convert toLex_zero
  ext c
  rw [f.evalCoeff_eq (y := 0) (by simp)]
  simp

theorem eval_smul [IsOrderedAddMonoid R] [Archimedean R] (k : K) (x : M) :
    f.eval (k • x) = k • f.eval x := by
  by_cases hk : k = 0
  · simp [hk]
  unfold eval
  rw [← toLex_smul, toLex.injective.eq_iff]
  ext c
  suffices f.evalCoeff (k • x) c = k • f.evalCoeff x c by simpa using this
  by_cases h : ∃ y : f.val.domain, y.val - x ∈ ball K c
  · obtain ⟨y, hy⟩ := h
    have heq : (k • y).val - k • x = k • (y.val - x) := by simp [smul_sub]
    have hy' : (k • y).val - k • x ∈ ball K c := by
      rw [heq]
      exact Submodule.smul_mem _ _ hy
    simp [f.evalCoeff_eq hy, f.evalCoeff_eq hy', LinearPMap.map_smul]
  have h' : ¬∃ y : f.val.domain, y.val - k • x ∈ ball K c := by
    contrapose! h
    obtain ⟨y, hy⟩ := h
    use k⁻¹ • y
    have heq : (k⁻¹ • y).val - x = k⁻¹ • (y.val - k • x) := by
      simp [smul_sub, smul_smul, inv_mul_cancel₀ hk]
    exact heq ▸ Submodule.smul_mem _ _ hy
  simp [f.evalCoeff_eq_zero h, f.evalCoeff_eq_zero h']

/-- If `f.eval x = f.val y`, then for any `z` in the domain, `x - z` can't be closer than `x - y`
in terms of Archimedean classes. -/
theorem archimedeanClassMk_le_of_eval_eq [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    {y : f.val.domain} (h : f.eval x = f.val y) (z : f.val.domain) :
    mk (x - z.val) ≤ mk (x - y.val) := by
  have : x - y.val = x - z.val + (z.val - y.val) := by abel
  rw [this]
  apply mk_left_le_mk_add
  by_cases hyz : z.val - y.val = 0
  · simp [hyz]
  have h1 (c : FiniteArchimedeanClass M) (hc : c.val < mk (x - z.val)) :
      (ofLex (f.eval x)).coeff c = (ofLex (f.val z)).coeff c := by
    rw [mk_sub_comm] at hc
    simp_rw [eval, ofLex_toLex]
    apply evalCoeff_eq
    simpa [c.prop] using hc
  have h2 : ∀ c : FiniteArchimedeanClass M, c.val < mk (x - z.val) →
      (ofLex (f.val (z - y))).coeff c = 0 := by
    intro c hc
    rw [LinearPMap.map_sub, ofLex_sub, HahnSeries.coeff_sub, sub_eq_zero, ← h]
    exact (h1 c hc).symm
  contrapose! h2
  exact ⟨FiniteArchimedeanClass.mk (z.val - y.val) hyz, h2, coeff_ne_zero _ _⟩

/-- If `x` isn't in `f`'s domain, `f.eval x` produces a brand new value not in `f`'s range. -/
theorem eval_ne [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
    (y : f.val.domain) : f.eval x ≠ f.val y := by
  have hxy0 : mk (x - y.val) ≠ ⊤ := by
    contrapose! hx with hxy
    rw [mk_eq_top_iff, sub_eq_zero] at hxy
    rw [hxy]
    exact y.prop
  -- decompose `x - y = u + v`, where `v ∈ submodule (x - y)` and
  -- `u` is at higher class than `x - y`
  have hxy : x - y.val ∈ closedBall K (mk (x - y.val)) := by simp
  rw [← seed.ball_sup_stratum_eq (mk (x - y.val)), Submodule.mem_sup] at hxy
  obtain ⟨u, hu, v, hv, huv⟩ := hxy
  have huv' : x - y.val - v = u := by simp [← huv]
  rw [mem_ball_iff K hxy0] at hu
  -- `z = x - u = y + v` is also in the domain.
  -- Assuming `f.eval x = f.val y` allows us to use `archimedeanClassMk_le_of_eval_eq` on `z`
  have hyv : y.val + v ∈ f.val.domain := Submodule.add_mem _ (by simp) (f.mem_domain hv)
  by_contra! h
  obtain h := f.archimedeanClassMk_le_of_eval_eq h ⟨y.val + v, hyv⟩
  contrapose! h
  simpa [← sub_sub, huv'] using hu

/-- If there is a `y` in `f`'s domain with `c = ArchimedeanClass (y - x)`, but there
is no closer `z` to `x` where the difference is of a higher `ArchimedeanClass`, then
`f.eval x` is simply `f.val y` truncated at `c`.

This doesn't mean every `x` can be evaluated this way: it is possible that one can find
an infinite chain of `y` that keeps getting closer to `x` in terms of Archimedean classes,
yet `x` is still isolated within a very high Archimedean class. In fact, in the next theorem,
we will show that there is always such chain for `x` not in `f`'s domain. -/
theorem eval_eq_truncLT [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    {c : FiniteArchimedeanClass M} {y : f.val.domain}
    (hy : mk (y.val - x) = c.val) (h : ∀ z : f.val.domain, z.val - x ∉ ball K c) :
    f.eval x = toLex (HahnSeries.truncLTLinearMap K c (ofLex (f.val y))) := by
  unfold eval
  rw [toLex.injective.eq_iff]
  ext d
  simp only
  obtain hd | hd := lt_or_ge d c
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_lt hd]
    apply evalCoeff_eq
    simpa [d.prop, hy] using hd
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_le hd]
    apply evalCoeff_eq_zero
    contrapose! h
    obtain ⟨z, hz⟩ := h
    exact ⟨z, ball_antitone K (by simpa using hd) hz⟩

/-- For `x` not in `f`'s domain, there is an infinite chain of `y` from `f`'s domain
that keeps getting closer to `x` in terms of Archimedean classes. -/
theorem exists_sub_mem_ball [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
    (y : f.val.domain) : ∃ z : f.val.domain, z.val - x ∈ ball K (mk (y.val - x)) := by
  have : y.val - x ≠ 0 := by
    contrapose! hx
    obtain rfl : x = y.val := (sub_eq_zero.mp hx).symm
    simp
  let c := FiniteArchimedeanClass.mk (y.val - x) this
  have hc : mk (y.val - x) = c.val := rfl
  contrapose! hx
  obtain h := f.eval_eq_truncLT hc hx
  obtain ⟨x', hx'⟩ := LinearMap.mem_range.mp (f.prop.truncLT_mem_range y c)
  rw [← hx'] at h
  contrapose! h
  exact f.eval_ne h _

/-- For `x` not in `f`'s domain, `f.eval x` is consistent with `f`'s monotonicity. -/
theorem eval_lt [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
    (y : f.val.domain) (h : x < y.val) : f.eval x < f.val y := by
  -- Expand the definition of `HahnSeries`' order. We need to find the first coefficient that
  -- dictates the < relation. This coefficient is exactly at the Archimedean class of `y - x`
  rw [HahnSeries.lt_iff]
  have hxy0 : y.val - x ≠ 0 := sub_ne_zero_of_ne h.ne.symm
  refine ⟨FiniteArchimedeanClass.mk (y.val - x) hxy0, ?_, ?_⟩
  · -- All coefficients before the dictating term are the same
    intro j hj
    apply evalCoeff_eq
    simpa [j.prop] using hj
  -- Show the dictating coefficient
  have hyxtop : mk (y.val - x) ≠ ⊤ := by simp [hxy0]
  suffices f.evalCoeff x (FiniteArchimedeanClass.mk (y.val - x) hxy0) <
      (ofLex (f.val y)).coeff (FiniteArchimedeanClass.mk (y.val - x) hxy0) by
    simpa [eval] using this
  -- We find `z` from `f`'s domain to approximate `x`. Such approximation obeys:
  -- * `f.eval x = f.val z`
  -- * `x < y → z < y`
  -- * `mk (x - y) = mk (z - y)`
  obtain ⟨z, hz⟩ := f.exists_sub_mem_ball hx y
  have hz' : z.val - x ∈ ball K (FiniteArchimedeanClass.mk (y.val - x) hxy0).val := hz
  rw [f.evalCoeff_eq hz']
  have hzy : z < y := by
    change z.val < y.val
    refine (sub_lt_sub_iff_right x).mp <| lt_of_mk_lt_mk_of_nonneg ?_ (sub_nonneg_of_le h.le)
    simpa [hyxtop] using hz
  have hzyne : z.val - y.val ≠ 0 := by
    apply sub_ne_zero_of_ne
    simpa using hzy.ne
  have hzyclass : FiniteArchimedeanClass.mk (y.val - x) hxy0 =
      FiniteArchimedeanClass.mk (z.val - y.val) hzyne := by
    suffices mk (y.val - x) = mk (z.val - y.val) by simpa [Subtype.eq_iff] using this
    have : y.val - z.val = y.val - x + (x - z.val) := by abel
    rw [mk_sub_comm z.val y.val, this]
    refine (mk_add_eq_mk_left ?_).symm
    rw [mk_sub_comm x z.val]
    simpa [hyxtop] using hz
  -- Since both `y` and `z` are in the domain, we can apply `f`'s monotonicity on them
  rw [← f.prop.strictMono.lt_iff_lt, HahnSeries.lt_iff] at hzy
  obtain ⟨i, hj, hi⟩ := hzy
  -- We show that the dictating coefficient of `f.val y < f.val z`
  -- is at the same position as the dictating coefficient of `f.eval x < f.val y`
  have hieq : i = FiniteArchimedeanClass.mk (y.val - x) hxy0 := by
    apply le_antisymm
    · by_contra! hlt
      obtain hj := sub_eq_zero_of_eq (hj (FiniteArchimedeanClass.mk (y.val - x) hxy0) hlt)
      contrapose! hj
      rw [← HahnSeries.coeff_sub, ← ofLex_sub, ← LinearPMap.map_sub, hzyclass]
      apply f.coeff_ne_zero
    · contrapose! hi
      rw [hzyclass] at hi
      have hzy : z.val - y.val ∈ ball K i.val := by simpa [i.prop] using hi
      exact (f.coeff_eq_of_mem y.val (by simp) hzy (by simp)).le
  exact hieq ▸ hi

/-- Extend `f` to a larger partial linear map by adding a new `x`. -/
noncomputable
def extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain) :
    M →ₗ.[K] Lex (HahnSeries (FiniteArchimedeanClass M) R) :=
  .supSpanSingleton f.val x (eval f x) hx

theorem extendFun_strictMono [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    (hx : x ∉ f.val.domain) : StrictMono (f.extendFun hx) := by
  have hx' {c : K} (hc : c ≠ 0) : -c • x ∉ f.val.domain := by
    contrapose! hx
    rwa [neg_smul, neg_mem_iff, Submodule.smul_mem_iff _ hc] at hx
  -- only need to prove `0 < f v` for `0 < v = z - y`
  intro y z hyz
  rw [← sub_pos] at hyz
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
  obtain hyzmem := (z - y).prop
  nth_rw 1 [extendFun, LinearPMap.domain_supSpanSingleton] at hyzmem
  -- decompose `v = a + c • x`, reducing this to eval_lt
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hyzmem
  have : z - y = ⟨a + b, hab.symm ▸ (z - y).prop⟩ := by simp_rw [hab]
  rw [this] at ⊢ hyz
  have habpos : 0 < a + b := by exact hyz
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hb
  rw [← hc] at habpos
  simp_rw [← hc, extendFun]
  rw [LinearPMap.supSpanSingleton_apply_mk _ _ _ hx _ ha]
  suffices f.eval (-c • x) < f.val ⟨a, ha⟩ by
    rw [eval_smul, neg_smul] at this
    exact neg_lt_iff_pos_add.mp this
  have hac : -c • x < a := by
    rw [neg_smul]
    exact neg_lt_iff_pos_add.mpr habpos
  by_cases hc : c = 0
  · rw [hc] at ⊢ hac
    suffices f.val 0 < f.val ⟨a, ha⟩ by simpa using this
    exact f.prop.strictMono (by simpa using hac)
  · exact f.eval_lt (hx' hc) ⟨a, ha⟩ hac

theorem baseEmbedding_le_extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    (hx : x ∉ f.val.domain) : seed.baseEmbedding ≤ f.extendFun hx := by
  rw [extendFun]
  exact le_trans f.prop.baseEmbedding_le <| LinearPMap.left_le_sup _ _ _

theorem truncLT_eval_mem_range_extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    (hx : x ∉ f.val.domain) (c : FiniteArchimedeanClass M) :
    toLex (HahnSeries.truncLTLinearMap K c (ofLex (f.eval x))) ∈
    LinearMap.range (f.extendFun hx).toFun := by
  rw [extendFun, LinearMap.mem_range]
  by_cases h : ∃ y : f.val.domain, y.val - x ∈ ball K c
  · -- if `x` is not isolated within `c`, the truncation at `c` equals to truncating
    -- a nearby `y` in the domain
    obtain ⟨y, hy⟩ := h
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp (f.prop.truncLT_mem_range y c)
    refine ⟨⟨z.val, by simpa using Submodule.mem_sup_left z.prop⟩, ?_⟩
    rw [LinearPMap.toFun_eq_coe] at hz
    rw [LinearPMap.toFun_eq_coe, LinearPMap.supSpanSingleton_apply_mk_of_mem _ _ _ z.prop]
    rw [hz, toLex_inj]
    ext d
    obtain hdc | hdc := lt_or_ge d c
    · simp_rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_lt hdc]
      refine (f.evalCoeff_eq (Set.mem_of_mem_of_subset hy ?_)).symm
      simpa using ball_antitone K hdc.le
    · simp_rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_le hdc]
  · -- if `x` is isolated within c, truncating has no effect because the trailing coefficients
    -- are already 0
    refine ⟨⟨x, by simpa using Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)⟩, ?_⟩
    apply_fun ofLex
    rw [ofLex_toLex, LinearPMap.toFun_eq_coe, LinearPMap.supSpanSingleton_apply_self]
    ext d
    obtain hdc | hdc := lt_or_ge d c
    · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_lt hdc]
    rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_le hdc, eval, ofLex_toLex]
    apply f.evalCoeff_eq_zero
    contrapose! h
    obtain ⟨y, hy⟩ := h
    exact ⟨y, Set.mem_of_mem_of_subset hy (by simpa using ball_antitone K hdc)⟩

theorem truncLT_mem_range_extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    (hx : x ∉ f.val.domain) (y : (f.extendFun hx).domain) (c : FiniteArchimedeanClass M) :
    toLex (HahnSeries.truncLTLinearMap K c (ofLex (f.extendFun hx y))) ∈
    LinearMap.range (f.extendFun hx).toFun := by
  obtain ⟨y', hy'⟩ := y
  rw [extendFun, LinearPMap.domain_supSpanSingleton] at hy'
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy'
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hb
  simp_rw [extendFun, ← hab, ← hk]
  rw [LinearPMap.supSpanSingleton_apply_mk _ _ _ _ _ ha]
  rw [ofLex_add, map_add, toLex_add, ofLex_smul, map_smul, toLex_smul]
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
  · obtain ⟨⟨a', ha'mem⟩, ha'⟩ := LinearMap.mem_range.mp (f.prop.truncLT_mem_range ⟨a, ha⟩ c)
    refine LinearMap.mem_range.mpr ⟨⟨a', by simpa using Submodule.mem_sup_left ha'mem⟩, ?_⟩
    rw [← ha']
    exact LinearPMap.supSpanSingleton_apply_mk_of_mem f.val _ hx ha'mem
  · apply truncLT_eval_mem_range_extendFun

theorem isPartial_extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    (hx : x ∉ f.val.domain) : IsPartial seed (extendFun f hx) where
  strictMono := f.extendFun_strictMono hx
  baseEmbedding_le := f.baseEmbedding_le_extendFun hx
  truncLT_mem_range := f.truncLT_mem_range_extendFun hx

/-- Promote `HahnEmbedding.Partial.extendFun` to a new `HahnEmbedding.Partial`. -/
noncomputable
def extend [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain) :
    Partial seed := ⟨f.extendFun hx, f.isPartial_extendFun hx⟩

theorem lt_extend [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain) :
    f < f.extend hx := by
  apply lt_of_le_of_ne
  · change f.val ≤ (f.extend hx).val
    simpa [extend, extendFun] using LinearPMap.left_le_sup _ _ _
  by_contra!
  have : f.val.domain = (f.extend hx).val.domain := by congr
  rw [this] at hx
  contrapose! hx with h
  simpa using Submodule.mem_sup_right (by simp)

/-! ### Step 4: use Zorn's lemma

We show that `sSup` makes sense on `HahnEmbedding.Partial`, which allows us to use Zorn's lemma
to assert the existence of maximal embedding. Since we already show that we can create greater
embeddings by adding new elements, the maximal embedding must have the maximal domain.
-/

/-- A partial linear map that contains every element in a directed set of
`HahnEmbedding.Partial`. -/
noncomputable
def sSupFun {c : Set (Partial seed)} (hc : DirectedOn (· ≤ ·) c) :
    M →ₗ.[K] Lex (HahnSeries (FiniteArchimedeanClass M) R) :=
  LinearPMap.sSup ((·.val) '' c) (hc.mono_comp (by simp))

theorem sSupFun_strictMono [IsOrderedAddMonoid R] {c : Set (Partial seed)}
    (hnonempty : c.Nonempty) (hc : DirectedOn (· ≤ ·) c) : StrictMono (sSupFun hc) := by
  intro x y h
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
  obtain hyx := (y - x).prop
  simp_rw [sSupFun, LinearPMap.domain_sSup] at hyx
  obtain ⟨f, hmem, hf⟩ :=
    (LinearPMap.mem_domain_sSup_iff (hnonempty.image _) (hc.mono_comp (by simp))).mp hyx
  have : (sSupFun hc) (y - x) = f ⟨(y - x).val, hf⟩ :=
    LinearPMap.sSup_apply _ hmem ⟨(y - x).val, hf⟩
  rw [this]
  obtain ⟨f', _, hf'⟩ := (Set.mem_image _ _ _).mp hmem
  have hmono : StrictMono f := hf'.symm ▸ f'.prop.strictMono
  rw [show 0 = f 0 by simp]
  apply hmono
  rw [← Subtype.coe_lt_coe]
  simp [h]

theorem le_sSupFun {c : Set (Partial seed)} (hc : DirectedOn (· ≤ ·) c)
    {f : Partial seed} (hf : f ∈ c) :
    f.val ≤ sSupFun hc :=
  LinearPMap.le_sSup _ <| (Set.mem_image _ _ _).mpr ⟨f, hf, rfl⟩

theorem baseEmbedding_le_sSupFun {c : Set (Partial seed)}
    (hnonempty : c.Nonempty) (hc : DirectedOn (· ≤ ·) c) : seed.baseEmbedding ≤ sSupFun hc := by
  obtain ⟨f, hf⟩ := hnonempty
  exact le_trans f.prop.baseEmbedding_le (le_sSupFun hc hf)

theorem truncLT_mem_range_sSupFun {c : Set (Partial seed)}
    (hnonempty : c.Nonempty) (hc : DirectedOn (· ≤ ·) c) (x : (sSupFun hc).domain)
    (c : FiniteArchimedeanClass M) :
    toLex ((HahnSeries.truncLTLinearMap K c) (ofLex (sSupFun hc x))) ∈
    LinearMap.range (sSupFun hc).toFun := by
  obtain hx := x.prop
  simp_rw [sSupFun, LinearPMap.domain_sSup] at hx
  obtain ⟨f, hmem, hf⟩ :=
    (LinearPMap.mem_domain_sSup_iff (hnonempty.image _) (hc.mono_comp (by simp))).mp hx
  obtain ⟨f', hmem', hf'⟩ := (Set.mem_image _ _ _).mp hmem
  obtain h := (hf'.symm ▸ f'.prop.truncLT_mem_range) ⟨x, hf⟩ c
  simp_rw [LinearMap.mem_range, LinearPMap.toFun_eq_coe] at ⊢ h
  obtain ⟨x', hx'⟩ := h
  have hmem' : x'.val ∈ (sSupFun hc).domain := by
    apply Set.mem_of_mem_of_subset x'.prop
    exact hf'.symm ▸ (le_sSupFun hc hmem').1
  refine ⟨⟨x'.val, hmem'⟩, ?_⟩
  have hleft : sSupFun hc ⟨x'.val, hmem'⟩ = f x' := LinearPMap.sSup_apply _ hmem _
  have hright : sSupFun hc x = f ⟨x, hf⟩ := LinearPMap.sSup_apply _ hmem ⟨x, hf⟩
  simpa [hleft, hright] using hx'

theorem isPartial_sSupFun [IsOrderedAddMonoid R]
    {c : Set (Partial seed)} (hnonempty : c.Nonempty) (hc : DirectedOn (· ≤ ·) c) :
    IsPartial seed (sSupFun hc) where
  strictMono := sSupFun_strictMono hnonempty hc
  baseEmbedding_le := baseEmbedding_le_sSupFun hnonempty hc
  truncLT_mem_range := truncLT_mem_range_sSupFun hnonempty hc

/-- Promote `HahnEmbedding.Partial.sSupFun` to a `HahnEmbedding.Partial`. -/
noncomputable
def sSup [IsOrderedAddMonoid R] {c : Set (Partial seed)}
    (hnonempty : c.Nonempty) (hc : DirectedOn (· ≤ ·) c) : Partial seed :=
  ⟨_, isPartial_sSupFun hnonempty hc⟩

variable (seed) in
theorem exists_isMax [IsOrderedAddMonoid R] :
    ∃ f : Partial seed, IsMax f := by
  apply zorn_le_nonempty
  intro c hc hnonempty
  exact ⟨sSup hnonempty hc.directedOn, mem_upperBounds.mpr fun _ hf ↦ le_sSupFun hc.directedOn hf⟩

variable (seed) in
/-- There exists a `HahnEmbedding.Partial` whose domain is the whole module. -/
theorem exists_domain_eq_top [IsOrderedAddMonoid R] [Archimedean R] :
    ∃ f : Partial seed, f.val.domain = ⊤ := by
  obtain ⟨f, hf⟩ := exists_isMax seed
  refine ⟨f, Submodule.eq_top_iff'.mpr ?_⟩
  rw [isMax_iff_forall_not_lt] at hf
  contrapose! hf with hx
  obtain ⟨x, hx⟩ := hx
  exact ⟨f.extend hx, f.lt_extend hx⟩

end Partial

end HahnEmbedding

/-- **Hahn embedding theorem for an ordered module**

There exists a strictly monotone `M →ₗ[K] Lex (HahnSeries (FiniteArchimedeanClass M) R)` that maps
`ArchimedeanClass M` to `HahnSeries.orderTop` in the expected way, as long as
`HahnEmbedding.Seed K M R` is nonempty. The `HahnEmbedding.Partial` with maximal domain is the
desired embedding. -/
theorem hahnEmbedding_isOrderedModule [IsOrderedAddMonoid R] [Archimedean R]
    [h : Nonempty (HahnEmbedding.Seed K M R)] :
    ∃ f : M →ₗ[K] Lex (HahnSeries (FiniteArchimedeanClass M) R), StrictMono f ∧
      ∀ (a : M), mk a = FiniteArchimedeanClass.withTopOrderIso M (ofLex (f a)).orderTop := by
  obtain ⟨e, hdomain⟩ := HahnEmbedding.Partial.exists_domain_eq_top h.some
  obtain harch := e.orderTop_eq_archimedeanClassMk
  obtain ⟨⟨fdomain, f⟩, hpartial⟩ := e
  obtain rfl := hdomain
  refine ⟨f ∘ₗ LinearMap.id.codRestrict ⊤ (by simp), ?_, ?_⟩
  · apply hpartial.strictMono.comp
    intro _ _ h
    simpa [← Subtype.coe_lt_coe] using h
  · simp_rw [LinearPMap.mk_apply] at harch
    simp [harch]
