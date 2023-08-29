/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Normalizer

#align_import algebra.lie.engel from "leanprover-community/mathlib"@"210657c4ea4a4a7b234392f70a3a2a83346dfa90"

/-!
# Engel's theorem

This file contains a proof of Engel's theorem providing necessary and sufficient conditions for Lie
algebras and Lie modules to be nilpotent.

The key result `LieModule.isNilpotent_iff_forall` says that if `M` is a Lie module of a
Noetherian Lie algebra `L`, then `M` is nilpotent iff the image of `L → End(M)` consists of
nilpotent elements. In the special case that we have the adjoint representation `M = L`, this says
that a Lie algebra is nilpotent iff `ad x : End(L)` is nilpotent for all `x : L`.

Engel's theorem is true for any coefficients (i.e., it is really a theorem about Lie rings) and so
we work with coefficients in any commutative ring `R` throughout.

On the other hand, Engel's theorem is not true for infinite-dimensional Lie algebras and so a
finite-dimensionality assumption is required. We prove the theorem subject to the assumption
that the Lie algebra is Noetherian as an `R`-module, though actually we only need the slightly
weaker property that the relation `>` is well-founded on the complete lattice of Lie subalgebras.

## Remarks about the proof

Engel's theorem is usually proved in the special case that the coefficients are a field, and uses
an inductive argument on the dimension of the Lie algebra. One begins by choosing either a maximal
proper Lie subalgebra (in some proofs) or a maximal nilpotent Lie subalgebra (in other proofs, at
the cost of obtaining a weaker end result).

Since we work with general coefficients, we cannot induct on dimension and an alternate approach
must be taken. The key ingredient is the concept of nilpotency, not just for Lie algebras, but for
Lie modules. Using this concept, we define an _Engelian Lie algebra_ `LieAlgebra.IsEngelian` to
be one for which a Lie module is nilpotent whenever the action consists of nilpotent endomorphisms.
The argument then proceeds by selecting a maximal Engelian Lie subalgebra and showing that it cannot
be proper.

The first part of the traditional statement of Engel's theorem consists of the statement that if `M`
is a non-trivial `R`-module and `L ⊆ End(M)` is a finite-dimensional Lie subalgebra of nilpotent
elements, then there exists a non-zero element `m : M` that is annihilated by every element of `L`.
This follows trivially from the result established here `LieModule.isNilpotent_iff_forall`, that
`M` is a nilpotent Lie module over `L`, since the last non-zero term in the lower central series
will consist of such elements `m` (see: `LieModule.nontrivial_max_triv_of_isNilpotent`). It seems
that this result has not previously been established at this level of generality.

The second part of the traditional statement of Engel's theorem concerns nilpotency of the Lie
algebra and a proof of this for general coefficients appeared in the literature as long ago
[as 1937](zorn1937). This also follows trivially from `LieModule.isNilpotent_iff_forall` simply by
taking `M = L`.

It is pleasing that the two parts of the traditional statements of Engel's theorem are thus unified
into a single statement about nilpotency of Lie modules. This is not usually emphasised.

## Main definitions

  * `LieAlgebra.IsEngelian`
  * `LieAlgebra.isEngelian_of_isNoetherian`
  * `LieModule.isNilpotent_iff_forall`
  * `LieAlgebra.isNilpotent_iff_forall`

-/


universe u₁ u₂ u₃ u₄

variable {R : Type u₁} {L : Type u₂} {L₂ : Type u₃} {M : Type u₄}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieSubmodule

open LieModule

variable {I : LieIdeal R L} {x : L} (hxI : (R ∙ x) ⊔ I = ⊤)

theorem exists_smul_add_of_span_sup_eq_top (y : L) : ∃ t : R, ∃ z ∈ I, y = t • x + z := by
  have hy : y ∈ (⊤ : Submodule R L) := Submodule.mem_top
  -- ⊢ ∃ t z, z ∈ I ∧ y = t • x + z
  simp only [← hxI, Submodule.mem_sup, Submodule.mem_span_singleton] at hy
  -- ⊢ ∃ t z, z ∈ I ∧ y = t • x + z
  obtain ⟨-, ⟨t, rfl⟩, z, hz, rfl⟩ := hy
  -- ⊢ ∃ t_1 z_1, z_1 ∈ I ∧ t • x + z = t_1 • x + z_1
  exact ⟨t, z, hz, rfl⟩
  -- 🎉 no goals
#align lie_submodule.exists_smul_add_of_span_sup_eq_top LieSubmodule.exists_smul_add_of_span_sup_eq_top

theorem lie_top_eq_of_span_sup_eq_top (N : LieSubmodule R L M) :
    (↑⁅(⊤ : LieIdeal R L), N⁆ : Submodule R M) =
      (N : Submodule R M).map (toEndomorphism R L M x) ⊔ (↑⁅I, N⁆ : Submodule R M) := by
  simp only [lieIdeal_oper_eq_linear_span', Submodule.sup_span, mem_top, exists_prop,
    true_and, Submodule.map_coe, toEndomorphism_apply_apply]
  refine' le_antisymm (Submodule.span_le.mpr _) (Submodule.span_mono fun z hz => _)
  -- ⊢ {m | ∃ x n, n ∈ N ∧ ⁅x, n⁆ = m} ⊆ ↑(Submodule.span R ((fun a => ⁅x, a⁆) '' ↑ …
  · rintro z ⟨y, n, hn : n ∈ N, rfl⟩
    -- ⊢ ⁅y, n⁆ ∈ ↑(Submodule.span R ((fun a => ⁅x, a⁆) '' ↑↑N ∪ {m | ∃ x, x ∈ I ∧ ∃  …
    obtain ⟨t, z, hz, rfl⟩ := exists_smul_add_of_span_sup_eq_top hxI y
    -- ⊢ ⁅t • x + z, n⁆ ∈ ↑(Submodule.span R ((fun a => ⁅x, a⁆) '' ↑↑N ∪ {m | ∃ x, x  …
    simp only [SetLike.mem_coe, Submodule.span_union, Submodule.mem_sup]
    -- ⊢ ∃ y, y ∈ Submodule.span R ((fun a => ⁅x, a⁆) '' ↑↑N) ∧ ∃ z_1, z_1 ∈ Submodul …
    exact
      ⟨t • ⁅x, n⁆, Submodule.subset_span ⟨t • n, N.smul_mem' t hn, lie_smul t x n⟩, ⁅z, n⁆,
        Submodule.subset_span ⟨z, hz, n, hn, rfl⟩, by simp⟩
  · rcases hz with (⟨m, hm, rfl⟩ | ⟨y, -, m, hm, rfl⟩)
    -- ⊢ (fun a => ⁅x, a⁆) m ∈ {m | ∃ x n, n ∈ N ∧ ⁅x, n⁆ = m}
    exacts [⟨x, m, hm, rfl⟩, ⟨y, m, hm, rfl⟩]
    -- 🎉 no goals
#align lie_submodule.lie_top_eq_of_span_sup_eq_top LieSubmodule.lie_top_eq_of_span_sup_eq_top

theorem lcs_le_lcs_of_is_nilpotent_span_sup_eq_top {n i j : ℕ}
    (hxn : toEndomorphism R L M x ^ n = 0) (hIM : lowerCentralSeries R L M i ≤ I.lcs M j) :
    lowerCentralSeries R L M (i + n) ≤ I.lcs M (j + 1) := by
  suffices
    ∀ l,
      ((⊤ : LieIdeal R L).lcs M (i + l) : Submodule R M) ≤
        (I.lcs M j : Submodule R M).map (toEndomorphism R L M x ^ l) ⊔
          (I.lcs M (j + 1) : Submodule R M)
    by simpa only [bot_sup_eq, LieIdeal.incl_coe, Submodule.map_zero, hxn] using this n
  intro l
  -- ⊢ ↑(LieIdeal.lcs ⊤ M (i + l)) ≤ Submodule.map (↑(toEndomorphism R L M) x ^ l)  …
  induction' l with l ih
  -- ⊢ ↑(LieIdeal.lcs ⊤ M (i + Nat.zero)) ≤ Submodule.map (↑(toEndomorphism R L M)  …
  · simp only [Nat.zero_eq, add_zero, LieIdeal.lcs_succ, pow_zero, LinearMap.one_eq_id,
      Submodule.map_id]
    exact le_sup_of_le_left hIM
    -- 🎉 no goals
  · simp only [LieIdeal.lcs_succ, i.add_succ l, lie_top_eq_of_span_sup_eq_top hxI, sup_le_iff]
    -- ⊢ Submodule.map (↑(toEndomorphism R L M) x) ↑(LieIdeal.lcs ⊤ M (i + l)) ≤ Subm …
    refine' ⟨(Submodule.map_mono ih).trans _, le_sup_of_le_right _⟩
    -- ⊢ Submodule.map (↑(toEndomorphism R L M) x) (Submodule.map (↑(toEndomorphism R …
    · rw [Submodule.map_sup, ← Submodule.map_comp, ← LinearMap.mul_eq_comp, ← pow_succ, ←
        I.lcs_succ]
      exact sup_le_sup_left coe_map_toEndomorphism_le _
      -- 🎉 no goals
    · refine' le_trans (mono_lie_right _ _ I _) (mono_lie_right _ _ I hIM)
      -- ⊢ LieIdeal.lcs ⊤ M (i + l) ≤ lowerCentralSeries R L M i
      exact antitone_lowerCentralSeries R L M le_self_add
      -- 🎉 no goals
#align lie_submodule.lcs_le_lcs_of_is_nilpotent_span_sup_eq_top LieSubmodule.lcs_le_lcs_of_is_nilpotent_span_sup_eq_top

theorem isNilpotentOfIsNilpotentSpanSupEqTop (hnp : IsNilpotent <| toEndomorphism R L M x)
    (hIM : IsNilpotent R I M) : IsNilpotent R L M := by
  obtain ⟨n, hn⟩ := hnp
  -- ⊢ LieModule.IsNilpotent R L M
  obtain ⟨k, hk⟩ := hIM
  -- ⊢ LieModule.IsNilpotent R L M
  have hk' : I.lcs M k = ⊥ := by
    simp only [← coe_toSubmodule_eq_iff, I.coe_lcs_eq, hk, bot_coeSubmodule]
  suffices ∀ l, lowerCentralSeries R L M (l * n) ≤ I.lcs M l by
    use k * n
    simpa [hk'] using this k
  intro l
  -- ⊢ lowerCentralSeries R L M (l * n) ≤ LieIdeal.lcs I M l
  induction' l with l ih
  -- ⊢ lowerCentralSeries R L M (Nat.zero * n) ≤ LieIdeal.lcs I M Nat.zero
  · simp
    -- 🎉 no goals
  · exact (l.succ_mul n).symm ▸ lcs_le_lcs_of_is_nilpotent_span_sup_eq_top hxI hn ih
    -- 🎉 no goals
#align lie_submodule.is_nilpotent_of_is_nilpotent_span_sup_eq_top LieSubmodule.isNilpotentOfIsNilpotentSpanSupEqTop

end LieSubmodule

section LieAlgebra

-- Porting note: somehow this doesn't hide `LieModule.IsNilpotent`, so `_root_.IsNilpotent` is used
-- a number of times below.
open LieModule hiding IsNilpotent

variable (R L)

/-- A Lie algebra `L` is said to be Engelian if a sufficient condition for any `L`-Lie module `M` to
be nilpotent is that the image of the map `L → End(M)` consists of nilpotent elements.

Engel's theorem `LieAlgebra.isEngelian_of_isNoetherian` states that any Noetherian Lie algebra is
Engelian. -/
def LieAlgebra.IsEngelian : Prop :=
  ∀ (M : Type u₄) [AddCommGroup M],
    ∀ [Module R M] [LieRingModule L M],
      ∀ [LieModule R L M],
        ∀ _ : ∀ x : L, _root_.IsNilpotent (toEndomorphism R L M x), LieModule.IsNilpotent R L M
#align lie_algebra.is_engelian LieAlgebra.IsEngelian

variable {R L}

theorem LieAlgebra.isEngelian_of_subsingleton [Subsingleton L] : LieAlgebra.IsEngelian R L := by
  intro M _i1 _i2 _i3 _i4 _h
  -- ⊢ LieModule.IsNilpotent R L M
  use 1
  -- ⊢ lowerCentralSeries R L M 1 = ⊥
  suffices (⊤ : LieIdeal R L) = ⊥ by simp [this]
  -- ⊢ ⊤ = ⊥
  haveI := (LieSubmodule.subsingleton_iff R L L).mpr inferInstance
  -- ⊢ ⊤ = ⊥
  apply Subsingleton.elim
  -- 🎉 no goals
#align lie_algebra.is_engelian_of_subsingleton LieAlgebra.isEngelian_of_subsingleton

theorem Function.Surjective.isEngelian {f : L →ₗ⁅R⁆ L₂} (hf : Function.Surjective f)
    (h : LieAlgebra.IsEngelian.{u₁, u₂, u₄} R L) : LieAlgebra.IsEngelian.{u₁, u₃, u₄} R L₂ := by
  intro M _i1 _i2 _i3 _i4 h'
  -- ⊢ LieModule.IsNilpotent R L₂ M
  letI : LieRingModule L M := LieRingModule.compLieHom M f
  -- ⊢ LieModule.IsNilpotent R L₂ M
  letI : LieModule R L M := compLieHom M f
  -- ⊢ LieModule.IsNilpotent R L₂ M
  have hnp : ∀ x, IsNilpotent (toEndomorphism R L M x) := fun x => h' (f x)
  -- ⊢ LieModule.IsNilpotent R L₂ M
  have surj_id : Function.Surjective (LinearMap.id : M →ₗ[R] M) := Function.surjective_id
  -- ⊢ LieModule.IsNilpotent R L₂ M
  haveI : LieModule.IsNilpotent R L M := h M hnp
  -- ⊢ LieModule.IsNilpotent R L₂ M
  apply hf.lieModuleIsNilpotent surj_id
  -- ⊢ ∀ (x : L) (m : M), ⁅↑f x, ↑LinearMap.id m⁆ = ↑LinearMap.id ⁅x, m⁆
  -- Porting note: was `simp`
  intros; simp only [LinearMap.id_coe, id_eq]; rfl
  -- ⊢ ⁅↑f x✝, ↑LinearMap.id m✝⁆ = ↑LinearMap.id ⁅x✝, m✝⁆
          -- ⊢ ⁅↑f x✝, m✝⁆ = ⁅x✝, m✝⁆
                                               -- 🎉 no goals
#align function.surjective.is_engelian Function.Surjective.isEngelian

theorem LieEquiv.isEngelian_iff (e : L ≃ₗ⁅R⁆ L₂) :
    LieAlgebra.IsEngelian.{u₁, u₂, u₄} R L ↔ LieAlgebra.IsEngelian.{u₁, u₃, u₄} R L₂ :=
  ⟨e.surjective.isEngelian, e.symm.surjective.isEngelian⟩
#align lie_equiv.is_engelian_iff LieEquiv.isEngelian_iff

-- Porting note: changed statement from `∃ ∃ ..` to `∃ .. ∧ ..`
theorem LieAlgebra.exists_engelian_lieSubalgebra_of_lt_normalizer {K : LieSubalgebra R L}
    (hK₁ : LieAlgebra.IsEngelian.{u₁, u₂, u₄} R K) (hK₂ : K < K.normalizer) :
    ∃ (K' : LieSubalgebra R L), LieAlgebra.IsEngelian.{u₁, u₂, u₄} R K' ∧ K < K' := by
  obtain ⟨x, hx₁, hx₂⟩ := SetLike.exists_of_lt hK₂
  -- ⊢ ∃ K', IsEngelian R { x // x ∈ K' } ∧ K < K'
  let K' : LieSubalgebra R L :=
    { (R ∙ x) ⊔ (K : Submodule R L) with
      lie_mem' := fun {y z} => LieSubalgebra.lie_mem_sup_of_mem_normalizer hx₁ }
  have hxK' : x ∈ K' := Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton _))
  -- ⊢ ∃ K', IsEngelian R { x // x ∈ K' } ∧ K < K'
  have hKK' : K ≤ K' := (LieSubalgebra.coe_submodule_le_coe_submodule K K').mp le_sup_right
  -- ⊢ ∃ K', IsEngelian R { x // x ∈ K' } ∧ K < K'
  have hK' : K' ≤ K.normalizer := by
    rw [← LieSubalgebra.coe_submodule_le_coe_submodule]
    exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx₁) hK₂.le
  refine' ⟨K', _, lt_iff_le_and_ne.mpr ⟨hKK', fun contra => hx₂ (contra.symm ▸ hxK')⟩⟩
  -- ⊢ IsEngelian R { x // x ∈ K' }
  intro M _i1 _i2 _i3 _i4 h
  -- ⊢ LieModule.IsNilpotent R { x // x ∈ K' } M
  obtain ⟨I, hI₁ : (I : LieSubalgebra R K') = LieSubalgebra.ofLe hKK'⟩ :=
    LieSubalgebra.exists_nested_lieIdeal_ofLe_normalizer hKK' hK'
  have hI₂ : (R ∙ (⟨x, hxK'⟩ : K')) ⊔ (LieSubmodule.toSubmodule I) = ⊤ := by
    rw [← LieIdeal.coe_to_lieSubalgebra_to_submodule R K' I, hI₁]
    apply Submodule.map_injective_of_injective (K' : Submodule R L).injective_subtype
    simp
  have e : K ≃ₗ⁅R⁆ I :=
    (LieSubalgebra.equivOfLe hKK').trans
      (LieEquiv.ofEq _ _ ((LieSubalgebra.coe_set_eq _ _).mpr hI₁.symm))
  have hI₃ : LieAlgebra.IsEngelian R I := e.isEngelian_iff.mp hK₁
  -- ⊢ LieModule.IsNilpotent R { x // x ∈ K' } M
  exact LieSubmodule.isNilpotentOfIsNilpotentSpanSupEqTop hI₂ (h _) (hI₃ _ fun x => h x)
  -- 🎉 no goals
#align lie_algebra.exists_engelian_lie_subalgebra_of_lt_normalizer LieAlgebra.exists_engelian_lieSubalgebra_of_lt_normalizer

attribute [local instance] LieSubalgebra.subsingleton_bot

variable [IsNoetherian R L]

/-- *Engel's theorem*.

Note that this implies all traditional forms of Engel's theorem via
`LieModule.nontrivial_max_triv_of_isNilpotent`, `LieModule.isNilpotent_iff_forall`,
`LieAlgebra.isNilpotent_iff_forall`. -/
theorem LieAlgebra.isEngelian_of_isNoetherian : LieAlgebra.IsEngelian R L := by
  intro M _i1 _i2 _i3 _i4 h
  -- ⊢ LieModule.IsNilpotent R L M
  rw [← isNilpotent_range_toEndomorphism_iff]
  -- ⊢ LieModule.IsNilpotent R { x // x ∈ LieHom.range (toEndomorphism R L M) } M
  let L' := (toEndomorphism R L M).range
  -- ⊢ LieModule.IsNilpotent R { x // x ∈ LieHom.range (toEndomorphism R L M) } M
  replace h : ∀ y : L', _root_.IsNilpotent (y : Module.End R M)
  -- ⊢ ∀ (y : { x // x ∈ L' }), _root_.IsNilpotent ↑y
  · rintro ⟨-, ⟨y, rfl⟩⟩
    -- ⊢ _root_.IsNilpotent ↑{ val := ↑↑(toEndomorphism R L M) y, property := (_ : ∃  …
    simp [h]
    -- 🎉 no goals
  change LieModule.IsNilpotent R L' M
  -- ⊢ LieModule.IsNilpotent R { x // x ∈ L' } M
  let s := {K : LieSubalgebra R L' | LieAlgebra.IsEngelian R K}
  -- ⊢ LieModule.IsNilpotent R { x // x ∈ L' } M
  have hs : s.Nonempty := ⟨⊥, LieAlgebra.isEngelian_of_subsingleton⟩
  -- ⊢ LieModule.IsNilpotent R { x // x ∈ L' } M
  suffices ⊤ ∈ s by
    rw [← isNilpotent_of_top_iff]
    apply this M
    simp [LieSubalgebra.toEndomorphism_eq, h]
  have : ∀ K ∈ s, K ≠ ⊤ → ∃ K' ∈ s, K < K' := by
    rintro K (hK₁ : LieAlgebra.IsEngelian R K) hK₂
    apply LieAlgebra.exists_engelian_lieSubalgebra_of_lt_normalizer hK₁
    apply lt_of_le_of_ne K.le_normalizer
    rw [Ne.def, eq_comm, K.normalizer_eq_self_iff, ← Ne.def, ←
      LieSubmodule.nontrivial_iff_ne_bot R K]
    have : Nontrivial (L' ⧸ K.toLieSubmodule) := by
      replace hK₂ : K.toLieSubmodule ≠ ⊤ := by
        rwa [Ne.def, ← LieSubmodule.coe_toSubmodule_eq_iff, K.coe_toLieSubmodule,
          LieSubmodule.top_coeSubmodule, ← LieSubalgebra.top_coe_submodule,
          K.coe_to_submodule_eq_iff]
      exact Submodule.Quotient.nontrivial_of_lt_top _ hK₂.lt_top
    have : LieModule.IsNilpotent R K (L' ⧸ K.toLieSubmodule) := by
      -- Porting note: was refine' hK₁ _ fun x => _
      apply hK₁
      intro x
      have hx := LieAlgebra.isNilpotent_ad_of_isNilpotent (h x)
      apply Module.End.IsNilpotent.mapQ ?_ hx
      -- Porting note: mathlib3 solved this on its own with `submodule.mapq_linear._proof_5`
      intro X HX
      simp only [LieSubalgebra.coe_toLieSubmodule, LieSubalgebra.mem_coe_submodule] at HX
      simp only [LieSubalgebra.coe_toLieSubmodule, Submodule.mem_comap, ad_apply,
        LieSubalgebra.mem_coe_submodule]
      exact LieSubalgebra.lie_mem K x.prop HX
    exact nontrivial_max_triv_of_isNilpotent R K (L' ⧸ K.toLieSubmodule)
  haveI _i5 : IsNoetherian R L' := by
    -- Porting note: was
    -- isNoetherian_of_surjective L _ (LinearMap.range_rangeRestrict (toEndomorphism R L M))
    -- abusing the relation between `LieHom.rangeRestrict` and `LinearMap.rangeRestrict`
    refine isNoetherian_of_surjective L (LieHom.rangeRestrict (toEndomorphism R L M)) ?_
    simp only [LieHom.range_coeSubmodule, LieHom.coe_toLinearMap, LinearMap.range_eq_top]
    exact LieHom.surjective_rangeRestrict (toEndomorphism R L M)
  obtain ⟨K, hK₁, hK₂⟩ := (LieSubalgebra.wellFounded_of_noetherian R L').has_min s hs
  -- ⊢ ⊤ ∈ s
  have hK₃ : K = ⊤ := by
    by_contra contra
    obtain ⟨K', hK'₁, hK'₂⟩ := this K hK₁ contra
    exact hK₂ K' hK'₁ hK'₂
  exact hK₃ ▸ hK₁
  -- 🎉 no goals
#align lie_algebra.is_engelian_of_is_noetherian LieAlgebra.isEngelian_of_isNoetherian

/-- Engel's theorem. -/
theorem LieModule.isNilpotent_iff_forall :
    LieModule.IsNilpotent R L M ↔ ∀ x, _root_.IsNilpotent <| toEndomorphism R L M x :=
  ⟨fun _ ↦ isNilpotent_toEndomorphism_of_isNilpotent R L M,
   fun h => LieAlgebra.isEngelian_of_isNoetherian M h⟩
#align lie_module.is_nilpotent_iff_forall LieModule.isNilpotent_iff_forall

/-- Engel's theorem. -/
theorem LieAlgebra.isNilpotent_iff_forall :
    LieAlgebra.IsNilpotent R L ↔ ∀ x, _root_.IsNilpotent <| LieAlgebra.ad R L x :=
  LieModule.isNilpotent_iff_forall
#align lie_algebra.is_nilpotent_iff_forall LieAlgebra.isNilpotent_iff_forall

end LieAlgebra
