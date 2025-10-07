/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Normalizer

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
include hxI

theorem exists_smul_add_of_span_sup_eq_top (y : L) : ∃ t : R, ∃ z ∈ I, y = t • x + z := by
  have hy : y ∈ (⊤ : Submodule R L) := Submodule.mem_top
  simp only [← hxI, Submodule.mem_sup, Submodule.mem_span_singleton] at hy
  obtain ⟨-, ⟨t, rfl⟩, z, hz, rfl⟩ := hy
  exact ⟨t, z, hz, rfl⟩

theorem lie_top_eq_of_span_sup_eq_top (N : LieSubmodule R L M) :
    (↑⁅(⊤ : LieIdeal R L), N⁆ : Submodule R M) =
      (N : Submodule R M).map (toEnd R L M x) ⊔ (↑⁅I, N⁆ : Submodule R M) := by
  simp only [lieIdeal_oper_eq_linear_span', Submodule.sup_span, mem_top, true_and,
    Submodule.map_coe, toEnd_apply_apply]
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono fun z hz => ?_)
  · rintro z ⟨y, n, hn : n ∈ N, rfl⟩
    obtain ⟨t, z, hz, rfl⟩ := exists_smul_add_of_span_sup_eq_top hxI y
    simp only [SetLike.mem_coe, Submodule.span_union, Submodule.mem_sup]
    exact
      ⟨t • ⁅x, n⁆, Submodule.subset_span ⟨t • n, N.smul_mem' t hn, lie_smul t x n⟩, ⁅z, n⁆,
        Submodule.subset_span ⟨z, hz, n, hn, rfl⟩, by simp⟩
  · rcases hz with (⟨m, hm, rfl⟩ | ⟨y, -, m, hm, rfl⟩)
    exacts [⟨x, m, hm, rfl⟩, ⟨y, m, hm, rfl⟩]

theorem lcs_le_lcs_of_is_nilpotent_span_sup_eq_top {n i j : ℕ}
    (hxn : toEnd R L M x ^ n = 0) (hIM : lowerCentralSeries R L M i ≤ I.lcs M j) :
    lowerCentralSeries R L M (i + n) ≤ I.lcs M (j + 1) := by
  suffices
    ∀ l,
      ((⊤ : LieIdeal R L).lcs M (i + l) : Submodule R M) ≤
        (I.lcs M j : Submodule R M).map (toEnd R L M x ^ l) ⊔
          (I.lcs M (j + 1) : Submodule R M)
    by simpa only [bot_sup_eq, LieIdeal.incl_coe, Submodule.map_zero, hxn] using this n
  intro l
  induction l with
  | zero =>
    simp only [add_zero, LieIdeal.lcs_succ, pow_zero, Module.End.one_eq_id,
      Submodule.map_id]
    exact le_sup_of_le_left hIM
  | succ l ih =>
    simp only [LieIdeal.lcs_succ, i.add_succ l, lie_top_eq_of_span_sup_eq_top hxI, sup_le_iff]
    refine ⟨(Submodule.map_mono ih).trans ?_, le_sup_of_le_right ?_⟩
    · rw [Submodule.map_sup, ← Submodule.map_comp, ← Module.End.mul_eq_comp, ← pow_succ', ←
        I.lcs_succ]
      grw [coe_map_toEnd_le]
    · norm_cast
      gcongr
      exact le_trans (antitone_lowerCentralSeries R L M le_self_add) hIM

theorem isNilpotentOfIsNilpotentSpanSupEqTop (hnp : IsNilpotent <| toEnd R L M x)
    (hIM : IsNilpotent I M) : IsNilpotent L M := by
  obtain ⟨n, hn⟩ := hnp
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R I M
  have hk' : I.lcs M k = ⊥ := by
    simp only [← toSubmodule_inj, I.coe_lcs_eq, hk, bot_toSubmodule]
  suffices ∀ l, lowerCentralSeries R L M (l * n) ≤ I.lcs M l by
    rw [isNilpotent_iff R]
    use k * n
    simpa [hk'] using this k
  intro l
  induction l with
  | zero => simp
  | succ l ih => exact (l.succ_mul n).symm ▸ lcs_le_lcs_of_is_nilpotent_span_sup_eq_top hxI hn ih

end LieSubmodule

section LieAlgebra

open LieModule hiding IsNilpotent

variable (R L)

/-- A Lie algebra `L` is said to be Engelian if a sufficient condition for any `L`-Lie module `M` to
be nilpotent is that the image of the map `L → End(M)` consists of nilpotent elements.

Engel's theorem `LieAlgebra.isEngelian_of_isNoetherian` states that any Noetherian Lie algebra is
Engelian. -/
def LieAlgebra.IsEngelian : Prop :=
  ∀ (M : Type u₄) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M],
    (∀ x : L, IsNilpotent (toEnd R L M x)) → LieModule.IsNilpotent L M

variable {R L}

theorem LieAlgebra.isEngelian_of_subsingleton [Subsingleton L] : LieAlgebra.IsEngelian R L := by
  intro M _i1 _i2 _i3 _i4 _h
  use 1
  simp

theorem Function.Surjective.isEngelian {f : L →ₗ⁅R⁆ L₂} (hf : Function.Surjective f)
    (h : LieAlgebra.IsEngelian.{u₁, u₂, u₄} R L) : LieAlgebra.IsEngelian.{u₁, u₃, u₄} R L₂ := by
  intro M _i1 _i2 _i3 _i4 h'
  letI : LieRingModule L M := LieRingModule.compLieHom M f
  letI : LieModule R L M := compLieHom M f
  have hnp : ∀ x, IsNilpotent (toEnd R L M x) := fun x => h' (f x)
  have surj_id : Function.Surjective (LinearMap.id : M →ₗ[R] M) := Function.surjective_id
  haveI : LieModule.IsNilpotent L M := h M hnp
  apply hf.lieModuleIsNilpotent _ surj_id
  aesop

theorem LieEquiv.isEngelian_iff (e : L ≃ₗ⁅R⁆ L₂) :
    LieAlgebra.IsEngelian.{u₁, u₂, u₄} R L ↔ LieAlgebra.IsEngelian.{u₁, u₃, u₄} R L₂ :=
  ⟨e.surjective.isEngelian, e.symm.surjective.isEngelian⟩

theorem LieAlgebra.exists_engelian_lieSubalgebra_of_lt_normalizer {K : LieSubalgebra R L}
    (hK₁ : LieAlgebra.IsEngelian.{u₁, u₂, u₄} R K) (hK₂ : K < K.normalizer) :
    ∃ (K' : LieSubalgebra R L), LieAlgebra.IsEngelian.{u₁, u₂, u₄} R K' ∧ K < K' := by
  obtain ⟨x, hx₁, hx₂⟩ := SetLike.exists_of_lt hK₂
  let K' : LieSubalgebra R L :=
    { (R ∙ x) ⊔ (K : Submodule R L) with
      lie_mem' := fun {y z} => LieSubalgebra.lie_mem_sup_of_mem_normalizer hx₁ }
  have hxK' : x ∈ K' := Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton _))
  have hKK' : K ≤ K' := (LieSubalgebra.toSubmodule_le_toSubmodule K K').mp le_sup_right
  have hK' : K' ≤ K.normalizer := by
    rw [← LieSubalgebra.toSubmodule_le_toSubmodule]
    exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx₁) hK₂.le
  refine ⟨K', ?_, lt_iff_le_and_ne.mpr ⟨hKK', fun contra => hx₂ (contra.symm ▸ hxK')⟩⟩
  intro M _i1 _i2 _i3 _i4 h
  obtain ⟨I, hI₁ : (I : LieSubalgebra R K') = LieSubalgebra.ofLe hKK'⟩ :=
    LieSubalgebra.exists_nested_lieIdeal_ofLe_normalizer hKK' hK'
  have hI₂ : (R ∙ (⟨x, hxK'⟩ : K')) ⊔ (LieSubmodule.toSubmodule I) = ⊤ := by
    rw [← LieIdeal.toLieSubalgebra_toSubmodule R K' I, hI₁]
    apply Submodule.map_injective_of_injective (K' : Submodule R L).injective_subtype
    simp only [LieSubalgebra.coe_ofLe, Submodule.map_sup, Submodule.map_subtype_range_inclusion,
      Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_subtype_span_singleton]
  have e : K ≃ₗ⁅R⁆ I :=
    (LieSubalgebra.equivOfLe hKK').trans
      (LieEquiv.ofEq _ _ ((LieSubalgebra.coe_set_eq _ _).mpr hI₁.symm))
  have hI₃ : LieAlgebra.IsEngelian R I := e.isEngelian_iff.mp hK₁
  exact LieSubmodule.isNilpotentOfIsNilpotentSpanSupEqTop hI₂ (h _) (hI₃ _ fun x => h x)

attribute [local instance] LieSubalgebra.subsingleton_bot

/-- *Engel's theorem*.

Note that this implies all traditional forms of Engel's theorem via
`LieModule.nontrivial_max_triv_of_isNilpotent`, `LieModule.isNilpotent_iff_forall`,
`LieAlgebra.isNilpotent_iff_forall`. -/
theorem LieAlgebra.isEngelian_of_isNoetherian [IsNoetherian R L] : LieAlgebra.IsEngelian R L := by
  intro M _i1 _i2 _i3 _i4 h
  rw [← isNilpotent_range_toEnd_iff R]
  let L' := (toEnd R L M).range
  replace h : ∀ y : L', IsNilpotent (y : Module.End R M) := by
    rintro ⟨-, ⟨y, rfl⟩⟩
    simp [h]
  change LieModule.IsNilpotent L' M
  let s := {K : LieSubalgebra R L' | LieAlgebra.IsEngelian R K}
  have hs : s.Nonempty := ⟨⊥, LieAlgebra.isEngelian_of_subsingleton⟩
  suffices ⊤ ∈ s by
    rw [← isNilpotent_of_top_iff (R := R)]
    apply this M
    simp [LieSubalgebra.toEnd_eq, h]
  have : ∀ K ∈ s, K ≠ ⊤ → ∃ K' ∈ s, K < K' := by
    rintro K (hK₁ : LieAlgebra.IsEngelian R K) hK₂
    apply LieAlgebra.exists_engelian_lieSubalgebra_of_lt_normalizer hK₁
    apply lt_of_le_of_ne K.le_normalizer
    rw [Ne, eq_comm, K.normalizer_eq_self_iff, ← Ne, ←
      LieSubmodule.nontrivial_iff_ne_bot R K]
    have : Nontrivial (L' ⧸ K.toLieSubmodule) := by
      replace hK₂ : K.toLieSubmodule ≠ ⊤ := by
        rwa [Ne, ← LieSubmodule.toSubmodule_inj, K.coe_toLieSubmodule,
          LieSubmodule.top_toSubmodule, ← LieSubalgebra.top_toSubmodule,
          K.toSubmodule_inj]
      exact Submodule.Quotient.nontrivial_of_lt_top _ hK₂.lt_top
    have : LieModule.IsNilpotent K (L' ⧸ K.toLieSubmodule) := by
      refine hK₁ _ fun x => ?_
      have hx := LieAlgebra.isNilpotent_ad_of_isNilpotent (h x)
      apply Module.End.IsNilpotent.mapQ ?_ hx
      intro X HX
      simp only [LieSubalgebra.coe_toLieSubmodule, LieSubalgebra.mem_toSubmodule] at HX
      simp only [LieSubalgebra.coe_toLieSubmodule, Submodule.mem_comap, ad_apply,
        LieSubalgebra.mem_toSubmodule]
      exact LieSubalgebra.lie_mem K x.prop HX
    exact nontrivial_max_triv_of_isNilpotent R K (L' ⧸ K.toLieSubmodule)
  haveI _i5 : IsNoetherian R L' := by
    refine isNoetherian_of_surjective L (LieHom.rangeRestrict (toEnd R L M)) ?_
    simp only [LinearMap.range_eq_top]
    exact LieHom.surjective_rangeRestrict (toEnd R L M)
  obtain ⟨K, hK₁, hK₂⟩ := (LieSubalgebra.wellFoundedGT_of_noetherian R L').wf.has_min s hs
  obtain rfl : K = ⊤ := by grind
  exact hK₁

/-- Engel's theorem.

See also `LieModule.isNilpotent_iff_forall'` which assumes that `M` is Noetherian instead of `L`. -/
theorem LieModule.isNilpotent_iff_forall [IsNoetherian R L] :
    LieModule.IsNilpotent L M ↔ ∀ x, _root_.IsNilpotent <| toEnd R L M x :=
  ⟨fun _ ↦ isNilpotent_toEnd_of_isNilpotent R L M,
   fun h => LieAlgebra.isEngelian_of_isNoetherian M h⟩

/-- Engel's theorem. -/
theorem LieModule.isNilpotent_iff_forall' [IsNoetherian R M] :
    LieModule.IsNilpotent L M ↔ ∀ x, _root_.IsNilpotent <| toEnd R L M x := by
  rw [← isNilpotent_range_toEnd_iff (R := R), LieModule.isNilpotent_iff_forall (R := R)]; simp

/-- Engel's theorem. -/
theorem LieAlgebra.isNilpotent_iff_forall [IsNoetherian R L] :
    LieRing.IsNilpotent L ↔ ∀ x, IsNilpotent <| LieAlgebra.ad R L x :=
  LieModule.isNilpotent_iff_forall

end LieAlgebra
