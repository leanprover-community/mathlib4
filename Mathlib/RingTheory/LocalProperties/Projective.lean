/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, David Swinarski
-/
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.LocalProperties.Submodule

/-!

# Being projective is a local property

## Main results
- `LinearMap.split_surjective_of_localization_maximal`
  If `N` is finitely presented, then `f : M →ₗ[R] N`
  being split injective can be checked on stalks (of maximal ideals).
- `Module.projective_of_localization_maximal` If `M` is finitely presented,
  then `M` being projective can be checked on stalks (of maximal ideals).

## TODO
- Show that being projective is Zariski-local (very hard)

-/

universe uM

variable {R N N' : Type*} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
variable [Module R N] [AddCommGroup N'] [Module R N'] (S : Submonoid R)

theorem Module.free_of_isLocalizedModule {Rₛ Mₛ} [AddCommGroup Mₛ] [Module R Mₛ]
    [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    (S) (f : M →ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Free R M] :
    Module.Free Rₛ Mₛ :=
  Free.of_equiv (IsLocalizedModule.isBaseChange S Rₛ f).equiv

universe uR' uM' in
/--
Also see `IsLocalizedModule.lift_rank_eq` for a version for non-free modules,
but requires `S` to not contain any zero-divisors.
-/
theorem Module.lift_rank_of_isLocalizedModule_of_free
    (Rₛ : Type uR') {Mₛ : Type uM'} [AddCommGroup Mₛ] [Module R Mₛ]
    [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ] (S : Submonoid R)
    (f : M →ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Free R M]
    [Nontrivial Rₛ] :
    Cardinal.lift.{uM} (Module.rank Rₛ Mₛ) = Cardinal.lift.{uM'} (Module.rank R M) := by
  apply Cardinal.lift_injective.{max uM' uR'}
  have := (algebraMap R Rₛ).domain_nontrivial
  have := (IsLocalizedModule.isBaseChange S Rₛ f).equiv.lift_rank_eq.symm
  simp only [rank_tensorProduct, rank_self,
    Cardinal.lift_one, one_mul, Cardinal.lift_lift] at this ⊢
  convert this
  exact Cardinal.lift_umax

theorem Module.finrank_of_isLocalizedModule_of_free
    (Rₛ : Type*) {Mₛ : Type*} [AddCommGroup Mₛ] [Module R Mₛ]
    [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ] (S : Submonoid R)
    (f : M →ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Free R M]
    [Nontrivial Rₛ] :
    Module.finrank Rₛ Mₛ = Module.finrank R M := by
  simpa using congr(Cardinal.toNat $(Module.lift_rank_of_isLocalizedModule_of_free Rₛ S f))

theorem Module.projective_of_isLocalizedModule {Rₛ Mₛ} [AddCommGroup Mₛ] [Module R Mₛ]
    [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    (S) (f : M →ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Projective R M] :
    Module.Projective Rₛ Mₛ :=
  Projective.of_equiv (IsLocalizedModule.isBaseChange S Rₛ f).equiv

theorem LinearMap.split_surjective_of_localization_maximal
    (f : M →ₗ[R] N) [Module.FinitePresentation R N]
    (H : ∀ (I : Ideal R) (_ : I.IsMaximal),
    ∃ (g : _ →ₗ[Localization.AtPrime I] _),
      (LocalizedModule.map I.primeCompl f).comp g = LinearMap.id) :
    ∃ (g : N →ₗ[R] M), f.comp g = LinearMap.id := by
  change LinearMap.id ∈ LinearMap.range (LinearMap.llcomp R N M N f)
  refine Submodule.mem_of_localization_maximal _ (fun P _ ↦ LocalizedModule.map P.primeCompl) _ _
    fun I hI ↦ ?_
  rw [LocalizedModule.map_id]
  have : LinearMap.id ∈ LinearMap.range (LinearMap.llcomp _
    (LocalizedModule I.primeCompl N) _ _ (LocalizedModule.map I.primeCompl f)) := H I hI
  convert this
  · ext f
    constructor
    · intro hf
      obtain ⟨a, ha, c, rfl⟩ := hf
      obtain ⟨g, rfl⟩ := ha
      use IsLocalizedModule.mk' (LocalizedModule.map I.primeCompl) g c
      apply ((Module.End.isUnit_iff _).mp <| IsLocalizedModule.map_units
        (LocalizedModule.map I.primeCompl) c).injective
      dsimp
      conv_rhs => rw [← Submonoid.smul_def]
      conv_lhs => rw [← LinearMap.map_smul_of_tower]
      rw [← Submonoid.smul_def, IsLocalizedModule.mk'_cancel', IsLocalizedModule.mk'_cancel']
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.ext I.primeCompl (LocalizedModule.mkLinearMap I.primeCompl N)
      · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap I.primeCompl N)
      ext
      simp only [LocalizedModule.map_mk, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
        Function.comp_apply, LocalizedModule.mkLinearMap_apply, LinearMap.llcomp_apply,
        LocalizedModule.map_mk]
    · rintro ⟨g, rfl⟩
      obtain ⟨⟨g, s⟩, rfl⟩ :=
        IsLocalizedModule.mk'_surjective I.primeCompl (LocalizedModule.map I.primeCompl) g
      simp only [Function.uncurry_apply_pair]
      refine ⟨f.comp g, ⟨g, rfl⟩, s, ?_⟩
      apply ((Module.End.isUnit_iff _).mp <| IsLocalizedModule.map_units
         (LocalizedModule.map I.primeCompl) s).injective
      simp only [Module.algebraMap_end_apply, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel',
        ← LinearMap.map_smul_of_tower]
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.ext I.primeCompl (LocalizedModule.mkLinearMap I.primeCompl N)
      · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap I.primeCompl N)
      ext
      simp only [coe_comp, coe_restrictScalars, Function.comp_apply,
        LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk, llcomp_apply]

theorem Module.projective_of_localization_maximal (H : ∀ (I : Ideal R) (_ : I.IsMaximal),
    Module.Projective (Localization.AtPrime I) (LocalizedModule I.primeCompl M))
    [Module.FinitePresentation R M] : Module.Projective R M := by
  have : Module.Finite R M := by infer_instance
  have : (⊤ : Submodule R M).FG := this.fg_top
  have : ∃ (s : Finset M), _ := this
  obtain ⟨s, hs⟩ := this
  let N := s →₀ R
  let f : N →ₗ[R] M := Finsupp.linearCombination R (Subtype.val : s → M)
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, Subtype.range_val]
    convert hs
  have (I : Ideal R) (hI : I.IsMaximal) :=
    letI := H I hI
    Module.projective_lifting_property (LocalizedModule.map I.primeCompl f) LinearMap.id
    (LocalizedModule.map_surjective _ _ hf)
  obtain ⟨g, hg⟩ := LinearMap.split_surjective_of_localization_maximal _ this
  exact Module.Projective.of_split _ _ hg

variable
  (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], CommRing (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
  (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommGroup (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Mₚ P)]
  (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
  [inst : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f P)]

attribute [local instance] RingHomInvPair.of_ringEquiv in
include f in
/--
A variant of `Module.projective_of_localization_maximal` that accepts `IsLocalizedModule`.
-/
theorem Module.projective_of_localization_maximal'
    (H : ∀ (I : Ideal R) (_ : I.IsMaximal), Module.Projective (Rₚ I) (Mₚ I))
    [Module.FinitePresentation R M] : Module.Projective R M := by
  apply Module.projective_of_localization_maximal
  intros P hP
  refine Module.Projective.of_ringEquiv (M := Mₚ P)
    (IsLocalization.algEquiv P.primeCompl (Rₚ P) (Localization.AtPrime P)).toRingEquiv
    { __ := IsLocalizedModule.linearEquiv P.primeCompl (f P)
        (LocalizedModule.mkLinearMap P.primeCompl M)
      map_smul' := ?_ }
  · intros r m
    obtain ⟨r, s, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl r
    apply ((Module.End.isUnit_iff _).mp
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap P.primeCompl M) s)).1
    dsimp
    simp only [← map_smul, ← smul_assoc, IsLocalization.smul_mk'_self, algebraMap_smul,
      IsLocalization.map_id_mk']
