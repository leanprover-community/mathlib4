import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.Regular.Depth
import Mathlib.RingTheory.LocalRing.Module

namespace CategoryTheory

universe w v u

open Abelian Limits ZeroObject Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {X I P Y : C}

section Injective

instance Abelian.Ext.subsingleton_of_injective [Injective I] (n : ℕ) [hn : NeZero n] :
    Subsingleton (Ext X I n) := by
  rw [← Nat.succ_pred_eq_of_ne_zero hn.1]
  exact subsingleton_of_forall_eq 0 eq_zero_of_injective

variable {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂]
  (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) [NeZero n₀]

noncomputable def injective_dim_shifting : Ext X S.X₃ n₀ ≃+ Ext X S.X₁ n₁ :=
  have : NeZero n₁ := by
    rw [← h]
    infer_instance
  have : IsIso (AddCommGrp.ofHom (hS.extClass.postcomp X h)) :=
    ComposableArrows.Exact.isIso_map' (covariantSequence_exact X hS n₀ n₁ h) 1 (by decide)
      (IsZero.eq_zero_of_src (AddCommGrp.of (Ext X S.X₂ n₀)).isZero_of_subsingleton _)
      (IsZero.eq_zero_of_tgt (AddCommGrp.of (Ext X S.X₂ n₁)).isZero_of_subsingleton _)
  (CategoryTheory.asIso (AddCommGrp.ofHom (hS.extClass.postcomp X h))).addCommGroupIsoToAddEquiv

lemma injective_dim_shifting_apply (e : Ext X S.X₃ n₀) :
  injective_dim_shifting hS n₀ n₁ h e = hS.extClass.postcomp X h e := rfl

end Injective

section Projective

omit [HasExt C] in
theorem shortExact_kernel_of_epi {X Y : C} (e : X ⟶ Y) [he : Epi e] :
    (ShortComplex.mk (kernel.ι e) e (kernel.condition e)).ShortExact where
  exact := ShortComplex.exact_kernel e
  mono_f := equalizer.ι_mono
  epi_g := he

instance projective_of_hasProjectiveDimensionLT_one [HasProjectiveDimensionLT P 1] :
    Projective P where
  factors {E X} f e he := by
    let S := ShortComplex.mk (kernel.ι e) e (kernel.condition e)
    have hS : S.ShortExact := shortExact_kernel_of_epi e
    rcases covariant_sequence_exact₃ P hS (addEquiv₀.symm f) rfl
      (eq_zero_of_hasProjectiveDimensionLT _ 1 (Eq.le rfl)) with ⟨g, h⟩
    rw [← addEquiv₀.eq_symm_apply.mp h, ← AddEquiv.symm_apply_apply addEquiv₀ g]
    exact ⟨addEquiv₀ g, addEquiv₀.symm_apply_eq.mp (mk₀_comp_mk₀ (addEquiv₀ g) S.g).symm⟩

instance Abelian.Ext.subsingleton_of_projective [Projective P] (n : ℕ) [hn : NeZero n] :
    Subsingleton (Ext P Y n) := by
  rw [← Nat.succ_pred_eq_of_ne_zero hn.1]
  exact subsingleton_of_forall_eq 0 eq_zero_of_projective

variable {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂]
  (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) [NeZero n₀]

noncomputable def projective_dim_shifting : Ext S.X₁ Y n₀ ≃+ Ext S.X₃ Y n₁ :=
  have : NeZero n₁ := by
    rw [← h]
    infer_instance
  have : IsIso (AddCommGrp.ofHom (hS.extClass.precomp Y h)) :=
    ComposableArrows.Exact.isIso_map' (contravariantSequence_exact hS Y n₀ n₁ h) 1 (by decide)
      (IsZero.eq_zero_of_src (AddCommGrp.of (Ext S.X₂ Y n₀)).isZero_of_subsingleton _)
      (IsZero.eq_zero_of_tgt (AddCommGrp.of (Ext S.X₂ Y n₁)).isZero_of_subsingleton _)
  (CategoryTheory.asIso (AddCommGrp.ofHom (hS.extClass.precomp Y h))).addCommGroupIsoToAddEquiv

lemma projective_dim_shifting_apply (e : Ext S.X₁ Y n₀) :
  projective_dim_shifting hS n₀ n₁ h e = hS.extClass.precomp Y h e := rfl

end Projective

end CategoryTheory

universe v u

#check Module.free_of_flat_of_isLocalRing

#check Module.Finite.finite_basis

open IsLocalRing
open RingTheory.Sequence Ideal CategoryTheory CategoryTheory.Abelian

variable {R : Type u} [CommRing R] [Small.{v} R]

lemma free_of_projectiveOverLocalRing [IsLocalRing R] (M : ModuleCat.{v} R) [Module.Finite R M]
    [Projective M]: Module.Free R M:= by
  -- Add your proof here
  sorry

local instance : CategoryTheory.HasExt.{max u v} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{max u v} (ModuleCat.{v} R)

lemma finte_free_ext_vanish_iff (M N : ModuleCat.{v} R) [Module.Finite R M] [Module.Free R M]
    (i : ℕ) : Subsingleton (Ext N M i) ↔
    Subsingleton (Ext N (ModuleCat.of R (Shrink.{v} R)) i) := by
  -- Add your proof here
  sorry

lemma basis_lift [IsLocalRing R] (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (ι : Type*) (b : Basis ι (R ⧸ maximalIdeal R) (M ⧸ maximalIdeal R • (⊤ : Submodule R M))) :
    Function.Surjective (Classical.choose (Module.projective_lifting_property
    (Submodule.mkQ (maximalIdeal R • (⊤ : Submodule R M)))
    ((LinearEquiv.restrictScalars R b.repr).symm.toLinearMap.comp (Finsupp.mapRange.linearMap
    (Submodule.mkQ (maximalIdeal R)))) (Submodule.mkQ_surjective _))).toFun := by
  let f := Classical.choose (Module.projective_lifting_property
    (Submodule.mkQ (maximalIdeal R • (⊤ : Submodule R M)))
    ((LinearEquiv.restrictScalars R b.repr).symm.toLinearMap.comp (Finsupp.mapRange.linearMap
    (Submodule.mkQ (maximalIdeal R)))) (Submodule.mkQ_surjective _))
  show Function.Surjective f
  have hf : (maximalIdeal R • (⊤ : Submodule R M)).mkQ.comp f = _ :=
    Classical.choose_spec (Module.projective_lifting_property
    (Submodule.mkQ (maximalIdeal R • (⊤ : Submodule R M)))
    ((LinearEquiv.restrictScalars R b.repr).symm.toLinearMap.comp (Finsupp.mapRange.linearMap
    (Submodule.mkQ (maximalIdeal R)))) (Submodule.mkQ_surjective _))
  have : Function.Surjective ((LinearEquiv.restrictScalars R b.repr).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap (Submodule.mkQ (maximalIdeal R))) := by
    apply Function.Surjective.comp (LinearEquiv.restrictScalars R b.repr).symm.surjective
    exact Finsupp.mapRange_surjective _ rfl (Submodule.mkQ_surjective _)
  rw [← hf, ← LinearMap.range_eq_top, LinearMap.range_comp] at this
  exact LinearMap.range_eq_top.mp (IsLocalRing.map_mkQ_eq_top.mp this)

lemma AuslanderBuchsbaum_one [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) [Nontrivial M] [Module.Finite R M]
    [Small.{v} (R ⧸ (IsLocalRing.maximalIdeal R))]
    (le1 : HasProjectiveDimensionLE M 1) (nle0 : ¬ HasProjectiveDimensionLE M 0) :
    1 + IsLocalRing.depth M = IsLocalRing.depth (ModuleCat.of R R) := by

  sorry

open scoped Classical in
theorem AuslanderBuchsbaum [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) [Nontrivial M] [Module.Finite R M]
    [Small.{v} (R ⧸ (IsLocalRing.maximalIdeal R))]
    (hfinprojdim : ∃ i : ℕ, CategoryTheory.HasProjectiveDimensionLE M i) :
    Nat.find hfinprojdim + IsLocalRing.depth M = IsLocalRing.depth (ModuleCat.of R R) := by
    generalize h: Nat.find hfinprojdim = n
    induction' n with n ih
    · simp
      have pdz: HasProjectiveDimensionLE M (Nat.find hfinprojdim) := Nat.find_spec hfinprojdim
      simp [h, HasProjectiveDimensionLE] at pdz
      have fm: Module.Free R M := by apply free_of_projectiveOverLocalRing
      simp [hasProjectiveDimensionLT_iff] at pdz
      --apply Module.Free.exists_set at fm
      sorry
    · by_cases eq0 : n = 0
      · simp only [eq0, zero_add, Nat.find_eq_iff, Nat.lt_one_iff, forall_eq, Nat.cast_one] at h ⊢
        exact AuslanderBuchsbaum_one M h.1 h.2
      · sorry
