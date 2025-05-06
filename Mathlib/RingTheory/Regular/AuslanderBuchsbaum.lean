/-
Copyright (c) 2025 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yongle Hu, Yijun Yuan
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Regular.Depth

/-!
# Auslander-Buchsbaum theorem

In this file, we prove the Auslander-Buchsbaum theorem, which states that for a finitely generated
module `M` over a Noetherian local ring `R`, if $\operatorname{proj\,dim} M < \infty$, then
$\operatorname{proj}\dim M + \operatorname{depth} M = \operatorname{depth} R$.

-/

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

section hom

open Module Free Pointwise

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  (I : Ideal R)

theorem smul_prod_of_smul {ι : Type*} [Finite ι] (x : ι → M)
    (h : ∀ i, x i ∈ I • (⊤ : Submodule R M)) : x ∈ I • (⊤ : Submodule R (ι → M)) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  rw [← Finset.univ_sum_single x]
  exact Submodule.sum_mem _ <| fun i hi ↦
    Submodule.smul_top_le_comap_smul_top I (LinearMap.single R (fun i ↦ M) i) (h i)

variable [Module.Finite R M] [Free R M] (f : M →ₗ[R] N)

theorem mem_smul_top_of_range_le_smul_top (hf : LinearMap.range f ≤ I • ⊤) :
    f ∈ I • (⊤ : Submodule R (M →ₗ[R] N)) := by
  let e : Basis _ R M := chooseBasis R M
  have hx : f = (e.constr R).toLinearMap (fun i ↦ f (e i)) := by
    apply e.ext
    simp
  rw [hx]
  exact Submodule.smul_top_le_comap_smul_top I (e.constr R).toLinearMap <|
    smul_prod_of_smul I (fun i ↦ f (e i)) (fun i ↦ hf (LinearMap.mem_range_self f (e i)))

end hom

universe v u

#check Module.free_of_flat_of_isLocalRing

#check Module.Finite.finite_basis

open IsLocalRing
open RingTheory.Sequence Ideal CategoryTheory Abelian Limits

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

instance (ι : Type*) : Module.Free R (ι →₀ Shrink.{v, u} R) :=
  Module.Free.of_equiv (Finsupp.mapRange.linearEquiv (α := ι) (Shrink.linearEquiv R R).symm)

lemma basis_lift [IsLocalRing R] (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (ι : Type*) (b : Basis ι (R ⧸ maximalIdeal R) (M ⧸ maximalIdeal R • (⊤ : Submodule R M))) :
    Function.Surjective (Classical.choose (Module.projective_lifting_property
    (Submodule.mkQ (maximalIdeal R • (⊤ : Submodule R M)))
    ((LinearEquiv.restrictScalars R b.repr).symm.toLinearMap.comp
    (Finsupp.mapRange.linearMap ((Submodule.mkQ (maximalIdeal R)).comp
    (Shrink.linearEquiv R R).toLinearMap))) (Submodule.mkQ_surjective _))).toFun := by
  let f := Classical.choose (Module.projective_lifting_property
    (Submodule.mkQ (maximalIdeal R • (⊤ : Submodule R M)))
    ((LinearEquiv.restrictScalars R b.repr).symm.toLinearMap.comp
    (Finsupp.mapRange.linearMap ((Submodule.mkQ (maximalIdeal R)).comp
    (Shrink.linearEquiv R R).toLinearMap))) (Submodule.mkQ_surjective _))
  show Function.Surjective f
  have hf : (maximalIdeal R • (⊤ : Submodule R M)).mkQ.comp f = _ :=
    Classical.choose_spec (Module.projective_lifting_property
    (Submodule.mkQ (maximalIdeal R • (⊤ : Submodule R M)))
    ((LinearEquiv.restrictScalars R b.repr).symm.toLinearMap.comp
    (Finsupp.mapRange.linearMap ((Submodule.mkQ (maximalIdeal R)).comp
    (Shrink.linearEquiv R R).toLinearMap))) (Submodule.mkQ_surjective _))
  have : Function.Surjective ((LinearEquiv.restrictScalars R b.repr).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap ((Submodule.mkQ (maximalIdeal R)).comp
    (Shrink.linearEquiv R R).toLinearMap)) := by
    apply Function.Surjective.comp (LinearEquiv.restrictScalars R b.repr).symm.surjective
    apply Finsupp.mapRange_surjective _ (by simp)
    apply Function.Surjective.comp (Submodule.mkQ_surjective _) (Shrink.linearEquiv R R).surjective
  rw [← hf, ← LinearMap.range_eq_top, LinearMap.range_comp] at this
  exact LinearMap.range_eq_top.mp (IsLocalRing.map_mkQ_eq_top.mp this)

noncomputable local instance [IsLocalRing R] : Field (R ⧸ maximalIdeal R) :=
  Quotient.field (maximalIdeal R)

instance (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : Module.Finite (R ⧸I) (M ⧸ I • (⊤ : Submodule R M)) :=
  let f : M →ₛₗ[Ideal.Quotient.mk I] (M ⧸ I • (⊤ : Submodule R M)) := {
    __ := Submodule.mkQ (I • ⊤)
    map_smul' _ _ := rfl }
  Module.Finite.of_surjective f (Submodule.mkQ_surjective _)

lemma ext_hom_zero_of_mem_ideal_smul (L M N : ModuleCat.{v} R) (n : ℕ) (f : M ⟶ N)
    (mem : f ∈ (Module.annihilator R L) • (⊤ : Submodule R (M ⟶ N))) :
    (AddCommGrp.ofHom <| ((Ext.mk₀ f)).postcomp L (add_zero n)) = 0 := by
  refine Submodule.smul_induction_on mem ?_ ?_
  · intro r hr f hf
    ext x
    show (((Ext.homEquiv₀_linearHom R).symm (r • f)).postcompOfLinear R L _) x = 0
    simp only [Ext.postcompOfLinear, LinearMap.flip_apply]
    rw [map_smul, map_smul, ← LinearMap.smul_apply, ← map_smul]
    have : r • x = 0 := by
      rw [← Ext.mk₀_id_comp x]
      show r • (Ext.bilinearCompOfLinear R L L M 0 n n (zero_add n)).flip
        x ((Ext.homEquiv₀_linearHom R).symm (𝟙 L)) = 0
      have : r • (𝟙 L) = 0 := by
        ext
        exact Module.mem_annihilator.mp hr _
      rw [← map_smul, ← map_smul, this]
      simp
    simp [this]
  · intro g1 g2 hg1 hg2
    ext x
    show (((Ext.homEquiv₀_linearHom R).symm (g1 + g2)).postcompOfLinear R L _) x = 0
    simp only [Ext.postcompOfLinear, LinearMap.flip_apply]
    rw [map_add, map_add]
    show AddCommGrp.ofHom ((Ext.mk₀ g1).postcomp L (add_zero n)) x +
      AddCommGrp.ofHom ((Ext.mk₀ g2).postcomp L (add_zero n)) x = 0
    simp [hg1, hg2]

lemma ENat.lt_of_add_one_lt {a b : ℕ∞} (lt : a + 1 < b + 1) : a < b := by
  have lttop : a < ⊤ := lt_of_add_lt_add_right (lt_top_of_lt lt)
  by_cases eqtop : b = ⊤
  · simpa [eqtop] using lttop
  · rw [ENat.lt_add_one_iff eqtop, ENat.add_one_le_iff (LT.lt.ne_top lttop)] at lt
    exact lt

lemma AuslanderBuchsbaum_one [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) [Nontrivial M] [Module.Finite R M]
    [Small.{v} (R ⧸ (maximalIdeal R))]
    (le1 : HasProjectiveDimensionLE M 1) (nle0 : ¬ HasProjectiveDimensionLE M 0) :
    1 + IsLocalRing.depth M = IsLocalRing.depth.{v} (ModuleCat.of.{v} R (Shrink.{v} R)) := by
  rcases Basis.exists_basis (R ⧸ maximalIdeal R) (M ⧸ maximalIdeal R • (⊤ : Submodule R M))
    with ⟨ι, ⟨B⟩⟩
  let fin := FiniteDimensional.fintypeBasisIndex B
  let f := Classical.choose (Module.projective_lifting_property
    (Submodule.mkQ (maximalIdeal R • (⊤ : Submodule R M)))
    ((LinearEquiv.restrictScalars R B.repr).symm.toLinearMap.comp
    (Finsupp.mapRange.linearMap ((Submodule.mkQ (maximalIdeal R)).comp
    (Shrink.linearEquiv R R).toLinearMap))) (Submodule.mkQ_surjective _))
  have hf : (maximalIdeal R • (⊤ : Submodule R M)).mkQ.comp f = _ :=
    Classical.choose_spec (Module.projective_lifting_property
    (Submodule.mkQ (maximalIdeal R • (⊤ : Submodule R M)))
    ((LinearEquiv.restrictScalars R B.repr).symm.toLinearMap.comp
    (Finsupp.mapRange.linearMap ((Submodule.mkQ (maximalIdeal R)).comp
    (Shrink.linearEquiv R R).toLinearMap))) (Submodule.mkQ_surjective _))
  have surjf : Function.Surjective f := basis_lift M ι B
  have : Module.Finite R (ι →₀ Shrink.{v, u} R) := by
    simp [Module.finite_finsupp_iff, Module.Finite.equiv (Shrink.linearEquiv R R).symm, fin.finite]
  have : Module.Finite R (LinearMap.ker f) := Module.IsNoetherian.finite R (LinearMap.ker f)
  have free : Module.Free R (ι →₀ Shrink.{v, u} R) := inferInstance
  let S : ShortComplex (ModuleCat.{v} R) := {
    f := ModuleCat.ofHom.{v} (LinearMap.ker f).subtype
    g := ModuleCat.ofHom.{v} f
    zero := by
      ext x
      simp }
  have S_exact : S.ShortExact := {
    exact := by
      apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr
      intro x
      simp [S]
    mono_f := (ModuleCat.mono_iff_injective S.f).mpr (LinearMap.ker f).injective_subtype
    epi_g := (ModuleCat.epi_iff_surjective S.g).mpr surjf }
  have ker_free : Module.Free R (LinearMap.ker f) := by
    apply @free_of_projectiveOverLocalRing _ _ _ _ (ModuleCat.of R (LinearMap.ker f)) _ ?_
    apply @projective_of_hasProjectiveDimensionLT_one _ _ _ _ _ ?_
    have proj : Projective (ModuleCat.of.{v} R (ι →₀ Shrink.{v, u} R)) := by
      rcases free with ⟨⟨B⟩⟩
      exact ModuleCat.projective_of_free B.2
    exact (S_exact.hasProjectiveDimensionLT_X₃_iff 0 proj).mp le1
  have ker_le : LinearMap.ker f ≤ (maximalIdeal R) • (⊤ : Submodule R (ι →₀ Shrink.{v, u} R)) := by
    apply le_trans (LinearMap.ker_le_ker_comp f (maximalIdeal R • (⊤ : Submodule R M)).mkQ) _
    rw [hf]
    intro x
    simp only [LinearEquiv.ker_comp, Finsupp.mapRange.linearMap_apply,
      LinearMap.coe_comp, LinearEquiv.coe_coe, f]
    have : x ∈ LinearMap.ker (Finsupp.mapRange.linearMap (Submodule.mkQ (maximalIdeal R) ∘ₗ
      (Shrink.linearEquiv R R))) ↔ ∀ i : ι, x i ∈ (maximalIdeal R).comap (Shrink.ringEquiv R) := by
      simp only [LinearMap.mem_ker, Finsupp.mapRange.linearMap_apply, LinearMap.coe_comp,
        LinearEquiv.coe_coe, mem_comap, Finsupp.ext_iff, Finsupp.zero_apply]
      congr!
      simp [Quotient.eq_zero_iff_mem, Shrink.ringEquiv]
    simp only [this, mem_comap]
    intro h
    rw [← (Finsupp.univ_sum_single x)]
    apply Submodule.sum_mem
    intro i hi
    have : Finsupp.single i (x i) = ((Shrink.ringEquiv R) (x i)) • Finsupp.single i 1 := by
      rw [Finsupp.smul_single]
      congr
      apply (Shrink.algEquiv R R).injective
      rw [map_smul, map_one, smul_eq_mul, mul_one]
      rfl
    rw [this]
    apply Submodule.smul_mem_smul (h i) (Set.mem_univ _)
  let K := ModuleCat.of R (Shrink.{v} (R ⧸ (maximalIdeal R)))
  have Sf_mem : S.f ∈ (Module.annihilator R K) • (⊤ : Submodule R (S.X₁ ⟶ S.X₂)) := by
    simp only [K, S, LinearEquiv.annihilator_eq (Shrink.linearEquiv (R ⧸ maximalIdeal R) R),
      Ideal.annihilator_quotient]
    rw [← (ModuleCat.homLinearEquiv (S := R)).symm_apply_apply
      (ModuleCat.ofHom (LinearMap.ker f).subtype), ← Submodule.mem_comap]
    apply Submodule.smul_top_le_comap_smul_top
    apply mem_smul_top_of_range_le_smul_top
    intro x hx
    have hx : x ∈ LinearMap.range (LinearMap.ker f).subtype := hx
    rw [Submodule.range_subtype] at hx
    exact ker_le hx
  have hom_zero (i : ℕ) := ext_hom_zero_of_mem_ideal_smul K S.X₁ S.X₂ i S.f Sf_mem
  have iff (i : ℕ) : Subsingleton (Ext K M i) ↔
    (Subsingleton (Ext K (ModuleCat.of R (Shrink.{v} R)) i) ∧
      Subsingleton (Ext K (ModuleCat.of R (Shrink.{v} R)) (i + 1))) := by
    refine ⟨fun h ↦ ?_, fun ⟨h1, h3⟩ ↦ ?_⟩
    · have zero : IsZero (AddCommGrp.of (Ext K M i)) := @AddCommGrp.isZero_of_subsingleton _ h
      constructor
      · have := AddCommGrp.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
          (Ext.covariant_sequence_exact₂' K S_exact i) (hom_zero i) (zero.eq_zero_of_tgt _)
        exact (finte_free_ext_vanish_iff S.X₂ K i).mp this
      · have := AddCommGrp.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
          (Ext.covariant_sequence_exact₁' K S_exact i (i + 1) rfl)
          (zero.eq_zero_of_src _) (hom_zero (i + 1))
        exact (finte_free_ext_vanish_iff S.X₁ K (i + 1)).mp this
    · have zero1 : IsZero (AddCommGrp.of (Ext K S.X₂ i)) :=
        @AddCommGrp.isZero_of_subsingleton _ ((finte_free_ext_vanish_iff _ _ i).mpr h1)
      have zero3 : IsZero  (AddCommGrp.of (Ext K S.X₁ (i + 1))) :=
        @AddCommGrp.isZero_of_subsingleton _ ((finte_free_ext_vanish_iff _ _ (i + 1)).mpr h3)
      exact AddCommGrp.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
        (Ext.covariant_sequence_exact₃' K S_exact i (i + 1) rfl)
        (zero1.eq_zero_of_src _) (zero3.eq_zero_of_tgt _)
  simp only [IsLocalRing.depth, Ideal.depth, moduleDepth]
  apply le_antisymm
  · rw [ENat.add_sSup ⟨0, by simp⟩]
    apply iSup_le (fun n ↦ iSup_le (fun hn ↦ ?_))
    apply le_sSup
    intro i hi
    by_cases eq0 : i = 0
    · rw [eq0, ← finte_free_ext_vanish_iff S.X₁]
      --consider Ext0 K A^q → Ext0 K A^p injective
      sorry
    · have eq : i - 1 + 1 = i := Nat.sub_one_add_one eq0
      have : i - 1 < n := by
        rw [add_comm, ← eq, ENat.coe_add, ENat.coe_sub, ENat.coe_one] at hi
        exact ENat.lt_of_add_one_lt hi
      have := ((iff (i - 1)).mp (hn (i - 1) this)).2
      simpa only [eq] using this
  · apply sSup_le (fun n hn ↦ ?_)
    by_cases eq0 : n = 0
    · simp [eq0]
    · have : n - 1 + 1 = n := by
        by_cases eqtop : n = ⊤
        · simp [eqtop]
        · rcases ENat.ne_top_iff_exists.mp eqtop with ⟨m, hm⟩
          simp only [← hm, ← ENat.coe_zero, ENat.coe_inj] at eq0
          rw [← hm, ← ENat.coe_one, ← ENat.coe_sub, ← ENat.coe_add, ENat.coe_inj,
            Nat.sub_one_add_one eq0]
      rw [add_comm, ← this]
      apply add_le_add_right
      apply le_sSup
      intro i hi
      have lt1 : i < n := sorry
      have lt2 : i + 1 < n := sorry
      exact (iff i).mpr ⟨hn i lt1, hn (i + 1) lt2⟩

open scoped Classical in
theorem AuslanderBuchsbaum [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) [Nontrivial M] [Module.Finite R M]
    [Small.{v} (R ⧸ (IsLocalRing.maximalIdeal R))]
    (hfinprojdim : ∃ i : ℕ, CategoryTheory.HasProjectiveDimensionLE M i) :
    Nat.find hfinprojdim + IsLocalRing.depth M =
    IsLocalRing.depth.{v} (ModuleCat.of R (Shrink.{v} R)) := by
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
