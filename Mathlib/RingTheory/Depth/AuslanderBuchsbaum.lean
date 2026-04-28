/-
Copyright (c) 2025 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yongle Hu
-/
module

public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Tactic.ENatToNat

/-!
# Auslander-Buchsbaum theorem

In this file, we prove the Auslander-Buchsbaum theorem, which states that for a nontrivial
finitely generated module `M` over a Noetherian local ring `R`, if `projectiveDimension M ≠ ⊤`,
then `projectiveDimension M + IsLocalRing.depth M = IsLocalRing.depth R`.

-/

@[expose] public section

section hom

open Module

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  (I : Ideal R)

theorem smul_prod_of_smul {ι : Type*} [Finite ι] (x : ι → M)
    (h : ∀ i, x i ∈ I • (⊤ : Submodule R M)) : x ∈ I • (⊤ : Submodule R (ι → M)) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  rw [← Finset.univ_sum_single x]
  exact Submodule.sum_mem _ <| fun i hi ↦
    Submodule.smul_top_le_comap_smul_top I (LinearMap.single R (fun i ↦ M) i) (h i)

variable [Module.Finite R M] [Module.Free R M] (f : M →ₗ[R] N)

theorem mem_smul_top_of_range_le_smul_top (hf : LinearMap.range f ≤ I • ⊤) :
    f ∈ I • (⊤ : Submodule R (M →ₗ[R] N)) := by
  let e : Basis _ R M := Free.chooseBasis R M
  have hx : f = (e.constr R).toLinearMap (fun i ↦ f (e i)) := by
    apply e.ext
    simp
  rw [hx]
  exact Submodule.smul_top_le_comap_smul_top I (e.constr R).toLinearMap <|
    smul_prod_of_smul I (fun i ↦ f (e i)) (fun i ↦ hf (LinearMap.mem_range_self f (e i)))

end hom

universe v u

open IsLocalRing RingTheory.Sequence Ideal CategoryTheory Abelian Limits

variable {R : Type u} [CommRing R] [Small.{v} R]

lemma ModuleCat.free_of_projective_of_isLocalRing [IsLocalRing R] (M : ModuleCat.{v} R)
    [Module.Finite R M] [Projective M] : Module.Free R M :=
  Module.free_of_flat_of_isLocalRing

omit [Small.{v} R] in
lemma nontrivial_ring_of_nontrivial_module (M : Type*) [AddCommGroup M] [Module R M]
    [ntr : Nontrivial M] : Nontrivial R := by
  by_contra! h
  absurd ntr
  apply not_nontrivial_iff_subsingleton.mpr (subsingleton_of_forall_eq 0 (fun m ↦ ?_))
  rw [← one_smul R m, Subsingleton.elim (1 : R) 0, zero_smul]

open Module

lemma subsingleton_of_pi {α β : Type*} [Nonempty α] (h : Subsingleton (α → β)) :
    Subsingleton β := by
  contrapose h
  have : Nontrivial β := not_subsingleton_iff_nontrivial.mp h
  exact not_subsingleton_iff_nontrivial.mpr Function.nontrivial

lemma finte_free_ext_vanish_iff (M N : ModuleCat.{v} R) [Module.Finite R M] [Module.Free R M]
    [Nontrivial M] (i : ℕ) :
    Subsingleton (Ext N M i) ↔ Subsingleton (Ext N (ModuleCat.of R (Shrink.{v} R)) i) := by
  classical
  have : Nontrivial R := nontrivial_ring_of_nontrivial_module M
  rcases Module.Free.exists_set R M with ⟨S, ⟨B⟩⟩
  have : Fintype S := Set.Finite.fintype (Module.Finite.finite_basis B)
  have : Nonempty S := B.index_nonempty
  have h := Ext.addEquivBiproduct N (biconeIsBilimitOfColimitCoconeOfIsColimit <|
    ModuleCat.coproductCoconeIsColimit (fun s : S ↦ ModuleCat.of R (Shrink.{v} R))) i
  simp only [ModuleCat.coproductCocone, Bicone.ofColimitCocone_pt, Cofan.mk_pt] at h
  change Subsingleton ((extFunctorObj N i).obj M) ↔ _
  let e := (B.repr ≪≫ₗ Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R).symm ≪≫ₗ
    finsuppLEquivDirectSum R (Shrink.{v} R) S).toModuleIso
  rw [((extFunctorObj.{v} N i).mapIso e).addCommGroupIsoToAddEquiv.subsingleton_congr]
  exact h.subsingleton_congr.trans ⟨subsingleton_of_pi, fun _ ↦ Pi.instSubsingleton⟩

lemma free_depth_eq_ring_depth (M N : ModuleCat.{v} R) [Module.Finite R M] [Module.Free R M]
    [Nontrivial M] : moduleDepth N M = moduleDepth N (ModuleCat.of R (Shrink.{v} R)) := by
  simp only [moduleDepth]
  congr! 5
  apply finte_free_ext_vanish_iff

lemma basis_lift [IsLocalRing R] (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (ι : Type*) (b : Basis ι (R ⧸ maximalIdeal R) (M ⧸ maximalIdeal R • (⊤ : Submodule R M)))
    (f : (ι →₀ Shrink.{v, u} R) →ₗ[R] M) (hf : (maximalIdeal R • (⊤ : Submodule R M)).mkQ ∘ₗ f =
    (LinearEquiv.restrictScalars R b.repr).symm ∘ₗ
    Finsupp.mapRange.linearMap (Submodule.mkQ (maximalIdeal R) ∘ₗ (Shrink.linearEquiv R R))) :
    Function.Surjective f := by
  have : Function.Surjective ((LinearEquiv.restrictScalars R b.repr).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap ((Submodule.mkQ (maximalIdeal R)).comp
    (Shrink.linearEquiv R R).toLinearMap)) := by
    apply (LinearEquiv.restrictScalars R b.repr).symm.surjective.comp
    apply Finsupp.mapRange_surjective _ (map_zero _)
    apply (Submodule.mkQ_surjective _).comp (Shrink.linearEquiv R R).surjective
  rw [← hf, ← LinearMap.range_eq_top, LinearMap.range_comp] at this
  exact LinearMap.range_eq_top.mp (IsLocalRing.map_mkQ_eq_top.mp this)

instance (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : Module.Finite (R ⧸I) (M ⧸ I • (⊤ : Submodule R M)) :=
  Module.Finite.of_restrictScalars_finite R _ _

lemma basis_lift_ker_le [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] (ι : Type*)
    (b : Basis ι (R ⧸ maximalIdeal R) (M ⧸ maximalIdeal R • (⊤ : Submodule R M)))
    (f : (ι →₀ Shrink.{v, u} R) →ₗ[R] M) (hf : (maximalIdeal R • (⊤ : Submodule R M)).mkQ ∘ₗ f =
    (LinearEquiv.restrictScalars R b.repr).symm ∘ₗ
    Finsupp.mapRange.linearMap (Submodule.mkQ (maximalIdeal R) ∘ₗ (Shrink.linearEquiv R R))) :
  LinearMap.ker f ≤ maximalIdeal R • (⊤ : Submodule R _) := by
  let _ := Quotient.field (maximalIdeal R)
  let fin := FiniteDimensional.fintypeBasisIndex b
  apply le_trans (LinearMap.ker_le_ker_comp f (maximalIdeal R • (⊤ : Submodule R M)).mkQ) _
  rw [hf]
  intro x
  have : x ∈ LinearMap.ker (Finsupp.mapRange.linearMap (Submodule.mkQ (maximalIdeal R) ∘ₗ
    (Shrink.linearEquiv R R))) ↔ ∀ i : ι, x i ∈ (maximalIdeal R).comap (Shrink.ringEquiv R) := by
    simp only [LinearMap.mem_ker, Finsupp.mapRange.linearMap_apply, LinearMap.coe_comp,
      LinearEquiv.coe_coe, mem_comap, Finsupp.ext_iff, Finsupp.zero_apply]
    congr!
    simpa [Shrink.ringEquiv] using Ideal.Quotient.eq_zero_iff_mem
  simp only [LinearEquiv.ker_comp, this, mem_comap]
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

lemma ext_hom_zero_of_mem_ideal_smul (L M N : ModuleCat.{v} R) (n : ℕ) (f : M ⟶ N)
    (mem : f ∈ (Module.annihilator R L) • (⊤ : Submodule R (M ⟶ N))) :
    (AddCommGrpCat.ofHom <| ((Ext.mk₀ f)).postcomp L (add_zero n)) = 0 := by
  refine Submodule.smul_induction_on mem ?_ ?_
  · intro r hr f hf
    ext x
    have : r • x = 0 := by
      have : r • (𝟙 L) = 0 := ModuleCat.hom_ext
        (LinearMap.ext (fun x ↦ Module.mem_annihilator.mp hr _))
      rw [← Ext.mk₀_id_comp x, ← Ext.smul_comp, ← Ext.mk₀_smul, this, Ext.mk₀_zero, Ext.zero_comp]
    simp [Ext.mk₀_smul, ← Ext.smul_comp, this]
  · intro g1 g2 hg1 hg2
    ext x
    have : AddCommGrpCat.ofHom ((Ext.mk₀ g1).postcomp L (add_zero n)) x +
      AddCommGrpCat.ofHom ((Ext.mk₀ g2).postcomp L (add_zero n)) x = 0 := by simp [hg1, hg2]
    simpa [Ext.mk₀_add] using this

lemma AuslanderBuchsbaum_one [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) [Nontrivial M] [Module.Finite R M]
    (le1 : HasProjectiveDimensionLE M 1) (nle0 : ¬ HasProjectiveDimensionLE M 0) :
    1 + IsLocalRing.depth M = IsLocalRing.depth (ModuleCat.of R (Shrink.{v} R)) := by
  let _ := Quotient.field (maximalIdeal R)
  rcases Basis.exists_basis (R ⧸ maximalIdeal R) (M ⧸ maximalIdeal R • (⊤ : Submodule R M))
    with ⟨ι, ⟨B⟩⟩
  let fin := FiniteDimensional.fintypeBasisIndex B
  obtain ⟨f, hf⟩ := Module.projective_lifting_property
    (Submodule.mkQ (maximalIdeal R • (⊤ : Submodule R M)))
    ((B.repr.restrictScalars R).symm.toLinearMap.comp (Finsupp.mapRange.linearMap
      ((Submodule.mkQ (maximalIdeal R)).comp (Shrink.linearEquiv R R).toLinearMap)))
        (Submodule.mkQ_surjective _)
  have surjf : Function.Surjective f := basis_lift M ι B f hf
  let S : ShortComplex (ModuleCat.{v} R) := f.shortComplexKer
  have S_exact : S.ShortExact := LinearMap.shortExact_shortComplexKer surjf
  have ntr2 : Nontrivial S.X₂ := Function.Surjective.nontrivial surjf
  have ntr1 : Nontrivial S.X₁ := by
    by_contra! h
    let ef : (ι →₀ Shrink.{v} R) ≃ₗ[R] M := LinearEquiv.ofBijective f
      ⟨LinearMap.ker_eq_bot.mp Submodule.eq_bot_of_subsingleton, surjf⟩
    have := Module.Free.of_equiv ef
    absurd nle0
    infer_instance
  have ker_free : Module.Free R (LinearMap.ker f) := by
    apply @(ModuleCat.of R (LinearMap.ker f)).free_of_projective_of_isLocalRing _ _ _ _ _ ?_
    rw [projective_iff_hasProjectiveDimensionLT_one]
    exact (S_exact.hasProjectiveDimensionLT_X₃_iff 0 inferInstance).mp le1
  have ker_le : LinearMap.ker f ≤ (maximalIdeal R) • (⊤ : Submodule R (ι →₀ Shrink.{v} R)) :=
    basis_lift_ker_le M ι B f hf
  let K := ModuleCat.of R (Shrink.{v} (R ⧸ (maximalIdeal R)))
  have Sf_mem : S.f ∈ (Module.annihilator R K) • (⊤ : Submodule R (S.X₁ ⟶ S.X₂)) := by
    simp only [K, S, (Shrink.linearEquiv R (R ⧸ maximalIdeal R)).annihilator_eq,
      Ideal.annihilator_quotient]
    rw [← (ModuleCat.homLinearEquiv (S := R)).symm_apply_apply
      (ModuleCat.ofHom (LinearMap.ker f).subtype)]
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
    · have zero : IsZero (AddCommGrpCat.of (Ext K M i)) :=
        AddCommGrpCat.isZero_iff_subsingleton'.mpr h
      constructor
      · have : Subsingleton (Ext K S.X₂ i) := AddCommGrpCat.subsingleton_of_isZero <|
          (Ext.covariant_sequence_exact₂' K S_exact i).isZero_of_both_zeros
          (hom_zero i) (zero.eq_zero_of_tgt _)
        exact (finte_free_ext_vanish_iff S.X₂ K i).mp this
      · have : Subsingleton (Ext K S.X₁ (i + 1)) := AddCommGrpCat.subsingleton_of_isZero <|
          (Ext.covariant_sequence_exact₁' K S_exact i (i + 1) rfl).isZero_of_both_zeros
          (zero.eq_zero_of_src _) (hom_zero (i + 1))
        exact (finte_free_ext_vanish_iff S.X₁ K (i + 1)).mp this
    · have zero1 : IsZero (AddCommGrpCat.of (Ext K S.X₂ i)) :=
        AddCommGrpCat.isZero_iff_subsingleton'.mpr ((finte_free_ext_vanish_iff _ _ i).mpr h1)
      have zero3 : IsZero (AddCommGrpCat.of (Ext K S.X₁ (i + 1))) :=
        AddCommGrpCat.isZero_iff_subsingleton'.mpr ((finte_free_ext_vanish_iff _ _ (i + 1)).mpr h3)
      exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
        (Ext.covariant_sequence_exact₃' K S_exact i (i + 1) rfl)
        (zero1.eq_zero_of_src _) (zero3.eq_zero_of_tgt _)
  simp only [IsLocalRing.depth, Ideal.depth, moduleDepth]
  apply le_antisymm
  · rw [ENat.add_sSup ⟨0, by simp⟩]
    apply iSup_le (fun n ↦ iSup_le (fun hn ↦ ?_))
    apply le_sSup
    intro i hi
    match i with
    | 0 =>
      rw [← finte_free_ext_vanish_iff S.X₁]
      have mono := Ext.mono_postcomp_mk₀_of_mono K S.f (hf := S_exact.mono_f)
      exact AddCommGrpCat.subsingleton_of_isZero (IsZero.of_mono_eq_zero _ (hom_zero 0))
    | i + 1 =>
      have : i < n := by simpa [add_comm 1 n] using hi
      exact ((iff i).mp (hn i this)).2
  · apply sSup_le (fun n hn ↦ ?_)
    by_cases eq0 : n = 0
    · simp [eq0]
    · have : n - 1 + 1 = n := by
        enat_to_nat
        omega
      rw [add_comm, ← this]
      apply add_le_add_left (le_sSup _) _
      intro i hi
      have lt2 : i + 1 < n := by
        rw [← this]
        exact (WithTop.add_lt_add_iff_right WithTop.one_ne_top).mpr hi
      have lt1 : i < n := lt_of_le_of_lt (self_le_add_right _ _) lt2
      exact (iff i).mpr ⟨hn i lt1, hn (i + 1) lt2⟩

theorem AuslanderBuchsbaum [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{v} R) [Nontrivial M]
    [Module.Finite R M] (netop : projectiveDimension M ≠ ⊤) :
    projectiveDimension M + IsLocalRing.depth M =
    IsLocalRing.depth (ModuleCat.of R (Shrink.{v} R)) := by
  classical
  obtain ⟨n, hn⟩: ∃ n : ℕ, projectiveDimension M = n := by
    generalize hd : projectiveDimension M = d
    induction d with
    | bot =>
      absurd (ModuleCat.isZero_iff_subsingleton.mp ((projectiveDimension_eq_bot_iff M).mp hd))
      exact not_subsingleton M
    | coe d =>
      induction d with
      | top => simp [hd] at netop
      | coe d => exact ⟨d, rfl⟩
  induction n generalizing M with
  | zero =>
    simp only [hn, CharP.cast_eq_zero, IsLocalRing.depth, Ideal.depth, zero_add, WithBot.coe_inj]
    have : HasProjectiveDimensionLE M 0 := by simp [← projectiveDimension_le_iff, hn]
    have := projective_iff_hasProjectiveDimensionLT_one.mpr this
    have : Module.Free R M := M.free_of_projective_of_isLocalRing
    exact free_depth_eq_ring_depth M _
  | succ n ih =>
    by_cases eq0 : n = 0
    · simpa [hn, eq0, zero_add, Nat.cast_one, ← WithBot.coe_one, ← WithBot.coe_add]
        using AuslanderBuchsbaum_one M ((projectiveDimension_le_iff M 1).mp (by simp [hn, eq0]))
        ((projectiveDimension_ge_iff M 1).mp (by simp [hn, eq0]))
    · rcases Module.exists_finite_presentation R M with ⟨P, _, _, free, _, f, surjf⟩
      let S : ShortComplex (ModuleCat.{v} R) := f.shortComplexKer
      have S_exact : S.ShortExact := LinearMap.shortExact_shortComplexKer surjf
      have ntr2 : Nontrivial S.X₂ := surjf.nontrivial
      have ntr1 : Nontrivial S.X₁ := by
        by_contra! H
        let ef : P ≃ₗ[R] M := LinearEquiv.ofBijective f
          ⟨LinearMap.ker_eq_bot.mp Submodule.eq_bot_of_subsingleton, surjf⟩
        have := Module.Free.of_equiv ef
        have proj : Projective M := inferInstance
        absurd proj
        simpa [← projectiveDimension_ge_iff, hn, projective_iff_hasProjectiveDimensionLT_one]
          using WithBot.le_add_self (WithBot.natCast_ne_bot n) 1
      have projX₂ : Projective S.X₂ := inferInstance
      have projdim : projectiveDimension S.X₁ = n := by
        apply le_antisymm
        · simpa [projectiveDimension_le_iff, ← S_exact.hasProjectiveDimensionLT_X₃_iff n projX₂]
            using (projectiveDimension_le_iff M (n + 1)).mp (le_of_eq hn)
        · have : n - 1 + 2 = n + 1 := by omega
          rw [projectiveDimension_ge_iff, (Nat.sub_one_add_one eq0).symm,
            ← S_exact.hasProjectiveDimensionLT_X₃_iff _ projX₂, ← projectiveDimension_ge_iff, this]
          simp [S, hn]
      have h_ker := ih S.X₁ (by simpa [projdim] using not_eq_of_beq_eq_false rfl) projdim
      have h_ker' : n + IsLocalRing.depth S.X₁ =
        IsLocalRing.depth (ModuleCat.of R (Shrink.{v} R)) := by
        rw [projdim] at h_ker
        exact WithBot.coe_inj.mp h_ker
      let K := ModuleCat.of R (Shrink.{v} (R ⧸ (maximalIdeal R)))
      have depth_pos : IsLocalRing.depth S.X₁ > 0 := by
        apply pos_of_ne_zero
        have : IsLocalRing.depth (ModuleCat.of R (Shrink.{v} R)) ≠ 0 := by simp [← h_ker', eq0]
        have : IsLocalRing.depth S.X₂ ≠ 0 := by
          simpa only [IsLocalRing.depth, Ideal.depth, free_depth_eq_ring_depth S.X₂ _]
        simp only [IsLocalRing.depth, Ideal.depth, ne_eq,
          moduleDepth_eq_zero_of_hom_nontrivial, not_nontrivial_iff_subsingleton] at this ⊢
        apply subsingleton_of_forall_eq 0 (fun F ↦ LinearMap.ext (fun x ↦ ?_))
        apply (LinearMap.ker f).subtype_injective
        rw [← LinearMap.comp_apply, Subsingleton.eq_zero ((LinearMap.ker f).subtype.comp F)]
        simp
      have ext_iso (i : ℕ) (lt : i + 1 < IsLocalRing.depth (ModuleCat.of R (Shrink.{v} R))) :
        IsIso (AddCommGrpCat.ofHom (S_exact.extClass.postcomp K (Eq.refl (i + 1)))) := by
        apply (isIso_iff_mono_and_epi _).mpr ⟨?_, ?_⟩
        · apply (Ext.covariant_sequence_exact₃' K S_exact i (i + 1) rfl).mono_g
          apply (AddCommGrpCat.isZero_iff_subsingleton'.mpr ?_).eq_zero_of_src
          simpa [finte_free_ext_vanish_iff] using
            ext_subsingleton_of_lt_moduleDepth (lt_of_le_of_lt (le_self_add) lt)
        · apply (Ext.covariant_sequence_exact₁' K S_exact i (i + 1) rfl).epi_f
          apply (AddCommGrpCat.isZero_iff_subsingleton'.mpr ?_).eq_zero_of_tgt
          simpa [finte_free_ext_vanish_iff] using ext_subsingleton_of_lt_moduleDepth lt
      have eq_add1 : IsLocalRing.depth S.X₁ = IsLocalRing.depth M + 1 := by
        by_cases eqtop : IsLocalRing.depth S.X₁ = ⊤
        · --might be able to removed using Ischbeck theorem
          simp only [eqtop, add_top, S] at h_ker'
          have M_depth_eqtop : IsLocalRing.depth M = ⊤ := by
            apply (moduleDepth_eq_top_iff _ _).mpr (fun i ↦ ?_)
            have := ext_iso i (by simp [← h_ker', ENat.add_lt_top])
            rw [(asIso (AddCommGrpCat.ofHom (S_exact.extClass.postcomp K
              (Eq.refl (i + 1))))).addCommGroupIsoToAddEquiv.subsingleton_congr]
            apply ext_subsingleton_of_lt_moduleDepth
            exact lt_of_lt_of_eq (ENat.coe_lt_top (i + 1)) eqtop.symm
          simp [M_depth_eqtop, eqtop]
        · rcases ENat.ne_top_iff_exists.mp eqtop with ⟨k, hk⟩
          simp only [← hk, gt_iff_lt, Nat.cast_pos] at depth_pos
          have eq : k - 1 + 1 = k := Nat.sub_one_add_one depth_pos.ne.symm
          have : IsLocalRing.depth M = (k - 1 : ℕ) := by
            simp only [IsLocalRing.depth, Ideal.depth, moduleDepth_eq_iff]
            have lt : (k - 1 : ℕ) + 1 < IsLocalRing.depth (ModuleCat.of R (Shrink.{v} R)) := by
              simp only [← h_ker', ← ENat.coe_one, ← ENat.coe_add, eq, ← hk, ENat.coe_lt_coe]
              omega
            refine ⟨?_, fun i hi ↦ ?_⟩
            · have := ext_iso (k - 1) lt
              rw [(asIso (AddCommGrpCat.ofHom (S_exact.extClass.postcomp K
                (Eq.refl (k - 1 + 1))))).addCommGroupIsoToAddEquiv.nontrivial_congr, eq]
              exact ((moduleDepth_eq_iff _ _ k).mp hk.symm).1
            · have := ext_iso i (lt_trans ((WithTop.add_lt_add_iff_right WithTop.one_ne_top).mpr
                (ENat.coe_lt_coe.mpr hi)) lt)
              rw [(asIso (AddCommGrpCat.ofHom (S_exact.extClass.postcomp K
                (Eq.refl (i + 1))))).addCommGroupIsoToAddEquiv.subsingleton_congr]
              exact ((moduleDepth_eq_iff _ _ k).mp hk.symm).2 _ (Nat.add_lt_of_lt_sub hi)
          simpa [hk, this] using ENat.coe_inj.mpr eq.symm
      rw [hn, Nat.cast_add, Nat.cast_one, add_assoc, add_comm 1, ← WithBot.coe_one,
        ← WithBot.coe_add, ← eq_add1, ← projdim]
      exact h_ker
