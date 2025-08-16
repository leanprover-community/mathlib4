/-
Copyright (c) 2025 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yongle Hu, Yijun Yuan
-/
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Regular.Depth
import Mathlib.Tactic.ENatToNat
/-!
# Auslander-Buchsbaum theorem

In this file, we prove the Auslander-Buchsbaum theorem, which states that for a finitely generated
module `M` over a Noetherian local ring `R`, if $\operatorname{proj}\dim M < \infty$, then
$\operatorname{proj}\dim M + \operatorname{depth} M = \operatorname{depth} R$.

-/

namespace CategoryTheory

universe w v u

open Abelian Limits ZeroObject Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C]

theorem shortExact_kernel_of_epi {X Y : C} (e : X ⟶ Y) [he : Epi e] :
    (ShortComplex.mk (kernel.ι e) e (kernel.condition e)).ShortExact where
  exact := ShortComplex.exact_kernel e
  mono_f := equalizer.ι_mono
  epi_g := he

instance Projective.of_hasProjectiveDimensionLT_one [HasExt.{w} C]
    (P : C) [HasProjectiveDimensionLT P 1] : Projective P where
  factors f e _ := by
    obtain ⟨g, h⟩ := covariant_sequence_exact₃ P (shortExact_kernel_of_epi e) (addEquiv₀.symm f) rfl
      (eq_zero_of_hasProjectiveDimensionLT _ 1 (Eq.le rfl))
    rw [← addEquiv₀.eq_symm_apply.mp h, ← AddEquiv.symm_apply_apply addEquiv₀ g]
    exact ⟨addEquiv₀ g, addEquiv₀.symm_apply_eq.mp (mk₀_comp_mk₀ (addEquiv₀ g) e).symm⟩

end CategoryTheory

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

variable [Module.Finite R M] [Free R M] (f : M →ₗ[R] N)

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

local instance : CategoryTheory.HasExt.{max u v} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{max u v} (ModuleCat.{v} R)

omit [Small.{v, u} R] in
lemma nontrivial_ring_of_nontrivial_module (M : Type*) [AddCommGroup M] [Module R M]
    [ntr : Nontrivial M] : Nontrivial R := by
  apply not_subsingleton_iff_nontrivial.mp
  by_contra h
  absurd ntr
  apply not_nontrivial_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0 (fun m ↦ ?_)
  rw [← one_smul R m, Subsingleton.elim (1 : R) 0, zero_smul]

namespace AddCommGrp

variable {ι : Type v} [DecidableEq ι] (Z : ι → AddCommGrp.{max u v})

open DirectSum

def coproductCocone : Cofan Z :=
  Cofan.mk (of (⨁ i : ι, Z i)) fun i => ofHom (DirectSum.of (fun i ↦ Z i) i)

def coproductCoconeIsColimit : IsColimit (coproductCocone Z) where
  desc s := ofHom <| DirectSum.toAddMonoid fun i ↦ (s.ι.app ⟨i⟩).hom
  fac := by
    rintro s ⟨i⟩
    ext (x : Z i)
    simp [coproductCocone, hom_comp]
  uniq := by
    rintro s f h
    ext : 1
    refine DirectSum.addHom_ext fun i x ↦ ?_
    simpa [LinearMap.coe_comp, Function.comp_apply, hom_ofHom, toModule_lof] using
      congr($(h ⟨i⟩) x)

noncomputable def coprodIsoDirectSum [HasCoproduct Z] : ∐ Z ≅ AddCommGrp.of (⨁ i, Z i) :=
  colimit.isoColimitCocone ⟨_, coproductCoconeIsColimit Z⟩

end AddCommGrp

open Module

lemma subsingleton_of_pi {α β : Type*} [Nonempty α] (h : Subsingleton (α → β)) :
    Subsingleton β := by
  contrapose h
  have : Nontrivial β := not_subsingleton_iff_nontrivial.mp h
  exact not_subsingleton_iff_nontrivial.mpr Function.nontrivial

lemma finte_free_ext_vanish_iff (M N : ModuleCat.{v} R) [Module.Finite R M] [Module.Free R M]
    [Nontrivial M] (i : ℕ) : Subsingleton (Ext.{max u v} N M i) ↔
    Subsingleton (Ext.{max u v} N (ModuleCat.of R (Shrink.{v} R)) i) := by
  classical
  have : Nontrivial R := nontrivial_ring_of_nontrivial_module M
  rcases Module.Free.exists_set R M with ⟨S, ⟨B⟩⟩
  have : Fintype S := Set.Finite.fintype (Module.Finite.finite_basis B)
  have : Nonempty S := B.index_nonempty
  have h := Ext.addEquivBiproduct N (biconeIsBilimitOfColimitCoconeOfIsColimit <|
    ModuleCat.coproductCoconeIsColimit (fun s : S ↦ ModuleCat.of R (Shrink.{v, u} R))) i
  simp only [ModuleCat.coproductCocone, Bicone.ofColimitCocone_pt, Cofan.mk_pt] at h
  change Subsingleton ((extFunctorObj N i).obj M) ↔ _
  let e := B.repr ≪≫ₗ Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R).symm ≪≫ₗ
    finsuppLEquivDirectSum R (Shrink.{v, u} R) ↑S |>.toModuleIso
  rw [((extFunctorObj.{max u v} N i).mapIso e).addCommGroupIsoToAddEquiv.subsingleton_congr]
  exact h.subsingleton_congr.trans ⟨subsingleton_of_pi, fun _ ↦ Pi.instSubsingleton⟩

lemma free_depth_eq_ring_depth (M N : ModuleCat.{v} R) [Module.Finite R M] [Module.Free R M]
    [Nontrivial M] : moduleDepth N M = moduleDepth N (ModuleCat.of R (Shrink.{v} R)) := by
  simp only [moduleDepth]
  congr! 5
  apply finte_free_ext_vanish_iff

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
    change (((Ext.homEquiv₀_linearHom R).symm (r • f)).postcompOfLinear R L _) x = 0
    simp only [Ext.postcompOfLinear, LinearMap.flip_apply]
    rw [map_smul, map_smul, ← LinearMap.smul_apply, ← map_smul]
    have : r • x = 0 := by
      have : r • (Ext.bilinearCompOfLinear R L L M 0 n n (zero_add n)).flip
        x ((Ext.homEquiv₀_linearHom R).symm (𝟙 L)) = 0 := by
        have : r • (𝟙 L) = 0 := ModuleCat.hom_ext
          (LinearMap.ext (fun x ↦ Module.mem_annihilator.mp hr _))
        rw [← map_smul, ← map_smul, this]
        simp
      rwa [← Ext.mk₀_id_comp x]
    simp [this]
  · intro g1 g2 hg1 hg2
    ext x
    change (((Ext.homEquiv₀_linearHom R).symm (g1 + g2)).postcompOfLinear R L _) x = 0
    have : AddCommGrp.ofHom ((Ext.mk₀ g1).postcomp L (add_zero n)) x +
      AddCommGrp.ofHom ((Ext.mk₀ g2).postcomp L (add_zero n)) x = 0 := by simp [hg1, hg2]
    simpa only [Ext.postcompOfLinear, map_add]


lemma ENat.add_one_lt_add_one_iff {a b : ℕ∞} : a < b ↔ a + 1 < b + 1 := by
  enat_to_nat
  omega

lemma CategoryTheory.Abelian.extFunctorObj_zero_preserve_momoMorphism (L M N : ModuleCat.{v} R)
    (f : M ⟶ N) (mono : Mono f) :
    Mono (AddCommGrp.ofHom <| ((Ext.mk₀ f)).postcomp L (add_zero 0)) := by
  apply ConcreteCategory.mono_of_injective
  rw [← AddMonoidHom.ker_eq_bot_iff]
  apply (AddSubgroup.eq_bot_iff_forall _).mpr (fun x hx ↦ ?_)
  simp only [AddCommGrp.hom_ofHom, AddMonoidHom.mem_ker, AddMonoidHom.flip_apply,
    Ext.bilinearComp_apply_apply] at hx
  rw [← Ext.mk₀_homEquiv₀_apply x, Ext.mk₀_comp_mk₀] at hx
  have : (Ext.addEquiv₀ x ≫ f) = 0 := (AddEquiv.map_eq_zero_iff Ext.addEquiv₀.symm).mp hx
  exact (AddEquiv.map_eq_zero_iff Ext.addEquiv₀).mp (zero_of_comp_mono f this)

lemma AuslanderBuchsbaum_one [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) [Nontrivial M] [Module.Finite R M]
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
  have ntr2 : Nontrivial S.X₂ := Function.Surjective.nontrivial surjf
  have ntr1 : Nontrivial S.X₁ := by
    by_contra h
    have : Subsingleton (LinearMap.ker f) := not_nontrivial_iff_subsingleton.mp h
    let ef : (ι →₀ Shrink.{v, u} R) ≃ₗ[R] M := LinearEquiv.ofBijective f
      ⟨LinearMap.ker_eq_bot.mp Submodule.eq_bot_of_subsingleton, surjf⟩
    obtain ⟨⟨B⟩⟩ := Module.Free.of_equiv ef
    absurd nle0
    have := ModuleCat.projective_of_free B.2
    infer_instance
  have ker_free : Module.Free R (LinearMap.ker f) := by
    apply @(ModuleCat.of R (LinearMap.ker f)).free_of_projective_of_isLocalRing _ _ _ _ _ ?_
    apply @Projective.of_hasProjectiveDimensionLT_one _ _ _ _ _ ?_
    have proj : Projective (ModuleCat.of.{v} R (ι →₀ Shrink.{v, u} R)) := by
      rcases free with ⟨⟨B⟩⟩
      exact ModuleCat.projective_of_free B.2
    exact (S_exact.hasProjectiveDimensionLT_X₃_iff 0 proj).mp le1
  have ker_le : LinearMap.ker f ≤ (maximalIdeal R) • (⊤ : Submodule R (ι →₀ Shrink.{v, u} R)) := by
    apply le_trans (LinearMap.ker_le_ker_comp f (maximalIdeal R • (⊤ : Submodule R M)).mkQ) _
    rw [hf]
    intro x
    have : x ∈ LinearMap.ker (Finsupp.mapRange.linearMap (Submodule.mkQ (maximalIdeal R) ∘ₗ
      (Shrink.linearEquiv R R))) ↔ ∀ i : ι, x i ∈ (maximalIdeal R).comap (Shrink.ringEquiv R) := by
      simp only [LinearMap.mem_ker, Finsupp.mapRange.linearMap_apply, LinearMap.coe_comp,
        LinearEquiv.coe_coe, mem_comap, Finsupp.ext_iff, Finsupp.zero_apply]
      congr!
      simp [Quotient.eq_zero_iff_mem, Shrink.ringEquiv]
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
  let K := ModuleCat.of R (Shrink.{v} (R ⧸ (maximalIdeal R)))
  have Sf_mem : S.f ∈ (Module.annihilator R K) • (⊤ : Submodule R (S.X₁ ⟶ S.X₂)) := by
    simp only [K, S, LinearEquiv.annihilator_eq (Shrink.linearEquiv R (R ⧸ maximalIdeal R)),
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
      have zero3 : IsZero (AddCommGrp.of (Ext K S.X₁ (i + 1))) :=
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
      have mono := extFunctorObj_zero_preserve_momoMorphism K S.X₁ S.X₂ S.f S_exact.mono_f
      exact AddCommGrp.subsingleton_of_isZero (IsZero.of_mono_eq_zero _ (hom_zero 0))
    · have eq : i - 1 + 1 = i := Nat.sub_one_add_one eq0
      have : i - 1 < n := by
        rw [add_comm, ← eq, ENat.coe_add, ENat.coe_sub, ENat.coe_one] at hi
        exact ENat.add_one_lt_add_one_iff.mpr hi
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
      have lt2 : i + 1 < n := by
        rw [← this]
        exact ENat.add_one_lt_add_one_iff.mp hi
      have lt1 : i < n := lt_of_le_of_lt (self_le_add_right _ _) lt2
      exact (iff i).mpr ⟨hn i lt1, hn (i + 1) lt2⟩

open scoped Classical in
theorem AuslanderBuchsbaum [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) [Nontrivial M] [Module.Finite R M]
    (hfinprojdim : ∃ i : ℕ, CategoryTheory.HasProjectiveDimensionLE M i) :
    Nat.find hfinprojdim + IsLocalRing.depth M =
    IsLocalRing.depth.{v} (ModuleCat.of R (Shrink.{v} R)) := by
    generalize h: Nat.find hfinprojdim = n
    induction' n with n ih generalizing M
    · simp only [CharP.cast_eq_zero, IsLocalRing.depth, Ideal.depth, moduleDepth, zero_add]
      have pdz: HasProjectiveDimensionLE M (Nat.find hfinprojdim) := Nat.find_spec hfinprojdim
      simp only [HasProjectiveDimensionLE, h, zero_add] at pdz
      have : Module.Free R M := M.free_of_projective_of_isLocalRing
      congr! 5
      apply finte_free_ext_vanish_iff
    · by_cases eq0 : n = 0
      · simp only [eq0, zero_add, Nat.find_eq_iff, Nat.lt_one_iff, forall_eq, Nat.cast_one] at h ⊢
        exact AuslanderBuchsbaum_one M h.1 h.2
      · rcases Basis.exists_basis (R ⧸ maximalIdeal R) (M ⧸ maximalIdeal R • (⊤ : Submodule R M))
          with ⟨ι, ⟨B⟩⟩
        let fin := FiniteDimensional.fintypeBasisIndex B
        let f := Classical.choose (Module.projective_lifting_property
          (Submodule.mkQ (maximalIdeal R • (⊤ : Submodule R M)))
          ((LinearEquiv.restrictScalars R B.repr).symm.toLinearMap.comp
          (Finsupp.mapRange.linearMap ((Submodule.mkQ (maximalIdeal R)).comp
          (Shrink.linearEquiv R R).toLinearMap))) (Submodule.mkQ_surjective _))
        have surjf : Function.Surjective f := basis_lift M ι B
        have : Module.Finite R (ι →₀ Shrink.{v, u} R) := by
          simp [Module.finite_finsupp_iff, Module.Finite.equiv (Shrink.linearEquiv R R).symm,
            fin.finite]
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
        have ntr2 : Nontrivial S.X₂ := Function.Surjective.nontrivial surjf
        have ntr1 : Nontrivial S.X₁ := by
          by_contra H
          have : Subsingleton (LinearMap.ker f) := not_nontrivial_iff_subsingleton.mp H
          let ef : (ι →₀ Shrink.{v, u} R) ≃ₗ[R] M := LinearEquiv.ofBijective f
            ⟨LinearMap.ker_eq_bot.mp Submodule.eq_bot_of_subsingleton, surjf⟩
          obtain ⟨⟨B⟩⟩ := Module.Free.of_equiv ef
          absurd Nat.find_min hfinprojdim (lt_of_lt_of_eq (Nat.zero_lt_succ n) h.symm)
          have := ModuleCat.projective_of_free B.2
          infer_instance
        have le_n : HasProjectiveDimensionLE S.X₁ n := by
          rcases free with ⟨⟨B⟩⟩
          have : HasProjectiveDimensionLT S.X₃ (n + 1 + 1) := by
            rw [← h]
            exact Nat.find_spec hfinprojdim
          exact (ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff S_exact n
            (ModuleCat.projective_of_free B.2)).mp this
        have hfinprojdim' : ∃ i, HasProjectiveDimensionLE S.X₁ i := by use n
        have find_eq : Nat.find hfinprojdim' = n := by
          simp only [Nat.find_eq_iff, le_n, true_and]
          intro k hk
          rcases free with ⟨⟨B⟩⟩
          apply (ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff S_exact k
            (ModuleCat.projective_of_free B.2)).not.mp
          exact Nat.find_min hfinprojdim (lt_of_lt_of_eq (Nat.add_lt_add_right hk 1) h.symm)
        have h_ker := ih S.X₁ hfinprojdim' find_eq
        let K := ModuleCat.of R (Shrink.{v} (R ⧸ (maximalIdeal R)))
        have depth_pos : IsLocalRing.depth S.X₁ > 0 := by
          apply pos_of_ne_zero
          have : IsLocalRing.depth (ModuleCat.of R (Shrink.{v, u} R)) ≠ 0 := by simp [← h_ker, eq0]
          have : IsLocalRing.depth S.X₂ ≠ 0 := by
            simpa only [IsLocalRing.depth, Ideal.depth, free_depth_eq_ring_depth S.X₂ _]
          simp only [IsLocalRing.depth, Ideal.depth, ne_eq,
            moduleDepth_eq_zero_of_hom_nontrivial, not_nontrivial_iff_subsingleton] at this ⊢
          apply subsingleton_of_forall_eq 0 (fun F ↦ LinearMap.ext (fun x ↦ ?_))
          apply (LinearMap.ker f).subtype_injective
          rw [← LinearMap.comp_apply, Subsingleton.eq_zero ((LinearMap.ker f).subtype.comp F)]
          simp
        have ext_iso (i : ℕ) (lt : i + 1 < IsLocalRing.depth (ModuleCat.of R (Shrink.{v, u} R))) :
          IsIso (AddCommGrp.ofHom (S_exact.extClass.postcomp K (Eq.refl (i + 1)))) := by
          apply (CategoryTheory.isIso_iff_mono_and_epi _).mpr ⟨?_, ?_⟩
          · apply ShortComplex.Exact.mono_g (Ext.covariant_sequence_exact₃' K S_exact i (i + 1) rfl)
            apply IsZero.eq_zero_of_src (@AddCommGrp.isZero_of_subsingleton _ ?_)
            rw [finte_free_ext_vanish_iff]
            exact ext_subsingleton_of_lt_moduleDepth (lt_of_le_of_lt (le_self_add) lt)
          · apply ShortComplex.Exact.epi_f (Ext.covariant_sequence_exact₁' K S_exact i (i + 1) rfl)
            apply IsZero.eq_zero_of_tgt (@AddCommGrp.isZero_of_subsingleton _ ?_)
            simp only [finte_free_ext_vanish_iff]
            exact ext_subsingleton_of_lt_moduleDepth lt
        have eq_add1 : IsLocalRing.depth S.X₁ = IsLocalRing.depth M + 1 := by
          by_cases eqtop : IsLocalRing.depth S.X₁ = ⊤
          · simp only [eqtop, add_top, f, S] at h_ker
            have M_depth_eqtop : IsLocalRing.depth M = ⊤ := by
              apply (moduleDepth_eq_top_iff _ _).mpr (fun i ↦ ?_)
              have lt : i + 1 < IsLocalRing.depth (ModuleCat.of R (Shrink.{v, u} R)) := by
                rw [← h_ker, ENat.add_lt_top]
                exact ⟨ENat.coe_lt_top i, ENat.coe_lt_top 1⟩
              have := ext_iso i lt
              rw [(asIso (AddCommGrp.ofHom (S_exact.extClass.postcomp K
                (Eq.refl (i + 1))))).addCommGroupIsoToAddEquiv.subsingleton_congr]
              apply ext_subsingleton_of_lt_moduleDepth
              exact lt_of_lt_of_eq (ENat.coe_lt_top (i + 1)) eqtop.symm
            simp [M_depth_eqtop, eqtop]
          · have lttop : IsLocalRing.depth (ModuleCat.of R (Shrink.{v, u} R)) < ⊤ := by
              rw [← h_ker]
              exact ENat.add_lt_top.mpr ⟨ENat.coe_lt_top n, Ne.lt_top' (Ne.symm eqtop)⟩
            have exist := (moduleDepth_lt_top_iff _ _).mp (Ne.lt_top' (Ne.symm eqtop))
            let k := Nat.find exist
            have eq_find : IsLocalRing.depth S.X₁ = k := by
              simp only [IsLocalRing.depth, Ideal.depth, moduleDepth_eq_find _ _ exist, k]
            simp only [eq_find, gt_iff_lt, Nat.cast_pos] at depth_pos
            have eq : k - 1 + 1 = k := Nat.sub_add_cancel depth_pos
            have : IsLocalRing.depth M = (k - 1 : ℕ) := by
              simp only [IsLocalRing.depth, Ideal.depth, moduleDepth_eq_iff]
              have lt : (k - 1 : ℕ) + 1 < IsLocalRing.depth (ModuleCat.of R (Shrink.{v, u} R)) := by
                simp only [← h_ker, eq_find, ← ENat.coe_one, ← ENat.coe_add, eq, ENat.coe_lt_coe]
                omega
              refine ⟨?_, fun i hi ↦ ?_⟩
              · have := ext_iso (k - 1) lt
                rw [(asIso (AddCommGrp.ofHom (S_exact.extClass.postcomp K
                  (Eq.refl (k - 1 + 1))))).addCommGroupIsoToAddEquiv.nontrivial_congr, eq]
                exact Nat.find_spec exist
              · have := ext_iso i <|
                  lt_trans (ENat.add_one_lt_add_one_iff.mp (ENat.coe_lt_coe.mpr hi)) lt
                rw [(asIso (AddCommGrp.ofHom (S_exact.extClass.postcomp K
                  (Eq.refl (i + 1))))).addCommGroupIsoToAddEquiv.subsingleton_congr]
                exact not_nontrivial_iff_subsingleton.mp
                  (Nat.find_min exist (Nat.add_lt_of_lt_sub hi))
            simpa [eq_find, this] using ENat.coe_inj.mpr eq.symm
        simpa [add_assoc, add_comm 1 (IsLocalRing.depth M), ← eq_add1] using h_ker
