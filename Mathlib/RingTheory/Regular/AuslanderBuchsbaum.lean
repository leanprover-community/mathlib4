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

section hom

open Module Free Pointwise

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  (I : Ideal R)

theorem smul_prod_of_smul {ι : Type*} [Finite ι] (x : ι → M)
    (h : ∀ i, x i ∈ I • (⊤ : Submodule R M)) : x ∈ I • (⊤ : Submodule R (ι → M)) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  rw [← Finset.univ_sum_single x]
  apply Submodule.sum_mem
  intro i hi
  show LinearMap.single R (fun i ↦ M) i (x i) ∈ _
  rw [← Submodule.mem_comap]
  exact Submodule.smul_top_le_comap_smul_top _ _ (h i)

variable [Module.Finite R M] [Free R M] (f : M →ₗ[R] N)

theorem mem_smul_top_of_range_le_smul_top (hf : LinearMap.range f ≤ I • ⊤) :
    f ∈ I • (⊤ : Submodule R (M →ₗ[R] N)) := by
  let ι := ChooseBasisIndex R M
  let e : Basis ι R M := chooseBasis R M
  let g : (ι → N) →ₗ[R] (M →ₗ[R] N) := (e.constr R).toLinearMap
  have h (i : ι) : f (e i) ∈ I • (⊤ : Submodule R N) := hf (LinearMap.mem_range_self f (e i))
  let x (i : ι) : N := f (e i)
  have hx : f = g x := by
    apply e.ext
    simp only [g, x, LinearEquiv.coe_coe, Basis.constr_apply_fintype, Basis.equivFun_self, ite_smul,
      one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, implies_true]
  rw [hx]
  exact Submodule.smul_top_le_comap_smul_top I g (smul_prod_of_smul I x h)

end hom

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

set_option linter.unusedTactic false

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

instance [IsLocalRing R] (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    FiniteDimensional (R ⧸ maximalIdeal R) (M ⧸ maximalIdeal R • (⊤ : Submodule R M)) := by
  let f : M →ₛₗ[Ideal.Quotient.mk (maximalIdeal R)] (M ⧸ maximalIdeal R • (⊤ : Submodule R M)) := {
    __ := Submodule.mkQ (maximalIdeal R • (⊤ : Submodule R M))
    map_smul' m r := by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, map_smul, Submodule.mkQ_apply]
      rfl }
  exact Module.Finite.of_surjective f (Submodule.mkQ_surjective _)

set_option maxHeartbeats 250000 in
-- a weird time out, for exact same two copy, the first passed but the second does not
lemma ext_hom_zero_of_mem_ideal_smul (L M N : ModuleCat.{v} R) (f : M ⟶ N)
    (mem : f ∈ (Module.annihilator R L) • (⊤ : Submodule R (M ⟶ N))) (n : ℕ) :
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
    dsimp
    convert zero_add (0 : Ext L N n)
    · show AddCommGrp.ofHom ((Ext.mk₀ g1).postcomp L (add_zero n)) x = 0
      simp [hg1]
    · show AddCommGrp.ofHom ((Ext.mk₀ g2).postcomp L (add_zero n)) x = 0
      simp [hg2]

lemma AuslanderBuchsbaum_one [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{v} R) [Nontrivial M] [Module.Finite R M]
    [Small.{v} (R ⧸ (IsLocalRing.maximalIdeal R))]
    (le1 : HasProjectiveDimensionLE M 1) (nle0 : ¬ HasProjectiveDimensionLE M 0) :
    1 + IsLocalRing.depth M = IsLocalRing.depth (ModuleCat.of R R) := by
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
  have ker_free : Module.Free R (LinearMap.ker f) := by
    apply @free_of_projectiveOverLocalRing _ _ _ _ (ModuleCat.of R (LinearMap.ker f)) _ ?_
    apply @projective_of_hasProjectiveDimensionLT_one _ _ _ _ _ ?_
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
    have proj : Projective (ModuleCat.of.{v} R (ι →₀ Shrink.{v, u} R)) := by
      obtain ⟨⟨B⟩⟩ : Module.Free R (ι →₀ Shrink.{v, u} R) := inferInstance
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
