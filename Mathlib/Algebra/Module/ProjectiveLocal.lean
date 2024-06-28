import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Module.Submodule.Localization


section Submodule

open scoped nonZeroDivisors

variable {R A M} [CommRing R] [CommRing A] [AddCommGroup M] [Algebra R A] [Module R M] [Module A M]

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

/-- Let `I J : Ideal R`. If the localization of `I` at each maximal ideal `P` is included in
the localization of `J` at `P`, then `I ≤ J`. -/
theorem Submodule.le_of_localization_maximal {I J : Submodule R M}
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      I.localized' (Rₚ P) P.primeCompl (f P) ≤ J.localized' (Rₚ P) P.primeCompl (f P)) :
    I ≤ J := by
  intro x hx
  suffices J.colon (Submodule.span R {x}) = ⊤ by
    simpa using Submodule.mem_colon.mp
      (show (1 : R) ∈ J.colon (Submodule.span R {x}) from this.symm ▸ Submodule.mem_top) x
      (Submodule.mem_span_singleton_self x)
  refine Not.imp_symm (J.colon (Submodule.span R {x})).exists_le_maximal ?_
  push_neg
  intro P hP le
  obtain ⟨a, ha, s, e⟩ := h P ⟨x, hx, 1, rfl⟩
  rw [IsLocalizedModule.mk'_eq_mk'_iff] at e
  obtain ⟨t, ht⟩ := e
  simp at ht
  refine (t * s).2 (le (Submodule.mem_colon_singleton.mpr ?_))
  simp only [Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def, ht]
  exact J.smul_mem _ ha

/-- Let `I J : Ideal R`. If the localization of `I` at each maximal ideal `P` is equal to
the localization of `J` at `P`, then `I = J`. -/
theorem Submodule.eq_of_localization_maximal {I J : Submodule R M}
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      I.localized' (Rₚ P) P.primeCompl (f P) = J.localized' (Rₚ P) P.primeCompl (f P)) :
    I = J :=
  le_antisymm (Submodule.le_of_localization_maximal Rₚ Mₚ f fun P _ => (h P).le)
    (Submodule.le_of_localization_maximal Rₚ Mₚ f fun P _ => (h P).ge)

@[simp]
lemma Submodule.localized'_bot {R S M N} [CommRing R] [CommRing S] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]
    (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N)
    [IsLocalizedModule p f] : (⊥ : Submodule R M).localized' S p f = ⊥ := by
  rw [← le_bot_iff]
  rintro _ ⟨_, rfl, s, rfl⟩
  simp only [IsLocalizedModule.mk'_zero, mem_bot]

@[simp]
lemma Submodule.localized'_span {R S M N} [CommRing R] [CommRing S] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]
    (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N)
    [IsLocalizedModule p f] (s : Set M) : (span R s).localized' S p f = span S (f '' s) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, t, rfl⟩
    have := IsLocalizedModule.mk'_smul_mk' S f 1 x t 1
    simp only [IsLocalizedModule.mk'_one, one_smul, mul_one] at this
    rw [← this]
    apply Submodule.smul_mem
    rw [← Submodule.restrictScalars_mem R, ← Submodule.mem_comap]
    refine (show span R s ≤ _ from ?_) hx
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_span]
    exact span_le_restrictScalars _ _ _
  · rw [Submodule.span_le, Set.image_subset_iff]
    intro x hx
    exact ⟨x, subset_span hx, 1, IsLocalizedModule.mk'_one _ _ _⟩

/-- An ideal is trivial if its localization at every maximal ideal is trivial. -/
theorem Submodule.eq_bot_of_localization_maximal (I : Submodule R M)
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      I.localized' (Rₚ P) P.primeCompl (f P) = ⊥) :
    I = ⊥ :=
  Submodule.eq_of_localization_maximal Rₚ Mₚ f fun P hP => by simpa using h P

theorem Submodule.mem_of_localization_maximal (r : M) (I : Submodule R M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], f P r ∈ I.localized' (Rₚ P) P.primeCompl (f P)) :
    r ∈ I := by
  rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← Submodule.span_le]
  apply Submodule.le_of_localization_maximal Rₚ Mₚ f
  intro J hJ
  rw [Submodule.localized'_span, Submodule.span_le, Set.image_subset_iff, Set.singleton_subset_iff]
  exact h J

theorem Module.eq_zero_of_localization_maximal (r : M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], f P r = 0) :
    r = 0 := by
  rw [← Submodule.mem_bot (R := R)]
  apply Submodule.mem_of_localization_maximal Rₚ Mₚ f r ⊥ (by simpa using h)

theorem Module.eq_of_localization_maximal (r s : M)
    (h : ∀ (P : Ideal R) [P.IsMaximal], f P r = f P s) :
    r = s := by
  rw [← sub_eq_zero]
  simp_rw [← @sub_eq_zero _ _ (f _ _), ← map_sub] at h
  exact Module.eq_zero_of_localization_maximal Rₚ Mₚ f _ h

end Submodule

variable (R : Type*) [CommRing R]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]

noncomputable
def LocalizedModule.map' {R M N} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M]
  [Module R N] (S : Submonoid R) :
    (M →ₗ[R] N) →ₗ[R] LocalizedModule S M →ₗ[R] LocalizedModule S N :=
  (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S N))

@[simp]
lemma LocalizedModule.map'_mk {R M N} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M]
  [Module R N] (S : Submonoid R) (f : M →ₗ[R] N) (x y) :
    map' S f (.mk x y) = LocalizedModule.mk (f x) y := by
  apply ((Module.End_isUnit_iff _).mp <| IsLocalizedModule.map_units (mkLinearMap _ _) y).injective
  simp only [Module.algebraMap_end_apply, smul'_mk, ← map_smul]
  rw [f.map_smul]
  simp only [ ← Submonoid.smul_def, mk_cancel]
  exact IsLocalizedModule.map_apply S (mkLinearMap _ _) (mkLinearMap _ _) _ _

lemma LocalizedModule.map'_surjective {R M N} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M]
  [Module R N] (S : Submonoid R) (l : M →ₗ[R] N) (hl : Function.Surjective l) :
    Function.Surjective (map' S l) := by
  intro x
  induction' x using LocalizedModule.induction_on with m s
  obtain ⟨m, rfl⟩ := hl m
  exact ⟨mk m s, map'_mk _ _ _ _⟩

noncomputable
def LocalizedModule.map {R M N} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M]
  [Module R N] (S : Submonoid R) (f : M →ₗ[R] N) :
    LocalizedModule S M →ₗ[Localization S] LocalizedModule S N :=
  LinearMap.extendScalarsOfIsLocalization S (Localization S)
  (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S N) f)

@[simps]
noncomputable
def LocalizedModule.mapLinear {R M N} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M]
  [Module R N] (S : Submonoid R) :
    (M →ₗ[R] N) →ₗ[R] LocalizedModule S M →ₗ[Localization S] LocalizedModule S N where
  toFun f := LocalizedModule.map S f
  map_add' f g := by ext x; exact DFunLike.congr_fun ((IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N)).map_add f g) x
  map_smul' r f := by
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.ringHom_ext S
      (LocalizedModule.mkLinearMap S M)
    · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S N)
    · ext
      simp only [map, LinearMapClass.map_smul,
        LinearMap.restrictScalars_extendScalarsOfIsLocalization, LinearMap.coe_comp,
        Function.comp_apply, mkLinearMap_apply, LinearMap.smul_apply, RingHom.id_apply,
        LinearMap.coe_restrictScalars]
      rfl

@[simp]
lemma LocalizedModule.map_mk {R M N} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M]
  [Module R N] (S : Submonoid R) (f : M →ₗ[R] N) (x y) :
    map S f (.mk x y) = LocalizedModule.mk (f x) y :=
  map'_mk _ _ _ _

section

variable {R M N N'} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup N'] [Module R N'] (S : Submonoid R)

lemma Module.FinitePresentation.localizedModule_mapLinear
    [Module.FinitePresentation R M] :
      IsLocalizedModule S (LocalizedModule.mapLinear S (M := M) (N := N)) := by
  constructor
  · intro s
    rw [Module.End_isUnit_iff]
    have := (Module.End_isUnit_iff _).mp (IsLocalizedModule.map_units (S := S)
      (f := LocalizedModule.mkLinearMap S N) s)
    constructor
    · exact fun _ _ e ↦ LinearMap.ext fun m ↦ this.left (LinearMap.congr_fun e m)
    · intro h;
      use LinearMap.extendScalarsOfIsLocalization S (Localization S)
        (((IsLocalizedModule.map_units (S := S) (f := LocalizedModule.mkLinearMap S N) s).unit⁻¹).1 ∘ₗ h)
      ext x
      exact Module.End_isUnit_apply_inv_apply_of_isUnit
        (IsLocalizedModule.map_units (S := S) (f := LocalizedModule.mkLinearMap S N) s) (h x)
  · intro h
    obtain ⟨h', s, e⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule S
      (LocalizedModule.mkLinearMap S N) (h.restrictScalars R ∘ₗ LocalizedModule.mkLinearMap S M)
    refine ⟨⟨h', s⟩, ?_⟩
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.ringHom_ext S (LocalizedModule.mkLinearMap S _)
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S _))
    refine e.symm.trans (by ext; simp)
  · intro h₁ h₂ e
    apply Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S (LocalizedModule.mkLinearMap S _)
    ext x
    simpa using LinearMap.congr_fun e (LocalizedModule.mkLinearMap S _ x)

end

theorem split_surjective_of_maximal
  {R M N} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M]
  [Module R N]
  [Module.FinitePresentation R N]
   (f : M →ₗ[R] N) (H : ∀ (I : Ideal R) (hI : I.IsMaximal),
    ∃ (g : _ →ₗ[Localization.AtPrime I] _), (LocalizedModule.map I.primeCompl f).comp g = LinearMap.id) :
    ∃ (g : N →ₗ[R] M), f.comp g = LinearMap.id := by
  show LinearMap.id ∈ LinearMap.range (LinearMap.llcomp R N M N f)
  have inst₁ (I : Ideal R) [I.IsMaximal] :
    IsLocalizedModule I.primeCompl (LocalizedModule.mapLinear (M := N) (N := N) I.primeCompl) :=
      Module.FinitePresentation.localizedModule_mapLinear I.primeCompl
  have inst₂ (I : Ideal R) [I.IsMaximal] :
    IsLocalizedModule I.primeCompl (LocalizedModule.mapLinear (M := N) (N := M) I.primeCompl) :=
      Module.FinitePresentation.localizedModule_mapLinear I.primeCompl
  apply
    @Submodule.mem_of_localization_maximal R (N →ₗ[R] N) _ _ _
      (fun P _ ↦ Localization.AtPrime P) _ _ _ _ _ _ _ _
      (fun P _ ↦ LocalizedModule.mapLinear P.primeCompl)
      (fun P _ ↦ inst₁ P)
  intro I hI
  have : LinearMap.id ∈ LinearMap.range (LinearMap.llcomp _
    (LocalizedModule I.primeCompl N) _ _ (LocalizedModule.map I.primeCompl f)) := H I hI
  convert this
  · apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.ringHom_ext I.primeCompl (LocalizedModule.mkLinearMap I.primeCompl N)
    · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap I.primeCompl N)
    ext; simp only [LinearMap.coe_comp, Function.comp_apply, LocalizedModule.mkLinearMap_apply,
      LinearMap.id_comp]
    exact IsLocalizedModule.map_apply _ _ _ _ _
  · ext f
    constructor
    · intro hf
      obtain ⟨a, ha, c, rfl⟩ := hf
      obtain ⟨g, rfl⟩ := ha
      use IsLocalizedModule.mk' (LocalizedModule.mapLinear I.primeCompl) g c
      apply ((Module.End_isUnit_iff _).mp <| IsLocalizedModule.map_units
        (LocalizedModule.mapLinear I.primeCompl) c).injective
      dsimp
      conv_rhs => rw [← Submonoid.smul_def]
      conv_lhs => rw [← LinearMap.map_smul_of_tower]
      rw [← Submonoid.smul_def, IsLocalizedModule.mk'_cancel', IsLocalizedModule.mk'_cancel']
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.ringHom_ext I.primeCompl (LocalizedModule.mkLinearMap I.primeCompl N)
      · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap I.primeCompl N)
      ext
      simp only [LocalizedModule.mapLinear_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
        Function.comp_apply, LocalizedModule.mkLinearMap_apply, LinearMap.llcomp_apply,
        LocalizedModule.map_mk]
    · rintro ⟨g, rfl⟩
      obtain ⟨⟨g, s⟩, rfl⟩ :=
        IsLocalizedModule.mk'_surjective I.primeCompl (LocalizedModule.mapLinear I.primeCompl) g
      simp only [Function.uncurry_apply_pair, Submodule.restrictScalars_mem]
      refine ⟨f.comp g, ⟨g, rfl⟩, s, ?_⟩
      apply ((Module.End_isUnit_iff _).mp <| IsLocalizedModule.map_units
         (LocalizedModule.mapLinear I.primeCompl) s).injective
      simp only [Module.algebraMap_end_apply, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel',
        ← LinearMap.map_smul_of_tower]
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.ringHom_ext I.primeCompl (LocalizedModule.mkLinearMap I.primeCompl N)
      · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap I.primeCompl N)
      ext; simp only [LocalizedModule.mapLinear_apply, LinearMap.coe_comp,
        LinearMap.coe_restrictScalars, Function.comp_apply, LocalizedModule.mkLinearMap_apply,
        LocalizedModule.map_mk, LinearMap.smul_apply, LinearMap.llcomp_apply]

theorem Module.projective_of_localization_maximal (H : ∀ (I : Ideal R) (_ : I.IsMaximal),
    Module.Projective (Localization.AtPrime I) (LocalizedModule I.primeCompl M))
    [Module.FinitePresentation R M] : Module.Projective R M := by
  have : Module.Finite R M := by infer_instance
  have : (⊤ : Submodule R M).FG := this.out
  have : ∃ (s : Finset M), _ := this
  obtain ⟨s, hs⟩ := this
  let N := s →₀ R
  let f : N →ₗ[R] M := Finsupp.total s M R (Subtype.val : s → M)
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Finsupp.range_total, Subtype.range_val]
    convert hs
  have (I : Ideal R) (hI : I.IsMaximal) :=
    letI := H I hI
    Module.projective_lifting_property (LocalizedModule.mapLinear I.primeCompl f) LinearMap.id
    (LocalizedModule.map'_surjective _ _ hf)
  obtain ⟨g, hg⟩ := split_surjective_of_maximal _ this
  exact Module.Projective.of_split _ _ hg

theorem Module.free_of_isLocalizedModule (Rₛ) {Mₛ} [AddCommGroup Mₛ] [Module R Mₛ]
    [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    (S) (f : M →ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Free R M] :
      Module.Free Rₛ Mₛ :=
  Module.Free.of_basis
    (Basis.ofIsLocalizedModule Rₛ S f (Module.Free.chooseBasis R M))

theorem Module.projective_of_isLocalizedModule {Rₛ Mₛ} [AddCommGroup Mₛ] [Module R Mₛ]
    [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    (S) (f : M →ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Projective R M] :
      Module.Projective Rₛ Mₛ :=
    Projective.of_equiv (IsLocalizedModule.isBaseChange S Rₛ f).equiv
