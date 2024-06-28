import Mathlib.RingTheory.Smooth.Projective
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Flat.Stability
import Mathlib.Algebra.Module.FinitePresentation
-- import Mathlib
universe u

variable {R S} [CommRing R] [CommRing S] [Algebra R S]

section

variable [LocalRing R] {M N} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

open Function (Injective Surjective Exact)
open LocalRing TensorProduct

local notation "k" => ResidueField R
local notation "𝔪" => maximalIdeal R

variable {P} [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
variable (hg : Surjective g) (h : Exact f g)

theorem LocalRing.map_mkQ_eq_top {N : Submodule R M} [Module.Finite R M] :
    N.map (Submodule.mkQ (𝔪 • ⊤)) = ⊤ ↔ N = ⊤ := by
  constructor
  · intro hN
    have : 𝔪 • ⊤ ⊔ N = ⊤ := by simpa using Submodule.comap_mono (f := Submodule.mkQ (𝔪 • ⊤)) hN.ge
    rw [sup_comm] at this
    exact top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.out
      (by rw [jacobson_eq_maximalIdeal]; exact bot_ne_top) this.ge)
  · rintro rfl; simp

theorem LocalRing.map_mkQ_eq {N₁ N₂ : Submodule R M} (h : N₁ ≤ N₂) (h' : N₂.FG) :
    N₁.map (Submodule.mkQ (𝔪 • N₂)) = N₂.map (Submodule.mkQ (𝔪 • N₂)) ↔ N₁ = N₂ := by
  constructor
  · intro hN
    have : N₂ ≤ 𝔪 • N₂ ⊔ N₁ := by simpa using Submodule.comap_mono (f := Submodule.mkQ (𝔪 • N₂)) hN.ge
    rw [sup_comm] at this
    exact h.antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot h'
      (by rw [jacobson_eq_maximalIdeal]; exact bot_ne_top) this)
  · rintro rfl; simp

variable (R S M) in
theorem TensorProduct.mk_surjective (S) [CommRing S] [Algebra R S]
    (h : Surjective (algebraMap R S)) :
    Surjective (TensorProduct.mk R S M 1) := by
  rw [← LinearMap.range_eq_top, ← top_le_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
  rintro _ ⟨x, y, rfl⟩
  obtain ⟨x, rfl⟩ := h x
  rw [Algebra.algebraMap_eq_smul_one, smul_tmul]
  exact ⟨x • y, rfl⟩

variable (R S M) in
theorem TensorProduct.mk_lift_lsmul_exact (S) (I) [CommRing S] [Algebra R S]
    (h : Surjective (algebraMap R S)) (hI : I = RingHom.ker (algebraMap R S)) :
    Function.Exact (lift (LinearMap.lsmul R M ∘ₗ I.subtype)) (TensorProduct.mk R S M 1) := by
  have : Function.Exact I.subtype (algebraMap R S) := sorry
  rw [← (TensorProduct.lid R _).symm.conj_exact_iff_exact]
  convert this

  sorry
  -- rw [← LinearMap.range_eq_top, ← top_le_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
  -- rintro _ ⟨x, y, rfl⟩
  -- obtain ⟨x, rfl⟩ := h x
  -- rw [Algebra.algebraMap_eq_smul_one, smul_tmul]
  -- exact ⟨x • y, rfl⟩

theorem LocalRing.map_mk_eq_top {N : Submodule R M} [Module.Finite R M] :
    N.map (TensorProduct.mk R k M 1) = ⊤ ↔ N = ⊤ := by
  constructor
  · intro hN
    letI : Module k (M ⧸ (𝔪 • ⊤ : Submodule R M)) :=
      inferInstanceAs (Module (R ⧸ 𝔪) (M ⧸ 𝔪 • (⊤ : Submodule R M)))
    letI : IsScalarTower R k (M ⧸ (𝔪 • ⊤ : Submodule R M)) :=
      inferInstanceAs (IsScalarTower R (R ⧸ 𝔪) (M ⧸ 𝔪 • (⊤ : Submodule R M)))
    let f := AlgebraTensorModule.lift (((LinearMap.ringLmapEquivSelf k k _).symm
      (Submodule.mkQ (𝔪 • ⊤ : Submodule R M))).restrictScalars R)
    have : f.comp (TensorProduct.mk R k M 1) = Submodule.mkQ (𝔪 • ⊤) := by ext; simp [f]
    have hf : Function.Surjective f := by
      intro x; obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x;
      rw [← this, LinearMap.comp_apply]; exact ⟨_, rfl⟩
    apply_fun Submodule.map f at hN
    rwa [← Submodule.map_comp, this, Submodule.map_top, LinearMap.range_eq_top.mpr hf,
      LocalRing.map_mkQ_eq_top] at hN
  · rintro rfl; rw [Submodule.map_top, LinearMap.range_eq_top]
    exact TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective

theorem LocalRing.span_eq_top_of_tmul_eq_basis [Module.Finite R M] {ι}
    (f : ι → M) (b : Basis ι k (k ⊗[R] M))
    (hb : ∀ i, 1 ⊗ₜ f i = b i) : Submodule.span R (Set.range f) = ⊤ := by
  rw [← LocalRing.map_mk_eq_top, Submodule.map_span, ← Submodule.restrictScalars_span R k
    Ideal.Quotient.mk_surjective, Submodule.restrictScalars_eq_top_iff,
    ← b.span_eq, ← Set.range_comp]
  simp only [Function.comp, mk_apply, hb, Basis.span_eq]

theorem LocalRing.exists_tmul_eq_basis [Module.Finite R M] {ι}
    (f : ι → M) (b : Basis ι k (k ⊗[R] M))
    (hb : ∀ i, 1 ⊗ₜ f i = b i) : Submodule.span R (Set.range f) = ⊤ := by
  rw [← LocalRing.map_mk_eq_top, Submodule.map_span, ← Submodule.restrictScalars_span R k
    Ideal.Quotient.mk_surjective, Submodule.restrictScalars_eq_top_iff,
    ← b.span_eq, ← Set.range_comp]
  simp only [Function.comp, mk_apply, hb, Basis.span_eq]

open LinearMap in
theorem TensorProduct.range_lift_lsmul_subtype (I : Ideal R) :
    range (TensorProduct.lift ((lsmul R M).comp I.subtype)) = I • ⊤ := by
  sorry

/--
Given `M₁ → M₂ → M₃ → 0` and `N₁ → N₂ → N₃ → 0`.

-/
theorem foofoo_aux
    {M₁ M₂ M₃ N₁ N₂ N₃}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] [AddCommGroup N₃] [Module R N₃]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃) (g₁ : M₁ →ₗ[R] M₂) (g₂ : M₂ →ₗ[R] N₃)
    (hfexact : Function.Exact f₁ f₂) (hfsurj : Function.Surjective f₂)
    (hgexact : Function.Exact f₁ g₂) (hgsurj : Function.Surjective g₂)
    (hinj : Function.Injective (f₁.rTensor M₃)) : Function.Injective (g₁.rTensor N₃) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have := g₂.qTensor_surjective
  -- obtain ⟨⟨x, hx'⟩, rfl⟩ :=
  --   TensorProduct.mk_surjective R (LinearMap.ker i) k Ideal.Quotient.mk_surjective x





#exit

theorem foo [Module.FinitePresentation R P]
    (H : Function.Injective (TensorProduct.lift ((LinearMap.lsmul R P).comp (𝔪).subtype))) :
    Module.Free R P := by
  let I := Module.Free.ChooseBasisIndex k (k ⊗[R] P)
  let b : Basis I k _ := Module.Free.chooseBasis k (k ⊗[R] P)
  letI : IsNoetherian k (k ⊗[R] (I →₀ R)) :=
    isNoetherian_of_isNoetherianRing_of_finite k (k ⊗[R] (I →₀ R))
  choose f hf using TensorProduct.mk_surjective R P k Ideal.Quotient.mk_surjective
  letI inst (M) [AddCommGroup M] [Module R M] : AddGroup (k ⊗[R] M) := inferInstance
  let i := Finsupp.total I P R (f ∘ b)
  letI := inst (LinearMap.ker i)
  have hi : Surjective i := by
    rw [← LinearMap.range_eq_top, Finsupp.range_total]
    exact LocalRing.exists_tmul_eq_basis (R := R) (f := f ∘ b) b (fun _ ↦ hf _)
  -- letI : Module k (k ⊗[R] (I →₀ R)) := inferInstance
  -- have : Function.Surjective (i.baseChange k) := LinearMap.lTensor_surjective _ hi
  -- have : Function.Bijective (i.baseChange k) := by sorry
    -- refine ⟨?_, this⟩
    -- rw [← LinearMap.ker_eq_bot (M := k ⊗[R] (I →₀ R)) (f := i.baseChange k),
    --   ← Submodule.finrank_eq_zero (R := k) (M := k ⊗[R] (I →₀ R)),
    --   ← Nat.add_right_inj (n := FiniteDimensional.finrank k (LinearMap.range <| i.baseChange k)),
    --   LinearMap.finrank_range_add_finrank_ker (V := k ⊗[R] (I →₀ R)),
    --   LinearMap.range_eq_top.mpr this, finrank_top]
    -- simp only [FiniteDimensional.finrank_tensorProduct, FiniteDimensional.finrank_self,
    --   FiniteDimensional.finrank_finsupp_self, one_mul, add_zero]
    -- rw [FiniteDimensional.finrank_eq_card_chooseBasisIndex]
  suffices Function.Injective i by sorry
  suffices Function.Injective ((LinearMap.ker i).subtype.baseChange k) by sorry
  rw [injective_iff_map_eq_zero]
  -- have := LinearMap.ker_eq_bot (τ₁₂ := RingHom.id k) (M := k ⊗[R] LinearMap.ker i)
  --   (M₂ := k ⊗[R] (I →₀ R)) (f := ((LinearMap.ker i).subtype.baseChange k))
  -- rw [← LinearMap.ker_eq_bot (f := ((LinearMap.ker i).subtype.baseChange k)), ← le_bot_iff]
  intro x hx
  obtain ⟨⟨x, hx'⟩, rfl⟩ :=
    TensorProduct.mk_surjective R (LinearMap.ker i) k Ideal.Quotient.mk_surjective x
  simp only [mk_apply, LinearMap.baseChange_tmul, Submodule.coeSubtype] at hx ⊢
  rw [← quotTensorEquivQuotSMul_symm_mk 𝔪 x,
    AddEquivClass.map_eq_zero_iff (quotTensorEquivQuotSMul (I →₀ R) 𝔪).symm,
    Submodule.Quotient.mk_eq_zero, ← range_lift_lsmul_subtype] at hx
  obtain ⟨x, rfl⟩ := hx
  have : x ∈ LinearMap.ker (i.lTensor 𝔪) := by sorry
    -- apply H
    -- simp only [LinearMap.mem_ker, map_zero, ← LinearMap.comp_apply] at hx' ⊢
    -- convert hx' using 2
    -- ext
    -- simp only [AlgebraTensorModule.curry_apply, LinearMap.coe_comp, Function.comp_apply,
    --   Finsupp.lsingle_apply, curry_apply, LinearMap.coe_restrictScalars, LinearMap.lTensor_tmul,
    --   lift.tmul, Submodule.coeSubtype, LinearMap.lsmul_apply, Finsupp.smul_single, smul_eq_mul,
    --   mul_one, ← map_smul]
  have h := lTensor_exact (M := LinearMap.ker i)
    (f := by exact (LinearMap.ker i).subtype) 𝔪 (LinearMap.exact_subtype_ker_map i) hi
  rw [LinearMap.exact_iff.mp h] at this
  obtain ⟨x, rfl⟩ := this
  have : TensorProduct.mk R k (LinearMap.ker i) 1 ∘ₗ
      (TensorProduct.lift ((LinearMap.lsmul R _).comp (𝔪).subtype)) = 0 := by
    ext x m
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.coe_comp, Function.comp_apply, lift.tmul, Submodule.coeSubtype,
      LinearMap.lsmul_apply, LinearMapClass.map_smul, mk_apply, LinearMap.zero_apply,
      TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one]
    show Ideal.Quotient.mk 𝔪 x.1 ⊗ₜ[R] m = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr x.2, TensorProduct.zero_tmul]
  have : (1 : k) ⊗ₜ[R] (TensorProduct.lift ((LinearMap.lsmul R _).comp (𝔪).subtype)) x = 0 :=
    DFunLike.congr_fun this x
  convert this
  simp_rw [← Submodule.subtype_apply, ← LinearMap.comp_apply]
  congr 1
  ext
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul, Submodule.coeSubtype,
    lift.tmul, LinearMap.lsmul_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,

  -- rw [lTensor_mkQ] at this

  -- Have :=
  -- simp? at hx'


-- --
--     -- rw [← LinearMap.ker_eq_bot, ← LocalRing.map_mk_eq_top]

-- theorem foo [Module.Finite R N] [Module.Flat R N]
--     (hf : Function.Injective (f.lTensor k)) :
--     Module.Free R P := by
--   let I := Module.Free.ChooseBasisIndex k (k ⊗[R] N)
--   let b : Basis I k _ := Module.Free.chooseBasis k (k ⊗[R] N)
--   letI : IsNoetherian k (k ⊗[R] (I →₀ R)) :=
--     isNoetherian_of_isNoetherianRing_of_finite k (k ⊗[R] (I →₀ R))
--   choose f hf using TensorProduct.mk_surjective R N k Ideal.Quotient.mk_surjective
--   let i := Finsupp.total I N R (f ∘ b)
--   -- have hi : Surjective i := by
--   --   rw [← LinearMap.range_eq_top, Finsupp.range_total]
--   --   exact LocalRing.exists_tmul_eq_basis (R := R) (f := f ∘ b) b (fun _ ↦ hf _)
--   -- have : Function.Surjective (i.baseChange k) := LinearMap.lTensor_surjective _ hi
--   have : Function.Bijective (i.baseChange k) := by
--     refine ⟨?_, this⟩
--     rw [← LinearMap.ker_eq_bot (M := k ⊗[R] (I →₀ R)) (f := i.baseChange k),
--       ← Submodule.finrank_eq_zero (R := k) (M := k ⊗[R] (I →₀ R)),
--       ← Nat.add_right_inj (n := FiniteDimensional.finrank k (LinearMap.range <| i.baseChange k)),
--       LinearMap.finrank_range_add_finrank_ker (V := k ⊗[R] (I →₀ R)),
--       LinearMap.range_eq_top.mpr this, finrank_top]
--     simp only [FiniteDimensional.finrank_tensorProduct, FiniteDimensional.finrank_self,
--       FiniteDimensional.finrank_finsupp_self, one_mul, add_zero]
--     rw [FiniteDimensional.finrank_eq_card_chooseBasisIndex]




-- theorem LocalRing.split_injective_iff_lTensor_injective (l : M →ₗ[R] N) :
--     (∃ l', l' ∘ₗ l = LinearMap.id) ↔ Function.Injective (l.lTensor (ResidueField R)) := by
--   constructor
--   · intro ⟨l', hl⟩
--     have : l'.lTensor (ResidueField R) ∘ₗ l.lTensor (ResidueField R) = .id := by
--       rw [← LinearMap.lTensor_comp, hl, LinearMap.lTensor_id]
--     exact Function.HasLeftInverse.injective ⟨_, LinearMap.congr_fun this⟩
--   · intro h




-- section mess

-- variable {A B C A' B' D F₁ F₀} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
--   [AddCommGroup C] [Module R C] [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
--   [AddCommGroup D] [Module R D] [AddCommGroup F₁] [Module R F₁] [AddCommGroup F₀] [Module R F₀]

-- variable {f : A →ₗ[R] B} {g : B →ₗ[R] C} {f' : A' →ₗ[R] B'} {g' : B' →ₗ[R] C}
-- variable {i₁ : F₁ →ₗ[R] F₀} {i₀ : F₀ →ₗ[R] C}
-- variable (h : Function.Exact f g) (h' : Function.Exact f' g') (hi : Function.Exact i₁ i₀)
-- variable [Module.Flat R B] [Module.Flat R F₁] [Module.Flat R F₀]




-- end mess




-- end

-- proof_wanted Algebra.FormallySmooth.iff_localization_prime :
--   Algebra.FormallySmooth R S ↔
--     ∀ (p : Ideal S) (_ : p.IsPrime), Algebra.FormallySmooth R (Localization.AtPrime p)

-- proof_wanted Algebra.FormallySmooth.iff_localization_span_finset
--     (s : Finset S) (_ : Ideal.span (s : Set S) = ⊤) :
--   Algebra.FormallySmooth R S ↔
--     ∀ f ∈ s, Algebra.FormallySmooth R (Localization.Away f)

-- proof_wanted Algebra.FormallySmooth.iff_localization_span (s : Set S) (_ : Ideal.span s = ⊤) :
--   Algebra.FormallySmooth R S ↔
--     ∀ f ∈ s, Algebra.FormallySmooth R (Localization.Away f)
