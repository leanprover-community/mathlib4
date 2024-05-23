import Mathlib.RingTheory.Smooth.Projective
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

variable (R S M) in
theorem TensorProduct.mk_surjective (S) [CommRing S] [Algebra R S]
    (h : Surjective (algebraMap R S)) :
    Surjective (TensorProduct.mk R S M 1) := by
  rw [← LinearMap.range_eq_top, ← top_le_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
  rintro _ ⟨x, y, rfl⟩
  obtain ⟨x, rfl⟩ := h x
  rw [Algebra.algebraMap_eq_smul_one, smul_tmul]
  exact ⟨x • y, rfl⟩

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

theorem foo [Module.Finite R N] [Module.Flat R N]
    (hf : Function.Injective (f.lTensor k)) :
    Module.Free R P := by
  let I := Module.Free.ChooseBasisIndex k (k ⊗[R] N)
  let b : Basis I k _ := Module.Free.chooseBasis k (k ⊗[R] N)
  choose f hf using TensorProduct.mk_surjective R N k Ideal.Quotient.mk_surjective
  let i := Finsupp.total I N R (f ∘ b)
  have hi : Surjective i := by
    rw [← LinearMap.range_eq_top, Finsupp.range_total]
    exact LocalRing.exists_tmul_eq_basis (R := R) (f := f ∘ b) b (fun _ ↦ hf _)
  have : Function.Bijective (i.baseChange k) := by
    refine ⟨?_, LinearMap.lTensor_surjective _ hi⟩
    rw [← LinearMap.ker_eq_bot (M := k ⊗[R] (I →₀ R)) (f := i.baseChange k),
      ← Submodule.finrank_eq_zero,
      ← Nat.add_right_inj (n := FiniteDimensional.finrank k (LinearMap.range <| i.baseChange k)),
      LinearMap.finrank_range_add_finrank_ker (V := k ⊗[R] (I →₀ R)),
      finrank_tensorproduct]


theorem LocalRing.split_injective_iff_lTensor_injective (l : M →ₗ[R] N) :
    (∃ l', l' ∘ₗ l = LinearMap.id) ↔ Function.Injective (l.lTensor (ResidueField R)) := by
  constructor
  · intro ⟨l', hl⟩
    have : l'.lTensor (ResidueField R) ∘ₗ l.lTensor (ResidueField R) = .id := by
      rw [← LinearMap.lTensor_comp, hl, LinearMap.lTensor_id]
    exact Function.HasLeftInverse.injective ⟨_, LinearMap.congr_fun this⟩
  · intro h



section mess

variable {A B C A' B' D F₁ F₀} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
  [AddCommGroup D] [Module R D] [AddCommGroup F₁] [Module R F₁] [AddCommGroup F₀] [Module R F₀]

variable {f : A →ₗ[R] B} {g : B →ₗ[R] C} {f' : A' →ₗ[R] B'} {g' : B' →ₗ[R] C}
variable {i₁ : F₁ →ₗ[R] F₀} {i₀ : F₀ →ₗ[R] C}
variable (h : Function.Exact f g) (h' : Function.Exact f' g') (hi : Function.Exact i₁ i₀)
variable [Module.Flat R B] [Module.Flat R F₁] [Module.Flat R F₀]




end mess




end

proof_wanted Algebra.FormallySmooth.iff_localization_prime :
  Algebra.FormallySmooth R S ↔
    ∀ (p : Ideal S) (_ : p.IsPrime), Algebra.FormallySmooth R (Localization.AtPrime p)

proof_wanted Algebra.FormallySmooth.iff_localization_span_finset
    (s : Finset S) (_ : Ideal.span (s : Set S) = ⊤) :
  Algebra.FormallySmooth R S ↔
    ∀ f ∈ s, Algebra.FormallySmooth R (Localization.Away f)

proof_wanted Algebra.FormallySmooth.iff_localization_span (s : Set S) (_ : Ideal.span s = ⊤) :
  Algebra.FormallySmooth R S ↔
    ∀ f ∈ s, Algebra.FormallySmooth R (Localization.Away f)
