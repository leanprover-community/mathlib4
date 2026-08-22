import Mathlib.CFT.Junk
import Mathlib.CFT.Nonsense
import Mathlib.CFT.SeparableResidueStruct

open IsLocalRing

local notation "𝓀[" R "]" => ResidueField R
local notation "𝓂[" R "]" => maximalIdeal R

/-! Let `R` be a complete DVR. -/
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsAdicComplete 𝓂[R] R]

/-! ## Essentially surjective
    Each finite separable extension over `𝓀[R]` comes from some finite unramified extension. -/
example {K : Type} [Field K] [Algebra 𝓀[R] K]
    [FiniteDimensional 𝓀[R] K] [Algebra.IsSeparable 𝓀[R] K] :
    ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : IsDiscreteValuationRing S)
      (_ : Algebra R S) (_ : FaithfulSMul R S) (_ : Module.Finite R S)
      (_ : Algebra.Unramified R S), Nonempty (𝓀[S] ≃ₐ[𝓀[R]] K) := by
  obtain ⟨𝓟, ⟨e⟩⟩ := SeparableResidueStruct.exists_of_isSeparable (R := R) (K := K)
  exact ⟨𝓟.Ring, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ⟨e⟩⟩

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [IsDomain A] [IsDiscreteValuationRing A]
    [FaithfulSMul R A] [Module.Finite R A] [Algebra.Unramified R A]
    [IsDomain B] [IsDiscreteValuationRing B]
    [FaithfulSMul R B] [Module.Finite R B] [Algebra.Unramified R B]

/-! ## Full
    Every map between residue fields lifts to a map between the unramified extension. -/
example (f : 𝓀[A] →ₐ[𝓀[R]] 𝓀[B]) :
    ∃ (g : A →ₐ[R] B), ResidueField.map g.toRingHom = f.toRingHom :=
  ⟨_, (HenselianLocalRing.exist_residueFieldMap_eq_of_etale f).choose_spec.choose_spec⟩

/-! ## Faithful
    Every map between unramified extensions are equal if they are equal on the residue field. -/
example (f₁ f₂ : 𝓀[A] →ₐ[𝓀[R]] 𝓀[B])
    (H : ResidueField.map f₁.toRingHom = ResidueField.map f₂.toRingHom) : f₁ = f₂ :=
  HenselianLocalRing.eq_of_residueFieldMap_eq _ _ H

/-! ## Reflects isos
    Unramified extensions with isomorphic residue fields are isomorphic. -/
example (e : 𝓀[A] ≃ₐ[𝓀[R]] 𝓀[B]) :
    ∃ (g : A ≃ₐ[R] B), ResidueField.map g.toRingHom = e.toRingHom :=
  ⟨_, (HenselianLocalRing.exist_algEquiv_residueFieldMap_eq_of_etale e).choose_spec.choose_spec⟩
