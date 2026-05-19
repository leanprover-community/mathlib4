/-
Copyright (c) 2026 Jingting Wang, Nailin Guan, Yi Yuan, Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Nailin Guan, Yi Yuan, Yongle Hu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# Definition of Koszul complex
-/

@[expose] public section

universe u v

open CategoryTheory Category MonoidalCategory Limits Module ExteriorAlgebra

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R)

/-- The alternating map on `(n + 1)`-tuples whose induced linear map is the Koszul differential. -/
noncomputable def koszulComplexAuxAlternating (n : ℕ) :
    M [⋀^Fin (n + 1)]→ₗ[R] ⋀[R]^n M :=
  AlternatingMap.alternatizeUncurryFin (φ.smulRight (exteriorPower.ιMulti R n))

lemma koszulComplexAuxAlternating_apply (n : ℕ) (x : Fin (n + 1) → M) :
    koszulComplexAuxAlternating φ n x =
      ∑ i : Fin (n + 1),
        ((-1 : R) ^ (i : ℕ) * φ (x i)) • exteriorPower.ιMulti R n (i.removeNth x) := by
  rw [koszulComplexAuxAlternating, AlternatingMap.alternatizeUncurryFin_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  have hremove : x ∘ i.succAbove = i.removeNth x := rfl
  simp [LinearMap.smulRight_apply, AlternatingMap.smul_apply, ← hremove,
    ← Int.cast_smul_eq_zsmul R, smul_smul]

/-- The auxiliary differential used to build the Koszul complex. -/
noncomputable def koszulComplexAux (n : ℕ) : ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M :=
  exteriorPower.alternatingMapLinearEquiv (koszulComplexAuxAlternating (R := R) (M := M) φ n)

lemma koszulComplexAux_comp_eq_zero (n : ℕ) :
    koszulComplexAux φ n ∘ₗ koszulComplexAux φ (n + 1) = 0 := by
  let β : M →ₗ[R] M →ₗ[R] M [⋀^Fin n]→ₗ[R] ⋀[R]^n M :=
    φ.smulRight (φ.smulRight (exteriorPower.ιMulti R n))
  have hβ : ∀ x y, β x y = β y x := by
    intro x y
    ext v
    simp [β, smul_smul, mul_comm]
  -- Unfold the concrete Koszul composite into the twice-uncurried alternating construction.
  have hcomp :
      (koszulComplexAux φ n).compAlternatingMap (koszulComplexAuxAlternating φ (n + 1)) =
        AlternatingMap.alternatizeUncurryFin (AlternatingMap.alternatizeUncurryFinLM ∘ₗ β) := by
    ext v
    simp [koszulComplexAux, koszulComplexAuxAlternating, β,
      AlternatingMap.alternatizeUncurryFin_apply, Finset.smul_sum, map_sum, smul_smul]
  -- Transport the linear-map composite to the alternating-map side,
  -- where the symmetry theorem applies directly.
  rw [show koszulComplexAux φ (n + 1) =
      exteriorPower.alternatingMapLinearEquiv (koszulComplexAuxAlternating φ (n + 1)) by rfl]
  rw [← exteriorPower.alternatingMapLinearEquiv_comp]
  rw [LinearEquiv.map_eq_zero_iff]
  rw [hcomp]
  exact AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric hβ

set_option backward.isDefEq.respectTransparency false in
noncomputable def koszulComplex : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of
    (ModuleCat.of R M).exteriorPower
    (fun n ↦ ModuleCat.ofHom (koszulComplexAux φ n))
    (fun n ↦ by simp [← ModuleCat.ofHom_comp, koszulComplexAux_comp_eq_zero])

lemma X_eq_exteriorPower (i : ℕ) : (koszulComplex φ).X i = ModuleCat.of R (⋀[R]^i M) := rfl

lemma d_eq_koszulComplexAux (i : ℕ) :
    (koszulComplex φ).d (i + 1) i = ModuleCat.ofHom (koszulComplexAux φ i) := by
  simp [koszulComplex]

section DifferentialGradedAlgebra

end DifferentialGradedAlgebra

namespace koszulComplex

variable {N : Type v} [AddCommGroup N] [Module R N]

noncomputable def ofList (l : List R) := koszulComplex (Fintype.linearCombination R l.get)

section functoriality

lemma mapAuxAlternating_apply (f : M →ₗ[R] N) (φ' : N →ₗ[R] R) (h : φ' ∘ₗ f = φ)
    (i : ℕ) (v : Fin (i + 1) → M) :
    ((koszulComplexAuxAlternating φ' i) (f ∘ v) : ⋀[R]^i N) =
      exteriorPower.map i f ((koszulComplexAuxAlternating φ i) v) := by
  calc
    _ = ∑ x : Fin (i + 1), (-1) ^ (x : ℕ) • φ' (f (v x)) •
          exteriorPower.ιMulti R i (x.removeNth (f ∘ v)) := by
      simp [koszulComplexAuxAlternating, AlternatingMap.alternatizeUncurryFin_apply]
    _ = ∑ x : Fin (i + 1), (-1) ^ (x : ℕ) • φ (v x) •
          exteriorPower.ιMulti R i (f ∘ x.removeNth v) := by
      refine Finset.sum_congr rfl (fun x hx ↦ ?_)
      simp only [← h, LinearMap.coe_comp, Function.comp_apply]
      rfl
    _ = exteriorPower.map i f ((koszulComplexAuxAlternating φ i) v) := by
      rw [koszulComplexAuxAlternating, AlternatingMap.alternatizeUncurryFin_apply]
      simp [map_sum, map_smul, exteriorPower.map_apply_ιMulti]

lemma map_aux_comm (f : M →ₗ[R] N) (φ' : N →ₗ[R] R) (h : φ' ∘ₗ f = φ) (i : ℕ) :
    ModuleCat.ofHom (exteriorPower.map (i + 1) f) ≫ ModuleCat.ofHom (koszulComplexAux φ' i) =
      ModuleCat.ofHom (koszulComplexAux φ i) ≫ ModuleCat.ofHom (exteriorPower.map i f) := by
  ext v
  simp [koszulComplexAux, mapAuxAlternating_apply (φ := φ) (f := f) (φ' := φ') h]

noncomputable def map (f : M →ₗ[R] N) (φ' : N →ₗ[R] R) (h : φ' ∘ₗ f = φ) :
    koszulComplex φ ⟶ koszulComplex φ' :=
  ChainComplex.ofHom
    (fun i ↦ ModuleCat.ofHom (exteriorPower.map i f))
    (fun i ↦ by simpa [d_eq_koszulComplexAux] using map_aux_comm φ f φ' h i)

variable {L : Type v} [AddCommGroup L] [Module R L]

variable {φ} in
lemma map_comp_condition {f : M →ₗ[R] N} {φ' : N →ₗ[R] R} {g : N →ₗ[R] L} {φ'' : L →ₗ[R] R}
    (h : φ' ∘ₗ f = φ) (h' : φ'' ∘ₗ g = φ') : φ'' ∘ₗ (g ∘ₗ f) = φ := by
  simp [← h, ← h', LinearMap.comp_assoc]

lemma map_comp (f : M →ₗ[R] N) (φ' : N →ₗ[R] R) (g : N →ₗ[R] L) (φ'' : L →ₗ[R] R)
    (h : φ' ∘ₗ f = φ) (h' : φ'' ∘ₗ g = φ') :
    koszulComplex.map φ f φ' h ≫ koszulComplex.map φ' g φ'' h' =
      koszulComplex.map φ (g ∘ₗ f) φ'' (map_comp_condition h h') := by
  ext i x
  simp [map, X_eq_exteriorPower, exteriorPower.map_comp]

noncomputable def isoOfEquiv (f : M ≃ₗ[R] N) (φ' : N →ₗ[R] R) (h : φ' ∘ₗ f = φ) :
    koszulComplex φ ≅ koszulComplex φ' where
  hom := koszulComplex.map φ f φ' h
  inv := koszulComplex.map φ' f.symm φ ((f.comp_toLinearMap_symm_eq φ' φ).mpr h.symm)
  hom_inv_id := by
    ext i x
    simp [map, X_eq_exteriorPower, ← exteriorPower.map_comp]
  inv_hom_id := by
    ext i x
    simp [map, X_eq_exteriorPower, ← exteriorPower.map_comp]

end functoriality

section specialX

noncomputable def XZeroLinearEquivRing : (koszulComplex φ).X 0 ≃ₗ[R] R :=
  exteriorPower.zeroEquiv R M

set_option backward.isDefEq.respectTransparency false in
lemma X_isZero_of_card_generators_le {ι : Type*} [Finite ι] [LinearOrder ι] (g : ι → M)
    (hg : Submodule.span R (Set.range g) = ⊤) (i : ℕ) (hi : Nat.card ι < i) :
    IsZero ((koszulComplex φ).X i) :=
  ModuleCat.isZero_of_iff_subsingleton.mpr (subsingleton_of_card_generators_le R M g hg i hi)

lemma ofList_X_isZero_of_length_le (l : List R) (i : ℕ) (hi : l.length < i) :
    IsZero ((ofList l).X i) := X_isZero_of_card_generators_le _
  (Pi.basisFun R (Fin l.length)) (Pi.basisFun R (Fin l.length)).span_eq i
  (by simpa [Nat.card_eq_fintype_card] using hi)

end specialX

section H0

noncomputable def zeroHomologyLinearEquiv (l : List R) :
    (ofList l).homology 0 ≃ₗ[R] R ⧸ Ideal.ofList l := sorry

end H0

section regular

open RingTheory.Sequence

lemma exactAt_of_isRegular (rs : List R) (reg : IsRegular R rs)
    (i : ℕ) (lt : i ≠ 0) : (ofList rs).ExactAt i := by
  sorry

end regular

section change_generators

lemma nonempty_linearEquiv_of_minimal_generators' [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤)
    (l l' : List R) (hl : Ideal.ofList l = I) (hl' : Ideal.ofList l' = I)
    (hl_min : l.length = I.spanFinrank) (hl'_min : l'.length = I.spanFinrank) :
  ∃ e : (Fin l.length → R) ≃ₗ[R] (Fin l'.length → R), e l.get = l'.get := sorry

theorem nonempty_iso_of_minimal_generators [IsLocalRing R]
    {I : Ideal R} (hI : I ≠ ⊤) {l l' : List R}
    (hl : Ideal.ofList l = I) (hl' : Ideal.ofList l' = I)
    (hl_min : l.length = I.spanFinrank) (hl'_min : l'.length = I.spanFinrank) :
    Nonempty <| ofList l ≅ ofList l' := by
  obtain ⟨e, h⟩ := nonempty_linearEquiv_of_minimal_generators' I hI l l' hl hl' hl_min hl'_min
  have h' : Fintype.linearCombination R l'.get ∘ₗ e = Fintype.linearCombination R l.get := by
    sorry
  exact ⟨isoOfEquiv _ e _ h'⟩

theorem nonempty_iso_of_minimal_generators'
    [IsNoetherianRing R] [IsLocalRing R] {I : Ideal R} (hI : I ≠ ⊤) {l : List R}
    (eq : Ideal.ofList l = I) (min : l.length = I.spanFinrank) :
    Nonempty (ofList (Submodule.FG.finite_generators I.fg_of_isNoetherianRing).toFinset.toList ≅
      ofList l) := by
  refine nonempty_iso_of_minimal_generators hI ?_ eq ?_ min
  · simp only [Ideal.ofList, Finset.mem_toList, Set.Finite.mem_toFinset, Set.setOf_mem_eq]
    exact I.span_generators
  · simp only [Finset.length_toList, ← Set.ncard_eq_toFinset_card _ _]
    exact Submodule.FG.generators_ncard Submodule.FG.of_finite

end change_generators

section basechange

variable (S : Type (max u v)) [CommRing S] (f : R →+* S)

instance (T : Type v) [CommRing T] (g : R →+* T) :
    (ModuleCat.extendScalars.{u, v, u} g).Additive where
  map_add {X Y a b} := by
    simp only [ModuleCat.extendScalars, ModuleCat.ExtendScalars.map',
      ModuleCat.hom_add, LinearMap.baseChange_add]
    rfl

open TensorProduct in
noncomputable def baseChange_iso (l : List R) (l' : List S) (eqmap : l.map f = l') :
    ofList l' ≅ ((ModuleCat.extendScalars f).mapHomologicalComplex _).obj (ofList l) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ LinearEquiv.toModuleIso ?_) (fun i j ↦ ?_)
  · sorry
  · sorry

end basechange

end koszulComplex
