/-
Copyright (c) 2026 Jingting Wang, Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Data.Fin.Tuple.Sort

/-!
# Definition of Koszul cocomplex
-/

@[expose] public section

universe u v w w'

open CategoryTheory Category MonoidalCategory Limits Module

section GradedAlgebra

variable {ι R A : Type*} [DecidableEq ι] [AddMonoid ι]
    [CommSemiring R] [Semiring A] [Algebra R A] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {i j k : ι}

def GradedAlgebra.linearGMul (h : k = i + j) : 𝒜 i →ₗ[R] (𝒜 j →ₗ[R] 𝒜 k) := sorry

@[simp]
lemma GradedAlgebra.linearGMul_eq_mul (h : k = i + j) (x : 𝒜 i) (y : 𝒜 j) :
    (GradedAlgebra.linearGMul 𝒜 h) x y = x.1 * y.1 := sorry

end GradedAlgebra

section

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

set_option backward.isDefEq.respectTransparency false in
variable {M} in
noncomputable def koszulCocomplex (x : M) : CochainComplex (ModuleCat.{max u v} R) ℕ :=
  CochainComplex.of
    (ModuleCat.of R M).exteriorPower
    (fun n ↦ ModuleCat.ofHom (GradedAlgebra.linearGMul (fun i : ℕ ↦ ⋀[R]^i M) (add_comm n 1)
      ((exteriorPower.oneEquiv R M).symm x)))
    (fun n ↦ by
      simp only [← ModuleCat.ofHom_comp]
      congr
      refine LinearMap.ext fun x ↦ Subtype.ext ?_
      simp only [exteriorPower.oneEquiv_symm_apply, LinearMap.coe_comp, Function.comp_apply,
        GradedAlgebra.linearGMul_eq_mul, exteriorPower.ιMulti_apply_coe,
        ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one, ← mul_assoc,
        CliffordAlgebra.ι_sq_scalar, QuadraticMap.zero_apply, map_zero, zero_mul]
      rfl)

namespace koszulCocomplex

noncomputable abbrev ofList (l : List R) :=
  koszulCocomplex R l.get

instance free [Module.Free R M] (x : M) (i : ℕ) : Module.Free R ((koszulCocomplex R x).X i) :=
  inferInstanceAs <| Module.Free R (⋀[R]^i M)

variable {M} {N : Type v} [AddCommGroup N] [Module R N]

section functoriality

set_option backward.isDefEq.respectTransparency false in
noncomputable def map (f : M →ₗ[R] N) {x : M} {y : N} (h : f x = y) :
    koszulCocomplex R x ⟶ koszulCocomplex R y :=
  CochainComplex.ofHom _ _ _ _ _ _
    (fun i ↦ (ModuleCat.exteriorPower.functor R i).map (ModuleCat.ofHom f))
    (fun i ↦ by
      refine ModuleCat.hom_ext <| LinearMap.ext fun z ↦ Subtype.ext ?_
      simp only [ModuleCat.exteriorPower, ModuleCat.exteriorPower.functor_map,
        ModuleCat.exteriorPower.map, ModuleCat.hom_ofHom, ModuleCat.hom_comp, LinearMap.coe_comp,
        Function.comp_apply, GradedAlgebra.linearGMul_eq_mul, exteriorPower.coe_map,
        exteriorPower.oneEquiv_symm_apply, map_mul, exteriorPower.ιMulti_apply_coe,
        ExteriorAlgebra.map_apply_ιMulti]
      congr
      exact funext fun _ ↦ h.symm)

lemma map_hom (f : M →ₗ[R] N) (x : M) (y : N) (h : f x = y) (i : ℕ) :
    (map R f h).f i = (ModuleCat.exteriorPower.functor R i).map (ModuleCat.ofHom f) := rfl

lemma map_id_refl (x : M) : koszulCocomplex.map R (M := M) .id (Eq.refl x) = 𝟙 _ := by
  ext i x
  simp only [map_hom, ModuleCat.ofHom_id, ModuleCat.exteriorPower.functor_map,
    ModuleCat.exteriorPower.map, ModuleCat.hom_id, exteriorPower.map_id, HomologicalComplex.id_f,
    LinearMap.id_coe, id_eq]
  rfl

lemma map_id (x y : M) (h : x = y) :
    koszulCocomplex.map R (M := M) .id h = eqToHom (by rw [h]) := by
  subst h
  exact map_id_refl R x

set_option backward.isDefEq.respectTransparency false in
lemma map_comp {P : Type v} [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) {x : M} {y : N} {z : P} (hxy : f x = y) (hyz : g y = z) :
    koszulCocomplex.map R f hxy ≫ koszulCocomplex.map R g hyz =
    koszulCocomplex.map R (g ∘ₗ f) (hxy ▸ hyz : g (f x) = z) := by
  refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
  simp only [HomologicalComplex.comp_f, map_hom, ModuleCat.ofHom_comp, Functor.map_comp]

noncomputable def isoOfEquiv (f : M ≃ₗ[R] N) {x : M} {y : N} (h : f x = y) :
    koszulCocomplex R x ≅ koszulCocomplex R y where
  hom := koszulCocomplex.map R f h
  inv := koszulCocomplex.map R f.symm (f.injective (by simpa using h.symm))
  hom_inv_id := by
    simp only [map_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap]
    exact map_id_refl R x
  inv_hom_id := by
    simp only [map_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap]
    exact map_id_refl R y

end functoriality

section specialX

noncomputable def topXLinearEquivOfBasis {ι : Type*} [Finite ι] [LinearOrder ι] (x : M)
    (b : Basis ι R M) : (koszulCocomplex R x).X (Nat.card ι) ≃ₗ[R] R := by sorry

noncomputable def topXLinearEquivOfBasisOfList (l : List R) :
    (ofList R l).X l.length ≃ₗ[R] R := by
  have : l.length = Nat.card (Fin l.length) := by simp
  rw [this]
  exact topXLinearEquivOfBasis R l.get (Pi.basisFun R (Fin l.length))

set_option backward.isDefEq.respectTransparency false in
lemma X_isZero_of_card_generators_le (x : M) {ι : Type*} [Finite ι] (g : ι → M)
    (hg : Submodule.span R (Set.range g) = ⊤) (i : ℕ) (hi : Nat.card ι < i) :
    IsZero ((koszulCocomplex R x).X i) := by
  have hIsZero : IsZero (ModuleCat.of R (⋀[R]^i M)) := by
    apply ModuleCat.isZero_of_iff_subsingleton.mpr
    exact subsingleton_of_card_generators_le R M g hg i hi
  simpa [koszulCocomplex, ModuleCat.exteriorPower] using hIsZero

lemma ofList_X_isZero_of_length_le (l : List R) (i : ℕ) (hi : l.length < i) :
    IsZero ((koszulCocomplex.ofList R l).X i) :=
  X_isZero_of_card_generators_le R l.get
  (Pi.basisFun R (Fin l.length)) (Pi.basisFun R (Fin l.length)).span_eq i
  (by simpa [Nat.card_eq_fintype_card] using hi)

end specialX

section Htop

noncomputable def topHomologyLinearEquiv (l : List R) :
    (ofList R l).homology l.length ≃ₗ[R] R ⧸ Ideal.ofList l := sorry

end Htop

section regular

open RingTheory.Sequence

lemma exactAt_of_lt_length_of_isRegular (rs : List R) (reg : IsRegular R rs)
    (i : ℕ) (lt : i < rs.length) : (koszulCocomplex.ofList R rs).ExactAt i := by
  sorry

theorem exactAt_of_ne_length_of_isRegular (rs : List R) (reg : IsRegular R rs)
    (i : ℕ) (lt : i ≠ rs.length) : (koszulCocomplex.ofList R rs).ExactAt i := by
  sorry

end regular

section change_generators

lemma nonempty_linearEquiv_of_minimal_generators (I : Ideal R) (hI : I ≤ Ring.jacobson R)
    (l l' : List R) (hl : Ideal.ofList l = I) (hl' : Ideal.ofList l' = I)
    (hl_min : l.length = I.spanFinrank) (hl'_min : l'.length = I.spanFinrank) :
  ∃ e : (Fin l.length → R) ≃ₗ[R] (Fin l'.length → R), e l.get = l'.get := sorry

theorem nonempty_iso_of_minimal_generators [IsLocalRing R]
    {I : Ideal R} {l l' : List R}
    (hl : Ideal.ofList l = I) (hl' : Ideal.ofList l' = I)
    (hl_min : l.length = I.spanFinrank) (hl'_min : l'.length = I.spanFinrank) :
    Nonempty <| ofList R l ≅ ofList R l' := by
  have hI : I ≤ Ring.jacobson R := sorry
  obtain ⟨e, h⟩ := nonempty_linearEquiv_of_minimal_generators R I hI l l' hl hl' hl_min hl'_min
  exact ⟨isoOfEquiv R e h⟩

theorem nonempty_iso_of_minimal_generators'
    [IsNoetherianRing R] [IsLocalRing R] {I : Ideal R} {l : List R}
    (eq : Ideal.ofList l = I) (min : l.length = I.spanFinrank) :
    Nonempty <| ofList R I.finite_generators_of_isNoetherian.toFinset.toList ≅ ofList R l := by
  refine nonempty_iso_of_minimal_generators R ?_ eq ?_ min
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
    ofList S l' ≅ ((ModuleCat.extendScalars f).mapHomologicalComplex _).obj (ofList R l) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ LinearEquiv.toModuleIso ?_) (fun i j ↦ ?_)
  · sorry
  · sorry

end basechange

end koszulCocomplex
