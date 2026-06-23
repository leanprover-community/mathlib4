/-
Copyright (c) 2026 Nailin Guan, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Jingting Wang
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

def GradedAlgebra.linearGMul (h : k = i + j) : 𝒜 i →ₗ[R] (𝒜 j →ₗ[R] 𝒜 k) :=
  h ▸ DirectSum.gMulLHom (R := R) (A := fun n ↦ 𝒜 n)

@[simp]
lemma GradedAlgebra.linearGMul_eq_mul (h : k = i + j) (x : 𝒜 i) (y : 𝒜 j) :
    (GradedAlgebra.linearGMul 𝒜 h) x y = x.1 * y.1 := by
  subst h
  rfl

end GradedAlgebra

section

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

noncomputable abbrev koszulCocomplexAux (x : M) (n : ℕ) :
    ⋀[R]^n M →ₗ[R] ⋀[R]^(n + 1) M :=
  GradedAlgebra.linearGMul (fun i : ℕ ↦ ⋀[R]^i M) (add_comm n 1)
    ((exteriorPower.oneEquiv R M).symm x)

set_option backward.isDefEq.respectTransparency false in
variable {M} in
noncomputable def koszulCocomplex (x : M) : CochainComplex (ModuleCat.{max u v} R) ℕ :=
  CochainComplex.of
    (ModuleCat.of R M).exteriorPower
    (fun n ↦ ModuleCat.ofHom (koszulCocomplexAux R M x n))
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

/-- The differential of `koszulCocomplex R x` is exterior multiplication by `x` in each degree. -/
theorem d_eq_aux (x : M) (i : ℕ) :
    (koszulCocomplex R x).d i (i + 1) = ModuleCat.ofHom (koszulCocomplexAux R M x i) := by
  simp [koszulCocomplex]

noncomputable abbrev ofList (l : List R) :=
  koszulCocomplex R l.get

instance free [Module.Free R M] (x : M) (i : ℕ) : Module.Free R ((koszulCocomplex R x).X i) :=
  inferInstanceAs <| Module.Free R (⋀[R]^i M)

variable {M} {N : Type v} [AddCommGroup N] [Module R N]

section functoriality

set_option backward.isDefEq.respectTransparency false in
noncomputable def map (f : M →ₗ[R] N) {x : M} {y : N} (h : f x = y) :
    koszulCocomplex R x ⟶ koszulCocomplex R y :=
  CochainComplex.ofHom
    (fun i ↦ (ModuleCat.exteriorPower.functor R i).map (ModuleCat.ofHom f))
    (fun i ↦ ModuleCat.hom_ext <| LinearMap.ext fun z ↦ Subtype.ext
      (by simp [koszulCocomplex, ModuleCat.exteriorPower, ModuleCat.exteriorPower.map,
        koszulCocomplexAux, exteriorPower.oneEquiv_symm_apply, h]))

lemma map_hom (f : M →ₗ[R] N) (x : M) (y : N) (h : f x = y) (i : ℕ) :
    (map R f h).f i = (ModuleCat.exteriorPower.functor R i).map (ModuleCat.ofHom f) := rfl

lemma map_id_refl (x : M) : koszulCocomplex.map R (M := M) .id (Eq.refl x) = 𝟙 _ := by
  ext i x
  simp only [map_hom, ModuleCat.ofHom_id, ModuleCat.exteriorPower.functor_map,
    ModuleCat.exteriorPower.map, ModuleCat.hom_id, exteriorPower.map_id, HomologicalComplex.id_f,
    LinearMap.id_coe, id_eq]
  rfl

lemma map_id (x y : M) (h : x = y) : koszulCocomplex.map R (M := M) .id h =
  eqToHom (congrArg _ h) := by
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

noncomputable def XZeroLinearEquivRing (x : M) : (koszulCocomplex R x).X 0 ≃ₗ[R] R :=
  exteriorPower.zeroEquiv R M

/-- The top-cardinality subset type consists only of the full finite set. -/
@[reducible]
noncomputable instance uniquePowersetCardCard {ι : Type*} [Finite ι] :
    (Unique (Set.powersetCard ι (Nat.card ι))) where
  default :=
    letI : Fintype ι := Fintype.ofFinite ι
    Set.powersetCard.ofCard (s := Finset.univ) (by simp [Nat.card_eq_fintype_card])
  uniq s := by
    let : Fintype ι := Fintype.ofFinite ι
    apply Subtype.ext
    simp [← Finset.card_eq_iff_eq_univ]

noncomputable def topXLinearEquivOfBasis {ι : Type*} [Finite ι] [LinearOrder ι] (x : M)
    (b : Basis ι R M) : (koszulCocomplex R x).X (Nat.card ι) ≃ₗ[R] R :=
  (b.exteriorPower (Nat.card ι)).equivFun.trans (LinearEquiv.funUnique _ R R)

noncomputable def topXLinearEquivOfBasisOfList (l : List R) :
    (ofList R l).X l.length ≃ₗ[R] R := by
  have : l.length = Nat.card (Fin l.length) := by simp
  rw [this]
  exact topXLinearEquivOfBasis R l.get (Pi.basisFun R (Fin l.length))

lemma X_isZero_of_card_generators_le (x : M) {ι : Type*} [Finite ι] [LinearOrder ι] (g : ι → M)
    (hg : Submodule.span R (Set.range g) = ⊤) (i : ℕ) (hi : Nat.card ι < i) :
    IsZero ((koszulCocomplex R x).X i) :=
  ModuleCat.isZero_of_iff_subsingleton.mpr
    (exteriorPower.subsingleton_of_card_generators_le g hg i hi)

lemma ofList_X_isZero_of_length_le (l : List R) (i : ℕ) (hi : l.length < i) :
    IsZero ((koszulCocomplex.ofList R l).X i) :=
  X_isZero_of_card_generators_le R l.get
  (Pi.basisFun R (Fin l.length)) (Pi.basisFun R (Fin l.length)).span_eq i
  (by simpa [Nat.card_eq_fintype_card] using hi)

end specialX

end koszulCocomplex
#lint
