/-
Copyright (c) 2024 Antoine Chambert-Loir, Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Oliver Nash
-/

import Mathlib.FieldTheory.Perfect
import Mathlib.Order.Sublattice
import Mathlib.LinearAlgebra.EigenSpace.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.AdjoinRoot

/-!
# Jordan-Chevalley-Dunford decomposition of a linear operator (additive version)

-/


open Ideal Polynomial

open Set Function

section

/- # Attempt to define invariantSubspace using the R[X]-module structure on V -/

variable {R V : Type*} [CommSemiring R] [AddCommGroup V] [Module R V]

def LinearMap.polynomialModule (_ : V →ₗ[R] V) := V

variable (f : V →ₗ[R] V)

instance : AddCommGroup f.polynomialModule := inferInstanceAs (AddCommGroup V)

instance : Module R[X] f.polynomialModule := Module.compHom V (aeval f).toRingHom

instance : Module R f.polynomialModule := inferInstanceAs (Module R V)

instance : IsScalarTower R R[X] f.polynomialModule := ⟨fun t p v ↦ by
  change aeval f (t • p) v = t • aeval f p v
  simp only [map_smul, LinearMap.smul_apply]⟩

example : CompleteLattice (Submodule R V) := Submodule.completeLattice

example : CompleteLattice (Submodule R[X] f.polynomialModule) := Submodule.completeLattice

example : CompleteLatticeHom (Submodule R[X] f.polynomialModule) (Submodule R V) where
  toFun := fun W ↦ {
    carrier := W.carrier
    add_mem' := by
      simp only [Submodule.mem_carrier, SetLike.mem_coe]
      apply Submodule.add_mem
    zero_mem' := by
      simp only [Submodule.mem_carrier, SetLike.mem_coe]
      exact Submodule.zero_mem W
    smul_mem' := by
      simp only [Submodule.mem_carrier, SetLike.mem_coe]
      intro c r hx
      refine Submodule.smul_of_tower_mem W c hx }
  map_sInf' s := by
    ext (v : f.polynomialModule)
    simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup, Submodule.mem_sInf, mem_image,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    convert Submodule.mem_sInf
  map_sSup' s := by
    sorry

end

section InvariantSubspace

namespace LinearMap

-- variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
-- variable (f : V →ₗ[K] V)

variable {R V : Type*} [CommSemiring R] [AddCommGroup V] [Module R V]
variable (f : V →ₗ[R] V)

/-- The lattice of invariant subspaces of a linear endomorphism -/
def invariantSubspace : Sublattice (Submodule R V) where
  carrier := {p | MapsTo f p p}
  supClosed' := by
    intro p hp q hq x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    exact map_add f _ _ ▸ Submodule.add_mem_sup (hp hy) (hq hz)
  infClosed' := fun p hp q hq x hx ↦ ⟨hp hx.1, hq hx.2⟩

namespace invariantSubspace

theorem injective_coeSubmodule :
    Injective ((↑) : f.invariantSubspace → Submodule R V) := fun x y h ↦ by
  cases x; cases y; congr

instance instTop : Top f.invariantSubspace := ⟨⊤, fun _ _ ↦ mem_univ _⟩

instance instBot : Bot f.invariantSubspace := ⟨⊥, fun x hx ↦ by
  replace hx : x = 0 := by simpa using hx
  simp [hx]⟩

instance instSupSet : SupSet f.invariantSubspace where
  sSup S := ⟨sSup {(p : Submodule R V) | p ∈ S}, by
    intro x hx
    simp only [Subtype.exists, exists_and_right, exists_eq_right, SetLike.mem_coe,
      Submodule.mem_sSup, mem_setOf_eq, forall_exists_index] at hx ⊢
    intro q hq
    refine hx (q.comap f) fun p (hp : p ≤ p.comap f) hp' ↦ ?_
    exact le_trans hp <|Submodule.comap_mono <| hq p hp hp'⟩

instance instInfSet : InfSet f.invariantSubspace where
  sInf S := ⟨sInf {(p : Submodule R V) | p ∈ S}, by
    rintro x hx - ⟨p, rfl⟩
    simp only [Subtype.exists, exists_and_right, exists_eq_right, mem_setOf_eq, iInter_exists,
      mem_iInter, Submodule.sInf_coe] at hx ⊢
    exact fun hp hp' ↦ hp (hx p hp hp')⟩

lemma coe_sup (p q : f.invariantSubspace) : (↑(p ⊔ q) : Submodule R V) = ↑p ⊔ ↑q := rfl

lemma coe_inf (p q : f.invariantSubspace) : (↑(p ⊓ q) : Submodule R V) = ↑p ⊓ ↑q := rfl

@[simp]
theorem sSup_coe_toSubmodule (S : Set f.invariantSubspace) :
    (↑(sSup S) : Submodule R V) = sSup {(s : Submodule R V) | s ∈ S} :=
  rfl

theorem sSup_coe_toSubmodule' (S : Set f.invariantSubspace) :
    (↑(sSup S) : Submodule R V) = ⨆ p ∈ S, (p : Submodule R V) := by
  rw [sSup_coe_toSubmodule, ← Set.image, sSup_image]

@[simp]
theorem sInf_coe_toSubmodule (S : Set f.invariantSubspace) :
    (↑(sInf S) : Submodule R V) = sInf {(s : Submodule R V) | s ∈ S} :=
  rfl

theorem sInf_coe_toSubmodule' (S : Set f.invariantSubspace) :
    (↑(sInf S) : Submodule R V) = ⨅ p ∈ S, (p : Submodule R V) := by
  rw [sInf_coe_toSubmodule, ← Set.image, sInf_image]

instance instCompleteLattice : CompleteLattice f.invariantSubspace :=
  { (invariantSubspace.injective_coeSubmodule f).completeLattice
      (↑) (coe_sup f) (coe_inf f) (sSup_coe_toSubmodule' f) (sInf_coe_toSubmodule' f) rfl rfl with }

end invariantSubspace

/-- The lattice of invariant subspaces of a linear endomorphism -/
protected abbrev IsSemisimple := ComplementedLattice f.invariantSubspace

end LinearMap

end InvariantSubspace


section Restriction

namespace LinearMap

open Polynomial

variable {R V : Type*} [CommSemiring R] [AddCommGroup V] [Module R V]
variable (f : V →ₗ[R] V)

lemma self_mul_aeval_eq_aeval_mul_self (f : V →ₗ[R] V) (P : R[X]) (v : V) :
  aeval f P (f v) = f (aeval f P v) := by
  suffices : (aeval f P) * f = f * (aeval f P)
  have := LinearMap.congr_fun this v
  simp only [mul_apply] at this
  simp only [this]
  nth_rewrite 2 [← aeval_X (R := R) f]
  nth_rewrite 3 [← aeval_X (R := R) f]
  simp only [← _root_.map_mul, mul_comm]

lemma aeval_ker_mem_invariantSubspace (f : V →ₗ[R] V) (P : R[X]) :
    ker (aeval f P) ∈ invariantSubspace f := by
  intro v
  simp only [SetLike.mem_coe, mem_ker, self_mul_aeval_eq_aeval_mul_self]
  intro hv
  rw [hv, map_zero]

lemma aeval_image_mem_invariantSubspace (f : V →ₗ[R] V) (P : R[X]) :
    LinearMap.range (Polynomial.aeval f P) ∈ invariantSubspace f := by
  intro v
  simp only [SetLike.mem_coe, mem_range]
  rintro ⟨w, rfl⟩
  use f w
  rw [self_mul_aeval_eq_aeval_mul_self]

lemma aeval_mapsTo (f : V →ₗ[R] V) (W : invariantSubspace f) (p : R[X]) :
    MapsTo (aeval f p) W W := by
  induction p using Polynomial.induction_on' with
  | h_add p q hp hq =>
    exact fun w hw ↦ by
      simp only [map_add, add_apply, SetLike.mem_coe]
      exact add_mem (hp hw) (hq hw)
  | h_monomial n c =>
    induction n with
    | zero =>
      exact fun w hw ↦ by
        simp only [Nat.zero_eq, monomial_zero_left, aeval_C, Module.algebraMap_end_apply,
          SetLike.mem_coe]
        convert Submodule.smul_mem  _ _ hw
    | succ n hn =>
      exact fun w hw ↦ by
        specialize hn hw
        simp only [aeval_monomial, mul_apply, Module.algebraMap_end_apply, pow_succ]
        rw [← map_smul]
        simp only [aeval_monomial, mul_apply, Module.algebraMap_end_apply, SetLike.mem_coe] at hn
        exact W.prop hn

lemma aeval_restrict_apply (f : V →ₗ[R] V) (W : invariantSubspace f) (p : R[X]) (w : ↑W) :
    aeval (restrict f W.prop) p w = aeval f p w := by
  induction p using Polynomial.induction_on' with
  | h_add p q hp hq =>
    simp only [map_add, add_apply, AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, hp, hq]
  | h_monomial n c =>
    induction n with
    | zero =>
      simp only [Nat.zero_eq, monomial_zero_left, aeval_C, Module.algebraMap_end_apply,
        SetLike.val_smul]
    | succ n hn =>
      simp only [aeval_monomial, mul_apply, Module.algebraMap_end_apply, SetLike.val_smul] at hn ⊢
      simp only [pow_succ, mul_apply, restrict_coe_apply]
      rw [← map_smul, hn, map_smul]

lemma aeval_restrict_eq (f : V →ₗ[R] V) (W : invariantSubspace f) (p : R[X]) :
    aeval (LinearMap.restrict f W.prop) p =
      LinearMap.restrict (aeval f p) (aeval_mapsTo f W p) := by
  ext w
  rw [aeval_restrict_apply, restrict_coe_apply]

end LinearMap

end Restriction

section Semisimple

namespace LinearMap

open Polynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The minimal polynomial of a semisimple endomorphism is square free -/
theorem minpoly_squarefree_of_isSemisimple [Module.Finite K V]
    (f : V →ₗ[K] V) (hf : f.IsSemisimple) : Squarefree (minpoly K f) := by
  classical
  intro p hp
  have hp' : p ≠ 0
  · intro hp'
    simp only [hp', mul_zero, zero_dvd_iff] at hp
    apply minpoly.ne_zero (A := K) (x := f) ?_ hp
    apply LinearMap.isIntegral
  by_contra hf'
  obtain ⟨q, hq⟩ := UniqueFactorizationMonoid.exists_mem_factors hp' hf'
  have hq' := UniqueFactorizationMonoid.irreducible_of_factor q hq
  have hq_dvd_p : q ∣ p := UniqueFactorizationMonoid.dvd_of_mem_factors hq
  have hq2_dvd_p2 : q * q ∣ p * p := mul_dvd_mul hq_dvd_p hq_dvd_p
  let W : invariantSubspace f := ⟨LinearMap.ker (Polynomial.aeval f q), aeval_ker_mem_invariantSubspace f q⟩
  obtain ⟨W', hWW'⟩ := hf.exists_isCompl W
  let f' := f.restrict W'.prop
  suffices lemma1 : minpoly K f ∣ q * minpoly K f'
  · have := dvd_trans (dvd_trans hq2_dvd_p2 hp) lemma1
    rw [mul_dvd_mul_iff_left (Irreducible.ne_zero hq')] at this
    obtain ⟨r, hr⟩ := this
    suffices : minpoly K f' ∣ r
    rw [hr] at this
    nth_rewrite 2 [← one_mul r] at this
    rw [mul_dvd_mul_iff_right, ← isUnit_iff_dvd_one] at this
    exact hq'.not_unit this
    · intro hr'
      simp only [hr', mul_zero] at hr
      apply minpoly.ne_zero (A := K) (LinearMap.isIntegral _) hr
    · apply minpoly.dvd
      apply LinearMap.ext
      rintro ⟨w, hw⟩
      simp only [zero_apply]
      rw [← Subtype.coe_inj]
      suffices : ∀ (x : V) (_ : x ∈ W.val) (_ : x ∈ W'.val), x = 0
      · apply this
        · simp only [W, LinearMap.mem_ker, LinearMap.aeval_restrict_apply]
          rw [← LinearMap.mul_apply, ← _root_.map_mul, ← hr]
          have := minpoly.aeval K f'
          simp only [f', LinearMap.ext_iff] at this
          specialize this ⟨w, hw⟩
          rw [← Subtype.coe_inj, aeval_restrict_apply] at this
          exact this
        · apply Submodule.coe_mem
      intro x hx hx'
      rw [← Submodule.mem_bot K]
      have := congr_arg Subtype.val (disjoint_iff.mp hWW'.disjoint)
      change _ = ⊥ at this
      rw [← this, Sublattice.coe_inf, Submodule.mem_inf]
      exact ⟨hx, hx'⟩
  · apply minpoly.dvd
    ext v
    conv_rhs => rw [zero_apply, ← add_zero 0]
    have hv_mem : v ∈ ⊤ := Submodule.mem_top (R := K)
    let h' := congr_arg Subtype.val (codisjoint_iff.mp hWW'.codisjoint)
    change _ = ⊤ at h'
    rw [← h', Sublattice.coe_sup, Submodule.mem_sup] at hv_mem
    obtain ⟨w, hw, w', hw', rfl⟩ := hv_mem
    rw [map_add]
    apply congr_arg₂
    · rw [mul_comm, _root_.map_mul, mul_apply]
      convert map_zero _
    · simp only [_root_.map_mul, mul_apply]
      convert map_zero _
      have := minpoly.aeval K f'
      simp only [f', LinearMap.ext_iff] at this
      specialize this ⟨w', hw'⟩
      rw [← Subtype.coe_inj, aeval_restrict_apply] at this
      exact this

end LinearMap

end Semisimple

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (f : V →ₗ[K] V)

section

open Polynomial

variable (p : K[X]) (hirr : Fact (Irreducible p)) (hdvd : p ∣ minpoly K f)

noncomputable
example : Field (K[X] ⧸ (Ideal.span {p})) := AdjoinRoot.field
  /-
  have : Ideal.IsMaximal (Ideal.span {p}) := AdjoinRoot.span_maximal_of_irreducible
  refine Ideal.Quotient.field (Ideal.span {p}) -/




noncomputable
def Ideal.module_of_quotient {R : Type*} [CommRing R] (I : Ideal R)
    (V : Type*) [AddCommGroup V] [Module R V]
    (h : ∀ a ∈ I, ∀ v : V, a • v = 0) : Module (R⧸I) V :=
  let h' : ∀ (r s : R) (v : V), Ideal.Quotient.mk I s = Ideal.Quotient.mk I r → s • v = r • v :=
    fun r s v hrs => by
    rw [← sub_eq_zero, ← sub_smul]
    exact h _ (Ideal.Quotient.eq.mp hrs) _
  let smul_aux := fun (r : R⧸I) (v : V) => (Ideal.Quotient.mk_surjective r).choose • v
  let smul_aux_eq : ∀ r v, smul_aux r v = (Ideal.Quotient.mk_surjective r).choose • v := fun _ _ => rfl
  { smul := smul_aux
    one_smul := fun v => by
      conv_rhs => rw [← one_smul R v]
      change smul_aux 1 v = _
      rw [smul_aux_eq]
      apply h'
      rw [(Ideal.Quotient.mk_surjective (1 : R ⧸ I)).choose_spec, map_one]
    mul_smul := fun r s v => by
      change smul_aux (r * s) v = smul_aux r (smul_aux s v)
      simp only [smul_aux_eq, ← mul_smul]
      apply h'
      simp only [_root_.map_mul]
      simp only [(Ideal.Quotient.mk_surjective (_ : R ⧸ I)).choose_spec]
    smul_zero := fun r => by
      change smul_aux _ _ = 0
      rw [smul_aux_eq, smul_zero]
    smul_add := fun r v w => by
      change smul_aux _ _ = smul_aux _ _ + smul_aux _ _
      simp only [smul_aux_eq, ← smul_add]
    add_smul := fun r s v => by
      change smul_aux _ _ = smul_aux _ _ + smul_aux _ _
      simp only [smul_aux_eq, ← add_smul]
      apply h'
      simp only [map_add]
      simp only [(Ideal.Quotient.mk_surjective (_ : R ⧸ I)).choose_spec]
    zero_smul := fun v => by
      change smul_aux _ _ = _
      simp only [smul_aux_eq]
      conv_rhs => rw [← zero_smul R v]
      apply h'
      simp only [(Ideal.Quotient.mk_surjective (_ : R ⧸ I)).choose_spec, map_zero] }

example (f : V →ₗ[K] V) : K[X] →ₐ[K] V →ₗ[K] V := aeval f

example (f : V →ₗ[K] V) : Module K[X] V :=
  Module.compHom _ (aeval f).toRingHom

example {R : Type*} [CommSemiring R] {S : Type*} [Semiring S] [Algebra R S]
  {V : Type*} [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V] :
    S →ₐ[R] V →ₗ[R] V := Algebra.lsmul R R V

example {R : Type*} [CommSemiring R] {S : Type*} [Semiring S] [Algebra R S]
  {V : Type*} [AddCommGroup V] [Module R V]
  (h : S →ₐ[R] V →ₗ[R] V) : Module S V :=
  Module.compHom _ h.toRingHom

example {R : Type*} [CommSemiring R] {V : Type*} [AddCommGroup V] [Module R V] :
  Module (V →ₗ[R] V) V := applyModule

theorem _root_.minpoly.dvd_iff {A : Type u_1} {B : Type u_2} [Field A] [Ring B]
    [Algebra A B] {x : B} {p : Polynomial A} :
    (Polynomial.aeval x) p = 0 ↔ minpoly A x ∣ p := by
  constructor
  · exact minpoly.dvd A x
  · rintro ⟨q, rfl⟩
    rw [_root_.map_mul, minpoly.aeval, zero_mul]

example (f : V →ₗ[K] V) (p : K[X]) (hp : minpoly K f ∣ p) :
    Module (AdjoinRoot p) V :=
  Module.compHom _ (AdjoinRoot.liftHom p f (minpoly.dvd_iff.mpr hp)).toRingHom



end

variable [PerfectField K] [FiniteDimensional K V]

def semisimpleComponent (f : V →ₗ[K] V) : V →ₗ[K] V :=
  sorry -- Data

def nilpotentComponent (f : V →ₗ[K] V) : V →ₗ[K] V := f - f.semisimpleComponent

lemma semisimpleComponent.IsSemisimple : f.semisimpleComponent.IsSemisimple :=
  sorry -- Prop

lemma nilpotentComponent.IsNilpotent : IsNilpotent f.nilpotentComponent :=
  sorry -- Prop

lemma Commute_semisimple_nilpotent : Commute f.semisimpleComponent f.nilpotentComponent :=
  sorry -- Prop

@[simp]
lemma semisimple_add_nilpotent_eq_self : f.semisimpleComponent + f.nilpotentComponent = f :=
  add_sub_cancel'_right (semisimpleComponent f) f

end LinearMap
