import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.FieldTheory.IntermediateField
import Mathlib.Data.Countable.Small
import Mathlib.Algebra.Algebra.Field

open DifferentialRing algebraMap

class DifferentialField (R : Type*) extends Field R, CommDifferentialRing R

def DifferentialField.equiv {R R2 : Type*} [Field R] [CommDifferentialRing R2] (h : R ≃+* R2) :
    DifferentialField R :=
  letI := CommDifferentialRing.equiv h
  DifferentialField.mk this.deriv

variable {R : Type*} [DifferentialField R] (a b : R)

def logd : R := a′ / a

@[simp]
lemma logd_zero : logd (0 : R) = 0 := by
  unfold logd
  simp

@[simp]
lemma logd_one : logd (1 : R) = 0 := by
  unfold logd
  simp

lemma logd_add (h₁ : a ≠ 0) (h₂ : b ≠ 0) : logd a + logd b = logd (a * b) := by
  unfold logd
  field_simp
  ring

lemma logd_sub (h₁ : a ≠ 0) (h₂ : b ≠ 0) : logd a - logd b = logd (a / b) := by
  unfold logd
  field_simp [Derivation.leibniz_div]
  ring

lemma nat_mul_logd (a : ℕ) : a * logd b = logd (b ^ a) := by
  by_cases h : b = 0
  · cases a <;> simp [h]
  induction a with
  | zero => simp
  | succ a h2 =>
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, h2, logd_add, pow_succ] <;>
  simp [h]

lemma logd_eq_zero_iff : logd a = 0 ↔ a′ = 0 :=
  ⟨fun h ↦ by simp only [logd, div_eq_zero_iff] at h; rcases h with h|h <;> simp [h],
  fun h ↦ by unfold logd at *; simp [h]⟩

lemma Multiset.logd_sum (ι : Type*) (s : Multiset ι) (f : ι → R) (h : ∀ x ∈ s, f x ≠ 0) :
    (s.map (fun x ↦ logd (f x))).sum = logd (s.map f).prod := by
  induction s using Multiset.induction_on
  · simp
  · rename_i h₂
    simp only [Function.comp_apply, Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons]
    rw [h₂]
    apply logd_add
    simp [h]
    apply Multiset.prod_ne_zero
    all_goals simp_all

lemma logd_sum (ι : Type*) (s : Finset ι) (f : ι → R) (h : ∀ x ∈ s, f x ≠ 0) :
    ∑ x ∈ s, logd (f x) = logd (∏ x ∈ s, f x) := Multiset.logd_sum _ _ _ h

lemma logd_sum_zero (ι : Type*) (s : Finset ι) (f : ι → R) (h : ∀ x ∈ s, f x = 0) :
    ∑ x ∈ s, logd (f x) = logd (∏ x ∈ s, f x) := by
  unfold logd
  simp_all

lemma logd_algebraMap {F K : Type*} [DifferentialField F] [DifferentialField K]
    [DifferentialAlgebra F K]
    (a : F) : logd (algebraMap F K a) = algebraMap F K (logd a) := by
  unfold logd
  simp [deriv_algebraMap]

@[norm_cast]
lemma algebraMap.coe_logd {F K : Type*} [DifferentialField F] [DifferentialField K]
    [DifferentialAlgebra F K]
    (a : F) : logd a = logd (a : K) := (logd_algebraMap a).symm

universe u v

class IsLiouville (F : Type u) (K : Type*) [DifferentialField F]
    [DifferentialField K] [DifferentialAlgebra F K] : Prop where
  is_liouville (a : F) (ι : Type u) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
    (u : ι → K) (v : K) (h : a = ∑ x, c x * logd (u x) + v′) :
    ∃ (ι' : Type u) (_ : Fintype ι') (c' : ι' → F) (_ : ∀ x, (c' x)′ = 0)
      (u' : ι' → F) (v' : F), a = ∑ x, c' x * logd (u' x) + v'′

instance IsLiouville.rfl (F : Type u) [DifferentialField F] : IsLiouville F F where
  is_liouville (a : F) (ι : Type u) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → F) (v : F) (h : a = ∑ x, c x * logd (u x) + v′) :=
    ⟨ι, _, c, hc, u, v, h⟩

lemma IsLiouville.trans {F : Type u} {K : Type v} {A : Type*} [DifferentialField F]
    [DifferentialField K] [DifferentialField A] [DifferentialAlgebra F K] [DifferentialAlgebra K A]
    [DifferentialAlgebra F A] [IsScalarTower F K A] [SharedConstants F K]
    (inst1 : IsLiouville F K) (inst2 : IsLiouville K A)
    : IsLiouville F A where
  is_liouville (a : F) (ι : Type u) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → A) (v : A) (h : a = ∑ x, c x * logd (u x) + v′) := by
    have : Fintype (Shrink.{v} ι) := Fintype.ofEquiv ι (equivShrink.{v} ι)
    obtain ⟨ι'', _, c'', hc', u'', v', h'⟩ := inst2.is_liouville (a : K) (Shrink.{v} ι)
        (fun (x : Shrink.{v} ι) ↦ c ((equivShrink.{v} ι).symm x)) (by
        intro
        simp only [← coe_deriv, lift_map_eq_zero_iff]
        apply hc
      ) (fun (x : Shrink.{v} ι) ↦ u ((equivShrink.{v} ι).symm x)) v (by
        convert h
        · simp only [← IsScalarTower.algebraMap_apply]
        · simp only [← IsScalarTower.algebraMap_apply]
          apply Equiv.sum_comp (g := fun x ↦ c x * logd (u x))
      )
    obtain ⟨ι' : Type u, ⟨eqv : ι'' ≃ ι'⟩⟩ := Small.equiv_small.{u, v} (α := ι'')
    have := Fintype.ofEquiv ι'' eqv
    have hc (x : ι'') := mem_of_constant F (hc' x)
    choose c' hc using hc
    apply inst1.is_liouville a ι' (c' ∘ eqv.symm) _ (u'' ∘ eqv.symm) v'
    rw [h']
    dsimp only [Function.comp_apply]
    · rw [Equiv.sum_comp eqv.symm (g := fun x ↦ c' x * logd (u'' x))]
      simp_rw [hc]
    · intro
      apply_fun ((↑) : F → K)
      simp only [Function.comp_apply, coe_deriv, hc, algebraMap.coe_zero]
      apply hc'
      apply NoZeroSMulDivisors.algebraMap_injective
