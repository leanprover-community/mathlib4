import Mathlib.Topology.Algebra.Algebra
import Mathlib.Algebra.MvPolynomial.CommRing
import DividedPowers.ForMathlib.RingTheory.MvPowerSeries.Trunc
import DividedPowers.ForMathlib.MvPowerSeries.Evaluation
import DividedPowers.ForMathlib.Topology.LinearTopology
import DividedPowers.ForMathlib.MvPowerSeries.LinearTopology
import DividedPowers.ForMathlib.PowerSeries.Topology
import DividedPowers.ForMathlib.Topology.Algebra.Algebra.Basic
import Mathlib.Data.Set.Finite

--import Mathlib.Topology.UniformSpace.CompleteSeparated

/- # Substitutions in power series

Here we define the substitution of power series into other power series.
We follow Bourbaki, Algèbre, chap. 4, §4, n° 3.

Evaluation of a power series at adequate elements has been defined
in `DividedPowers.ForMathlib.MvPowerSeries.Evaluation.lean`.
The goal here is to check the relevant hypotheses:
* The ring of coefficients is endowed the discrete topology.
* The main condition rewrites as having vanishing constant coefficient
* Power series have a linear topology
-/

theorem Set.Finite.support_of_summable
    {α : Type*} [AddCommGroup α] [TopologicalSpace α] [DiscreteTopology α]
    {β : Type*} (f : β → α) (h : Summable f) : Set.Finite f.support := by
  obtain ⟨a, ha⟩ := h
  simp only [HasSum] at ha
  classical
  simp_rw [tendsto_atTop_nhds] at ha
  obtain ⟨s, hs⟩ := ha {a} rfl (isOpen_discrete _)
  apply Set.Finite.subset s.finite_toSet
  intro b
  rw [Function.mem_support, not_imp_comm]
  intro hb
  let hs' := hs (insert b s) (s.subset_insert b)
  specialize hs s (subset_of_eq rfl)
  simp only [Set.mem_singleton_iff] at hs hs'
  simpa [Finset.sum_insert hb, hs, add_left_eq_self] using hs'

theorem add_pow_add_pred_eq_zero_of_pow_eq_zero {α : Type*} [CommSemiring α]
    {a b : α} {m n : ℕ} (ha : a ^ m = 0) (hb : b ^ n = 0) :
    (a + b) ^ (m + n).pred = 0 := by
  rw [add_pow]
  apply Finset.sum_eq_zero
  intro k hk
  simp only [Finset.mem_range] at hk
  by_cases h : k < m
  · have : n ≤ (m + n).pred - k  := by
      rw [Nat.le_sub_iff_add_le (Nat.le_of_lt_succ hk), add_comm]
      rw [Nat.le_pred_iff_lt (lt_of_le_of_lt (zero_le k) (Nat.lt_add_right n h))]
      exact Nat.add_lt_add_right h n
    rw [← Nat.add_sub_of_le this, pow_add, hb]
    simp only [zero_mul, mul_zero]
  · simp only [not_lt] at h
    rw [← Nat.add_sub_of_le h, pow_add, ha]
    simp only [zero_mul]

theorem IsNilpotent.add {α : Type*} [CommSemiring α]
    {a b : α} (ha : IsNilpotent a) (hb : IsNilpotent b) :
    IsNilpotent (a + b) := by
  obtain ⟨m, ha⟩ := ha
  obtain ⟨n, hb⟩ := hb
  exact ⟨_, add_pow_add_pred_eq_zero_of_pow_eq_zero ha hb⟩

theorem IsNilpotent.finset_sum {α : Type*} [CommSemiring α] {β : Type*} {f : β → α}
    (s : Finset β) (hf : ∀ b ∈ s, IsNilpotent (f b)) :
    IsNilpotent (s.sum f) := by
  classical
  induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, IsNilpotent.zero]
    | @insert b s hb hs =>
      rw [Finset.sum_insert hb]
      apply IsNilpotent.add
      exact hf b (s.mem_insert_self b)
      exact hs (fun b hb ↦ hf b (by exact Finset.mem_insert_of_mem hb))

theorem IsNilpotent.finsum {α : Type*} [CommSemiring α] {β : Type*} (f : β → α)
  (hf : ∀ b, IsNilpotent (f b)) : IsNilpotent (finsum f) := by
  classical
  by_cases h : Set.Finite f.support
  · rw [finsum_def, dif_pos h]
    exact IsNilpotent.finset_sum _ (fun b _ ↦ hf b)
  · simp only [finsum_def, dif_neg h, IsNilpotent.zero]

def MvPowerSeries.mapAlgHom (σ : Type*) {R : Type*} [CommSemiring R] {S : Type*}
    [Semiring S] [Algebra R S] {T : Type*} [Semiring T] [Algebra R T] (φ : S →ₐ[R] T) :
    MvPowerSeries σ S →ₐ[R] MvPowerSeries σ T where
  toRingHom   := MvPowerSeries.map σ φ
  commutes' r := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, MvPowerSeries.algebraMap_apply, map_C, RingHom.coe_coe, AlgHom.commutes]

def PowerSeries.mapAlgHom {R : Type*} [CommSemiring R]
  {S : Type*} [Semiring S] [Algebra R S] {T : Type*} [Semiring T] [Algebra R T]
  (φ : S →ₐ[R] T) :
  PowerSeries S →ₐ[R] PowerSeries T := MvPowerSeries.mapAlgHom Unit φ

theorem MvPowerSeries.monomial_one_eq {σ : Type*} {R : Type*} [CommSemiring R] (e : σ →₀ ℕ) :
    MvPowerSeries.monomial R e 1 = e.prod fun s n ↦ (X s : MvPowerSeries σ R) ^ n := by
  simp only [← MvPolynomial.coe_X, ← MvPolynomial.coe_pow, ← MvPolynomial.coe_monomial, MvPolynomial.monomial_eq, map_one, one_mul]
  simp only [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, ← map_finsupp_prod]

theorem MvPowerSeries.prod_smul_X_eq_smul_monomial_one {σ : Type*}
    {A : Type*} [CommSemiring A] (R : Type*) [CommSemiring R] [Algebra A R]
    (e : σ →₀ ℕ) (a : σ → A)  :
    e.prod (fun s n ↦ ((a s • X s : MvPowerSeries σ R) ^ n))
      = (e.prod fun s n ↦ (a s) ^ n) • monomial R e 1 := by
  rw [Finsupp.prod_congr (g2 := fun s n ↦ ((C σ R (algebraMap A R (a s)) * (X s : MvPowerSeries σ R)) ^ n))]
  simp only [mul_pow, Finsupp.prod_mul]
  simp only [← map_pow, ← map_finsupp_prod]
  rw [← monomial_one_eq]
  rw [← smul_eq_C_mul, ← algebra_compatible_smul]
  · intro x _
    rw [algebra_compatible_smul R, smul_eq_C_mul]

theorem MvPowerSeries.monomial_eq'
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommSemiring R]
    (e : σ →₀ ℕ) (r : σ → R) :
    MvPowerSeries.monomial R e (e.prod (fun s n => r s ^  n))
      = (Finsupp.prod e fun s e => (r s • MvPowerSeries.X s) ^ e) := by
  rw [prod_smul_X_eq_smul_monomial_one, ← map_smul, smul_eq_mul, mul_one]

theorem MvPowerSeries.monomial_smul_const
    {σ : Type*} [DecidableEq σ] {R : Type*} [CommSemiring R]
    (e : σ →₀ ℕ) (r : R) :
    MvPowerSeries.monomial R e (r ^ (Finsupp.sum e fun _ n => n))
      = (Finsupp.prod e fun s e => (r • MvPowerSeries.X s) ^ e) := by
  rw [prod_smul_X_eq_smul_monomial_one, ← map_smul, smul_eq_mul, mul_one]
  simp only [Finsupp.sum, Finsupp.prod, Finset.prod_pow_eq_pow_sum]

section DiscreteUniformity

class DiscreteUniformity (α : Type*) [u : UniformSpace α] : Prop where
  eq_principal_idRel : uniformity α = Filter.principal idRel

instance discreteUniformity_bot (α : Type*) : @DiscreteUniformity α ⊥ := by
  apply @DiscreteUniformity.mk α ⊥ rfl

instance discreteTopology_of_discreteUniformity (α : Type*)
    [UniformSpace α] [DiscreteUniformity α] : DiscreteTopology α := by
    rw [discreteTopology_iff_singleton_mem_nhds]
    intro a
    rw [UniformSpace.mem_nhds_iff]
    simp only [Set.subset_singleton_iff, DiscreteUniformity.eq_principal_idRel]
    simp only [Filter.mem_principal, idRel_subset]
    use Set.diagonal α
    simp only [Set.mem_diagonal_iff, implies_true, true_and]
    intro x
    simp only [UniformSpace.ball, Set.mem_preimage, Set.mem_diagonal_iff]
    exact fun a => a.symm

instance bot_uniformAddGroup {R : Type*} [AddGroup R]
    [UniformSpace R] [DiscreteUniformity R] : UniformAddGroup R :=
  { uniformContinuous_sub := fun s hs ↦ by
      simp only [uniformity_prod, DiscreteUniformity.eq_principal_idRel, Filter.comap_principal,
        Filter.inf_principal, Filter.map_principal, Filter.mem_principal, Set.image_subset_iff]
      rintro ⟨⟨x, y⟩, z, t⟩
      simp only [Set.mem_inter_iff, Set.mem_preimage, mem_idRel, and_imp]
      rintro ⟨rfl⟩ ⟨rfl⟩
      exact mem_uniformity_of_eq hs rfl }

instance discreteUniformity_complete (α : Type*) [UniformSpace α] [DiscreteUniformity α] : CompleteSpace α :=
  { complete := fun {f} hf ↦ by
      simp [cauchy_iff, bot_uniformity] at hf
      rcases hf with ⟨f_NeBot, hf⟩
      let d := (fun (a : α) ↦ (a, a)) '' Set.univ
      obtain ⟨t, ht, ht'⟩ := hf d (by
        simp only [DiscreteUniformity.eq_principal_idRel, Filter.mem_principal, idRel_subset]
        exact (fun a ↦ Set.mem_image_of_mem (fun a => (a, a)) (Set.mem_univ a)))
      obtain ⟨x, hx⟩ := f_NeBot.nonempty_of_mem ht
      use x
      intro s hs
      apply f.sets_of_superset ht
      intro y hy
      convert mem_of_mem_nhds hs
      apply symm
      simpa only [d, Set.image_univ, Set.range_diag, Set.mem_diagonal_iff] using ht' (Set.mk_mem_prod hx hy)
      }

end DiscreteUniformity

namespace MvPowerSeries

variable {σ : Type*} [DecidableEq σ]
  {A : Type*} [CommSemiring A]
  {R : Type*} [CommRing R] [Algebra A R]
  -- [TopologicalSpace α] [TopologicalRing α]
  {τ : Type*} [DecidableEq τ]
  {S : Type*} [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower A R S]
  -- [TopologicalSpace R] [TopologicalRing R][TopologicalAlgebra α R]

open WithPiTopology WithPiUniformity

/-- Families of power series which can be substituted -/
structure SubstDomain (a : σ → MvPowerSeries τ S) : Prop where
  const_coeff : ∀ s, IsNilpotent (constantCoeff τ S (a s))
  tendsto_zero : Filter.Tendsto a Filter.cofinite (@nhds _ (@topologicalSpace τ S ⊥) 0)

theorem substDomain_X :
    SubstDomain (fun (s : σ) ↦ (X s : MvPowerSeries σ S)) :=
  letI : UniformSpace S := ⊥
  { const_coeff := fun s ↦ by
     simp only [constantCoeff_X, IsNilpotent.zero]
    tendsto_zero := variables_tendsto_zero }

theorem substDomain_zero :
    SubstDomain (fun (_ : σ) ↦ (0 : MvPowerSeries τ S)) :=
  letI : UniformSpace S := ⊥
  { const_coeff := fun _ ↦ by simp only [Pi.zero_apply, map_zero, IsNilpotent.zero]
    tendsto_zero := tendsto_const_nhds }

theorem substDomain_add {a b : σ → MvPowerSeries τ S}
    (ha : SubstDomain a) (hb : SubstDomain b) :
    SubstDomain (a + b) where
  const_coeff := fun s ↦ by
    simp only [Pi.add_apply, map_add]
    exact IsNilpotent.add (ha.const_coeff s) (hb.const_coeff s)
  tendsto_zero := by
    letI : UniformSpace S := ⊥
    convert Filter.Tendsto.add (ha.tendsto_zero) (hb.tendsto_zero)
    rw [add_zero]

@[simp]
theorem constantCoeff_smul {R : Type*} [Semiring R] {S : Type*} [Semiring S] [Module R S] (φ : MvPowerSeries σ S) (a : R) :
    constantCoeff σ S (a • φ) = a • constantCoeff σ S φ := by
  rfl

theorem substDomain_mul (b : σ → MvPowerSeries τ S) {a : σ → MvPowerSeries τ S} (ha : SubstDomain a) :
    SubstDomain (b * a) :=
  letI : UniformSpace S := ⊥
  { const_coeff := fun s ↦ by
      simp only [Pi.mul_apply, map_mul]
      exact Commute.isNilpotent_mul_right (Commute.all _ _) (ha.const_coeff _)
    tendsto_zero := LinearTopology.tendsto_zero_mul _ b a ha.tendsto_zero }

theorem substDomain_smul (r : MvPowerSeries τ S) {a : σ → MvPowerSeries τ S} (ha : SubstDomain a) :
    SubstDomain (r • a) := by convert substDomain_mul _ ha

noncomputable def substDomain.submodule : Ideal (σ → MvPowerSeries τ S) :=
  letI : UniformSpace S := ⊥
  { carrier := setOf SubstDomain
    add_mem' := substDomain_add
    zero_mem' := substDomain_zero
    smul_mem' := substDomain_mul }

/-- If σ is finite, then the nilpotent condition is enough for SubstDomain -/
def substDomain_of_constantCoeff_nilpotent [Finite σ]
    {a : σ → MvPowerSeries τ S} (ha : ∀ s, IsNilpotent (constantCoeff τ S (a s))) :
    SubstDomain a where
  const_coeff := ha
  tendsto_zero := by simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]

/-- If σ is finite, then having zero constant coefficient is enough for SubstDomain -/
def substDomain_of_constantCoeff_zero [Finite σ]
    {a : σ → MvPowerSeries τ S} (ha : ∀ s, constantCoeff τ S (a s) = 0) :
    SubstDomain a :=
  substDomain_of_constantCoeff_nilpotent (fun s ↦ by simp only [ha s, IsNilpotent.zero])

/-- Substitution of power series into a power series -/
noncomputable def subst (a : σ → MvPowerSeries τ S) (f : MvPowerSeries σ R) :
    MvPowerSeries τ S :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  MvPowerSeries.eval₂ (algebraMap _ _) a f

variable {a : σ → MvPowerSeries τ S} (ha : SubstDomain a)

def SubstDomain.evalDomain :
  @EvalDomain σ (MvPowerSeries τ S) _ (@topologicalSpace τ S ⊥) a :=
  letI : UniformSpace S := ⊥
  { hpow := fun s ↦ (tendsto_pow_of_constantCoeff_nilpotent_iff (a s)).mpr (ha.const_coeff s)
    tendsto_zero := ha.tendsto_zero }

-- NOTE: We need `by exact` or the proof breaks!!!!
/-- Substitution of power series into a power series -/
noncomputable def substAlgHom : MvPowerSeries σ R →ₐ[R] MvPowerSeries τ S := by
-- NOTE : Could there be a tactic that introduces these local instances?
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  exact MvPowerSeries.aeval ha.evalDomain

theorem coe_substAlgHom :
  ⇑(substAlgHom ha) = subst (R := R) a := rfl

theorem subst_add (f g : MvPowerSeries σ R) :
    subst a (f + g) = subst a f + subst a g := by
  rw [← coe_substAlgHom ha, map_add]

theorem subst_mul (f g : MvPowerSeries σ R) :
    subst a (f * g) = subst a f * subst a g := by
  rw [← coe_substAlgHom ha, map_mul]

theorem subst_pow (f : MvPowerSeries σ R) (n : ℕ) :
    subst a (f ^ n) = (subst a f ) ^ n := by
  rw [← coe_substAlgHom ha, map_pow]

theorem subst_smul (r : A) (f : MvPowerSeries σ R) :
    subst a (r • f) = r • (subst a f) := by
  rw [← coe_substAlgHom ha, AlgHom.map_smul_of_tower]

theorem substAlgHom_coe (p : MvPolynomial σ R) :
    substAlgHom (R := R) ha p = MvPolynomial.aeval a p :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  aeval_coe ha.evalDomain p

theorem substAlgHom_X (s : σ) :
    substAlgHom (R := R) ha (X s) = a s := by
  rw [← MvPolynomial.coe_X, substAlgHom_coe, MvPolynomial.aeval_X]

theorem substAlgHom_monomial (e : σ →₀ ℕ) (r : R) :
    substAlgHom ha (monomial R e r) =
      (algebraMap R (MvPowerSeries τ S) r) * (e.prod (fun s n ↦ (a s) ^ n)) := by
  rw [← MvPolynomial.coe_monomial, substAlgHom_coe, MvPolynomial.aeval_monomial]

theorem subst_coe (p : MvPolynomial σ R) :
    subst (R := R) a p = MvPolynomial.aeval a p := by
  rw [← coe_substAlgHom ha, substAlgHom_coe]

theorem subst_X (s : σ) :
    subst (R := R) a (X s) = a s := by
  rw [← coe_substAlgHom ha, substAlgHom_X]

theorem subst_monomial (e : σ →₀ ℕ) (r : R) :
    subst a (monomial R e r) =
      (algebraMap R (MvPowerSeries τ S) r) * (e.prod (fun s n ↦ (a s) ^ n)) := by
  rw [← coe_substAlgHom ha, substAlgHom_monomial]

theorem continuous_subst :
    letI : UniformSpace R := ⊥
    letI : UniformSpace S := ⊥
    Continuous (subst a : MvPowerSeries σ R → MvPowerSeries τ S) :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  continuous_aeval ha.evalDomain

theorem coeff_subst_finite (f : MvPowerSeries σ R) (e : τ →₀ ℕ) :
    Set.Finite (fun (d : σ →₀ ℕ) ↦ (coeff R d f) • (coeff S e (d.prod fun s e => (a s) ^ e))).support :=
  letI : UniformSpace S := ⊥
  letI : UniformSpace R := ⊥
  Set.Finite.support_of_summable _
    ((hasSum_aeval ha.evalDomain f).map (coeff S e) (continuous_coeff e)).summable

theorem coeff_subst (f : MvPowerSeries σ R) (e : τ →₀ ℕ) :
    coeff S e (subst a f) = finsum (fun (d : σ →₀ ℕ) ↦ (coeff R d f) • (coeff S e (d.prod fun s e => (a s) ^ e))) := by
  letI : UniformSpace S := ⊥
  letI : UniformSpace R := ⊥
  have := ((hasSum_aeval ha.evalDomain f).map (coeff S e) (continuous_coeff e))
  erw [← this.tsum_eq, tsum_def]
  erw [dif_pos this.summable, if_pos (coeff_subst_finite ha f e)]
  rfl

theorem constantCoeff_subst (f : MvPowerSeries σ R) :
    constantCoeff τ S (subst a f) = finsum (fun (d : σ →₀ ℕ) ↦ (coeff R d f) • (constantCoeff τ S (d.prod fun s e => (a s) ^ e))) := by
  simp only [← coeff_zero_eq_constantCoeff_apply, coeff_subst ha f 0]

theorem map_algebraMap_eq_subst_X (f : MvPowerSeries σ R):
    map σ (algebraMap R S) f = subst X f := by
  ext e
  rw [coeff_map, coeff_subst substDomain_X f e, finsum_eq_single _ e]
  · rw [← MvPowerSeries.monomial_one_eq, coeff_monomial_same,
      algebra_compatible_smul S, smul_eq_mul, mul_one]
  · intro d hd
    rw [← MvPowerSeries.monomial_one_eq, coeff_monomial_ne hd.symm, smul_zero]

variable
    {T : Type*} [CommRing T]
    [UniformSpace T] [T2Space T] [CompleteSpace T]
    [UniformAddGroup T] [TopologicalRing T] [LinearTopology T]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    {ε : MvPowerSeries τ S →ₐ[R] T}

theorem comp_substAlgHom :
    letI : UniformSpace S := ⊥
    letI : UniformSpace R := ⊥
    (hε : Continuous ε) →
      ε.comp (substAlgHom ha) = aeval (EvalDomain.map hε ha.evalDomain) :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  fun hε ↦ comp_aeval ha.evalDomain hε

theorem comp_subst :
    letI : UniformSpace R := ⊥
    letI : UniformSpace S := ⊥
    (hε : Continuous ε) →
      ⇑ε ∘ (subst a) = ⇑(aeval (R := R) (EvalDomain.map hε ha.evalDomain)) :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  fun hε ↦ by rw [← comp_substAlgHom ha hε, AlgHom.coe_comp, coe_substAlgHom]

theorem comp_subst_apply :
    letI : UniformSpace R := ⊥
    letI : UniformSpace S := ⊥
    (hε : Continuous ε) → (f : MvPowerSeries σ R) →
      ε (subst a f) = aeval (R := R) (EvalDomain.map hε ha.evalDomain) f :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  fun hε ↦ congr_fun (comp_subst ha hε)

theorem eval₂_subst {b : τ → T} (hb : EvalDomain b) (f : MvPowerSeries σ R) :
    letI : UniformSpace R := ⊥
    letI : UniformSpace S := ⊥
    eval₂ (algebraMap S T) b (subst a f) =
      eval₂ (algebraMap R T) (fun s ↦ eval₂ (algebraMap S T) b (a s)) f :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  let ε : MvPowerSeries τ S →ₐ[R] T := (aeval hb).restrictScalars R
  have hε : Continuous ε := continuous_aeval hb
  comp_subst_apply ha hε f

/- a : σ → MvPowerSeries τ S
   b : τ → MvPowerSeries υ T
   f ∈ R⟦σ⟧, f(a) = substAlgHom ha f ∈ S⟦τ⟧
   f(a) (b) = substAlgHom hb (substAlgHom ha f)
   f = X s, f (a) = a s
   f(a) (b) = substAlgHom hb (a s)
   -/

variable {υ : Type*} [DecidableEq υ]
  {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {b : τ → MvPowerSeries υ T}
  (hb : @SubstDomain τ υ T _ b)

-- TODO? : the converse holds when the kernel of `algebraMap R S` is a nilideal
theorem IsNilpotent_subst
    {f : MvPowerSeries σ R} (hf : IsNilpotent (constantCoeff σ R f)) :
    IsNilpotent (constantCoeff τ S ((substAlgHom ha) f)) := by
  rw [coe_substAlgHom, constantCoeff_subst ha]
  apply IsNilpotent.finsum
  intro d
  by_cases hd : d = 0
  · rw [← algebraMap_smul S, smul_eq_mul, mul_comm, ← smul_eq_mul, hd]
    exact IsNilpotent.smul (IsNilpotent.map hf _) _
  · apply IsNilpotent.smul
    rw [← ne_eq, Finsupp.ne_iff] at hd
    obtain ⟨t, hs⟩ := hd
    rw [← Finsupp.prod_filter_mul_prod_filter_not (fun i ↦ i = t), map_mul,
      mul_comm, ← smul_eq_mul]
    apply IsNilpotent.smul
    rw [Finsupp.prod_eq_single t]
    · simp only [Finsupp.filter_apply_pos, map_pow]
      exact IsNilpotent.pow_of_pos (ha.const_coeff t) hs
    · intro t' htt' ht'
      simp only [Finsupp.filter_apply, if_neg ht', ne_eq, not_true_eq_false] at htt'
    · exact fun _ ↦ by rw [pow_zero]

def SubstDomain.comp : SubstDomain (fun s ↦ substAlgHom hb (a s)) where
  const_coeff s := IsNilpotent_subst hb (ha.const_coeff s)
  tendsto_zero := by
    letI : TopologicalSpace S := ⊥
    letI : TopologicalSpace T := ⊥
    apply Filter.Tendsto.comp _ (ha.tendsto_zero)
    rw [coe_substAlgHom, ← (substAlgHom (R := S) hb).map_zero]
    apply (continuous_subst hb).continuousAt

theorem substAlgHom_comp_substAlgHom :
    ((substAlgHom hb).restrictScalars R).comp (substAlgHom ha) = substAlgHom (ha.comp hb) :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  letI : UniformSpace T := ⊥
  comp_aeval (R := R) (ε := (substAlgHom hb).restrictScalars R)
    ha.evalDomain (continuous_subst (R := S) hb)

theorem substAlgHom_comp_substAlgHom_apply (f : MvPowerSeries σ R) :
    (substAlgHom hb) (substAlgHom ha f) = substAlgHom (ha.comp hb) f :=
  DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f

theorem subst_comp_subst :
    (subst b) ∘ (subst a) = subst (R := R) (fun s ↦ subst b (a s)) := by
  apply funext
  simpa only [DFunLike.ext_iff, AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply] using
    substAlgHom_comp_substAlgHom (R := R) ha hb

theorem subst_comp_subst_apply (f : MvPowerSeries σ R) :
    subst b (subst a f) = subst (fun s ↦ subst b (a s)) f :=
  congr_fun (subst_comp_subst (R := R) ha hb) f

/-  Not the needed function
theorem comp_substAlgHom
    {T : Type*} [CommRing T] [Algebra R T] (ε : S →ₐ[R] T) :
    (MvPowerSeries.mapAlgHom τ ε).comp (substAlgHom ha) = substAlgHom (ha.map ε)  := by
  apply MvPowerSeries.comp_aeval
  sorry
-/

section scale

noncomputable def scale (a : σ → A) (f : MvPowerSeries σ R) :
    MvPowerSeries σ R :=
  subst (a • X) f

theorem scale_eq_subst (a : σ → A) (f : MvPowerSeries σ R) :
    scale a f = subst (a • X) f := rfl

variable (R) in
theorem substDomain_scale (a : σ → A) :
    SubstDomain ((a • X) : σ → MvPowerSeries σ R) := by
  convert substDomain_mul (fun s ↦ algebraMap A (MvPowerSeries σ R) (a s))
    substDomain_X using 1
  rw [Function.funext_iff]
  intro s
  simp only [Pi.smul_apply', Pi.mul_apply]
  rw [algebra_compatible_smul (MvPowerSeries σ R), smul_eq_mul]

variable (R) in
noncomputable def scale_algHom (a : σ → A) :
    MvPowerSeries σ R →ₐ[R] MvPowerSeries σ  R :=
  substAlgHom (substDomain_scale R a)

theorem coe_scale_algHom (a : σ → A) :
    ⇑(scale_algHom R a) = scale a := rfl

theorem scale_algHom_comp (a b : σ → A) :
    (scale_algHom R a).comp (scale_algHom R b) = scale_algHom R (a * b) := by
  rw [AlgHom.ext_iff]
  intro f
  simp only [AlgHom.coe_comp, Function.comp_apply, scale_algHom]
  rw [substAlgHom_comp_substAlgHom_apply]
  congr
  rw [Function.funext_iff]
  intro s
  simp only [Pi.smul_apply', Pi.mul_apply]
  rw [AlgHom.map_smul_of_tower]
  rw [← MvPolynomial.coe_X, substAlgHom_coe, MvPolynomial.aeval_X, MvPolynomial.coe_X]
  simp only [Pi.smul_apply', algebraMap_smul]
  rw [← mul_smul, mul_comm]

theorem scale_scale_apply (a b : σ → A) (f : MvPowerSeries σ R) :
    (f.scale b).scale a = f.scale (a * b) := by
  simp only [← coe_scale_algHom, ← AlgHom.comp_apply, scale_algHom_comp]

theorem coeff_scale (r : σ → A) (f : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    coeff R d (scale r f) = (d.prod fun s n ↦ r s ^ n) • coeff R d f := by
  unfold scale
  rw [coeff_subst (substDomain_scale R _)]
  simp only [Pi.smul_apply', smul_eq_mul, prod_smul_X_eq_smul_monomial_one]
  simp only [LinearMap.map_smul_of_tower, Algebra.mul_smul_comm]
  rw [finsum_eq_single _ d]
  · simp only [coeff_monomial_same, mul_one]
  · intro e he
    simp only [coeff_monomial_ne he.symm, mul_zero, smul_zero]

theorem scale_one :
    scale (1 : σ → A) = @id (MvPowerSeries σ R) := by
  ext f d
  simp only [coeff_scale, Pi.one_apply, one_pow, Finsupp.prod, id_eq,
    Finset.prod_const_one, one_smul]

theorem scale_algHom_one :
    scale_algHom R (Function.const σ (1 : A)) = AlgHom.id R (MvPowerSeries σ R):= by
  rw [DFunLike.ext_iff]
  intro f
  simp only [Function.const_one, coe_scale_algHom, AlgHom.coe_id, id_eq, scale_one]

noncomputable def scale_MonoidHom : (σ → A) →* MvPowerSeries σ R →ₐ[R] MvPowerSeries σ R where
  toFun := scale_algHom R
  map_one' := scale_algHom_one
  map_mul' a b := by
    dsimp only
    rw [← scale_algHom_comp, AlgHom.End_toSemigroup_toMul_mul]

theorem scale_zero_apply (f : MvPowerSeries σ R) :
  (scale (Function.const σ (0 : A))) f = MvPowerSeries.C σ R (constantCoeff σ R f) := by
  ext d
  simp only [coeff_scale, coeff_C]
  by_cases hd : d = 0
  · simp only [hd, Function.const_apply, Finsupp.prod_zero_index, coeff_zero_eq_constantCoeff,
    one_smul, ↓reduceIte]
  · simp only [if_neg hd]
    convert zero_smul A _
    simp only [DFunLike.ext_iff, Finsupp.coe_zero, Pi.zero_apply, not_forall] at hd
    obtain ⟨s, hs⟩ := hd
    simp only [Finsupp.prod]
    apply Finset.prod_eq_zero (i := s)
    rw [Finsupp.mem_support_iff]
    exact hs
    simp only [Function.const_apply, zero_pow hs]

/-- Scaling a linear power series is smul -/
lemma scale_linear_eq_smul (r : A) (f : MvPowerSeries σ R)
    (hf : ∀ (d : σ →₀ ℕ), (d.sum (fun _ n ↦ n) ≠ 1) → MvPowerSeries.coeff R d f = 0) :
    MvPowerSeries.scale (Function.const σ r) f = r • f := by
  ext e
  simp only [MvPowerSeries.coeff_scale, map_smul]
  simp only [Finsupp.prod, Function.const_apply, Finset.prod_pow_eq_pow_sum, smul_eq_mul]
  by_cases he : Finsupp.sum e (fun _ n ↦ n) = 1
  · simp only [Finsupp.sum] at he
    simp only [he, pow_one, LinearMap.map_smul_of_tower]
  · simp only [hf e he, smul_zero, LinearMap.map_smul_of_tower]


end scale

end MvPowerSeries

namespace PowerSeries

variable
  {A : Type*} [CommRing A]
  {R : Type*} [CommRing R] [Algebra A R]
  {τ : Type*} [DecidableEq τ]
  {S : Type*} [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower A R S]

open MvPowerSeries.WithPiUniformity WithPiTopology
/-
local instance us : UniformSpace R := ⊥
local instance : TopologicalRing R := DiscreteTopology.topologicalRing

local instance us2 : UniformSpace S := ⊥
local instance : DiscreteUniformity S := discreteUniformity_bot S
local instance : TopologicalAlgebra R S := inferInstance -/

-- variable [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]

/- noncomputable local instance : LinearTopology (MvPowerSeries τ S) :=
  MvPowerSeries.WithPiTopology.isLinearTopology τ S
-/

--noncomputable local instance : TopologicalSpace (PowerSeries S) := inferInstance

-- TODO : PowerSeries.LinearTopology file
/- noncomputable local instance : LinearTopology (PowerSeries S) :=
   MvPowerSeries.isLinearTopology Unit S
-/

/- noncomputable local instance : TopologicalAlgebra R (MvPowerSeries τ S) := by
    refine DiscreteTopology.topologicalAlgebra R (MvPowerSeries τ S)
local instance : CompleteSpace (MvPowerSeries τ S) := by refine completeSpace τ S
-/

/-- Families of power series which can be substituted -/
structure SubstDomain (a : MvPowerSeries τ S) : Prop where
  const_coeff : IsNilpotent (MvPowerSeries.constantCoeff τ S a)

def substDomain_of_constantCoeff_nilpotent
    {a : MvPowerSeries τ S}
    (ha : IsNilpotent (MvPowerSeries.constantCoeff τ S a)) :
    SubstDomain a where
  const_coeff := ha

theorem substDomain_iff (a : MvPowerSeries τ S) :
    SubstDomain a ↔ MvPowerSeries.SubstDomain (Function.const Unit a) :=
  ⟨fun ha ↦ MvPowerSeries.substDomain_of_constantCoeff_nilpotent (Function.const Unit ha.const_coeff),
   fun ha  ↦ substDomain_of_constantCoeff_nilpotent (ha.const_coeff ())⟩

def substDomain_of_constantCoeff_zero
    {a : MvPowerSeries τ S}
    (ha : MvPowerSeries.constantCoeff τ S a = 0) :
    SubstDomain a where
  const_coeff := by simp only [ha, IsNilpotent.zero]

theorem substDomain_X : SubstDomain (X : R⟦X⟧) :=
  substDomain_of_constantCoeff_zero (by
    change constantCoeff R X = 0
    rw [constantCoeff_X])

theorem substDomain_smul_X (a : A) : SubstDomain (a • X : R⟦X⟧) :=
  substDomain_of_constantCoeff_zero (by
    change constantCoeff R (a • X) = 0
    rw [← coeff_zero_eq_constantCoeff]
    simp only [LinearMap.map_smul_of_tower, coeff_zero_X, smul_zero])

variable {υ : Type*} [DecidableEq υ]
  {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Substitution of power series into a power series -/
noncomputable def subst (a : MvPowerSeries τ S) (f : PowerSeries R) :
    MvPowerSeries τ S :=
  MvPowerSeries.subst (fun _ ↦ a) f

variable {a : MvPowerSeries τ S} (ha : SubstDomain a)

def SubstDomain.const : MvPowerSeries.SubstDomain (fun (_ : Unit) ↦ a) where
  const_coeff  := fun _ ↦ ha.const_coeff
  tendsto_zero := by simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]

/-- Substitution of power series into a power series -/
noncomputable def substAlgHom  : PowerSeries R →ₐ[R] MvPowerSeries τ S :=
  MvPowerSeries.substAlgHom ha.const

theorem coe_substAlgHom :
  ⇑(substAlgHom ha) = subst (R := R) a := rfl

theorem subst_add (f g : PowerSeries R) :
    subst a (f + g) = subst a f + subst a g := by
  rw [← coe_substAlgHom ha, map_add]

theorem subst_pow (f : PowerSeries R) (n : ℕ) :
    subst a (f ^ n) = (subst a f ) ^ n := by
  rw [← coe_substAlgHom ha, map_pow]

theorem subst_mul (f g : PowerSeries R) :
    subst a (f * g) = subst a f * subst a g := by
  rw [← coe_substAlgHom ha, map_mul]

theorem subst_smul (r : A) (f : PowerSeries R) :
    subst a (r • f) = r • (subst a f) := by
  rw [← coe_substAlgHom ha, AlgHom.map_smul_of_tower]

/-
-- TODO LIST:
- Add PowerSeries.toMvPowerSeries_Unit
- Show it is a topological equivalence.
- The support under finsuppUnitEquiv should be the image of the support.
-/

theorem coeff_subst_finite (f : PowerSeries R) (e : τ →₀ ℕ) :
    Set.Finite (fun (d : ℕ) ↦ (coeff R d f) • (MvPowerSeries.coeff S e (a ^ d))).support := by
  convert (MvPowerSeries.coeff_subst_finite ha.const f e).image
    ⇑(Finsupp.LinearEquiv.finsuppUnique ℕ ℕ Unit).toEquiv
  rw [← Equiv.preimage_eq_iff_eq_image, ← Function.support_comp_eq_preimage]
  apply congr_arg
  rw [← Equiv.eq_comp_symm]
  ext d
  simp only [Finsupp.prod_pow, Finset.univ_unique, PUnit.default_eq_unit, Finset.prod_singleton,
    LinearEquiv.coe_toEquiv_symm, EquivLike.coe_coe, Function.comp_apply,
    Finsupp.LinearEquiv.finsuppUnique_symm_apply, Finsupp.single_eq_same]
  congr

theorem coeff_subst (f : PowerSeries R) (e : τ →₀ ℕ) :
    MvPowerSeries.coeff S e (subst a f) =
      finsum (fun (d : ℕ) ↦
        (coeff R d f) • (MvPowerSeries.coeff S e (a ^ d))) := by
  erw [MvPowerSeries.coeff_subst ha.const f e]
  rw [← finsum_comp_equiv (Finsupp.LinearEquiv.finsuppUnique ℕ ℕ Unit).toEquiv.symm]
  apply finsum_congr
  intro d
  congr
  · ext; simp
  · simp

theorem constantCoeff_subst (f : PowerSeries R) :
    MvPowerSeries.constantCoeff τ S (subst a f) =
      finsum (fun d ↦ (coeff R d f) • (MvPowerSeries.constantCoeff τ S (a ^ d))) := by
  simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst ha f 0]

theorem map_algebraMap_eq_subst_X (f : R⟦X⟧) :
    map (algebraMap R S) f = subst X f :=
  MvPowerSeries.map_algebraMap_eq_subst_X f

theorem _root_.Polynomial.toPowerSeries_toMvPowerSeries (p : Polynomial R) :
    (p : PowerSeries R) =
      ((Polynomial.aeval (MvPolynomial.X ()) p : MvPolynomial Unit R) : MvPowerSeries Unit R) := by
  change (Polynomial.coeToPowerSeries.algHom R) p =
    (MvPolynomial.coeToMvPowerSeries.algHom R) (Polynomial.aeval (MvPolynomial.X () : MvPolynomial Unit R) p)
  rw [← AlgHom.comp_apply]
  apply AlgHom.congr_fun
  apply Polynomial.algHom_ext
  simp only [Polynomial.coeToPowerSeries.algHom_apply, Algebra.id.map_eq_id, Polynomial.coe_X,
    map_X]
  erw [AlgHom.comp_apply]
  simp only [Polynomial.aeval_X, MvPolynomial.coeToMvPowerSeries.algHom_apply,
    Algebra.id.map_eq_id, MvPowerSeries.map_id, MvPolynomial.coe_X, RingHom.id_apply]
  rfl

/- example :(substAlgHom ha).comp
    ((MvPolynomial.coeToMvPowerSeries.algHom R).comp
      (Polynomial.aeval (MvPolynomial.X () : MvPolynomial Unit R)))
    = (Polynomial.aeval a) := by
  apply Polynomial.algHom_ext
  simp only [AlgHom.coe_comp, Function.comp_apply, Polynomial.aeval_X]
  erw [AlgHom.comp_apply]
  simp only [Polynomial.aeval_X, MvPolynomial.coeToMvPowerSeries.algHom_apply, Algebra.id.map_eq_id,
    MvPowerSeries.map_id, MvPolynomial.coe_X, RingHom.id_apply]
  -- we need substAlgHom_coe
  rw [← MvPolynomial.coe_X, substAlgHom]
  erw [MvPowerSeries.substAlgHom_apply]
  rw [MvPowerSeries.subst_coe, MvPolynomial.aeval_X]
-/

theorem substAlgHom_coe (p : Polynomial R) :
    substAlgHom ha (p : PowerSeries R) = ↑(Polynomial.aeval a p) := by
  rw [p.toPowerSeries_toMvPowerSeries, substAlgHom]
  erw [MvPowerSeries.coe_substAlgHom]
  rw [MvPowerSeries.subst_coe ha.const, ← AlgHom.comp_apply]
  apply AlgHom.congr_fun
  apply Polynomial.algHom_ext
  simp only [AlgHom.coe_comp, Function.comp_apply, Polynomial.aeval_X, MvPolynomial.aeval_X]

theorem substAlgHom_X : substAlgHom ha (X : R⟦X⟧) = a := by
  rw [← Polynomial.coe_X, substAlgHom_coe, Polynomial.aeval_X]

theorem subst_coe (p : Polynomial R) :
    subst (R := R) a (p : PowerSeries R) = ↑(Polynomial.aeval a p) := by
  rw [← coe_substAlgHom ha, substAlgHom_coe]

theorem subst_X : subst a (X : R⟦X⟧) = a := by
  rw [← coe_substAlgHom ha, substAlgHom_X]

-- TODO: remove
/-
theorem comp_substAlgHom
    {T : Type*} [CommRing T] [Algebra R T] {ε : S →ₐ[R] T} :
    (MvPowerSeries.mapAlgHom τ ε).comp (substAlgHom ha) = substAlgHom (ha.map ε)  :=
  MvPowerSeries.comp_subst ha.const ε

theorem comp_substAlgHom
    {T : Type*} [CommRing T] [Algebra R T] (ε : S →ₐ[R] T) :
    (MvPowerSeries.mapAlgHom τ ε).comp (substAlgHom ha) = substAlgHom (ha.map ε)  :=
  MvPowerSeries.comp_substAlgHom ha.const ε
-/

def SubstDomain.comp {a : PowerSeries S} (ha : SubstDomain a)
    {b : MvPowerSeries υ T} (hb : SubstDomain b):
    SubstDomain (substAlgHom hb a) where
  const_coeff := MvPowerSeries.IsNilpotent_subst hb.const (ha.const_coeff)

variable
    {υ : Type*} [DecidableEq υ] {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    {a : PowerSeries S} (ha : SubstDomain a)
    {b : MvPowerSeries υ T} (hb : SubstDomain b)
    {a' : MvPowerSeries τ S} (ha' : SubstDomain a')
    {b' : τ → MvPowerSeries υ T} (hb' : MvPowerSeries.SubstDomain b')

theorem substAlgHom_comp_substAlgHom :
    ((substAlgHom hb).restrictScalars R).comp (substAlgHom ha)
      = substAlgHom (ha.comp hb) :=
  MvPowerSeries.substAlgHom_comp_substAlgHom _ _

theorem substAlgHom_comp_substAlgHom_apply (f : PowerSeries R) :
    (substAlgHom hb) (substAlgHom  ha f) = substAlgHom (ha.comp hb) f :=
  DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f

theorem subst_comp_subst :
    (subst b) ∘ (subst a) = subst (R := R) (subst b a) := by
  have h := substAlgHom_comp_substAlgHom (R := R) ha hb
  simp only [DFunLike.ext_iff, AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply] at h
  exact funext h

theorem subst_comp_subst_apply (f : PowerSeries R) :
    subst b (subst a f) = subst (subst b a) f :=
  congr_fun (subst_comp_subst (R := R) ha hb) f

section scale

-- oops, it exists as PowerSeries.rescale
noncomputable def scale (a : A) (f : R⟦X⟧) : R⟦X⟧ :=
    MvPowerSeries.scale (Function.const Unit a) f

theorem scale_eq_subst (a : A) (f : R⟦X⟧) :
    scale a f = subst (a • X) f := rfl

variable (R) in
theorem substDomain_scale (a : A) : SubstDomain (a • (X : R⟦X⟧)) :=
  (substDomain_iff _).mpr (MvPowerSeries.substDomain_scale R _)

variable (R) in
noncomputable def scale_algHom (a : A) :
    R⟦X⟧ →ₐ[R] R⟦X⟧ :=
  MvPowerSeries.scale_algHom R (Function.const Unit a)

theorem coe_scale_algHom (a : A) :
    ⇑(scale_algHom R a) = scale a := rfl

theorem scale_algHom_comp (a b : A) :
    (scale_algHom R a).comp (scale_algHom R b) = scale_algHom R (a * b) := by
  simp only [scale_algHom]
  rw [MvPowerSeries.scale_algHom_comp]
  rfl

theorem scale_scale_apply (a b : A) (f : R⟦X⟧) :
    (f.scale b).scale a = f.scale (a * b) :=
  MvPowerSeries.scale_scale_apply _ _ f

theorem coeff_scale (a : A) (f : R⟦X⟧) (d : ℕ) :
    coeff R d (scale a f) = a ^ d • coeff R d f := by
  convert MvPowerSeries.coeff_scale (Function.const Unit a) f (Finsupp.single default d)
  simp only [PUnit.default_eq_unit, Function.const_apply, pow_zero, Finsupp.prod_single_index]

theorem scale_algebraMap (a : A) :
    scale (algebraMap A R a) = scale (R := R) a := by
  ext f n
  simp only [coeff_scale]
  rw [← algebraMap_smul (R := A) R, map_pow]

theorem scale_one : scale (1 : A) = @id (R⟦X⟧) :=
  MvPowerSeries.scale_one

theorem scale_algHom_one :
    scale_algHom R (1 : A) = AlgHom.id R R⟦X⟧ :=
  MvPowerSeries.scale_algHom_one

noncomputable def scale_MonoidHom : A →* R⟦X⟧ →ₐ[R] R⟦X⟧ where
  toFun := scale_algHom R
  map_one' := scale_algHom_one
  map_mul' a b := by
    dsimp only
    rw [← scale_algHom_comp, AlgHom.End_toSemigroup_toMul_mul]

theorem scale_zero_apply (f : R⟦X⟧) :
    scale (0 : A) f = PowerSeries.C R (constantCoeff R f) :=
  MvPowerSeries.scale_zero_apply f

/-- When p is linear, substitution of p and then a scalar homothety
  is substitution of the homothety then p -/
lemma subst_linear_subst_scalar_comm (a : A)
    {σ : Type*} [DecidableEq σ] [Finite σ] (p : MvPowerSeries σ R)
    (hp_lin : ∀ (d : σ →₀ ℕ), (d.sum (fun _ n ↦ n) ≠ 1) → MvPowerSeries.coeff R d p = 0)
    (f : PowerSeries R) :
    subst p (scale a f)
      = MvPowerSeries.scale (Function.const σ a) (subst p f) := by
  have hp : PowerSeries.SubstDomain p := by
    apply substDomain_of_constantCoeff_zero
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    apply hp_lin
    simp only [Finsupp.sum_zero_index, ne_eq, zero_ne_one, not_false_eq_true]
  rw [scale_eq_subst, MvPowerSeries.scale_eq_subst]
  rw [subst_comp_subst_apply (substDomain_scale R _) hp]
  nth_rewrite 3 [subst]
  rw [MvPowerSeries.subst_comp_subst_apply hp.const (MvPowerSeries.substDomain_scale R _)]
  rw [Function.funext_iff]
  intro _
  rw [subst_smul hp, ← Polynomial.coe_X, subst_coe hp, Polynomial.aeval_X]
  rw [← MvPowerSeries.scale_eq_subst]
  rw [MvPowerSeries.scale_linear_eq_smul _ _ hp_lin]
  rfl

theorem scale_map_eq_map_scale' (φ : R →+* S) (a : A) (f : R⟦X⟧) :
    scale (φ (algebraMap A R a)) (PowerSeries.map φ f)
    = PowerSeries.map (φ : R →+* S) (scale a f) := by
  ext n
  simp only [coeff_scale, coeff_map,
    algebra_compatible_smul S (a ^ n), algebra_compatible_smul R (a ^ n),
    smul_eq_mul, smul_eq_mul, map_mul, map_pow]

theorem scale_map_eq_map_scale (φ : R →ₐ[A] S) (a : A) (f : R⟦X⟧) :
    scale a (PowerSeries.map φ f)
    = PowerSeries.map (φ : R →+* S) (scale a f) := by
  rw [← scale_map_eq_map_scale', ← scale_algebraMap, RingHom.coe_coe, AlgHom.commutes]

end scale

end PowerSeries
