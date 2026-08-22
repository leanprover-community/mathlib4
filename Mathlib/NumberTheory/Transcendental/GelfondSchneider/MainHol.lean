/-
Copyright (c) 2025 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module
public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainAnalyticBounds

/-!
# Gelfond-Schneider: holomorphy of the auxiliary function

`R` is factored at each zero as `(z - (l + 1)) ^ r * R'` with `R'` analytic, and the resulting
quotient `S` is entire away from the evaluation points.

## References
* Loo-Keng Hua, Introduction to Number Theory, Springer, 1982. Chapter 17.9.
-/

@[expose] public section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt Differentiable Complex


noncomputable section


namespace GelfondSchneider

variable {K : Type} [Field K] (α : ℂ) (β : ℂ) (σ : K →+* ℂ) (α' : K) (β' : K) (γ' : K)
  (hirr : ∀ i j : ℤ, β ≠ i / j) (htriv : α ≠ 0 ∧ α ≠ 1)
  (habc : α = σ α' ∧ β = σ β' ∧ α ^ β = σ γ')

variable [NumberField K]

variable (q : ℕ) (hq0 : 0 < q)

variable (u : Fin (m K * n K q)) (t : Fin (q * q))

variable (h2mq : 2 * m K ∣ q ^ 2)

variable [DecidableEq (K →+* ℂ)]

/-
We formalize the existence of a function R' : ℂ → ℂ,
analytic in a neighborhood of l' + 1,
such that R(z) = (z - (l' + 1))^r * R'(z) in a neighborhood of l' + 1.
so this o is (I hope) rOrder l' -/
include α β σ α' β' γ' hirr htriv habc in
lemma exists_analyticOn_factor_R_at_add_one (l' : Fin (m K)) :
  ∃ (R' : ℂ → ℂ) (U : Set ℂ),
    U ∈ nhds (l' + 1 : ℂ) ∧
    (l' + 1 : ℂ) ∈ U ∧
    (∀ z ∈ U, (R α β σ α' β' γ' hirr htriv habc) q hq0 h2mq z = (z - (l' + 1)) ^ ((r α β σ α' β' γ'
        hirr htriv habc) q hq0 h2mq) * R' z) ∧
    AnalyticOn ℂ R' U := by
  have hRanalytic : AnalyticAt ℂ ((R α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) (l' + 1 : ℂ) := by
    fun_prop
  have hAO := (AnalyticAt.analyticOrderAt_eq_natCast
      (f := (R α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) (z₀ := (l' + 1 : ℂ))
      (n := (rOrder α β σ α' β' γ' hirr htriv habc) q hq0 h2mq (l' + 1)) hRanalytic).1
      ((R_order_eq α β σ α' β' γ' hirr htriv habc) q hq0 h2mq (l' + 1))
  rcases hAO with ⟨R'', horder, -, hfilter⟩
  let o : ℕ := (rOrder α β σ α' β' γ' hirr htriv habc) q hq0 h2mq (l' + 1)
  have ho : (r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq ≤ o := by
    rcases (rProp α β σ α' β' γ' hirr htriv habc) q hq0 h2mq with ⟨_, hr⟩
    simpa [o, ge_iff_le, (R_order_eq α β σ α' β' γ' hirr htriv habc) q hq0 h2mq (l' +
        1)] using hr l'
  rcases (Filter.eventually_iff_exists_mem).1 hfilter with ⟨U, hU, hU_prop⟩
  rcases AnalyticAt.exists_mem_nhds_analyticOnNhd horder with ⟨U2, hU2, hU2prop⟩
  refine ⟨(fun z => (z - (l' + 1)) ^ (o - (r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) * R'' z), U
      ∩ U2,
  Filter.inter_mem hU hU2, mem_of_mem_nhds (Filter.inter_mem hU hU2), ?_, ?_⟩
  · intro z hz
    calc
      (R α β σ α' β' γ' hirr htriv habc) q hq0 h2mq z = (z - (l' + 1)) ^ o * R'' z := by
        simpa [smul_eq_mul] using hU_prop z hz.1
      _ = (z - (l' + 1)) ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) *
        ((z - (l' + 1)) ^ (o - (r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) * R'' z) := by
        rw [← Nat.add_sub_of_le ho, pow_add]
        simp [mul_assoc, mul_left_comm, mul_comm]
  · intro z hz
    have hpow : AnalyticAt ℂ (fun z : ℂ => (z - (l' + 1)) ^ (o - (r α β σ α' β' γ' hirr htriv habc)
        q hq0 h2mq)) z := by
      exact (AnalyticAt.sub analyticAt_id analyticAt_const).pow (o - (r α β σ α' β' γ' hirr htriv
          habc) q hq0 h2mq)
    exact (hpow.mul (hU2prop z hz.2)).analyticWithinAt

/-- An analytic function agreeing with the factored `R` near `l' + 1`. -/
noncomputable def R'U (l' : Fin (m K)) : ℂ → ℂ :=
  (exists_analyticOn_factor_R_at_add_one α β σ α' β' γ' hirr htriv habc q hq0 h2mq l').choose

/-- A neighbourhood of `l' + 1` on which `R` factors as `(z - (l' + 1)) ^ r * R'U`. -/
noncomputable def U (l' : Fin (m K)) : Set ℂ :=
  (exists_analyticOn_factor_R_at_add_one α β σ α' β' γ' hirr htriv habc q hq0 h2mq
      l').choose_spec.choose

include α β σ α' β' γ' hirr htriv habc in
lemma R'_spec (l' : Fin (m K)) :
    U α β σ α' β' γ' hirr htriv habc q hq0 h2mq l' ∈ nhds (l' + 1 : ℂ) ∧
    (l' + 1 : ℂ) ∈ U α β σ α' β' γ' hirr htriv habc q hq0 h2mq l' ∧
    (∀ z ∈ U α β σ α' β' γ' hirr htriv habc q hq0 h2mq l',
      (R α β σ α' β' γ' hirr htriv habc) q hq0 h2mq z = (z - (l' + 1)) ^ (r α β σ α' β' γ' hirr
          htriv habc) q hq0 h2mq * R'U α β σ α' β' γ' hirr htriv habc q hq0 h2mq l' z) ∧
    AnalyticOn ℂ (R'U α β σ α' β' γ' hirr htriv habc q hq0 h2mq l') (U α β σ α' β' γ' hirr htriv
        habc q hq0 h2mq l') :=
  (exists_analyticOn_factor_R_at_add_one α β σ α' β' γ' hirr htriv habc q hq0 h2mq
      l').choose_spec.choose_spec

/-- The everywhere-analytic representative of the factored `R`. -/
noncomputable def R'R (l' : Fin (m K)) (z : ℂ) : ℂ :=
  (R α β σ α' β' γ' hirr htriv habc) q hq0 h2mq z * (z - (l' + 1)) ^ (-((r α β σ α' β' γ' hirr htriv
      habc) q hq0 h2mq : ℤ))

/-- The analytic function with `R z = (z - (l' + 1)) ^ r * R' z` near `l' + 1`. -/
def R' (l' : Fin ((m K))) : ℂ → ℂ :=
  let U := U α β σ α' β' γ' hirr htriv habc q hq0 h2mq l'
  letI : ∀ z, Decidable (z ∈ U) := by
    intros z
    exact Classical.propDecidable (z ∈ U)
  fun z ↦
    if z = l' + 1 then
      (R'U α β σ α' β' γ' hirr htriv habc q hq0 h2mq l') z
    else
      (R'R α β σ α' β' γ' hirr htriv habc q hq0 h2mq l') z

include α β σ α' β' γ' hirr htriv habc in
lemma R'_eq_R'U_on_nhds (l' : Fin ((m K))) :
  let U := (U α β σ α' β' γ' hirr htriv habc) q hq0 h2mq l'
  ∀ z ∈ U, (R' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq l' z = (R'U α β σ α' β' γ' hirr htriv
      habc) q hq0 h2mq l' z := by
  intros U z hz
  unfold R'
  split_ifs with h
  · rfl
  · unfold R'R
    rw [(R'_spec α β σ α' β' γ' hirr htriv habc q hq0 h2mq l').2.2.1 z hz, mul_right_comm,
        ← zpow_natCast, ← zpow_add₀ (sub_ne_zero.mpr h)]
    simp

include α β σ α' β' γ' hirr htriv habc in
lemma R'_eq_R'R (l' : Fin (m K)) :
    ∀ z ∈ {z : ℂ | z ≠ l' + 1},
      (R' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq l' z = (R'R α β σ α' β' γ' hirr htriv
          habc) q hq0 h2mq l' z := by
  intro z hz
  unfold R'
  split_ifs with h
  · exact (hz h).elim
  · rfl

include α β σ α' β' γ' hirr htriv habc in
lemma R_mul_pow_neg_analyticOn (l' : Fin (m K)) :
    let R'R := (R'R α β σ α' β' γ' hirr htriv habc) q hq0 h2mq l'
    AnalyticOn ℂ R'R {z | z ≠ l' + 1} := by
  unfold R'R
  refine AnalyticOn.mul ?_ ?_
  · apply AnalyticOn.mono
    · have : ∀ (z : ℂ), AnalyticAt ℂ ((R α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) z := by fun_prop
      · apply analyticOn_univ.mpr (fun x a ↦ this x)
    simp only [Set.subset_univ]
  · apply AnalyticOn.zpow (AnalyticOn.sub analyticOn_id analyticOn_const)
    exact fun z hz ↦ sub_ne_zero.mpr hz

include α β σ α' β' γ' hirr htriv habc in
lemma R'_analyticAt (l' : Fin ((m K))) :
  ∀ z : ℂ, AnalyticAt ℂ (R' α β σ α' β' γ' hirr htriv habc q hq0 h2mq l') z := by
  intro z
  by_cases hz : z = l' + 1
  · rcases R'_spec α β σ α' β' γ' hirr htriv habc q hq0 h2mq l' with ⟨hU, -, -, hA⟩
    have hAt :
      AnalyticAt ℂ (R'U α β σ α' β' γ' hirr htriv habc q hq0 h2mq l') z :=
      AnalyticOn.analyticAt
        (f := R'U α β σ α' β' γ' hirr htriv habc q hq0 h2mq l')
        (z := z) (s := U α β σ α' β' γ' hirr htriv habc q hq0 h2mq l')
        hA (hU := by simpa [hz] using hU)
    refine hAt.congr ?_
    refine Filter.eventually_of_mem (by simpa [hz] using hU) ?_
    intro w hw
    symm
    exact (R'_eq_R'U_on_nhds α β σ α' β' γ' hirr htriv habc q hq0 h2mq l' _ hw)
  · have hU : ({w : ℂ | w ≠ l' + 1} : Set ℂ) ∈ nhds z :=
      IsOpen.mem_nhds isOpen_ne (by simpa using hz)
    have hAt :
      AnalyticAt ℂ (R'R α β σ α' β' γ' hirr htriv habc q hq0 h2mq l') z :=
      AnalyticOn.analyticAt
        (f := R'R α β σ α' β' γ' hirr htriv habc q hq0 h2mq l')
        (z := z) (s := {w : ℂ | w ≠ l' + 1})
        (R_mul_pow_neg_analyticOn α β σ α' β' γ' hirr htriv habc q hq0 h2mq l')
        (hU := hU)
    refine hAt.congr ?_
    refine Filter.eventually_of_mem hU ?_
    intro w hw
    symm
    exact (R'_eq_R'R α β σ α' β' γ' hirr htriv habc q hq0 h2mq l' _ hw)

include α β σ α' β' γ' hirr htriv habc in
lemma R_eq_pow_mul_R' (l' : Fin (m K)) (z : ℂ) :
    (R α β σ α' β' γ' hirr htriv habc) q hq0 h2mq z = (z - (l' + 1)) ^ (r α β σ α' β' γ' hirr htriv
        habc) q hq0 h2mq *
    (R' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq l' z := by
  unfold R'
  split_ifs with h
  · exact h ▸ (R'_spec α β σ α' β' γ' hirr htriv habc q hq0 h2mq l').2.2.1 _
      (R'_spec α β σ α' β' γ' hirr htriv habc q hq0 h2mq l').2.1
  · unfold R'R
    rw [mul_left_comm, ← zpow_natCast, ← zpow_add₀ (sub_ne_zero.mpr h),
        add_neg_cancel, zpow_zero, mul_one]

/-- The evaluation points `1, …, m`, as a `Finset ℂ`. -/
def evaluationPoints (K : Type) [Field K] [NumberField K] : Finset ℂ :=
   Finset.image (fun (k': ℕ) ↦ (k' + 1 : ℂ)) (Finset.range (m K))

@[nolint unusedArguments]
lemma mem_evaluationPoints_iff {z : ℂ} :
    z ∈ (evaluationPoints K) ↔ ∃ k : Fin (m K), z = k + 1 := by
  simp [evaluationPoints, Finset.mem_image, Fin.exists_iff]
  grind

/-- The complement of the evaluation points. -/
def evaluationPointsCompl (K : Type) [Field K] [NumberField K] : Set ℂ := ((evaluationPoints K))ᶜ


@[nolint unusedArguments]
lemma S_U_isOpen : IsOpen (evaluationPointsCompl K) :=
  isOpen_compl_iff.mpr (Finset.isClosed _)


lemma S.U_nhds :
  ∀ z, z ∈ evaluationPointsCompl K → (evaluationPointsCompl K) ∈ nhds z :=
  fun z hz ↦ IsOpen.mem_nhds (S_U_isOpen) hz

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma sub_ne_zero_of_mem_evaluationPoints_compl {z : ℂ}
    (hz : z ∈ (evaluationPointsCompl K)) (k : Fin (m K)) :
    z - (k + 1 : ℂ) ≠ 0 := by
  rw [sub_ne_zero]
  exact fun h => hz ((mem_evaluationPoints_iff) |>.mpr ⟨k, h⟩)

/-- The auxiliary function divided by its zeros. -/
def SR : ℂ → ℂ := fun z ↦
  ((R α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) z * ((r α β σ α' β' γ' hirr htriv habc) q hq0
      h2mq).factorial *
    ((z - ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + 1 : ℂ)) ^ (-((r α β σ α' β' γ' hirr
        htriv habc) q hq0 h2mq) : ℤ)) *
    (∏ k' ∈ Finset.range ((m K)) \ {↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)},
      ((((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + 1) - (k' + 1)) / (z - (k' + 1 :
          ℂ))) ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq))

include α β σ α' β' γ' hirr htriv habc in
lemma SR_analyticOn_evaluationPoints_compl :
    AnalyticOn ℂ ((SR α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) ((evaluationPointsCompl K)) := by
  unfold SR
  refine .mul (.mul (.mul ?_ analyticOn_const) ?_) ?_
  · have : ∀ (z : ℂ), AnalyticAt ℂ ((R α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) z := by fun_prop
    apply AnalyticOn.mono (f:=((R α β σ α' β' γ' hirr htriv habc) q hq0
        h2mq)) (s:=(evaluationPointsCompl K))
    · apply analyticOn_univ.mpr fun x a ↦ this x
    simp only [Set.subset_univ]
  · refine AnalyticOn.zpow (AnalyticOn.sub analyticOn_id analyticOn_const) fun z hz ↦ ?_
    exact sub_ne_zero_of_mem_evaluationPoints_compl α β σ α' β' γ' hirr htriv habc hz _
  · apply Finset.analyticOn_fun_prod
    intros u hu
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hu
    apply AnalyticOn.fun_pow
    refine AnalyticOn.div (analyticOn_const) ?_ ?_
    · refine DifferentiableOn.analyticOn ?_ (S_U_isOpen)
      fun_prop
    · exact fun z hz ↦ sub_ne_zero_of_mem_evaluationPoints_compl α β σ α' β' γ' hirr htriv habc hz
        ⟨u, hu.1⟩

include α β σ α' β' γ' hirr htriv habc in
lemma SR_AnalyticAt (z : ℂ) (hz : z ∈ evaluationPointsCompl K) :
    AnalyticAt ℂ ((SR α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) z :=
  AnalyticOn.analyticAt (f:=((SR α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)) (z := z)
    (s := evaluationPointsCompl K)
    (SR_analyticOn_evaluationPoints_compl α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
    (hU:= S.U_nhds z hz)

/-- The restriction of `SR` used near the distinguished point `l₀' + 1`. -/
def SRl0 : ℂ → ℂ := fun z ↦
  ((R' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0
      h2mq)) z * (((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq).factorial)  *
    (∏ k' ∈ Finset.range ((m K)) \ {↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)},
    ((((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq +1) - (k' + 1)) / (z - (k' + 1 : ℂ))) ^ ((r α
        β σ α' β' γ' hirr htriv habc) q hq0 h2mq))

/-- The restriction of `SR` used near a point `l' + 1` other than `l₀' + 1`. -/
def SRl (l' : Fin ((m K))) : ℂ → ℂ := fun z ↦
  ((R' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq l') z *
    ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq).factorial *
    ((z - ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + 1 : ℂ)) ^ (-((r α β σ α' β' γ' hirr
        htriv habc) q hq0 h2mq) : ℤ)) *
    (∏ k' ∈ (Finset.range ((m K)) \ ({↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℕ)} ∪
        {↑(l' : ℕ)})),
      ((((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + 1) - (k' + 1)) / (z - (k' + 1 :
          ℂ))) ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)) *
    ((((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + 1)- (l' + 1)) ^ ((r α β σ α' β' γ' hirr
        htriv habc) q hq0 h2mq))

/-- The entire function obtained from `R` by dividing out all of its zeros. -/
def S : ℂ → ℂ :=
  fun z ↦
    if H : ∃ (k' : Fin ((m K))), z = (k' : ℂ) + 1 then
      if z = ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + 1) then
        (SRl0 α β σ α' β' γ' hirr htriv habc) q hq0 h2mq z
      else
        (SRl α β σ α' β' γ' hirr htriv habc) q hq0 h2mq (H.choose) z
    else
      (SR α β σ α' β' γ' hirr htriv habc) q hq0 h2mq z

include α β σ α' β' γ' hirr htriv habc in
lemma SR_eq_SRl0 {z : ℂ} :
  z ∈ (evaluationPointsCompl K) →
  ((SRl0 α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) z = ((SR α β σ α' β' γ' hirr htriv habc) q hq0
      h2mq) z := by
  intro hz
  let a : ℂ := ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℂ) + 1
  have hne : z - a ≠ 0 := by
   simpa [a] using
    sub_ne_zero_of_mem_evaluationPoints_compl α β σ α' β' γ' hirr htriv habc hz ((l₀' α β σ α' β' γ'
        hirr htriv habc) q hq0 h2mq)
  have hpow :
    (z - a) ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) *
    (z - a) ^ (-((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℤ)) = (1 : ℂ) := by
   rw [← zpow_natCast, ← zpow_add₀ hne, add_neg_cancel, zpow_zero]
  unfold SRl0 SR
  rw [(R_eq_pow_mul_R' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq ((l₀' α β σ α' β' γ' hirr htriv
      habc) q hq0 h2mq) z]
  calc
  ((R' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0
      h2mq)) z *
    ↑(((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq).factorial) *
    ∏ k' ∈ Finset.range (m K) \ {↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)},
      ((((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + 1) - (k' + 1)) / (z - (k' + 1 : ℂ))) ^
      ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)
    =
    ((z - a) ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) * (z - a) ^ (-((r α β σ α' β' γ' hirr
        htriv habc) q hq0 h2mq : ℤ))) *
      (((R' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0
          h2mq)) z *
      ↑(((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq).factorial) *
      ∏ k' ∈ Finset.range (m K) \ {↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)},
        ((((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + 1) - (k' + 1)) / (z - (k' + 1 : ℂ))) ^
        ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)) := by
    simp [hpow]
    grind
  _ =
    ((z - a) ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) *
      ((R' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0
          h2mq)) z) *
      ↑(((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq).factorial) *
      (z - a) ^ (-((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℤ)) *
      ∏ k' ∈ Finset.range (m K) \ {↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)},
      ((((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + 1) - (k' + 1)) / (z - (k' + 1 : ℂ))) ^
        ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) := by
    ac_rfl





--fix l+1
include α β σ α' β' γ' hirr htriv habc in
lemma SR_eq_SRl {z : ℂ} (l' : Fin ((m K))) (hl : l' ≠ (l₀' α β σ α' β' γ' hirr htriv habc) q hq0
    h2mq) :
    z ∈ (evaluationPointsCompl K) →
    ((SRl α β σ α' β' γ' hirr htriv habc) q hq0 h2mq l') z = ((SR α β σ α' β' γ' hirr htriv habc) q
        hq0 h2mq) z := by
  intros hz
  unfold evaluationPointsCompl at *
  dsimp [SR, SRl]
  nth_rw 3 [mul_assoc]
  simp only [zpow_neg, zpow_natCast]
  dsimp [evaluationPoints] at hz
  simp only [coe_image, coe_range, mem_compl_iff,
    Set.mem_image, Set.mem_Iio, not_exists,
    not_and] at hz
  have := R_eq_pow_mul_R' α β σ α' β' γ' hirr htriv habc q hq0 h2mq l' z
  rw [this]; clear this
  simp only [← mul_assoc]
  nth_rw 8 [mul_comm]
  rw [mul_assoc  ((R' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq (l') z) ((z - (↑↑(l') + 1)) ^ (r α
      β σ α' β' γ' hirr htriv habc) q hq0 h2mq)]
  rw [mul_comm ((z - (↑↑(l') + 1)) ^ (r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) ↑((r α β σ α' β'
      γ' hirr htriv habc) q hq0 h2mq).factorial]
  unfold R'
  simp only [mul_assoc]
  have : l' < (m K) := by simp only [Fin.is_lt]
  have H := (hz l' this)
  have : 1 =  (z - (↑↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) + 1)) ^ ↑((r α β σ α' β' γ'
      hirr htriv habc) q hq0 h2mq) *
      (z - (↑↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) + 1)) ^ (-↑(((r α β σ α' β' γ' hirr
          htriv habc) q hq0 h2mq) : ℤ)) := by
    simp only [zpow_neg, zpow_natCast]
    symm
    apply Complex.mul_inv_cancel
    intros Hz
    simp only [pow_eq_zero_iff', ne_eq] at Hz
    have : ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) < (m K) :=  by simp only [Fin.is_lt]
    have H := hz  ↑(((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)) this
    apply H
    rw [sub_eq_add_neg] at Hz
    rw [add_eq_zero_iff_eq_neg] at Hz
    simp only [neg_neg] at Hz
    symm
    rw [Hz.1]
  split
  · rename_i H
    rw [H]
    simp only [add_sub_add_right_eq_sub, sub_self,
      mul_eq_mul_left_iff, Nat.cast_eq_zero]
    left; left
    rw [zero_pow]
    simp only [zero_mul, mul_eq_zero, inv_eq_zero, pow_eq_zero_iff', ne_eq]
    right
    right
    constructor
    by_contra HR
    apply hl
    (expose_names; exact False.elim (hz (↑l') this_1 (id (Eq.symm H))))
    (expose_names; exact fun a ↦ hz (↑l') this_1 (id (Eq.symm H)))
    (expose_names; exact fun a ↦ hz (↑l') this_1 (id (Eq.symm H)))
  · nth_rw 6 [← mul_assoc]
    nth_rw 5 [← mul_assoc]
    nth_rw 8 [mul_comm]
    simp only [mul_assoc]
    simp only [mul_eq_mul_left_iff, inv_eq_zero,
      pow_eq_zero_iff', ne_eq, Nat.cast_eq_zero]
    left
    left
    left
    rw [mul_comm]
    nth_rw 2 [mul_comm]
    clear this
    have H :=  Finset.prod_union
      (s₁:= Finset.range (m K) \ ({↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) }∪ {↑l'}))
      (s₂:= {↑l'})
      (f:= fun k' ↦ ((↑↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) + 1 -
       (↑k' + 1)) / (z - (↑k' + 1))) ^ (r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)
      (by aesop)
    have : Finset.range (m K) \ ({↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) }∪
        {↑l'}) ∪ {↑l'}
     = Finset.range (m K) \ {(↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq))} := by grind

    simp only [Finset.prod_singleton] at H
    rw [this] at H
    rw [H]; clear H this
    rw [mul_comm]
    simp only [mul_assoc]
    congr
    simp only [add_sub_add_right_eq_sub]
    rw [← inv_mul_eq_div, mul_pow, mul_comm]
    simp only [← mul_assoc]
    rw [← mul_pow, mul_inv_cancel₀]
    · simp only [one_pow, one_mul]
    grind only


include α β σ α' β' γ' hirr htriv habc in
lemma S_eq_restricted_of_mem_compl {z : ℂ} :
  z ∈ (evaluationPointsCompl K) →
  (SR α β σ α' β' γ' hirr htriv habc) q hq0 h2mq z = (S α β σ α' β' γ' hirr htriv
      habc) q hq0 h2mq z := by
  intros hz
  unfold evaluationPointsCompl at *
  unfold S
  split
  · rename_i H1
    exact (hz ((mem_evaluationPoints_iff) |>.mpr H1)).elim
  · rfl

lemma dist_nat_cast_lt_one (n m : ℕ) : dist (n : ℂ) (m : ℂ) < 1 ↔ n = m := by
  apply Iff.intro
  rw [Complex.dist_eq]
  by_cases H : m ≤ n
  · have : norm (((n : ℂ)) - (m : ℂ)) = (n - m : ℕ) := by
     norm_cast
    rw [this]
    simp only [Nat.cast_lt_one]
    intros H'
    grind
  · have : norm (((n : ℂ)) - (m : ℂ)) = norm ((m : ℂ) - (n : ℂ)) := by
      calc _ = norm (-((m : ℂ) - (n : ℂ))) := ?_
           _ = norm (((m : ℂ)) - (n : ℂ)) := ?_
      · simp only [neg_sub]
      · symm
        rw [← norm_neg]
    rw [this]
    have : norm (((m : ℂ)) - (n : ℂ)) = (m - n : ℕ) := by
     simp only [not_le] at H
     have : n ≤ m := by grind
     norm_cast
    rw [this]
    simp only [Nat.cast_lt_one]
    intros H'
    grind
  · aesop


--SR_analytic_S.U follow this for srl0 too
include α β σ α' β' γ' hirr htriv habc in
lemma SRl_is_analytic_at_ball_of_radius_one (l' : Fin ((m K))) (hl : l' ≠ (l₀' α β σ α' β' γ' hirr
    htriv habc) q hq0 h2mq) :
  AnalyticOn ℂ ((SRl α β σ α' β' γ' hirr htriv habc) q hq0 h2mq l') (Metric.ball ((l' : ℂ) + 1)
      1) := by
  unfold SRl
  refine AnalyticOn.mul ?_ ?_
  · apply AnalyticOn.mul ?_ ?_
    · apply AnalyticOn.mul ?_ ?_
      · have := (R'_analyticAt α β σ α' β' γ' hirr htriv habc) q hq0 h2mq
        apply AnalyticOn.mul (AnalyticOnNhd.analyticOn fun x a ↦ this l' x) analyticOn_const
      · apply AnalyticOn.fun_zpow
        · apply AnalyticOn.mono
          · refine analyticOn_univ_iff_differentiable.mpr ?_
            refine (fun_sub_iff_left ?_).mpr ?_
            simp only [differentiable_const]
            simp only [differentiable_fun_id]
          · exact fun ⦃a⦄ a ↦ trivial
        · intros z hz
          simp only [Metric.mem_ball] at hz
          apply sub_ne_zero_of_ne
          intro H
          rw [H] at hz
          simp only [dist_add_right] at hz
          have : (((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℕ) : ℂ)≠ ((l' : ℕ) : ℂ) := by
            intros HC
            apply hl
            simp only [Nat.cast_inj] at HC
            symm
            aesop
          rw [← dist_pos] at this
          have Hdist := ( dist_nat_cast_lt_one (((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq))
              ↑↑l').1
          have Hdist := Hdist hz
          rw [Hdist] at this
          aesop
    · apply Finset.analyticOn_fun_prod
      intros u hu
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_range,
          Finset.mem_singleton] at hu
      apply AnalyticOn.fun_pow (AnalyticOn.div analyticOn_const
         (DifferentiableOn.analyticOn (by fun_prop) Metric.isOpen_ball) (fun x hx ↦ ?_))
      · simp only [Metric.mem_ball] at hx
        obtain ⟨h1, h2⟩ := hu
        · intros HC
          simp only [not_or] at h2
          obtain ⟨hu, hul0⟩ := h2
          rw [sub_eq_zero] at HC
          rw [HC] at hx
          simp only [dist_add_right] at hx
          rw [← ne_eq] at *
          have Hdist := ( dist_nat_cast_lt_one u ↑↑l').1
          have Hdist := Hdist hx
          rw [Hdist] at hx
          simp only [dist_self, zero_lt_one] at hx
          exact hul0 Hdist
  · exact analyticOn_const


include α β σ α' β' γ' hirr htriv habc in
lemma SRl0_is_analytic_at_ball_of_radius_one :
  AnalyticOn ℂ ((SRl0 α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)
    (Metric.ball ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + 1) 1) := by
  unfold SRl0
  refine AnalyticOn.mul ?_ ?_
  · refine AnalyticOn.mul ?_ analyticOn_const
    have hA := (R'_analyticAt α β σ α' β' γ' hirr htriv habc) q hq0 h2mq
    exact AnalyticOnNhd.analyticOn (fun z hz ↦ hA ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)
        z)
  · apply Finset.analyticOn_fun_prod
    intro u hu
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hu
    refine (AnalyticOn.fun_pow (𝕜 := ℂ) (n := (r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) ?_)
    refine AnalyticOn.div (𝕜 := ℂ) analyticOn_const
      (AnalyticOn.sub analyticOn_id analyticOn_const) ?_
    intro z hz hzero
    have hz1 : dist ((u : ℂ) + 1) (((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℂ) +
        1) < 1 := by
      have hz' : z = (u : ℂ) + 1 := sub_eq_zero.mp hzero
      simpa [Metric.mem_ball, hz'] using hz
    have hz0 : dist (u : ℂ) ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℂ) < 1 := by
      simpa [dist_add_right] using hz1
    have hu' : u = ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℕ) :=
      (dist_nat_cast_lt_one u ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℕ)).1 hz0
    exact hu.2 hu'

lemma AnalyticAtEq (f g : ℂ → ℂ) (U : Set ℂ) (z : ℂ) :
  (hU : U ∈ nhds z) → z ∈ U → (∀ z ∈ U, f z = g z) →
     AnalyticAt ℂ f z → AnalyticAt ℂ g z := by
    intros hU _ hfg hf
    exact hf.congr (Filter.eventually_of_mem hU hfg)

include α β σ α' β' γ' hirr htriv habc in
lemma holS :
  ∀ z, AnalyticAt ℂ ((S α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) z := by
  intro z
  by_cases H : ∃ k' : Fin (m K), z = (k' : ℂ) + 1
  · rcases H with ⟨l', hl'⟩
    by_cases Hzl0 : z = ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℂ) + 1
    · refine AnalyticAtEq
        (f := (SRl0 α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)
        (g := (S α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)
        (U := Metric.ball (((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℂ) + 1) 1)
        (z := z)
        ?_ ?_ ?_ ?_
      · rw [Hzl0]
        exact Metric.ball_mem_nhds _ zero_lt_one
      · rw [Hzl0]
        simp [Metric.mem_ball]
      · intro w hw
        by_cases hw0 : w = ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℂ) + 1
        · unfold S
          let Hw : ∃ k' : Fin (m K), w = (k' : ℂ) + 1 := ⟨(l₀' α β σ α' β' γ' hirr htriv habc) q hq0
              h2mq, hw0⟩
          simp [Hw, hw0]
        · have hwCompl : w ∈ evaluationPointsCompl K := by
            intro hwEval
            rcases ((mem_evaluationPoints_iff)).1 hwEval with ⟨k, rfl⟩
            have hdist : dist (k : ℂ) ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq :
                ℂ) < 1 := by
              have : dist ((k : ℂ) + 1) (((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℂ) +
                  1) < 1 := by
                simpa [Metric.mem_ball] using hw
              simpa [dist_add_right] using this
            have hk : (k : ℕ) = ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℕ) :=
              (dist_nat_cast_lt_one (k : ℕ) ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq :
                  ℕ)).1 hdist
            exact hw0 (by simpa [hk])
          exact ((SR_eq_SRl0 α β σ α' β' γ' hirr htriv habc) q hq0 h2mq hwCompl).trans
            ((S_eq_restricted_of_mem_compl α β σ α' β' γ' hirr htriv habc) q hq0 h2mq hwCompl)
      · have hU :
          Metric.ball (((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℂ) + 1) 1 ∈ nhds z := by
          simpa [Hzl0] using
            (Metric.ball_mem_nhds (((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℂ) + 1)
                zero_lt_one)
        exact AnalyticOn.analyticAt
          (f := (SRl0 α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)
          (s := Metric.ball (((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℂ) + 1) 1)
          (z := z)
          ((SRl0_is_analytic_at_ball_of_radius_one α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)
          (hU := hU)
    · refine AnalyticAtEq
        (f := (SRl α β σ α' β' γ' hirr htriv habc) q hq0 h2mq l')
        (g := (S α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)
        (U := Metric.ball ((l' : ℂ) + 1) 1)
        (z := z)
        ?_ ?_ ?_ ?_
      · rw [hl']
        exact Metric.ball_mem_nhds _ zero_lt_one
      · rw [hl']
        simp [Metric.mem_ball]
      · intro w hw
        by_cases hw1 : w = (l' : ℂ) + 1
        · unfold S
          let Hw : ∃ k' : Fin (m K), w = (k' : ℂ) + 1 := ⟨l', hw1⟩
          have hw_ne_l0 : w ≠ ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℂ) + 1 := by
            intro hw0
            apply Hzl0
            calc
              z = (l' : ℂ) + 1 := hl'
              _ = w := by simpa [hw1]
              _ = ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℂ) + 1 := hw0
          have hchoose : Hw.choose = l' := by
            apply Fin.ext
            have hEq : ((Hw.choose : Fin (m K)) : ℂ) + 1 = (l' : ℂ) + 1 := by
              calc
                ((Hw.choose : Fin (m K)) : ℂ) + 1 = w := by simpa using Hw.choose_spec.symm
                _ = (l' : ℂ) + 1 := hw1
            have hNat : (Hw.choose : ℕ) = (l' : ℕ) := by
              have := congrArg (fun x : ℂ => x - 1) hEq
              simpa using this
            simpa using hNat
          simp [Hw, hw_ne_l0, hchoose]
        · have hwCompl : w ∈ evaluationPointsCompl K := by
            intro hwEval
            rcases ((mem_evaluationPoints_iff)).1 hwEval with ⟨k, rfl⟩
            have hdist : dist (k : ℂ) (l' : ℂ) < 1 := by
              have : dist ((k : ℂ) + 1) ((l' : ℂ) + 1) < 1 := by
                simpa [Metric.mem_ball] using hw
              simpa [dist_add_right] using this
            have hk : (k : ℕ) = (l' : ℕ) :=
              (dist_nat_cast_lt_one (k : ℕ) (l' : ℕ)).1 hdist
            exact hw1 (by simpa [hk])
          have hl_ne : l' ≠ (l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq := by
            intro hEq
            apply Hzl0
            simpa [hl', hEq]
          exact ((SR_eq_SRl α β σ α' β' γ' hirr htriv habc) q hq0 h2mq l' hl_ne hwCompl).trans
            ((S_eq_restricted_of_mem_compl α β σ α' β' γ' hirr htriv habc) q hq0 h2mq hwCompl)
      · have hl_ne : l' ≠ (l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq := by
          intro hEq
          apply Hzl0
          simp [hl', hEq]
        have hU : Metric.ball ((l' : ℂ) + 1) 1 ∈ nhds z := by
          rw [hl']
          exact Metric.ball_mem_nhds _ zero_lt_one
        exact ((SRl_is_analytic_at_ball_of_radius_one α β σ α' β' γ' hirr htriv habc) q hq0 h2mq l'
            hl_ne).analyticAt hU
  · have hzCompl : z ∈ evaluationPointsCompl K := by
      intro hzEval
      exact H (((mem_evaluationPoints_iff)).1 hzEval)
    refine AnalyticAtEq
      (f := (SR α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)
      (g := (S α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)
      (U := evaluationPointsCompl K)
      (z := z)
      ?_ ?_ ?_ ?_
    · exact S.U_nhds z hzCompl
    · exact hzCompl
    · intro w hw
      exact (S_eq_restricted_of_mem_compl α β σ α' β' γ' hirr htriv habc) q hq0 h2mq hw
    · exact (SR_AnalyticAt α β σ α' β' γ' hirr htriv habc) q hq0 h2mq z hzCompl


include α β σ α' β' γ' hirr htriv habc in
lemma hcauchy :
  (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(0, (m K) * (1 + ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq /
      q))),
    (z - ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + 1 : ℂ))⁻¹ * ((S α β σ α' β' γ' hirr
        htriv habc) q hq0 h2mq) z) =
    ((S α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq
        + 1) := by
  apply two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (s := (∅ : Set ℂ))
  · simpa using (Set.countable_empty : Set.Countable (∅ : Set ℂ))
  · have hmpos : (0 : ℝ) < (m K) := by
      simp only [Nat.cast_pos]
      exact Nat.zero_lt_succ (2 * (h K) + 1)
    have hdivpos : (0 : ℝ) < ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / q := by
      exact div_pos (by exact_mod_cast r_qt_0 α β σ α' β' γ' hirr htriv habc q hq0 h2mq) (by exact_mod_cast hq0)
    have hmul : ((m K) : ℝ) < (m K) * (1 + ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) /
        q) := by
      have h1 : (1 : ℝ) < 1 + ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / q := by linarith
      simpa [one_mul] using mul_lt_mul_of_pos_left h1 hmpos
    have hle : ((((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℕ) + 1 : ℕ) : ℝ) ≤ (m K) := by
      exact_mod_cast Nat.succ_le_of_lt ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq).isLt
    have hz : ‖((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + 1 : ℂ)‖ < (m K) * (1 + ((r α β σ
        α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / q) := by
      norm_cast
      exact lt_of_le_of_lt hle hmul
    simpa [Metric.mem_ball, dist_zero_right] using hz
  · intro x hx
    simpa using
      (DifferentiableAt.differentiableWithinAt
      (AnalyticAt.differentiableAt (holS α β σ α' β' γ' hirr htriv habc q hq0 h2mq
          x))).continuousWithinAt
  · intro x hx
    simpa using AnalyticAt.differentiableAt (holS α β σ α' β' γ' hirr htriv habc q hq0 h2mq x)

include α β σ α' β' γ' hirr htriv habc in
lemma S_eq_SR_on_circle : ∀ (z : ℂ) (hz : z ∈ Metric.sphere 0
    ((m K) * (1 + ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / (q : ℝ)))),
  (S α β σ α' β' γ' hirr htriv habc) q hq0 h2mq z = (SR α β σ α' β' γ' hirr htriv
      habc) q hq0 h2mq z := by
  intros z hz
  unfold S
  split
  · rename_i H1
    obtain ⟨k',hk'⟩ := H1
    have : norm z ≤ (m K) := by
      rw [hk']
      norm_cast
      apply Fin.isLt
    simp only [mem_sphere_iff_norm, sub_zero] at hz
    rw [hz] at this
    by_contra HC
    apply absurd (this)
    simp only [not_le]
    nth_rw 1 [← mul_one (a:=((m K):ℝ))]
    apply mul_lt_mul' (le_refl _)
    · simp only [lt_add_iff_pos_right]
      refine div_pos ?_ ?_
      · simp only [Nat.cast_pos]; exact r_qt_0 α β σ α' β' γ' hirr htriv habc q hq0 h2mq
      · simp only [Nat.cast_pos]; exact hq0
    · simp only [zero_le_one]
    · simp only [Nat.cast_pos];exact Nat.zero_lt_succ (2 * (h K) + 1)
  · rfl

end GelfondSchneider

end
