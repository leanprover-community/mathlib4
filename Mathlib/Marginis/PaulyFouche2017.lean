import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-

In Pauly and Fouche's paper "How constructive is constructing measures?"
in the proof of Example 15 they write:
`let d be the restriction of the usual metric on Cantor space.`

Here we specify what we think they meant by `the usual metric on Cantor space`.
(In an earlier version of this file we did so by hand, but now we just import from Mathlib.)

Speaking of constructing measures, we also include the `Lebesgue measure`
on Cantor space as a Hausdorff measure,
which is also relevant to their paper as
"Particular attention is paid to Frostman measures on sets with positive Hausdorff dimension".


In `theorem measure_univ_prototype` we give a prototype of the argument from compactness that
the Hausdorff measure of the whole space is 1.

-/
noncomputable instance  myInstance :
  MetricSpace (ℕ → Bool) :=  PiNat.metricSpaceOfDiscreteUniformity (λ _ ↦ rfl)

noncomputable def μ : MeasureTheory.Measure (ℕ → Bool) := MeasureTheory.Measure.hausdorffMeasure 1

lemma dist_one {t f : ℕ → Bool} (h : t 0 ≠ f 0) :
  1 = PiNat.dist.dist t f := by
    unfold dist PiNat.dist
    simp -- use simp? instead of squeeze_scope simp
    have : PiNat.firstDiff t f = 0 := by
      rw [PiNat.firstDiff_def];simp;tauto
    split_ifs with H
    · exfalso; tauto
    · rw [this]; simp

lemma dist_of_diff {k:ℕ} {t f : ℕ → Bool} (h : t k ≠ f k) :
  (1/2)^k ≤ PiNat.dist.dist t f := by
    unfold dist PiNat.dist
    simp -- use simp? instead of squeeze_scope simp
    have : t ≠ f := by intro hc; subst hc; simp at h;
    rw [if_neg this]
    simp
    ring_nf
    suffices hh : PiNat.firstDiff t f ≤ k by
      suffices  ((1:ℝ) / 2) ^ k ≤ (1 / 2) ^ PiNat.firstDiff t f by
        norm_num;norm_num at this;tauto
      apply pow_le_pow_of_le_one;aesop;linarith;tauto
    rw [PiNat.firstDiff_def, dif_pos this];simp;use k

def fa : ℕ → Bool := λ _ ↦ false
def tr : ℕ → Bool := λ _ ↦ true

lemma dist_tf : 1 = PiNat.dist.dist tr fa :=
    dist_one (by unfold tr fa;simp)

open Classical -- this is needed below
lemma dist_bound (x y : ℕ → Bool) : PiNat.dist.dist x y ≤ 1 := by
    unfold dist PiNat.dist
    simp
    split_ifs with H
    · simp
    · rw [PiNat.firstDiff_def]
      simp
      rw [dif_neg H]
      apply inv_le_one
      norm_cast -- since both sides are ℕ cast to ℝ, let's go back to ℕ
      exact Nat.one_le_two_pow

noncomputable def d := (@PiNat.dist (λ _ : ℕ ↦ Bool)).dist
noncomputable def de := λ x y ↦ @edist (ℕ → Bool) _ x y

noncomputable def F  := λ t ↦ sSup (Set.range fun y ↦ d  t y)
noncomputable def Fe := λ t ↦ sSup (Set.range fun y ↦ de t y)

noncomputable def F_on (S : Set (ℕ → Bool)) := λ t ↦ ⨆ y ∈ S, d t y

example : F_on (Set.univ) = F := by
  apply funext;intro x;unfold F F_on;simp;rfl

lemma de_d (x y : ℕ → Bool) : (de x y).toReal = d x y := by rfl


lemma ENNReal_div_pow {k:ℕ} : (((1:ENNReal) / 2) ^ k).toNNReal = ((1:NNReal)/2)^k := by
  rw [ENNReal.toNNReal_pow,ENNReal.toNNReal_div]
  rfl

lemma edist_of_diff {k : ℕ} {t f : ℕ → Bool} (h : t k ≠ f k) :
  (1/2)^k ≤ edist t f := by
    let Q := dist_of_diff h
    let R := @de_d t f
    unfold d at R
    rw [← R] at Q
    exact ENNReal.le_of_top_imp_top_of_toNNReal_le (by simp_all)
      (by intros; rw [ENNReal_div_pow]; exact Q)

lemma sup_dist_bound (x : ℕ → Bool) : F x ≤ 1 := by
    refine Real.sSup_le ?hS (by linarith); intro _ ⟨y,hy⟩; rw [← hy]; apply dist_bound


lemma edist_bound (x z : ℕ → Bool): edist x z ≤ 1 := by
  suffices  (edist x z).toReal ≤ 1 by
    let R := (@edist_le_ofReal (ℕ → Bool) _ x z 1 zero_le_one).mpr this
    simp at R
    exact R
  exact dist_bound x z

lemma sup_edist_bound' (z : ℕ → Bool):  ⨆ i, edist i z ≤ 1 := by
  simp;intro x;exact edist_bound _ _

lemma sup_edist_lower_bound'1  {k : ℕ} (S : Set (ℕ → Bool)) (t f : ℕ → Bool)
  (h₀ : t k ≠ f k) (h₁ : t ∈ S ∧ f ∈ S)
: (1/2)^k ≤ (⨆ x ∈ S, ⨆ y ∈ S, edist x y) := by
  let Q := @edist_of_diff k t f h₀
  have : edist t f ≤ (⨆ x ∈ S, ⨆ y ∈ S, edist x y) := by
    apply EMetric.edist_le_of_diam_le h₁.1 h₁.2
    apply le_refl
  calc
  _ ≤ edist t f := Q
  _ ≤ _ := this

lemma sup_edist_lower_bound' (S : Set (ℕ → Bool)) (t f : ℕ → Bool)
  (h₀ : t 0 ≠ f 0) (h₁ : t ∈ S ∧ f ∈ S)
: 1 ≤ (⨆ x ∈ S, ⨆ y ∈ S, de x y) := by
  let U := sup_edist_lower_bound'1 S t f h₀ h₁
  simp at U;exact U

lemma sup_dist_lower_bound : 1 ≤ (⨆ x ∈ Set.univ, ⨆ y ∈ Set.univ, d x y) := by
  rw [dist_tf]
  simp only [Set.mem_univ, ciSup_unique, ge_iff_le]
  have Q₀ : d tr fa ≤ F tr := by
      refine (Real.le_sSup_iff ?h ?h').mpr ?_
      · exists 1; unfold upperBounds; simp; apply dist_bound
      · exact Set.range_nonempty fun y ↦ d tr y
      · intros; exists d tr fa; simp;tauto
  have Q₁: F tr ≤ sSup (Set.range F) := by
    apply (Real.le_sSup_iff _ _).mpr ?_
    · exists 1; unfold upperBounds; simp; exact sup_dist_bound
    · exists 1; exists tr; apply le_antisymm;
      exact sup_dist_bound _; exact le_of_eq_of_le dist_tf Q₀
    · intros; exists F tr; simp;tauto
  exact Preorder.le_trans _ _ _ Q₀ Q₁

lemma sup_sup_dist_eq : (⨆ x ∈ Set.univ, ⨆ y ∈ Set.univ,
  (@PiNat.dist (λ _ : ℕ ↦ Bool)).dist x y) = 1 := by
  apply le_antisymm
  · simp;show sSup (Set.range F) ≤ 1;apply Real.sSup_le
    intro _ ⟨y,hy⟩; rw [← hy];apply sup_dist_bound;linarith
  · exact sup_dist_lower_bound

example (x y : ℕ → Bool) : edist x y ≠ ⊤ := by
  exact @edist_ne_top (ℕ → Bool) _ x y

lemma sub_edist_ne_top : ∀ (i : ℕ → Bool), (⨆ y, edist y) i ≠ ⊤ := by
        intro z;simp;apply LT.lt.ne_top;show ⨆ i, edist i z < 2
        suffices ⨆ i, edist i z ≤ 1 by calc
          _ ≤ 1 := this
          _ < 2 := ENNReal.one_lt_two
        apply sup_edist_bound'

noncomputable def toReal_sup := λ x ↦ (⨆ y ∈ Set.univ,  @edist (ℕ → Bool) _ x y).toReal
noncomputable def sup_toReal := λ x ↦ ⨆ y ∈ Set.univ, (@edist (ℕ → Bool) _ x y).toReal

lemma toReal_sup_eq_sup_toReal₀ : ∀ x, (⨆ y ∈ Set.univ,  @edist (ℕ → Bool) _ x y).toReal =
                 ⨆ y ∈ Set.univ, (@edist (ℕ → Bool) _ x y).toReal := by
      intro x;simp;apply ENNReal.toReal_iSup;intro y;rw [edist_dist];exact ENNReal.ofReal_ne_top

lemma fubini : ⨆ (x : ℕ → Bool), ⨆ y, edist x y
             = ⨆ (y : ℕ → Bool), ⨆ x, edist x y := by
      refine iSup_congr ?h;intro i;congr;apply funext;intro x;exact edist_comm i x

lemma fubini_toReal : ⨆ (x : ℕ → Bool), (⨆ y, edist x y).toReal
                    = ⨆ (y : ℕ → Bool), (⨆ x, edist x y).toReal := by
      refine iSup_congr ?h;intro i;congr;apply funext;intro x;exact edist_comm i x

lemma toReal_sup_sup_eq_sup_toReal_sup :
  (iSup (⨆ y, @edist (ℕ → Bool) _ y)).toReal
       = ⨆ i, ((⨆ y, @edist (ℕ → Bool) _ y) i).toReal :=
  @ENNReal.toReal_iSup (ℕ → Bool) (⨆ y, @edist (ℕ → Bool) _ y) sub_edist_ne_top

lemma toReal_sup_sup_eq_sup_toReal_sup' :
  (⨆ x ∈ Set.univ, ⨆ y ∈ Set.univ, @edist (ℕ → Bool) _ x y).toReal
          = ⨆ x ∈ Set.univ, toReal_sup x := by
  simp;let Q := toReal_sup_sup_eq_sup_toReal_sup;simp at Q
  show (⨆ x, ⨆ y, edist x y).toReal = ⨆ x, (⨆ y ∈ Set.univ,  @edist (ℕ → Bool) _ x y).toReal
  simp;rw [fubini_toReal,← Q,fubini]
  congr;apply funext;intro x;simp

lemma diameter_one : Metric.diam (Set.univ : Set (ℕ → Bool)) = 1 := by
    unfold Metric.diam
    unfold EMetric.diam
    have h₁ : ⨆ x ∈ Set.univ, toReal_sup x
            = ⨆ x ∈ Set.univ, sup_toReal x := biSup_congr fun i _ ↦ toReal_sup_eq_sup_toReal₀ i

    have h₂ : (⨆ x ∈ Set.univ, ⨆ y ∈ Set.univ, @edist (ℕ → Bool) _ x y).toReal
            = ⨆ x ∈ Set.univ, sup_toReal x :=
      Eq.trans toReal_sup_sup_eq_sup_toReal_sup' h₁
    rw [h₂]
    exact sup_sup_dist_eq

lemma e_diameter_one : EMetric.diam (Set.univ : Set (ℕ → Bool)) = 1 := by
    have : (EMetric.diam (Set.univ : Set (ℕ → Bool))).toReal = 1 := diameter_one
    exact (ENNReal.toReal_eq_one_iff (EMetric.diam Set.univ)).mp this

lemma e_diameter_bound (S : Set (ℕ → Bool)) : EMetric.diam S ≤ 1 := by
  have h : S ⊆ Set.univ := by exact fun ⦃a⦄ _ ↦ trivial
  let Q := EMetric.diam_mono h
  rw [e_diameter_one] at Q
  tauto

lemma diam_one
(S : Set (ℕ → Bool))
(hS : ∃ x y, x ∈ S ∧ y ∈ S ∧ x 0 = true ∧ y 0 = false)
: EMetric.diam S = 1 := by
        obtain ⟨t,ht⟩ := hS
        obtain ⟨f,hf⟩ := ht
        let Q := sup_edist_lower_bound' S t f (by aesop) (by tauto)
        apply le_antisymm
        · exact e_diameter_bound S
        · exact Q

lemma half_nonneg {k:ℕ} : 0 ≤ ((1:ℝ)/2)^(k:ℕ) := by
  apply pow_nonneg
  apply one_div_nonneg.mpr
  exact zero_le_two

lemma ENNReal_simp {k:ℕ}:
  ENNReal.ofNNReal (((1:NNReal)      /2)^(k:ℕ))
                  = ((1:ENNReal)/2)^(k:ℕ) := by
  simp
  exact ENNReal.inv_pow

lemma NNReal_proof {k:ℕ}:
    ENNReal.ofNNReal ((⟨((1:ℝ)      /2)^(k:ℕ),@half_nonneg k⟩ : NNReal))
  = ENNReal.ofNNReal (((1:NNReal)      /2)^(k:ℕ)) := by
  exact rfl

lemma ENNReal_mess (k:ℕ) : ENNReal.ofNNReal ((⟨((1:ℝ)/2)^(k:ℕ),by
  apply pow_nonneg
  apply one_div_nonneg.mpr
  exact zero_le_two
⟩ : NNReal))
  = ((1:ENNReal)/2)^(k:ℕ) := by
  rw [NNReal_proof]
  rw [ENNReal_simp]

def ft : ℕ → Bool := fun n ↦ if n = 0 then false else if n = 1 then true else false
def ff : ℕ → Bool := fun n ↦ if n = 0 then false else if n = 1 then false else false
def tt := (λ n : ℕ ↦ ite (n=0) true (ite (n=1) true false))
def tf := (λ n : ℕ ↦ ite (n=0) true (ite (n=1) false false))

lemma edist_half {b : Bool}:
  ⨆ x ∈ {x : ℕ → Bool | x 0 = b},
  ⨆ y ∈ {x | x 0 = b}, edist x y ≤ 1 / 2 := by
              unfold
                edist
                PseudoEMetricSpace.toEDist
                EMetricSpace.toPseudoEMetricSpace
                MetricSpace.toEMetricSpace
                EMetricSpace.ofT0PseudoEMetricSpace
                PseudoMetricSpace.toPseudoEMetricSpace
                PseudoMetricSpace.edist
                MetricSpace.toPseudoMetricSpace
                myInstance
                PiNat.metricSpaceOfDiscreteUniformity
                PseudoMetricSpace.toUniformSpace
                dist
                PiNat.dist
              simp only [Set.mem_setOf_eq, iSup_le_iff]
              intro x hx y hy
              split_ifs with H
              · have : (1:ENNReal)/2 = ((1:ENNReal)/2)^1 := by exact Eq.symm (pow_one (1 / 2))
                rw [this]
                suffices PiNat.firstDiff x y ≥ 1 by
                  have : ENNReal.ofNNReal ⟨(1 / 2) ^ PiNat.firstDiff x y, by
                    refine pow_nonneg ?H (PiNat.firstDiff x y)
                    refine one_div_nonneg.mpr ?H.a
                    exact zero_le_two
                  ⟩ =  (1 / 2) ^ PiNat.firstDiff x y := by
                    apply ENNReal_mess
                  rw [this]
                  apply pow_le_pow_of_le_one
                  simp only [one_div, zero_le]
                  simp only [one_div, ENNReal.inv_le_one, Nat.one_le_ofNat]
                  tauto
                simp
                rw [PiNat.firstDiff]
                rw [dif_pos H]
                simp
                rw [hx,hy]

              · apply zero_le

lemma one_or_other
{S T : Set (ℕ → Bool)}
(hS : ¬∃ x y, x ∈ S ∧ y ∈ S ∧ x 0 = true ∧ y 0 = false)
(hT : ¬∃ x y, x ∈ T ∧ y ∈ T ∧ x 0 = true ∧ y 0 = false)
(h₀ : tr ∈ S ∨ tr ∈ T)
(h₁ : fa ∈ S ∨ fa ∈ T)
: tr ∈ S ↔ tr ∉ T := by
          constructor;intro htr₀;by_contra htr₁
          have : ¬ (fa ∈ S ∨ fa ∈ T) := by
            intro hc;cases hc with
            |inl hl =>
              apply hS;simp;use tr;constructor;
              tauto
              use fa;tauto
            |inr hr =>
              apply hT;simp;use tr;constructor;
              tauto
              use fa;tauto
          tauto;tauto

lemma four_sets_and_disjointness
{S T : Set (ℕ → Bool)}
(h : Set.univ ⊆ S ∪ T)
(hT : ¬∃ x y, x ∈ T ∧ y ∈ T ∧ x 0 = true ∧ y 0 = false)
(hl₀ : S ⊆ {x | x 0 = false})
: S = {x | x 0 = false} ∧ T = {x | x 0 = true} := by
            have h₀ : tr ∈ S ∨ tr ∈ T := h (by trivial)
            have g₀: tr ∈ T := by
              cases h₀ with
              |inl hl =>
                exfalso;
                let Q := hl₀ hl
                simp at Q
                have : true = false := Q
                tauto
              |inr hr => tauto
            constructor
            · apply Set.eq_of_subset_of_subset
              tauto
              intro x hx
              have : x ∈ S ∨ x ∈ T := h (by trivial)
              cases this with
              |inl hl => tauto
              |inr hr =>
                contrapose hT
                simp
                use tr
                aesop
            apply Set.eq_of_subset_of_subset
            · intro f hfT
              contrapose hT
              simp
              simp at hT
              use tr
              constructor
              tauto
              use f;aesop
            · intro t htt
              by_contra H
              have : t ∈ S := by
                have : t ∈ S ∨ t ∈ T := h (by trivial)
                tauto
              let Q := hl₀ this
              simp at Q
              simp at htt
              rw [htt] at Q;tauto
-- This is a prototype for why, given compactness, we can prove the measure of 2^ℕ
-- is 1.
theorem measure_univ_prototype (S T : Set (ℕ → Bool)) (h : Set.univ ⊆ S ∪ T) :
  1 ≤ EMetric.diam S + EMetric.diam T := by
    by_cases hS : ∃ x y, x ∈ S ∧ y ∈ S ∧ x 0 = true ∧ y 0 = false
    · rw [diam_one _ hS]; simp
    · by_cases hT : ∃ x y, x ∈ T ∧ y ∈ T ∧ x 0 = true ∧ y 0 = false
      · rw [diam_one _ hT]; simp
      · have h₀: tr ∈ S ∨ tr ∈ T := by exact h trivial
        have h₁: fa ∈ S ∨ fa ∈ T := by exact h trivial
        have ht: tr ∈ S ↔ ¬ tr ∈ T := one_or_other hS hT h₀ h₁
        have hf: fa ∈ S ↔ ¬ fa ∈ T := by -- and the same for fa
          constructor;intro htr₀;by_contra htr₁
          have : ¬ (tr ∈ S ∨ tr ∈ T) := by
            intro hc
            cases hc with
            |inl hl => apply hS;simp;use tr;aesop
            |inr hr => apply hT;simp;use tr;aesop
          tauto;tauto
        have hss: S ⊆ {x | x 0 = false} ∨ S ⊆ { x | x 0 = true} := by
          cases h₀ with
          |inl hl =>
            right;intro a ha;contrapose hS;simp;exists tr;constructor
            tauto;exists a;aesop
          |inr hr =>
            left
            intro a ha
            have : fa ∈ S := by rw [hf];contrapose hT;simp;aesop
            contrapose hT;simp;exists tr;constructor;tauto
            contrapose hS;simp;exists a;constructor;tauto;
            exists fa;constructor;tauto;simp at hT;tauto

        have H : (S = {x | x 0 = false} ∧ T = {x | x 0 = true}) ∨
                 (T = {x | x 0 = false} ∧ S = {x | x 0 = true}) := by
          cases hss with
          |inl hl₀ =>
            left
            exact four_sets_and_disjointness h hT hl₀
          |inr hr =>
            right
            let Q := @four_sets_and_disjointness T S (by
              rw [Set.union_comm];tauto
            ) hS (by
              intro t htT
              contrapose hT
              simp
              simp at hT
              use t
              constructor
              tauto
              use fa;
              constructor
              cases h₁ with
              |inl hl =>
                exfalso
                let Q := hr hl
                simp at Q
                have : false = true := Q
                tauto
              |inr hr => tauto
              tauto
            ) -- just tedious logic
            exact Q
        let Uf := @sup_edist_lower_bound'1
          1 {x | x 0 = false} ft ff (Bool.true_eq_false_eq_False) (by
            constructor;simp;rfl;simp;rfl
          )
        let Ut := @sup_edist_lower_bound'1
          1 {x | x 0 = true} tt tf (Ne.symm (Bool.ne_of_lt rfl)) (by
            constructor;simp;rfl;simp;rfl
          )
        have hS₀ : EMetric.diam S = 1/2 := by
          cases H with
          |inl hl =>
            rw [hl.1]
            unfold EMetric.diam
            apply le_antisymm
            · apply edist_half
            · simp at Uf
              simp
              tauto
          |inr hr =>
            rw [hr.2]
            unfold EMetric.diam
            apply le_antisymm
            · exact @edist_half true
            · simp at Ut
              simp
              tauto
        have hT₀ : EMetric.diam T = 1/2 := by
          cases H with
          |inl hl =>
            rw [hl.2]
            unfold EMetric.diam
            apply le_antisymm
            · apply edist_half
            · simp at Ut
              simp
              tauto
          |inr hr =>
            rw [hr.1]
            unfold EMetric.diam
            apply le_antisymm
            · exact @edist_half false
            · simp at Uf
              simp
              tauto
        rw [hS₀, hT₀, ENNReal.add_halves]
