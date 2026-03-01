import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section
open scoped RealInnerProductSpace

universe u
variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

def Coercive (A : 𝓗 → 𝓗) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x : 𝓗, c * ⟪x, x⟫ ≤ ⟪A x, x⟫

def coercivityConstant (A : 𝓗 → 𝓗) (hA : Coercive A) : ℝ :=
  Classical.choose hA

lemma coercivityConstant_pos (A : 𝓗 → 𝓗) (hA : Coercive A) :
    0 < coercivityConstant A hA :=
  (Classical.choose_spec hA).1

lemma coercivityConstant_ineq (A : 𝓗 → 𝓗) (hA : Coercive A) (x : 𝓗) :
    coercivityConstant A hA * ⟪x, x⟫ ≤ ⟪A x, x⟫ :=
  (Classical.choose_spec hA).2 x

def Rayleigh (A : 𝓗 → 𝓗) (x : 𝓗) : ℝ :=
  ⟪A x, x⟫ / ⟪x, x⟫

theorem rayleigh_ge_coercive
  (A : 𝓗 → 𝓗) (hA : Coercive A)
  {x : 𝓗} (hx : x ≠ 0) :
  coercivityConstant A hA ≤ Rayleigh A x := by
  have h := coercivityConstant_ineq (A := A) hA x
  have hxnorm : ‖x‖ ≠ 0 := by
    intro h0
    have : x = 0 := by simpa [norm_eq_zero] using h0
    exact hx this
  have hpos : 0 < ⟪x, x⟫ := by
    have : 0 < ‖x‖ ^ 2 := sq_pos_of_ne_zero hxnorm
    simpa [real_inner_self_eq_norm_sq] using this
  simpa [Rayleigh] using (le_div_iff₀ hpos).2 h

def SymmetricOp (A : 𝓗 → 𝓗) : Prop :=
  ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫

def GapCandidate (A : 𝓗 → 𝓗) : ℝ :=
  sInf {r : ℝ | ∃ x : 𝓗, x ≠ 0 ∧ Rayleigh A x = r}

theorem coercive_implies_positive_gap
  (A : 𝓗 → 𝓗) [Nontrivial 𝓗] (hA : Coercive A) :
  0 < GapCandidate A := by
  classical
  let S : Set ℝ := {r : ℝ | ∃ x : 𝓗, x ≠ 0 ∧ Rayleigh A x = r}
  have hS_nonempty : S.Nonempty := by
    rcases exists_ne (0 : 𝓗) with ⟨x, hx⟩
    refine ⟨Rayleigh A x, ?_⟩
    exact ⟨x, hx, rfl⟩
  have hS_lb :
      ∀ r, r ∈ S → coercivityConstant A hA ≤ r := by
    intro r hr
    rcases hr with ⟨x, hx, hr⟩
    simpa [hr] using (rayleigh_ge_coercive (A := A) hA hx)
  have hcs :
      coercivityConstant A hA ≤ GapCandidate A := by
    have : coercivityConstant A hA ≤ sInf S :=
      le_csInf hS_nonempty (by intro r hr; exact hS_lb r hr)
    simpa [GapCandidate, S] using this
  exact lt_of_lt_of_le (coercivityConstant_pos (A := A) hA) hcs
