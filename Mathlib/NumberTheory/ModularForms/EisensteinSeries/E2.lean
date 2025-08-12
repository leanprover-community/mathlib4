import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence

/-!
# Eisenstein Series E2

We define the Eisenstein series `E2` of weight `2` and level `1` as a limit of partial sums
over non-symmetric intervals.

-/

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace  intervalIntegral
  Metric Filter Function Complex MatrixGroups Finset

open scoped Interval Real Topology BigOperators Nat

noncomputable section


/-- This is an auxilary summand used to define the Eisenstein serires `G2`. -/
def e2Summand (m : ℤ) (z : ℍ) : ℂ := ∑' (n : ℤ), eisSummand 2 ![m, n] z

lemma e2Summand_summable (m : ℤ) (z : ℍ) : Summable (fun n => eisSummand 2 ![m, n] z) := by
  apply (linear_right_summable z m (k := 2) (by omega)).congr
  simp [eisSummand]

/-- The Eisenstein series of weight `2` and level `1` defined as the limit as `N` tends to
infinity of the partial sum of `m` in `[N,N)` of `e2Summand m`. This sum over non-symmetric
intervals is handy in proofs of its transformation property. -/
def G2 : ℍ → ℂ := fun z => limUnder (atTop) (fun N : ℕ => ∑ m ∈ Ico (-N : ℤ) N, e2Summand m z)

def E2 : ℍ → ℂ := (1 / (2 * riemannZeta 2)) •  G2

def D2 (γ : SL(2, ℤ)) : ℍ → ℂ := fun z => (2 * π * Complex.I * γ 1 0) / (denom γ z)



/- lemma Asymptotics.IsBigO.map {α β ι γ : Type*} [Norm α] [Norm β] {f : ι → α} {g : ι → β}
  {p : Filter ι} (hf : f =O[p] g) (c : γ → ι) :
    (fun (n : γ) => f (c n)) =O[p.comap c] fun n => g (c n) := by
  rw [isBigO_iff] at *
  obtain ⟨C, hC⟩ := hf
  refine ⟨C, ?_⟩
  simp only [eventually_comap] at *
  filter_upwards [hC] with n hn
  exact fun a ha ↦ Eq.mpr (id (congrArg (fun _a ↦ ‖f _a‖ ≤ C * ‖g _a‖) ha)) hn

lemma Asymptotics.IsBigO.nat_of_int {α β : Type*} [Norm α] [SeminormedAddCommGroup β] {f : ℤ → α}
    {g : ℤ → β} (hf : f =O[cofinite] g) : (fun (n : ℕ) => f n) =O[cofinite] fun n => g n := by
  have := Asymptotics.IsBigO.map hf Nat.cast
  simp only [Int.cofinite_eq, isBigO_sup, comap_sup, Asymptotics.isBigO_sup] at *
  rw [Nat.cofinite_eq_atTop]
  simpa using this.2 -/
