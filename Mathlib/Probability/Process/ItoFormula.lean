import MathLab.BrownianMotion
import Mathlib.Data.Real.Basic
import Aesop

namespace StochasticCalculus

/--
In stochastic calculus, we use formal differentials dW and dt.
We define a structure to represent the algebra of these differentials.
A generic stochastic differential is given by: dz = a * dt + b * dW
-/
@[ext]
structure StochasticDifferential where
  dt_coeff : ℝ
  dW_coeff : ℝ

/--
The multiplication rule for Ito Calculus (The Stochastic Multiplication Table):
1. dt * dt = 0
2. dt * dW = 0
3. dW * dt = 0
4. dW * dW = dt  <-- The fundamental theorem of Stochastic Calculus
-/
def mul (x y : StochasticDifferential) : StochasticDifferential :=
  -- (a₁ dt + b₁ dW) * (a₂ dt + b₂ dW)
  -- = a₁a₂ (dt)² + a₁b₂ dt dW + b₁a₂ dW dt + b₁b₂ (dW)²
  -- By Ito's rules, only (dW)² survives as dt.
  -- Therefore, the product results in a purely dt term: (b₁ * b₂) dt
  { dt_coeff := x.dW_coeff * y.dW_coeff,
    dW_coeff := 0 }

instance : Mul StochasticDifferential := ⟨mul⟩

instance : Add StochasticDifferential :=
  ⟨fun x y => { dt_coeff := x.dt_coeff + y.dt_coeff, dW_coeff := x.dW_coeff + y.dW_coeff }⟩

instance : SMul ℝ StochasticDifferential :=
  ⟨fun c x => { dt_coeff := c * x.dt_coeff, dW_coeff := c * x.dW_coeff }⟩

-- Define the fundamental bases for stochastic differentials
def dt : StochasticDifferential := { dt_coeff := 1, dW_coeff := 0 }
def dW : StochasticDifferential := { dt_coeff := 0, dW_coeff := 1 }
def zero : StochasticDifferential := { dt_coeff := 0, dW_coeff := 0 }

/--
THEOREM: The square of a Brownian infinitesimal increment is equal to time.
(dW)² = dt
This is the core mathematical engine driving the Black-Scholes model.
-/
theorem dW_sq_eq_dt : dW * dW = dt := by
  ext
  · exact mul_one 1
  · rfl

/-- THEOREM: The cross term of time and Brownian motion vanishes. -/
theorem dt_mul_dW_eq_zero : dt * dW = zero := by
  ext
  · exact zero_mul 1
  · rfl

/-- THEOREM: The square of an infinitesimal time increment vanishes in continuous time. -/
theorem dt_sq_eq_zero : dt * dt = zero := by
  ext
  · exact zero_mul 0
  · rfl

/--
General Ito Multiplication Theorem:
For any two stochastic differentials dx = a dt + b dW and dy = c dt + d dW,
their cross variation dx * dy is purely determined by their volatilities (b * d) dt.
-/
theorem ito_cross_variation (a b c d : ℝ) :
  ({ dt_coeff := a, dW_coeff := b } : StochasticDifferential) *
  ({ dt_coeff := c, dW_coeff := d } : StochasticDifferential) = { dt_coeff := b * d, dW_coeff := 0 } := by
  rfl

end StochasticCalculus
