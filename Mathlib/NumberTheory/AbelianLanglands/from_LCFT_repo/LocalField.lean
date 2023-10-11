
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Topology.Algebra.ValuedField
import Mathlib.NumberTheory.FunctionField
-- NICKED FROM https://github.com/mariainesdff/local_class_field_theory

/-!
# Local fields
In this file we define the `class local_field` on a valued field `K`, requiring that it is
* complete (with respect to the uniform structure induced by the valuation)
* that its valuation is discrete
* that the residue field of its unit ball is finite

## Main Definitions
* `local_field` is the key definition, see above.


## Main Results
* For an `eq_char_local_field p K` that is separable over `FpX_completion p` we show that `K` is a
local
field. The separability assumption is required to use some result in mathlib concerning
the finiteness of the ring of integers.
* For a `mixed_char_local_field p K`, we show that `K` is a local field.
-/
universe v u

open Valuation DiscreteValuation
open scoped DiscreteValuation

class IsDiscrete {A : Type _} [Ring A] (v : Valuation A ℤₘ₀) :=
(surj : Function.Surjective v)

/-- The class `local_field`, extending `valued K ℤₘ₀` by requiring that `K` is complete, that the
valuation is discrete, and that the residue field of the unit ball is finite. -/
class LocalField (K : Type _) [Field K] [hv : Valued K ℤₘ₀] :=
(complete : CompleteSpace K)
(isDiscrete : IsDiscrete hv.v)
(finite_residue_field : Fintype (LocalRing.ResidueField hv.v.valuationSubring))

namespace eq_char_local_field

#exit
variables (p : ouaram ℕ) [fact(nat.prime p)]
variables (K : Type*) [field K] [eq_char_local_field p K]

/-- An `eq_char_local_field p K` that is separable over `FpX_completion` is a local field.
  The separability assumption is required to use some result in mathlib concerning
  the finiteness of the ring of integers.-/
@[priority 100]
noncomputable
definition local_field [fact (is_separable (FpX_completion p) K)] : local_field K :=
{ complete             := eq_char_local_field.complete_space p K,
  is_discrete          := v.valuation.is_discrete p K,
  finite_residue_field :=
  begin
    haveI : is_separable (FpX_completion p) K := fact.out _,
    apply finite_residue_field_of_unit_ball,
    apply FpX_int_completion.residue_field_fintype_of_completion,
  end,
  ..(eq_char_local_field.with_zero.valued p K) }

end eq_char_local_field

namespace mixed_char_local_field
open padic

variables (p : out_param ℕ) [fact(nat.prime p)]
variables (K : Type*) [field K] [mixed_char_local_field p K]

/-- A `mixed_char_local_field` is a local field. -/
@[priority 100]
noncomputable
definition local_field : local_field K :=
{ complete             := mixed_char_local_field.complete_space p K,
  is_discrete          := v.valuation.is_discrete p K,
  finite_residue_field :=
  begin
    apply finite_residue_field_of_unit_ball,
    apply ring_of_integers.residue_field_fintype_of_completion,
  end,
  ..(mixed_char_local_field.with_zero.valued p K) }

end mixed_char_local_field
