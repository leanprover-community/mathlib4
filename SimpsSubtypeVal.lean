import Mathlib.Data.Set.Function
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Says
import LeanReducer.Command

/--
info: [simps.verbose] The projections for this structure have already been initialized by a previous invocation of `initialize_simps_projections` or `@[simps]`.
    Generated projections for Subtype:
    Projection val: fun {α} p x => ↑x
    No lemmas are generated for the projections: property.
-/
#preserve_this in
initialize_simps_projections? Subtype
