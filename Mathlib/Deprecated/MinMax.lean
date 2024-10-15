import Mathlib.Deprecated.Logic
import Mathlib.Order.MinMax

universe u

variable {α : Type u} [LinearOrder α]

set_option linter.deprecated false

@[deprecated instCommutativeMax (since := "2024-09-12")]
theorem max_commutative : Commutative (α := α) max := max_comm
@[deprecated instAssociativeMax (since := "2024-09-12")]
theorem max_associative : Associative (α := α) max := max_assoc
@[deprecated instCommutativeMin (since := "2024-09-12")]
theorem min_commutative : Commutative (α := α) min := min_comm
@[deprecated instAssociativeMin (since := "2024-09-12")]
theorem min_associative : Associative (α := α) min := min_assoc
