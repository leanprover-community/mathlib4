/-!
# Lemmas about `Array.extract`

Some useful lemmas about Array.extract
-/

public section

universe u
variable {α : Type u} {i : Nat}

namespace Array

@[deprecated (since := "2025-11-03")]
alias extract_eq_nil_of_start_eq_end := extract_empty_of_start_eq_stop

@[deprecated (since := "2025-11-03")]
alias extract_append_left' := extract_append_of_stop_le_size_left

@[deprecated (since := "2025-11-03")]
alias extract_append_right' := extract_append_of_size_left_le_start

@[deprecated (since := "2025-11-03")]
alias extract_eq_of_size_le_end := extract_eq_of_size_le_stop

end Array
