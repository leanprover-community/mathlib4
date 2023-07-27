import Mathlib.ModelTheory.FieldTheory.Basic

namespace FirstOrder

namespace Language

namespace field

def ofNat {α : Type} : ℕ → Language.field.Term α
  | 0 => 0
  | n+1 => ofNat n + 1



end field

end Language

end FirstOrder
