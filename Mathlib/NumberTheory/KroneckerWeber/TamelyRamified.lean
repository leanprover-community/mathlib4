import Mathlib

open IntermediateField NumberField

variable {E : Type*} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
variable {ζ : E} (hζ : IsPrimitiveRoot ζ p) {K L : IntermediateField ℚ E}
variable (hL : L ≤ ℚ⟮ζ⟯) (hL' : Module.finrank ℚ L = (Ideal.span {(p : ℤ)}).ramificationIdxIn (𝓞 K))

def foo
