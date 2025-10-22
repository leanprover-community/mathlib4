import Lean.Level

namespace Lean.Level

/-- Variant of `Lean.Level.dec` -/
def dec' : Level → Option Level
  | zero       => none
  | param _    => none
  | mvar _     => none
  | succ l     => l
  | max 0 l₂   => dec' l₂
  | max l₁ 0   => dec' l₁
  | max l₁ l₂  => return mkLevelMax (← dec' l₁) (← dec' l₂)
  | imax _  0  => none
  | imax 0  l₂ => dec' l₂
  | imax l₁ l₂ => return mkLevelMax (← dec' l₁) (← dec' l₂)

end Lean.Level
