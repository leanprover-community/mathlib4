class Mem (α : outParam $ Type u) (γ : Type v) where
  mem : α → γ → Prop

infix:50 " ∈ " => Mem.mem

notation:50 x " ∉ " s => ¬ x ∈ s
