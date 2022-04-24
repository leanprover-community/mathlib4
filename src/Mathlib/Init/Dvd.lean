class Dvd (α : Type u) where
  dvd : α → α → Prop

infix:50 " ∣ " => Dvd.dvd
