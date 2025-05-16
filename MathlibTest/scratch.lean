instance : Coe PUnit.{u} PUnit.{v} where
  coe _ := ⟨⟩

set_option pp.universes true

theorem foo {l : Option PUnit} {m : Option PUnit} : l = m := by
  sorry
