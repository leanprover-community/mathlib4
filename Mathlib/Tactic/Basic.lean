
macro mods:declModifiers "lemma" n:declId sig:declSig val:declVal : command =>
  `($mods:declModifiers theorem $n $sig $val)

macro "exfalso" : tactic => `(apply False.elim)

macro_rules | `(tactic| rfl) => `(tactic| exact Iff.rfl)