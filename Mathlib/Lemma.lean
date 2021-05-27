-- this macro, written by Sebastian Ullrich, enables us to have lemmas
macro mods:declModifiers "lemma" n:declId sig:declSig val:declVal : command => `($mods:declModifiers theorem $n $sig $val)
@[simp] lemma foo : True = True := rfl
