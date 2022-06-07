import Mathlib.Lean.Deriving.Optics

set_option trace.derive_optics true

inductive Wow
  | foo (cheese : Nat) (plops : Wow)
  | bar (lemon : String) (posset : Nat) : String → Wow
derive_optics Wow


inductive MyList (α β : Type) :  Type
  | nil : MyList α β
  | cons (head : α × β) (tail : MyList α β) : MyList α β

derive_optics MyList

def t : Wow := (Wow.bar "asdf" 3 "green")

#check Wow.bar.lemon?
#check Wow.bar.withLemon
#eval Wow.bar.lemon? t
#eval Wow.foo.cheese? t
#eval Wow.bar.lemon? $  Wow.bar.withLemon "qwerty" t
#eval Wow.bar.lemon? $  Wow.bar.modifyLemon (· ++ "qwerty") t
#eval Wow.bar.lemon? <$>  @Wow.bar.modifyMLemon (OptionT Id) _ _ (fun x => pure (x ++ "qwerty")) t
