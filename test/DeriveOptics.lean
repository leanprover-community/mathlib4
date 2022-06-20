import Mathlib.Lean.Deriving.Optics

set_option trace.derive_optics true

inductive Wow
  | foo (cheese : Nat) (plops : Wow) (data : String)
  | bar (lemon : String) (posset : Nat) (data : String): String → Wow
  | foo2 (cheese : Nat) (plops : String) (data : String)
derive_optics Wow


inductive MyList (α β : Type) :  Type
  | nil : MyList α β
  | cons (head : α × β) (tail : MyList α β) : MyList α β
  | otherCons (numberwang : Nat) (head : α × β) (tail : MyList α β) : MyList α β

derive_optics MyList

def t : Wow := (Wow.bar "asdf" 3 "green" "32")

#check Wow.bar.lemon?
#check Wow.bar.withLemon
#check Wow.cheese?
#check Wow.lemon?
#check MyList.head?
#check Wow.cheese!
#check Wow.lemon!
#check MyList.head!
-- #check Wow.plops? -- should fail
#eval Wow.bar.lemon? t
#check Wow.bar.modifyMLemon
#eval Wow.foo.cheese? t
#eval Wow.bar.lemon? $  Wow.bar.withLemon "qwerty" t
#eval Wow.bar.lemon? $  Wow.bar.modifyLemon (· ++ "qwerty") t
#eval Wow.bar.lemon? <$>  @Wow.bar.modifyMLemon (OptionT Id) _ _ (fun x => pure (x ++ "qwerty")) t
