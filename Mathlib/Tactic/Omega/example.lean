set_option autoImplicit true
set_option relaxedAutoImplicit true

example {a : α} {bs : Array β} :
    (Id.run do
      let mut r := a
      for b in bs do r := f r b
      return r) =
      bs.foldl f a := by
  simp [Id.run]

#print Id.run
#print Array.instForInArray
#print forIn

#eval
  let f := (· + ·)
  let a := 0
  let bs := #[1,2,3]
  (Id.run do
    let mut r := a
    for b in bs do r := f r b
    return r)
