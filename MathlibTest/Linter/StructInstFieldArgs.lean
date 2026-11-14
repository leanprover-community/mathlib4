module

import Mathlib.Tactic.Linter.StructInstFieldArgs

set_option linter.style.structInstFieldArgs true
set_option linter.unusedVariables false

class A where
  a : Nat → Nat → Nat

set_option linter.style.structInstFieldArgs false in
example : A where
  a := fun x y : Nat => x

/--
@ +2:11...14
info: Fix:
  x̲ ̲y̲ ̲:= ̵f̵u̵n̵ ̵x̵ ̵y̵ ̵=̵>̵
-/
#guard_msgs (info, drop warning, positions := true) in
example : A where
  a := fun x y => x

/--
@ +2:11...14
info: Fix:
  (̲x̲ ̲y̲ ̲:̲ ̲N̲a̲t̲)̲ ̲:= ̵f̵u̵n̵ ̵x̵ ̵y̵ ̵:̵ ̵N̵a̵t̵ ̵=̵>̵
-/
#guard_msgs (info, drop warning, positions := true) in
example : A where
  a := fun x y : Nat => x

example : A where
  a (x y : Nat) := x

/--
@ +2:11...16
info: Fix:
  x̲ ̲{̲y̲}̲ ̲:= ̵f̵u̵n̵ ̵x̵ ̵{̵y̵}̵ ̵=̵>̵
-/
#guard_msgs (info, drop warning, positions := true) in
example : A where
  a := fun x {y} => x

example : A where
  a x {y} := x

/--
@ +2:10...13
info: Fix:
   ̲x̲ ̲y̲ ̲:= ̵f̵u̵n̵ ̵x̵ ̵y̵ ̵=̵>̵
-/
#guard_msgs (info, drop warning, positions := true) in
example : A where
  a:= fun x y => x

/--
@ +2:12...13
info: Fix:
   ̲y̲ ̲:= ̵f̵u̵n̵ ̵y̵ ̵=̵>̵
-/
#guard_msgs (info, drop warning, positions := true) in
example : A where
  a x:= fun y => y

/--
@ +2:19...20
info: Fix:
   ̲y̲ ̲:= ̵f̵u̵n̵ ̵y̵ ̵=̵>̵
-/
#guard_msgs (info, drop warning, positions := true) in
example : A where
  a (x: Nat):= fun y => y

/--
@ +2:11...14
info: Fix:
  x̲ ̲_̲ ̲:= ̵f̵u̵n̵ ̵x̵ ̵_̵ ̵=̵>̵
-/
#guard_msgs (info, drop warning, positions := true) in
example : A where
  a := fun x _ => x

-- ensure the suggestion is valid syntax
example : A where
  a x _ := x

/--
@ +2:11...22
info: Fix:
  x̲ ̲(̲y̲ ̲:̲ ̲N̲a̲t̲)̲ ̲:= ̵f̵u̵n̵ ̵x̵ ̵(̵y̵ ̵:̵ ̵N̵a̵t̵)̵ ̵=̵>̵
-/
#guard_msgs (info, drop warning, positions := true) in
example : A where
  a := fun x (y : Nat) => x

/--
@ +2:11...22
info: Fix:
  :̵=̵ ̵f̵u̵n̵ ̵(x : Nat) y =̵>̵:̲=̲
-/
#guard_msgs (info, drop warning, positions := true) in
example : A where
  a := fun (x : Nat) y => x

/--
@ +3:11...12
info: Fix:
  x̲ ̲:= ̵f̵u̵n̵ ̵x̵ ̵↦̵
-/
#guard_msgs (info, drop warning, positions := true) in
-- the linter looks at the first `fun`. Applying
example : A where
  a := fun x ↦ fun y ↦ x

-- cannot move anything on functions with matching pattern
example : A where
  a _ := fun | 0 => 0 | n => n

/-- deconstructed arguments like `⟨y, z⟩` cannot be moved -/
class B where
  b : (Nat × Nat) → (Nat × Nat) → (Nat × Nat) → (Nat × Nat)

example : B where
  b := fun ⟨x, y⟩ z w => w


/--
@ +2:11...12
info: Fix:
  x̲ ̲:= fun x̵ ̵⟨y, z⟩ w  ̲=>
-/
#guard_msgs (info, drop warning, positions := true) in
example : B where
  b := fun x ⟨y, z⟩ w => x

/--
@ +2:11...26
info: Fix:
  :̵=̵ ̵f̵u̵n̵ ̵(x : Nat × Nat) :̲=̲ ̲f̲u̲n̲ ̲⟨y, z⟩ w  ̲=>
-/
#guard_msgs (info, drop warning, positions := true) in
example : B where
  b := fun (x : Nat × Nat) ⟨y, z⟩ w => x

/-- The linter does not trigger on arguments which are not functions. -/
class C where
  c₁ : Prop
  c₂ : Nat
  c₄ : False → Nat

example : C where
  c₁ := True
  c₂ := 0
  c₄ := nofun

class D where
  d : ∀ a : Nat, a = a

/--
@ +2:11...12
info: Fix:
  (̲x̲ ̲:̲ ̲N̲a̲t̲)̲ ̲:= ̵f̵u̵n̵ ̵x̵ ̵:̵ ̵N̵a̵t̵ ̵=̵>̵
-/
#guard_msgs (info, drop warning, positions := true) in
example : D where
  d := fun x : Nat => rfl

example : D where
  d (x : Nat) := rfl

/--
@ +3:15...16
info: Fix:
  g̲ ̲:= fun g̵ ̵a  ̲↦
-/
#guard_msgs (info, drop warning, positions := true) in
set_option linter.style.structInstFieldArgs.useExpectedType true in
example : Add (Nat → Nat) where
  add f := fun g a ↦ f a + g a

example : Add (Nat → Nat) where
  add f g := fun a ↦ f a + g a

/--
@ +3:17...18
info: Fix:
  a̲ ̲:= ̵f̵u̵n̵ ̵a̵ ̵↦̵
-/
#guard_msgs (info, drop warning, positions := true) in
set_option linter.style.structInstFieldArgs.useExpectedType false in
example : Add (Nat → Nat) where
  add f g := fun a ↦ f a + g a

example : Add (Nat → Nat) where
  add f g a := f a + g a
