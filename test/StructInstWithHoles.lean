import Mathlib.Lean.Elab.StructInstWithHoles

structure Foo where
  x : Nat := 0
  y : Nat

structure Bar extends Foo where
  z : Nat := x

example := by refine { ?.. : Foo }; case y => exact 0
example := by refine { ?.. : Bar }; case y => exact 0
example := by refine { ?..a : Bar }; case a.y => exact 0
example := by refine { ?..! : Bar }; case x | y | z => exact 0;
example := by refine { ?..!a : Bar }; case a.x | a.y | a.z => exact 0;
-- example := by refine' { ... : Bar }; exact 0
example := by refine' { .. : Bar };  exact 0; exact 0; exact 0
-- example := by refine' { ..! : Bar }; exact 0; exact 0; exact 0

structure rflFoo where
  x  : Nat
  y  : Nat
  xy : x = y := by rfl

example := by refine { ?.. : rflFoo }; (case x | y => exact 0); case xy => rfl
example := by refine { ?..! : rflFoo }; (case x | y => exact 0); case xy => rfl

structure autoFoo where
  x  : Nat := 0
  y  : Nat := 0
  xy : x = y := by rfl

example := { ?.. : autoFoo }
example := by refine { ?..! : autoFoo }; (case x | y => exact 0); case xy => rfl

def f : Foo → Nat := fun _ => 0
def ff : Foo → Foo → Unit := fun _ _ => ()
def ffb : Foo → Bar → Unit := fun _ _ => ()
def ffa : Foo → autoFoo → Unit := fun _ _ => ()

example := by refine { x := f { ?.. }, ?.. : Foo }; case y | y_1 => exact 0
example := by refine { x := f { ?..x }, ?.. : Foo }; case x.y | y => exact 0
example := by refine { x := f { ?.. }, ?..x : Foo }; case y | x.y => exact 0
example := by refine { x := f { ?..x }, ?..x : Foo }; case x.y | x.y_1 => exact 0

example := by refine ff { ?.. } { ?.. }; case y | y_1 => exact 0
example := by refine ff { ?..! } { ?.. }; case x | y | y_1 => exact 0
example := by refine ffb { ?..! } { ?..! }; case x | y | x_1 | y_1 | z_1 => exact 0
example := by refine ffa { ?..! } { ?..! }; (case x | y | x_1 | y_1 => exact 0); rfl

structure Foo' where
  x : Nat

structure dFoo' where
  x : Nat := 0

def ff' : Foo → Foo' → Unit := fun _ _ => ()
def fdf' : Foo → dFoo' → Unit := fun _ _ => ()

example := by refine ff' { ?.. } { ?.. }; case y | x_1 => exact 0
example := by refine fdf' { ?.. } { ?.. }; case y => exact 0

structure Fooα (α : Type) where
  x : α

example := by refine { ?.. : Fooα Nat}; case x => exact 0

structure Fooαi where
  {α : Type}
  x : α

example := by refine { ?.. : Fooαi }; (case α => exact Nat); case x => exact 0

/- haveFieldProj tests (subject to be moved)-/
section haveFieldProj

structure Foo'' where
  x : Bool
  y : Nat

def foo'': Foo'' := { x := true, y := 0 }

example := by
  refine { ?.. : Foo''};
  haveFieldProj;
  case x => exact x.proj foo'';
  case y => exact 0
example := by
  refine { ?.. : Foo''};
  haveFieldProj as a;
  case x => exact a foo'';
  case y => exact 0
example := by
  refine { ?.. : Foo''};
  haveFieldProj y;
  case x => exact 0 == y.proj foo'';
  case y => exact 0
example := by
  refine { ?.. : Foo''};
  haveFieldProj y as a;
  case x => exact 0 == a foo'';
  case y => exact 0

end haveFieldProj
