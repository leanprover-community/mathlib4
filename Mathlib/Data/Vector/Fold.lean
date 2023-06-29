import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Snoc


/-!
## Foldl & Foldr
-/

namespace Vector

variable (x : α) (xs : Vector α n) (init : β)

@[simp]
theorem foldl_nil : foldl f init nil = init :=
  rfl

@[simp]
theorem foldl_cons : foldl f init (x ::ᵥ xs) = foldl f (f init x) xs :=
  rfl

@[simp]
theorem foldl_snoc : foldl f init (xs.snoc x) = f (foldl f init xs) x := by
  induction xs using Vector.inductionOn generalizing init <;> simp_all



@[simp]
theorem foldr_nil : foldr f init nil = init :=
  rfl

@[simp]
theorem foldr_cons : foldr f init (x ::ᵥ xs) = f x (foldr f init xs) :=
  rfl

@[simp]
theorem foldr_snoc : foldr f init (xs.snoc x) = foldr f (f x init) xs := by
  induction xs using Vector.inductionOn generalizing init <;> simp_all



@[simp] theorem foldl_reverse (v : Vector α n) (f : β → α → β) (b) :
    v.reverse.foldl f b = v.foldr (fun x y => f y x) b :=
  List.foldl_reverse ..

@[simp] theorem foldr_reverse (v : Vector α n) (f : α → β → β) (b) :
    v.reverse.foldr f b = v.foldl (fun x y => f y x) b :=
  List.foldr_reverse ..




end Vector
