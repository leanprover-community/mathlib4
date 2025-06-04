inductive Free (f : Type -> Type) (a : Type) where
| pure : a -> Free f a
| bind : ∀ x, f x -> (x -> Free f a) -> Free f a

/-
Map will take a function f : α → β and type constructor F : Type u → Type v and return a
function Free Ff : Fα → Fβ
-/
def Free.map {α β : Type} (F : Type → Type) (f : α → β) : Free F α → Free F β :=
λ FFa =>
match FFa with
| pure a => Free.pure (f a)
| bind X Fx k => Free.bind X Fx (λ z => map F f (k z))

instance {F : Type → Type} : Functor (Free F) where
map := Free.map F

instance {F : Type → Type} : LawfulFunctor (Free F) where
map_const := by
  intro α β
  simp [Functor.mapConst, Functor.map]
id_map := by
  intro α x
  simp [Functor.map]
  induction x
  case pure a =>
    simp [Free.map]
  case bind X Fx f ih =>
    simp [Free.map, ih]
comp_map := by
  intro α β γ g h x
  simp [Functor.map]
  induction x
  case pure a =>
    simp [Free.map]
  case bind X Fx f ih =>
    simp [Free.map, ih]

/--
Now we define our pure and bind morphisms for the Free Monad.
-/

def bindFree {a b : Type} (F : Type → Type) (x : Free F a) (f : a → Free F b) : Free F b :=
match x with
| .pure a => f a
| .bind X Fx k => .bind X Fx (λ z => bindFree F (k z) f)

instance FreeMonad (F : Type → Type) : Monad (Free F) where
  pure := Free.pure
  bind := bindFree F

instance {F : Type → Type} : LawfulMonad (Free F) where
bind_pure_comp := by
  intro α β x y; simp [Functor.map, bind, pure]; induction y
  · case pure a => simp [bindFree, Free.map]
  · case bind X Fx k ih => simp [bindFree, Free.map, ih]
bind_map := by
  intro α β f x; simp [bind, Seq.seq]
pure_bind := by
  intro α x a f; simp [bind, pure, bindFree]
bind_assoc := by
  intro α β γ x f g; simp [bind]; induction x
  case pure a => simp [bindFree, Free.map]
  case bind X Fx k ih => simp [bindFree, Free.map, ih]
seqLeft_eq := by
  intro α β x y; simp [Functor.map, SeqLeft.seqLeft, Seq.seq]; induction x
  case pure a =>
    simp [bindFree, Free.map]
    induction y
    case pure b => simp [bindFree, Free.map]
    case bind X Fy k ih => simp [bindFree, Free.map, ih]
  case bind X Fx k ih => simp [bindFree, Free.map, ih]
seqRight_eq := by
  intro α β x y; simp [Functor.map, bindFree, Free.map]; induction x
  case pure a =>
    simp [bindFree, Free.map]
    induction y
    case pure b => simp [SeqRight.seqRight, Seq.seq, Functor.map, bindFree, Free.map]
    case bind X Fy k ih =>
      simp [SeqRight.seqRight, Seq.seq, Functor.map, bindFree, Free.map, ih] at ih ⊢
      apply funext; intro x; exact ih x
  case bind X Fx k ih =>
    simp [Free.map, Seq.seq, bindFree, Functor.map, SeqRight.seqRight] at ih ⊢
    apply funext; intro x; exact ih x
pure_seq := by
  intro α β f x; simp [Seq.seq, Functor.map, pure, bindFree]
