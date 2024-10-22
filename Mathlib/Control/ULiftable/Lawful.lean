import Mathlib.Control.ULiftable.Basic


theorem up_down {f : Type u₀ → Type u₁} {g : Type max u₀ v₀ → Type v₁} [ULiftable f g] {α}
    (x : g (ULift.{v₀} α)) : up (down x : f α) = x :=
  (ULiftable.congr Equiv.ulift.symm).right_inv _

theorem down_up {f : Type u₀ → Type u₁} {g : Type max u₀ v₀ → Type v₁} [ULiftable f g] {α}
    (x : f α) : down (up x : g (ULift.{v₀} α)) = x :=
  (ULiftable.congr Equiv.ulift.symm).left_inv _

/-- for specific state types, this function helps to create a uliftable instance -/
def StateT.uliftable' {m : Type u₀ → Type v₀} {m' : Type u₁ → Type v₁} [ULiftable m m']
    (F : s ≃ s') : ULiftable (StateT s m) (StateT s' m') where
  congr G :=
    StateT.equiv <| Equiv.piCongr F fun _ => ULiftable.congr <| Equiv.prodCongr G F

instance {m m'} [ULiftable m m'] : ULiftable (StateT s m) (StateT (ULift s) m') :=
  StateT.uliftable' Equiv.ulift.symm

instance StateT.instULiftableULiftULift {m m'} [ULiftable m m'] :
    ULiftable (StateT (ULift.{max v₀ u₀} s) m) (StateT (ULift.{max v₁ u₀} s) m') :=
  StateT.uliftable' <| Equiv.ulift.trans Equiv.ulift.symm

/-- for specific reader monads, this function helps to create a uliftable instance -/
def ReaderT.uliftable' {m m'} [ULiftable m m'] (F : s ≃ s') :
    ULiftable (ReaderT s m) (ReaderT s' m') where
  congr G := ReaderT.equiv <| Equiv.piCongr F fun _ => ULiftable.congr G

instance {m m'} [ULiftable m m'] : ULiftable (ReaderT s m) (ReaderT (ULift s) m') :=
  ReaderT.uliftable' Equiv.ulift.symm

instance ReaderT.instULiftableULiftULift {m m'} [ULiftable m m'] :
    ULiftable (ReaderT (ULift.{max v₀ u₀} s) m) (ReaderT (ULift.{max v₁ u₀} s) m') :=
  ReaderT.uliftable' <| Equiv.ulift.trans Equiv.ulift.symm

/-- for specific continuation passing monads, this function helps to create a uliftable instance -/
def ContT.uliftable' {m m'} [ULiftable m m'] (F : r ≃ r') :
    ULiftable (ContT r m) (ContT r' m') where
  congr := ContT.equiv (ULiftable.congr F)

instance {s m m'} [ULiftable m m'] : ULiftable (ContT s m) (ContT (ULift s) m') :=
  ContT.uliftable' Equiv.ulift.symm

instance ContT.instULiftableULiftULift {m m'} [ULiftable m m'] :
    ULiftable (ContT (ULift.{max v₀ u₀} s) m) (ContT (ULift.{max v₁ u₀} s) m') :=
  ContT.uliftable' <| Equiv.ulift.trans Equiv.ulift.symm

/-- for specific writer monads, this function helps to create a uliftable instance -/
def WriterT.uliftable' {m m'} [ULiftable m m'] (F : w ≃ w') :
    ULiftable (WriterT w m) (WriterT w' m') where
  congr G := WriterT.equiv <| ULiftable.congr <| Equiv.prodCongr G F

instance {m m'} [ULiftable m m'] : ULiftable (WriterT s m) (WriterT (ULift s) m') :=
  WriterT.uliftable' Equiv.ulift.symm

instance WriterT.instULiftableULiftULift {m m'} [ULiftable m m'] :
    ULiftable (WriterT (ULift.{max v₀ u₀} s) m) (WriterT (ULift.{max v₁ u₀} s) m') :=
  WriterT.uliftable' <| Equiv.ulift.trans Equiv.ulift.symm

instance Except.instULiftable {ε : Type u₀} : ULiftable (Except.{u₀,v₁} ε) (Except.{u₀,v₂} ε) where
  congr e :=
    { toFun := Except.map e
      invFun := Except.map e.symm
      left_inv := fun f => by cases f <;> simp [Except.map]
      right_inv := fun f => by cases f <;> simp [Except.map] }

instance Option.instULiftable : ULiftable Option.{u₀} Option.{u₁} where
  congr e :=
    { toFun := Option.map e
      invFun := Option.map e.symm
      left_inv := fun f => by cases f <;> simp
      right_inv := fun f => by cases f <;> simp }
