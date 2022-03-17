

instance : Monad id where
  seq := fun f x => f $ x ()
  bind := fun a f => f a
  pure := id
  map := id
