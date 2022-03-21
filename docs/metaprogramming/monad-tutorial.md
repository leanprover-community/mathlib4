
There are loads of good monad tutorials on the web. [todo] link some.

The particular monads that get used a lot in Lean are:
- `ReaderM ρ α := (ρ → α)` for giving the monad a context
- `StateM σ α := (σ → σ × α)` for having a state.
- `ErrorM ε α := ε + α` for having errors.

The problem is that there are lots of cases where we need a state and a context, and there might be lots of different states and contexts flying around. Eg suppose that you wanted to have context `ρ` and state `σ`, then you would make `MyMonad α := ρ → σ → σ × α`, but then you might later want error handling or need a bit of extra state and need to make another monad.

Monad transformers are a thing to solve this:

- `ReaderT ρ M α := ρ → M α`
- `StateT σ M α := σ → M (σ × α)`
- `ErrorT ε M α := M (ε ⊕ α)`

Now you can create your monad from a tower of different transformers. You can write `ReaderT MyContext $ StateT MyState $ ErrorT MyError $ Id` and it will create the monad that you want.
