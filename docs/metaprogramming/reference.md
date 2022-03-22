Author: E.W.Ayers

# Monads used in Lean

If it ends in an `M`, it's a monad. If it ends with a `T` it is a monad transformer.
See the [tutorial on monads](monad-tutorial.md).

| monad name       | description | used for | definition |
| -----   			   | ----------- | -------- | ---------- |
| `ReaderM ρ` | This is a standard monad that manages a context for you. | | `(ρ → ∙)`
| `IO` | IO is a monad used to talk about interacting with the rest of the computer. Things like: connecting to the internet, writing files etc. You do this to say, "hey! this code can cause arbitrary OS-level side effects". | |
| `EStateM ε σ α`  | A stateful monad with errors. | |  `σ → (α × σ) ⊕ (ε × σ)`
| `EIO ε`          | IO monad with exceptions.        |          | `EStateM ε IO.RealWorld`
| `StateRefT`       | This is the same as `StateT`, but there is some efficiency gain from using a reference. It is not clear whether this is still needed, you can just use `StateT`
| `CoreM` | The main thing that this does is keep the enviroment, name generator and some syntax info for you. I think it's more just a set of common context and state for the other metaprogramming monads.  | Don't use unless you are Lean maintainer. | `ReaderT Context $ StateRefT State $ EIO Exception`
| `MetaM` | CoreM with a local context and a metavariable state. The difference with a tactic monad is that it doesn't include a list of goals.| Building expressoins where you need to handle metavariables and local contexts. | `ReaderT Context $ StateRefT State CoreM`
| `TermElabM`      | The `TermElabM` tracks a lot of extra information: pending elaboration problems, pending tactics to be executed, etc. | | `ReaderT Context $ StateRefT State MetaM`
| `CommandElabM`   | [todo] |  | `ReaderT Context $ StateRefT State $ EIO Exception`
| `MacroM`   | A macro is a function `Syntax → MacroM Syntax`. | Creating macros | `ReaderT Macro.Context $ EStateM Macro.Exception Macro.State`

# Ways of formatting things

- `String` is just text without any fancyness on it. There are two main ways to make strings:
	- `toString : α → String` is for when you want to convert something for humans to read. The goal `toString` is to be __readable__.
	- `repr : α → String` is for when you want to produce a string which _should_ work as valid lean code. The goal of `repr` is to be __unambiguous__.
- `Format` is a string with some information about how to linebreak and how to wrap text when the viewing box isn't big enough. The constructors for `Format` might look a bit strange, the best place to learn how it works is the paper [_A Prettier Printer_ by Wadler](https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf).
- `Meta.ppExpr` is used to make expressions that look nice and which can be interactive etc.
- `MessageData` is like Format but it has a few extra features for showing interactively; expressions, metavariable contexts and collapsible regions.

## String interpolation:

You can write things like `f!"Hello {person.name} your age is {person.age}"` like in python and javascript.
See https://leanprover.github.io/lean4/doc/stringinterp.html

# Useful `MetaM`s

- `kabstract`
- `subst`
- [todo]


# Useful `Tactic`s

Reference: https://leanprover.github.io/lean4/doc/tactics.html

[todo] these need updating and explaining

- `define n β` : `(?𝑚 : α) ~~> let n : β := ?𝑚₁ in (?𝑚₂ : α)'`. That is, it fills in the goal with a `let` expression and makes two new goals.
- `assert n β` : `?𝑚 ~~> (λ n : β, ?𝑚₁) ?𝑚₂`.
- `exact e` : `?𝑚 ~~> e`
- `intro n` : `(?𝑚 : ((a : α) → β) ~~> fun n : α => (?𝑚₁ : β[a/n])`
- `revert x` : `(?𝑚 : β) ~~> (?𝑚₁ : ((a : α) → β)) x`. That is, undo an `intro`.
- `show α` : `?𝑚 ~~> (?𝑚 : α)`
