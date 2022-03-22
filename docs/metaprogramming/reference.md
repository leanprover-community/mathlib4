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


# Useful `MetaM`s

- `kabstract`
- `subst`
- [todo]


## fun_info

[todo] port this
A lot of the time, you want to think of `app (app (app f x) y) z` as just `f` applied to arguments `[x,y,z]`.
`library/init/meta/fun_info.lean` is your friend here.

Suppose expression `f`'s type is a telescope of `pi`s (that is, of the form `Π x, Π y, ... r`).
Call the `x`, `y` etc __parameters__ and `r` the __result type__.
Then the `get_fun_info f` tactic will return a `fun_info` object, which has fields:
- `params` which is a list of `param_info` objects. One for each parameter in `f`'s type. A `param_info` is
    + `is_implicit` -- Is the parameter implicit (that is, in curly braces)?
    + `is_inst_implicit` -- Is the parameter an implicit typeclass instance argument?
    + `is_prop` -- is it a proposition? Ie: is it's type of type `Prop`?
    + `has_fwd_deps` -- Do later paramters or the result type depend on this parameter?
    + `back_deps : list nat` -- a list of references to the indices of the previous parameters that it depends on.
- `result_deps : list nat` -- the paramters that the result type depends on.

`get_fun_info` doesn't give the types of the parameter or the result type. You have to inspect these manually using pattern matching on the type.

[TODO] Does `get_fun_info` work when it has already been applied?

[TODO] I don't understand subsingletons.
What is a subsingleton? It seems to be any type which is isomorphic to a member of Prop. Ie, it's either uninhabited or has one member.
- `get_subsingleton_info`
- `get_spec_prefix_size`
- `get_spec_subsingleton_info`


# Useful `Tactic`s

[todo] these need updating and explaining

- `define n β` : `(?𝑚 : α) ~~> let n : β := ?𝑚₁ in (?𝑚₂ : α)'`. That is, it fills in the goal with a `let` expression and makes two new goals.
- `assert n β` : `?𝑚 ~~> (λ n : β, ?𝑚₁) ?𝑚₂`.
- `exact e` : `?𝑚 ~~> e`
- `intro n` : `(?𝑚 : ((a : α) → β) ~~> fun n : α => (?𝑚₁ : β[a/n])`
- `revert x` : `(?𝑚 : β) ~~> (?𝑚₁ : ((a : α) → β)) x`. That is, undo an `intro`.
- `show α` : `?𝑚 ~~> (?𝑚 : α)`



# SCRATCH SPACE, WIP [todo]

### `mk_app` and friends.

The docstring is great for this one so I'm just going to paste it in.
> Helper tactic for creating simple applications where some arguments are inferred usingntype inference.
> Example, given
>   ```lean
>       rel.{l_1 l_2} : Pi (α : Type.{l_1}) (β : α -> Type.{l_2}), (Pi x : α, β x) -> (Pi x : α, β x) -> , Prop
>       nat     : Type
>       real    : Type
>       vec.{l} : Pi (α : Type l) (n : nat), Type.{l1}
>       f g     : Pi (n : nat), vec real n
>   ```
>   then
>   ```lean
>   mk_app_core semireducible "rel" [f, g]
>   ```
>   returns the application
>   ```lean
>   rel.{1 2} nat (fun n : nat, vec real n) f g
>   ```

There are a lot of variants of `mk_app` that are also included for efficiency on equational reasoning.

- `mk_mapp` -- explicitly state which arguments should be inferred.
- `mk_congr_arg` -- `eq.congr_arg : Π (f : α → β),  a₁ = a₂ → f a₁ = f a₂`
- `mk_congr_fun` -- `eq.congr_fun : (f = g) → Π (a : α), f a = g a `
- `mk_congr` -- `eq.congr : (f₁ = f₂) → (a₁ = a₂) → f₁ a₁ = f₂ a₂`
- `mk_eq_refl` -- `eq.refl : Π(a : α), a = a`
- `mk_eq_symm` -- `eq.symm : a = b → b = a`
- `mk_eq_trans` -- `eq.trans : a = b → b = c → a = c`
- `mk_eq_mp` -- `eq.mp : α = β → α → β`
- `mk_eq_mpr` -- `eq.mrp : α = β → β → α`
