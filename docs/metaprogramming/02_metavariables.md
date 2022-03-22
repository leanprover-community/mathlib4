Author: E.W.Ayers

# How meta works. Part 2: The tactic state

## How tactics work

Let's look at how tactics work first.

I have massively simplified how Lean actually works to the point that the Lean developers will probably cringe when they read this.
My goal is to give a kind of working abstraction that tactic writers can use to reason about how Lean will behave.
I am expecting readers to already have some experience using simple tactics such as `intro`, `apply`, `rw` etc.

Suppose that we are trying to construct a valid `Expr` of a certain type `T` using tactics. If `T : Prop`, then this is the same task as proving the statement `T`.
We might start by writing (say):
```lean
lemma my_lemma (p q r : Prop) : (p → q → r) → (p → q) → p → q × r := by
  <cursor goes here>
```

At this point, if you open the _Display Goal_ viewer in your editor, you will see:
```lean
p q r : Prop
⊢ (p → q → r) → (p → q) → p → q × r
```

This is Lean's __tactic state__. When you plant your cursor in the tactic block (or on a placeholder "`_`"), Lean knows that you are trying to create an `Expr` which typechecks to `∀ (p q r : Prop), (p → q → r) → (p → q) → p → q × r`.
We don't always know how to write down an `Expr` straight away, so instead we want to build the `Expr` from the root up, and the bits that we haven't finished yet are left as 'holes' that we promise to figure out later.
These holes are called __metavariables__, a metavariable is an `Expr` that will be filled in with a proper `Expr` later.

Another new concept we need are __free variables__ (also called 'local constants'). These are all of the things above the `⊢` in the tactic state. In our case `p`,`q` and `r`.

An `Expr` containing metavariables is not technically in Lean's formal foundations, so any expression containing a metavariable is not a well-typed term. It will not count as a valid `Expr` until all of the `mvar`s are replaced with other valid `Expr`s of the correct type.

(Remember: this is a huge simplification, in fact there are lots of different states built in a huge monad transformer tower, but this is a good working model for now. I will explain how this is done in Lean 4 later.)
So, when you plonk your cursor in the `by` block. Lean makes a tactic state.
The tactic state comprises following pieces of data:
- The __environment__. In our example it would be the environment created by all of the Lean code before this `lemma`.
- A __local context__ `Γ`. A list of free variable declarations. To be discussed below.
- A __metavariable context__ `𝑀`. A set of metavariable declarations. To be discussed below.
- An `Expr` called the __result__, that depends on the metavariables and local constants given in `Γ` and `𝑀`.
- A list of __goals__, these are just a selection of metavariables from `𝑀` that we particularly care about. We refer to the head of this list to be the __main goal__.
- Lots of other configuration settings and options that I will gloss over here.

### The local context

The [local context](https://github.com/leanprover/lean4/blob/master/src/Lean/LocalContext.lean) is a list of __free variable declarations__.
A free variable declaration holds on to the following data:
- `(fvarId : FVarId)` a unique identifier for the variable
- `(userName : Name)` a pretty name that the user sees for this variable
- `(type : Expr)` the type
- `(bi : BinderInfo)` the binder info
- Optionally, if the declaration arose from a `let` binding we also get a `value : Expr` containing a expansion of the local constant. So for example you might have a local definition in the context. You can see one of these if you write `let x := f(y),` in the tactic block.

So when your `Expr` contains a `fvar id`, Lean figures out what that variable is by looking up it's unique identifier `id` in the local context `Γ`.

### The metavariable context

Reference: [src/Lean/MetavarContext.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/MetavarContext.lean) has a good docstring explaining the details. I am simplifying here.
I also discuss this in my thesis [§2.4](https://www.edayers.com/thesis/background#mvars) and [§A.1](https://www.edayers.com/thesis/zipper_appendix#dev-typing).

Similarly to the local context, a metavariable context has a dictionary of __metavariable declarations__. A metavariable declaration holds on to the following data:

- `userName : Name := Name.anonymous` a pretty name to show to the user. Metavariable names by convention start with a question mark.
- `lctx : LocalContext` the free variables that the metavariable is allowed to depend on
- `type : Expr` the type of the metavariable, which may itself contain metavariables.
- `id : MVarID` a unique identifier for the metavariable
- some extra data and flags for tracking typeclasses, caching, nesting mvar-contexts and other tricks

The metavariable context also has an __assignments__ table of `Expr`s indexed by `MVarId`. Once a metavariable gets assigned -- i.e. the hole is _filled_ by another `Expr` -- the `Expr` it is assigned to is stored in here. Given an expression `t : Expr`, write `𝑀 t` to be the expression `t` with each assigned metavariable in `t` replaced by its corresponding assignment. This process is called __instantiating the metavariables__ of `t`.

There are two actions we can perform on a metavariable context `𝑀`, we can __declare__ a new metavariable `Γ ⊢ ?𝑚 : α` by specifying a local context `Γ`, a type `α` and a variable name "`?𝑚`". For the declaration to be valid we need to have `α` is a valid sort in `𝑀;Γ`.
The other action is to __assign__ a metavariable `?𝑚` in `𝑀` with a value `v : Expr`. The steps in an assignment operation are as follows:

1. Instantiate the metavariables in `v`. That is, set `v` to be `𝑀 v`.
2. Find the declaration `⟨?𝑚, Γ, α⟩` in `𝑀`.
2. Assert that `?𝑚` is not already assigned. That is, `?𝑚` is not in `𝑀`'s assignment table.
3. Assert that `𝑀;Γ ⊢ v : α`. That is, `v` typechecks to `α` in the context of `𝑀` and `Γ`. This could fail because;
   - `v` does not type check to `α`
   - `v` depends on a free variable `𝑥` which is not in `Γ`
   - `v` depends on a metavariable `?𝑚₂` whose context `Γ₂` contains free variables not present in `Γ`. (sidenote: in the case that `Γ ⊆ Γ₂` instead of failing you can tell the assigner to make a new mvar `?𝑚₃` with context `Γ`, and assign `?𝑚₂` to `?𝑚₃`. This is called __restricting__ `?𝑚₂`. )
4. Assert that assigning `?𝑚` to `v` does not introduce any dependency loops. This could happen if `v ≡ ?𝑚 + 1`. There are more complicated cases too, like maybe `v` depends on a metavariable `?𝑛` which is assigned to an expression containing `?𝑚`. Or perhaps the dependency loop is introduced in the contexts `Γ` for the metavariables.
5. Replace every occurrence of `?𝑚` in `𝑀`'s expressions with `v`.

It's important to rember that just because a metavariable has been _assigned_ -- that is, has an entry in the assignments table -- that metavariable won't be magically removed from all of the expressions that depend on it. We say an expression `t` has been __instantiated__ with `m` when all of the occurrences of `m` in `t` have been replaced with its assignment.

Similarly, there is also an assignments dictionary for type universe (`Level`) metavariables.

### The tactic state lifecycle

Now lets go back to our running example:

```lean
lemma my_lemma (p q r : Prop) : (p → q → r) → (p → q) → p → q × r := by
  <cursor goes here>
```

Now let's go back to putting the cursor in the `by` block. Lean then initialises the tactic state as follows.
- A metavariable context and local context for the tactic state are initialised ([note] technically it's initialised by the elaborator beforehand)
- Any arguments of the lemma (eg the `(p q r : Prop)` before the `:`) get added to the local context `Γ`. This also happens for names and typeclass instances that appear in a `variable` declaration that appear somewhere in the type definition.
- A fresh metavariable `?result` is created with context `Γ`. The type of `?result` is set to be the statement to be shown. So in the example `?result` would have type `(p → q → r) → (p → q) → p → q × r` and context `[p,q,r]`.
- The `result` of the tactic state is set to be `?result`.
- The `goals` of the tactic state are set to be `[?result]`.

The picture to keep in mind is that of a [growing coral](https://www.youtube.com/watch?v=dU6KmDP0qhw), where the tips of the growth are metavariables, we grow the tree by replacing the metavariables with new bits of tree capped by new metavariables.
The `result : Expr` is the root of this tree. The `goals` are a list of the metavariables that we wish to grow next; once we have solved the first in the list we move on to the next.
The `tactic` monad is a monad that can access the tactic state and use it's various methods to successively grow this tree.

Now in the `by` block we specify a sequence of tactics, which are themselves composed of more tactics and so on until you reach some atomic tactics that manipulate the expressions directly.

These atomic tactics have been chosen in such a way that it is difficult to make the `result` be an invalid expression. It's not a risk to the integrity of the system if you make an invalid expression though, because it will still be caught by the kernel.

After all of the tactics have been applied, and assuming none of them failed. You will now have a new tactic state. At the end of the tactic block, Lean will do the following checks

- Is the goal list empty? If not error with "tactic failed, there are unsolved goals".
- Does the `result`, depend on any unassigned metavariables? If so then error with "tactic failed, result contains meta-variables". You are allowed to have unassigned variables that are not present on `result`, these are called __dangling__ metavariables.
- Does the `result` typecheck? If not then error with "tactic failed, result does not typecheck" ([todo] what was the error in Lean 4)

If it passes these then Lean is satisfied and you have constructed a valid proof term for your lemma.
If your proof contains `sorry`, then Lean will give you a disapproving warning. You can almost hear Lean sighing, lamenting your inadequacy.

## An example tactic: `intro`

[todo] I think this would be better written in Lean 4 as an example. Also not sure it is a good starter.

The `intro : Name → Tactic Expr` tactic is used to turn goals which look like `⊢ (a : α) → β` into goals which look like `(a : α) ⊢ β`.

Here is the explicit routine for `my_intro n` for if you were to write the tactic yourself.
1. Look at the first metavariable `?𝑚` in `goals` (the main goal) and look up its `type : Expr` and `Γ : LocalContext` in the metavariable context.
2. Assert that `type = ($a : $α) → $β` for some `a : Name` and `α β : Expr`.
3. Create a new free variable `𝑎` with name `n` (the argument to `intro`) and type `α`.
5. Instantiate `β` with `𝑎`. That is, replace the topmost `bvar` in `β` with `𝑎`.
4. Make a new metavariable `?𝑏` with `Γ,(𝑎 : α) ⊢ ?𝑏 : β`.
5. Assign `?𝑚` with `fun (𝑎 : α) => ?𝑏`  ([todo] complication here with delayed abstraction, not sure how this works in Lean 4)
6. Set the goals to be `[?𝑏]`
7. Return `𝑎`.

Now we can run this tactic in our proof. [todo] actually make this example work.
Explain how to do this with tactic syntax and so on.

```lean
open tactic
lemma my_lemma (p q r : Prop) :
    (p → q → r) → (p → q) → p → q ∧ r := by
    my_intro `h₁
    my_intro `h₂
```

## Comparing Expressions: Reduction, Matching, Unifying and so on

We often need to take two `Expr`s and check if they are 'the same'. We will write an "are they the same?" question as `s =?= t`.
But alas there are lots of ways to interpret `the same' and we need to use different interpretations in different circumstances.

- The most obvious measure of sameness is just to check that the `Expr`'s trees look _precisely_ the same: just go through the tree and recursively check that all of the arguments for the `Expr` cases are equal. This is called __structural equality__.
- The next one is the same as the above but we forget about the `Name` parameter on `Expr`s which bind things. This is called __equality up to α-equivalence__. In Lean this is done automatically because of de-Bruijn indices so Lean calls this structural equality too.
- Our type theory CIC comes with a set of reduction rules -- [stated below](#reduction-in-lean). Which are ways of transforming exprs. If two `Expr`s are structurally equal up to performing reductions, we say the expressions are __definitionally equal__. Lean's kernel uses definitional equality to check if things are equal.
- Often the expressions we are matching will involve metavariables. Then if we find ourselves needing `?m =?= t` to be true, we can assign `t` to `?m` to force the terms to match. This is called __unification__. There is a huge amount of CS theory about unification. As long as none of the metavariables are functions, it can be shown that there is a decidable, most general set of assignments to metavariables that works ([todo] cite Nipkow). Higher order unification, where you also have to fill metavariables which are functions, is known to be undecidable. [Todo] check this isn't misleading.
- If you are only allowed to assign metavariables on the _left_ ([TODO] check this) hand side of the `=?=` then we call it __matching__. (In Lean, this is morally true but matching can also sometimes assign typeclass metavariables on the right, [todo] still true in Lean 4?)
- Finally, given a set of equations `E`, we can ask: "is there a sequence of `E` rewrites that will make these terms equal?". The best book to read about this kind of 'sameness' is Nipkov's _Term Rewriting and All That_. There are plenty of interesting algorithms and theory here too.

[TODO] What does Lean do for (undecidable) higher unification problems? It looks like in some special cases it actually has a go at doing it. Eg when guessing the motive for `rec`. I think this is discussed in the `Elaboration in Lean` paper.

[todo] What are unification hints?

[todo] Unification is a huge area of research so I am having some trouble deciding what to include in this doc. I am also finding it difficult to figure out exactly which unification algorithms Lean is using. Eg. It seems to be doing higher order unification in some special cases so I guess it's using something like Huet's algorithm to do this. There are also loads of settings that one can pass to the unifier which I don't understand (eg what exactly does the `approx` setting do in `apply_core`?) [todo] this has potentially all changed in Lean 4

In general, expressions can reduce to gigantic objects, so the definitional equality checker uses heuristics and caching to run in a reasonable amount of time.

### Reduction in Lean

Let's write out all of the fundamental reductions we have in Lean's type theory. We write 'equivalence' when we have a reduction which doesn't terminate. So for example we could perform α-equivalence forever.
- __α-equivalence__ is renaming bound variables. Thanks to de-Bruijn indices this is done automatically.
- __β-reduction__ is `(λ x : a, b) c ~~> b[x/c]`. That is, 'running' a lambda expression.
- __δ-reduction__ is replacing a constant with its definition.
- __ζ-reduction__ is reduction of `let` bindings: `let x : a := b in c ~~> c[x/b]`. Perform it on an expression with the `zeta` or `head_zeta` tactic.
- __η-equivalence__ is the rule that  `(λ x, f x)` can be reduced to `f`. Perform it with the `eta` or `head_eta` tactic.
    You can also use the tactic `headEtaExpand` to do η-reduction backwards. Eg; `f` is converted to `(λ x, f x)`. If `f` isn't a function then it just returns `f`. [todo] Lean 4?
- __ι-reduction__ is reducing recursors on inductive datatypes: for example `Nat.rec i r (succ n) ~~> r n (Nat.rec i r n)` and `Nat.rec i r 0 ~~> i`. Reducing any recursively defined function.
- __proof-irrelevance__ if `P : Prop` and `a b : P`, then (according to Lean), `a` is definitionally equal to `b`.

Interestingly, ι-reduction and proof-irrelevance together make definitional equality undecidable. But only cases which we don't really care about are undecidable so it's ok. See section 3.7 of the [Lean Reference Manual](https://leanprover.github.io/reference/lean_reference.pdf).

### What is WHNF?

'WHNF' stands for "weak head normal form". This basically means "apply the minimal amount of reductions so that the root of the `expr` can't be reduced further". Often this is less work than fully reducing the expression and often we only care what the root looks like anyway.
There is [a stack overflow answer](https://stackoverflow.com/questions/6872898/haskell-what-is-weak-head-normal-form) that explains WHNF well. Finding the WHNF is decidable but in general but can take arbitrarily long to compute.
You can put an expression in WHNF using the `whnf` tactic. You can see this used in the `intro` tactic.

### Transparency

In general, expressions can reduce to gigantic objects, so the definitional equality checker uses heuristics and caching to run in a reasonable amount of time. One of these is to give certain constants a 'transparency' setting which tells Lean's definitional equality system how eagerly it should try to expand definitions.


You can tell the definitional equality system how keenly to expand these constants by setting the `TransparencyMode`. This is an option that can be set on the `MetaM` ([todo] check?) monad.
Transparency mode is a parameter representing how aggressively definitions should be unfolded when trying to decide if two terms match, unify or are definitionally equal.
By default, theorem declarations are never unfolded.
You can decorate constants with the attributes `@[reducible]` and `@[irreducible]` which will be respected by the transparency mode.
There are four available transparency modes:
- `all` will unfold everything, including irreducible definitions and theorems
- `default` will unfold everything except theorems and definitions tagged as irreducible.
- `instances` will unfold all class instance definitions and reducible definitions.
- `reducible` will only unfold definitions tagged with the `reducible` attribute.

How to decide what to use? Choosing the transparency mode is hard, you are trading off speed vs ability to spot that things are equal. In general it should be fine to use the default mode. I found when writing tactics that if you know things aren't going to need to be unfolded then you can get a significant speedup by using the `reducible` mode.

Choosing the `@[reducible]` and `@[irreducible]` attributes is ok too. Generally you give `@[reducible]` to things that are like aliases or just convenience definitions. For example it would make sense to make `def MyMonad := ReaderT ρ $ StateT σ $ IO` a reducible definition because the definition only exists to save you typing.
You should consider using `@[irreducible]` when you know that expanding a definition is almost never going to be useful. An example is the definition of real numbers (which might be something complicated with Dedekind cuts or Cauchy sequences). To prove things about real numbers you are almost always better off using existing lemmas that don't talk about the implementation of real numbers.

## How `apply` works

Here is what `apply fn` does:

- Get the type signature of `fn`. Unwind the `forallE`s to get `fn : Π (a:A) (b:B) (c:C) ..., X → Y → Z(a,b,c. ...)`. That is, `fn`'s type is a telescope of `forallE`s and I am using the convention that the return type `Z` depends on the bound variables `a,b,c` at the start of the alphabet but not on `X,Y`. `X`,`Y` might also depend on `a`,`b` and so on.
- For each argument `A,B` ... `X,Y`, make a fresh metavariable `?a,?b, ... ?x,?y`.
- Unify (that is, do definitional equality while assigning metavariables) the return type of `fn` with the main goal type `G`: `Z(?a,...) =?= G`. There are various settings which change exactly how the unification works to be discussed below. If unification fails, then `apply` fails too.
- Now that unification has succeeded, assign `fn ?a ?b ... ?x ?y` to the goal metavariable and add all of the new metavariables that weren't assigned by the unification as a goal.

[TODO] what definitions are we allowed to expand? Does it put it in WHNF first?
