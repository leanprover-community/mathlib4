
# How metaprogramming works. Part 01: Datatypes that Lean uses for metaprogramming

I'll now talk about all of the main datatypes in the Lean metaprogramming world.

## Expressions

The Lean type `Expr` is just an inductive datatype that you can look at like any other. Let me give a cut down version of the one given in [Lean/Expr.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Expr.lean) where I throw away some details to add back in later.

```lean
inductive Expr where
  | bvar    : Nat → Expr                       -- bound variables
  | fvar    : FVarId → Expr                    -- free variables
  | mvar    : MVarId → Expr                    -- meta variables
  | sort    : Level → Expr                     -- Sort
  | const   : Name → List Level → Expr         -- constants
  | app     : Expr → Expr → Expr               -- application
  | lam     : Name → Expr → Expr → Expr        -- lambda abstraction
  | forallE : Name → Expr → Expr → Expr        -- (dependent) arrow
  | letE    : Name → Expr → Expr → Expr → Expr -- let expressions

  -- less essential constructors:
  | lit     : Literal → Expr                   -- literals
  | mdata   : MData → Expr → Expr              -- metadata
  | proj    : Name → Nat → Expr → Expr         -- projection
```

We can represent any Lean term using the above definition.
Multiple arguments are done using _partial application_: `f x y ↝ app (app f x) y`.

What is each of these constructors doing?

- `bvar` is a __bound variable__. For example, the `x` in `fun x => x + 2` or `∑ x, x²`. This is any occurrence of a variable in an expression where there is a binder above it. Why is the argument a `Nat`? This is called a de-Bruijn index and is explained [here](#de-bruijn-indexes). You can figure out the type of a bound variable by looking at its binder, since the binder always has the type information for it.
- `fvar` is a __free variable__. These are variables which are not bound by a binder. An example is `x` in `x + 2`. Note that you can't just look at a free variable `x` and tell what its type is, you need there to be a context (denoted `Γ` from the previous section) which contains an declaration for `x` and its type.
  A free variable has an ID that tells you where to look for it in a `LocalContext`
  In Lean 3, free variables were called "local constants" or "locals".
- `mvar` is a __metavariable__. There will be much more on these later, but you can think of it as a placeholder or a 'hole' in an expression that needs to be filled at a later point.
- `sort` is used for `Type u`, `Prop`. The meaning of `Level` is discussed [here](#type-universes).
- `const` is a constant that has been defined earlier in the Lean document.
- `app` is function application.
- `lam n t b` is a lambda expression (`fun ($n : $t) => $b`). The `b` argument is called the __body__. Note that you have to give the type of the variable you are binding.
- `forallE n t b` is a dependent arrow expression (`($n : $t) → $b`). This is also sometimes called a Π-type or Π-expression. Note that the non-dependent arrow `α → β` is a special case of `(a : α) → β` where `β` doesn't depend on `a`. The `E` on the end of `forallE` is to distinguish it from the `forall` keyword.
- `letE n t v b` is a __let binder__ (`let ($n : $t) := $v in $b`).
- `lit` is a __literal__, this is a number or string literal like `4` or `"hello world"`. These are not strictly necessary for the kernel, but they are kept mainly for convenience. (Ie in Lean 3, there were a load of tricks needed to store `11234 : Nat` as something more efficient than `succ $ succ $ succ ... $ succ zero`)
- `mdata` is just a way of storing extra information on expressions that might be useful, without changing the nature of the expression.
- `proj` is for projection. Suppose you have a structure such as `p : α × β`, rather that storing the projection `π₁ p` as `app π₁ p`, it is expressed as `proj Prod 0 p`. This is for efficiency reasons ([todo] find link to docstring explaining this).

## de-Bruijn Indexes

Consider the following lambda expression ` (λ f x, f x x) (λ x y, x + y) 5`, we have to be very careful when we reduce this, because we get a clash in the  variable `x`.
To avoid variable name-clash carnage, `expr`s use a nifty trick called __de-Bruijn indexes__.
In de-Bruijn indexing, each variable bound by a `lam` or a `pi` is converted into a number `#n`.
The number says how many binders up the `expr` tree we should look to find the binder which binds this variable.
So our above example would become (putting wildcards `_` in the type arguments for now for brevity):
``app (app (lam `f _ (lam `x _ (app (app #1 #0) #0))) (lam `x _ (lam `y _ (app (app plus #1) #0)))) five``
Now we don't need to rename variables when we perform β-reduction. We also really easily check if two `expr`s containing bound expressions are equal.

This is why the signature of the `var` case is `nat → expr` and not `name → expr`.
If in our `expr`, all `var`s are bound, we say that the `expr` is __closed__.
The process of replacing all instances of an unbound `var` with an `expr` is called __instantiation__.
Going the other way is called __abstraction__.




## Type Universes

To avoid paradoxes (think; "does the type of all types contain itself?"), we have an infinite hierarchy of type universes. This is one of the more confusing things for newcomers but it can be ignored most of the time.

You can think of a universe level as just a natural number. But remember that these numbers are at the meta level. So you can't perform induction on them etc. That means that the numbers are used to talk about things within Lean, rather than being an object of study itself. Here is a (simplified) definition, given in `library/init/meta/level.lean` in the Lean codebase with my comments

```lean
inductive Level where
   -- The zeroth universe. This is also called `Prop`.
  | zero   : Level
  -- The successor of the given universe
  | succ   : Level → Level
  -- The maximum of the given two universes
  | max    : Level → Level → Level
  -- Same as `max`, except that `imax u zero` reduces to `zero`.
  -- This is used to make sure `(x : α) → t` is a `Prop` if `t` is too.
  | imax   : Level → Level → Level
  -- A named parameter universe. Eg, at the beginning of a Lean
  -- file you would write `universe u`. `u` is a parameter.
  | param  : Name → Level
  -- A metavariable, to be explained later.
  -- It is a placeholder universe that Lean is expected to guess later.
  | mvar   : MVarId → Level
```

Universes can be thought of as a tedious-but-necessary bookkeeping exercise to stop the paradoxes and Lean does a good job of hiding them from the user in most circumstances.
Because of this, I will try my hardest to omit details about type universes for the rest of this document.

## Names


A name is just a list of strings and numbers `string1.3.string2.string3.55`. We use a list of strings because then we can have things like `namespaces`.


```lean
/- Hierarchical names -/
inductive Name where
  | anonymous : Name             -- the empty name
  | str : Name → String → Name -- append a string to the name
  | num : Name → Nat → Name    -- append a number to the name
```



## Environments and declarations

When we write a Lean document, Lean constructs an `Environment` that contains all of the axioms, inductive types, theorems and definitions that we we have put in the document.
You can think of the environment as a giant sequence of things called __constants__.
Each constant in an environment has a unique `Name` and a type. Depending on whether it is an axiom, theorem, definition and so on, it can have other things too. For example a theorem and definition both have a value.

```lean
/-- Information associated with constant declarations. -/
inductive ConstantInfo where
  | axiomInfo    (val : AxiomVal)
  | defnInfo     (val : DefinitionVal)
  | thmInfo      (val : TheoremVal)
  -- ... lots of oterh
```

When one writes `map succ [4,5,6,7]` in a new Lean file, it doesn't parse, because Lean can't find anything in the environment or context with the name `map` or `succ`. We have to give their full names `List.map Nat.succ [4,5,6,7]`. Alternatively, we can add `open Nat List` above, this tells Lean that if it can't find something called `x`, it should also try out `List.x` and `Nat.x`.
Lean is also clever and can usually disambiguate a name clash using their type information.

Environments also contain lots of other information through the use of __environment extensions__.
These are used to store information for syntax, options, simp lemmas and many more things.
You can write your own environment extensions, which I hope to be a topic of a future chapter.

## Getting `Name`s in Lean

We can use backticks `` ` `` to access names from Lean objects.

* `` `my.name`` is the way to refer to a name. It is essentially a form of string quoting; no checks are done besides parsing dots into namespaced names
* ``` ``some ``` does name resolution at parse time, so it expands to `` `option.some``. It will error if the given name doesn't exist. [todo] check if this is still true in Lean 4.

When you write `namespace x ... end x` in your document, this is the same as using `open x` and prepending `x.` to all of your declarations within the `namespace/end` block.

## Getting `Expr`s in Lean.

[todo] update this section for Lean 4

As fun as it would be to type out `Expr`s in terms of `var`, `lam`, etc and doing all of the de-Bruijn index bookkepping yourself,
Lean provides a syntax to quickly convert any Lean expression into an `Expr`.

* `` `(my expr)`` constructs an expression at parse time, resolving what it can in the current (of the tactic) namespace
* ``` ``(my pexpr)``` constructs a pre-expression (an expression where implicit arguments have not been filled in) at parse time, resolving in the current (of the tactic) namespace
* ```` ```(my pexpr)```` constructs a pexpr, but defers resolution to run time (of the tactic), meaning that any references will be resolved in the namespace of the begin end block of the user of the tactic, rather than the tactic itself

The process of taking a string of unicode characters and converting them a Lean expression is called __elaboration__. Elaboration is a huge topic that will be covered later ([NOTE] still to do.).

A shorthand for going from an `Expr` `e` to a Lean object is to use `%%e`. This is called  an __anti-quotation__. So for example ```(f $ %%e)`` would create ``expr.app (expr.const `f) e``. [todo] is this still the Lean 4 syntax?

## Implicit arguments and `binderInfo`

Lean supports some extra information about binders that lets us write more concise code.
The two main mechanisms that Lean uses are __implicit arguments__ and __typeclass instances__.

Each `lam` or `forallE` binder comes with a `binderInfo` argument (stored in metadata for Lean 4). This can be set to
- `default` -- `(x : α)`
- `implicit` --  `{x : α}`
- `strict_implicit` -- `⦃x : α⦄`
- `inst_implicit` -- `[x : α]`.
- `aux_decl` -- Auxillary definitions are helper methods that Lean generates. `aux_decl` is used for `_match`, `_fun_match`, `_let_match` and the self reference that appears in recursive pattern matching.

The difference between `{}` and `⦃⦄` is how implicit arguments are treated that are *not* followed by explicit arguments.
`{}` arguments are applied eagerly, while `⦃⦄` arguments are left partially applied:
```lean
def foo {x : ℕ} : ℕ := x
def bar ⦃x : ℕ⦄ : ℕ := x
#check foo -- foo : ℕ
#check bar -- bar : Π ⦃x : ℕ⦄, ℕ
```

## Constructing valid `Expr`s

You may have noticed that it is possible to make lots of badly typed `Expr`s.
For example, `lam "f" nat (app [0] [0])`.

So just having an `Expr` term tree is not enough to count as something that Lean can use to prove theorems.
Lean has to be able to show that the `Expr` could have been built using the inference rules of CIC. We say that an `Expr` with this property is __valid__.

Lean does this by running an `Expr` through the __type-checker__. The type-checker takes an `Expr` and recursively type-checks it's sub-`Expr`s until eventually erroring or returning a new `Expr` giving the type of the provided `Expr`.
Type-checking is done by Lean's __kernel__.
If there is a bug in the kernel, then you might be able to derive an instance of `False` which type-checks and the entire system will become useless.
So it's important that the kernel is small so that it can be easily reviewed by lots of humans for bugs.
The Lean (3) kernel is about 40,000 lines of code and lives in `src/kernel` ([todo] update for Lean 4).
So if you want to be _totally sure_ that your proof in Lean is correct you have to learn C++ and carefully read all of the kernel.

Now, writing down `Expr` trees is very time consuming, because you have to manually add all of the type arguments.
For example,
```lean
set_option pp.all true -- show all of the gory details.
#check (λ x , x + 2 )
/- outputs:
λ (x : nat), @has_add.add.{0} nat nat.has_add x (@bit0.{0} nat nat.has_add (@has_one.one.{0} nat nat.has_one))
-/
```

[todo] update above for Lean 4

We don't want to have to write out all of that every single time, so we use an __elaborator__ to figure out what all of the implicit arguments and typeclass arguments are.

Briefly, we turn a string of text into a Lean expression by first __parsing__ the text to get a `Syntax` object.
The `Syntax` is then converted to an `Expr` through a procedure called __elaboration__. The elaboration procedure in Lean 4 is very complex, but it essentially does the following things:

- Figure out what values implicit arguments should have
- Figure out what typeclasses should be used
- Expand macros
- Figure out what type universes should be used
- Give you a nice error when one of the above goes wrong

Similarly, when we make a proof using tactics, we use tactics to figure out all of the details of the `Expr` representing the proof term. Both tactics and the elaborator are programs for constructing well-typed expressions.
These expressions are constructed gradually using things called __metavariables__.
