# A dialogue between AIs

Giovanni Francesco Sagredo was a Venetian mathematician,
who appears as one of the three protagonists in
Galileo's "Dialogue Concerning the Two Chief World Systems".

He wants to hear and understand the arguments of
Salviati (a Copernican, in fact Galileo in a fake moustache) and
Simplicio (a die-hard Ptolemaist, set up for scorn, starting at his name).

`sagredo` is a tactic for constructing mathematical proofs,
and works by facilitating a dialogue between two very different AIs.
On one side we have GPT4, the large language model from OpenAI.
On the other, we have the interactive theorem prover Lean 4.

At this moment, GPT4 needs little introduction.
I really enjoyed reading
[Sparks of Artifical General Intelligence](https://arxiv.org/abs/2303.12712)
for a great overview. It is astonishingly capable across many domains.
While creative, it is also prone to bullshitting.

The claim that we should think of Lean 4 as an AI warrants further scrutiny,
and perhaps some poetic licence.
Lean 4 is a programming langauge (functional, fast, and with powerful metaprogramming)
with both a sufficiently expressive type system to allow formalisation of modern mathematics,
and the tooling and tactics which make it to enjoyable to do so.
See the [system description](https://leanprover.github.io/papers/lean4.pdf),
[do unchained](https://leanprover.github.io/papers/do.pdf),
and [Lean entering the big league](https://www.quantamagazine.org/lean-computer-program-confirms-peter-scholze-proof-20210728/).

As an interactive theorem proving tool, you should think of it as a specialized AI
which can read and understand mathematical proofs.
It not only *verifies* that proofs are correct, but *identifies mistakes*,
and can explain the remaining logical obligations when presented with a partial proof.
While it has some tactics that fill in low-level proofs automatically,
and tools that assist in searching for proof steps,
it is not creative. It is a great skeptic, but not an artist.

`sagredo` puts these two in a room together, and makes them talk to each.

## An example

We use `sagredo` by invoking it in a proof environment in Lean 4, for example as:

```lean
theorem length_append (L M : List α) : (L ++ M).length = L.length + M.length := by
  sagredo
```

The tactic wakes up and inspects the environment it is running in.
It gathers the source code of the current declaration,
replaces the word `sagredo` with the word `sorry`
(this is a universal "proof of anything" in Lean, which langauge flags with a warning),
and sends off a request to GPT4 that it try to extend the proof.
We include a quite substantial prompt, which we'll defer discussion of for now.

GPT4 responds, perhaps with something like:

```lean
theorem length_append (L M : List α) : (L ++ M).length = L.length + M.length := by
  induction L with
  | nil => sorry
  | cons x L' ih => sorry
```

We see that it has begun a proof by induction on the list `L`, and plans to do a base case
and an inductive step. (Our prompting encourages it not to do everything at once.)

We then take this code and run it in Lean. `sagredo` asks Lean first of all if there are any errors
(in this example there are not). Then it inspects the proof for completeness.
Incompleteness can occur either because of use of `sorry` in the proof,
or because the goal has not been closed by the final step.
In either case, we report back to GPT4 what it still needs to do.
In this example, along with other prompting, we might say that there is a new goal state on line 3:

```lean
case nil
α : Type u_1
ys : List α
⊢ List.length ([] ++ ys) = List.length [] + List.length ys
```

We now go back and forth, in a fully automated loop, getting proposals from GPT,
and asking Lean to identify errors or remaining proof obligations.

After several steps we either give up for lack of progress, or report back to the user
a *verified proof*. In this example `sagredo` takes roughly 4 or 5 iterations to obtain:

```lean
theorem length_append (L M : List α) : (L ++ M).length = L.length + M.length := by
  induction L with
  | nil =>
    rw [List.nil_append, List.length_nil, Nat.zero_add]
  | cons x L' ih =>
    rw [List.cons_append, List.length_cons, List.length_cons, Nat.succ_add, ih]
```

It would be hard to ask for a nicer proof!

## Autoformalization and proof outlines

We wanted to see if we could give problems stated in natural langauge,
or provide natural langauge proof outlines to assist GPT4.

We haven't tested much here, but as `sagredo` includes comments in the initial problem sent to GPT4,
it was easy enough to try.

```lean
/-- The length of the concatenation of two lists is the sum of the lengths of the lists. -/
theorem length_append : sorry := by sagredo
```

gives roughly the same results as the example above!

```lean
/-- The length of the concatenation of two lists is the sum of the lengths of the lists. -/
theorem length_append (xs ys : List α) : List.length (xs ++ ys) = List.length xs + List.length ys := by
  induction xs with
  | nil => rw [List.nil_append, List.length_nil, Nat.zero_add]
  | cons x xs' ih => rw [List.cons_append, List.length_cons, List.length_cons, ih]; rw [Nat.succ_add]
```

In this case it came up with different variable names,
wrote the statement in slightly different syntax,
and used two successive calls to the rewrite tactic in the inductive step, rather than one.
(In this run, it first attempted just the initial string of rewrites, and then,
when prompted that the goal wasn't quite closed, added the last one.)

Even without adjusting the prompting to warn GPT4 that the theorem statement itself
would be missing, it caught on immediately and used the natural language comment.
In fact, in this admittedly easy case, you can omit even the comment,
and in most runs GPT4 starts off in the right direction solely based on the name of the theorem.

## Prompting

We begin with a initial prompt, which needs to address several issues.

First, the GPT4 training data includes rather little Lean 4 code.
Most of this probably came from the compiler code itself.
The community only started porting `mathlib`, the main mathematical library for Lean,
in earnest in late 2022.
We include in the system prompt a tutorial on the syntax changes between Lean 3 and Lean 4.

We ask GPT4 not to attempt to complete the whole proof at once.
Instead, we ask it to write a natural langauge plan,
and then only to write the first step of the tactic proof.
We're still experimenting here,
but this combination seems to be a good compromise between
getting it to think about the overall structure, so it can start in the right direction,
and not pressing on past its own capabilities in writing the detailed proof.
We want to ensure that Lean has a chance to speak too,
and to provide timely feedback before GPT4 commits to its mistakes.

We currently turn the "temperature" setting for GPT4 down quite low (e.g. `0.2`),
but futher experimentation is warranted here.

## Usage

It's not quite ready for primetime,
but if you have an OpenAI key with access to GPT4 you can run it.
Put your key in the `OPENAI_API_KEY` environment variable.

You'll need to grab the `sagredo` branch of the `mathlib4` repository.
Importing `Mathlib.Tactic.Sagredo` gives access to the tactic.

At present there is no user feedback until the end of the conversation,
when the tactic reports the last solution it considered, and whether it works.

We're working on better user interface, to show intermediate steps
and allow tweaking various knobs, which for now you need to modify the source code for.

## Future work

We obviously need to test this on many more examples.
So far it's just of proof of concept implementation, written over several days.
We're getting ready to try it on `minif2f` and `proofnet` problems.
