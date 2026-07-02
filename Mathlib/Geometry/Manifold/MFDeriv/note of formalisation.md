## Formalisation notes

**ext lemmas**
ext-like arguments using injective_eval_vectorField, injective_inner_vectorField
test agreement of continuous linear maps

should we make this a domain-specific tactic?
say, `mfld_ext` tactic (perhaps allowing to specify details such as `mfld_ext ContMDiff 1` )

is it always clear which one we want?
  one applies to a vector bundle with an inner product, the other to a Hom bundle
  there is a situation where both could apply (e.g., induced inner product of the Hom bundle)




**notation**
Should we be able to talk about "let ∇^g be the L-C connection on M w.r.t. g"?
- Is it possible to talk about the class of R metric on a mfd? Not easy, right now
- Can we do Ricci flow iwth the current set-up, i.e. for a family of Riemannian metric?
----> add a TODO in the module doc-string to state that we want this
  enable this formalisation



rhs_aux: would be nice if it never existed; two reasons why not yet
  one is the typeclass issues (inner_bundle' etc.)
  the other is that we want fun_prop to support MDifferentiable, so we can just automate this
eventually, all of the proofs of their properties should be `simp (disch := fun_prop)`

other issue: `rhs_aux` should be inlined instead, once all the automation works right


stop-gap solution: tag `MDifferentiable` with fun_prop in this file, all the lemmas we want,
  and just hope things work (fingers crossed)
more robust automation would be nice!


leviCivitaRhs_add_applyY lemmas are all fine, as auxiliary data


**about the design**
lcAux is the underlying function of our connection
  needs to assign a section given any inputs, so there needs to be a junk valu



future tactic support: tactic for normalising expressions involving inner products and Lie brackets
  e.g., swap terms into canonical order (such as, atom order as determined in AtomM),
  perhaps apply Jacobi identities if I want to? inspired by the lie_ring tactic?
  and generate side goals as I need them...
  (mlieBracket_swap_apply doesn't need differentiability hypotheses -> so perhaps none?)
