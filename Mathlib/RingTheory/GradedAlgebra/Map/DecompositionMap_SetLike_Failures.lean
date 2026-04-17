import Mathlib

/-
   This file contains two failed attempts at generalizing the construction of an induced
   decomposition/grading to an abstract `SetLike` situation, along with "reasons" why they
   failed.
-/

section ADDITIVE
/- PART I:  The additive decomposition -/
/-
   Problem:  I cannot find an adequate replacement for the span of some
   AddSubmonoid's / Submodule's `ℳ i` of `M` in the context of
   `[SetLike σ M] [AddSubmoduleclass σ ℳ]`.

   - For AddSubmonoid's / Submodule's, the span is given by `iSup i, ℳ i`.
     But that does not generalize well, see details below.
   - It also does not seem promising to try to work with
     "the image of the canonical map `⨁ i, ℳ i → M`" instead
     -- what *is* the image in the context of AddSubmonoidClass?

     I don't even know how to formulate the following question in a
     syntactically correct way:
     Given some "generalized submonoids" `ℳ : ι → σ`, i.e.
     `[SetLike σ M] [AddSubmoduleclass σ ℳ]`, is a each single
     submonoid `ℳ i` also a "generalized  submonoid" of `(⨁ i, ℳ i)`?
-/


open DirectSum

variable {M : Type*} [AddCommMonoid M]
variable {ι : Type*} [DecidableEq ι]
variable {σ : Type*} [SetLike σ M] [AddSubmonoidClass σ M] [CompleteLattice σ] [IsConcreteLE σ M]
variable (ℳ : ι → σ)

def SetLike.inclusion {p q : σ} (h : p ≤ q) : ↥p →+ ↥q :=
    (AddSubmonoidClass.subtype p).codRestrict q
      (fun x ↦ IsConcreteLE.coe_subset_coe'.mpr h x.2)

def toIsup : (⨁ i, ℳ i) →+ (⨆ i, ℳ i : σ) :=
    DirectSum.toAddMonoid fun i ↦ SetLike.inclusion (le_iSup ℳ i)

lemma toIsup_surjective : Function.Surjective (toIsup ℳ):= by
  sorry

/-
This is where things break.

The maps is surjective for `AddSubmonoid` and `Submodule M` because `iSup_eq_closure` and
closure_induction` — namely ⨆  is computed as "the additive closure of the union of carriers".
For an abstract σ with just [CompleteLattice σ] [AddSubmonoidClass σ M] [IsConcreteLE σ M], this
is not guaranteed. The lattice operations on σ could perform additional closure beyond additivity.
Concretely, take σ = Submodule R M: ⨆ i, S i is the span, which a priori is larger than the
additive closure. (It happens to coincide for submodule families because each summand is already
scalar-closed — but this coincidence is not derivable from the SetLike+AddSubmonoidClass+
CompleteLattice+IsConcreteLE typeclasses alone.)

Even if I assume that I start with a decomposition of `M` into pieces `ℳ i`, I don't see any
guarantee why a partial direct sum `⨁ i, ℳ i` should agree with a partial internal supremum
`⨆ i, ℳ i`.  Just consider `M` to be given as `M = M₁ ⊕ M₂`, with the noted decomposition,
but the closure operation being trivial, so that the closure of `M₁` is already all of `M`.
Why should the above assumptions rule out this situation?

Claude suggests introducing an additional typeclass:

class IsAddSubmonoidClosure (σ : Type*) (M : Type*) [AddCommMonoid M]
    [SetLike σ M] [AddSubmonoidClass σ M] [CompleteLattice σ] : Prop where
  iSup_induction : ∀ {ι : Sort*} (S : ι → σ) {motive : M → Prop} {x : M},
      x ∈ ⨆ i, S i →
      (∀ i, ∀ x ∈ S i, motive x) →
      motive 0 →
      (∀ x y, motive x → motive y → motive (x + y)) →
      motive x

-/
end ADDITIVE


section MULTIPLICATIVE
/- PART II:  The multiplicative structure -/

/- A failed attempt to generalize the induced decomposition of a graded algebra to
`SetLike.GradedMonoid`, i.e. to use `S` with `[SetLike S M]` instead of `S = Submodule R M`.

**Upshot: This is likely impossible, or in any case impractical.  Details below.**

To get started, I assume `[SetLike S M]` and `[SubmonoidClass S M]`.
The second assumption is unproblematic as `SetLike.GradedMonoid`
assumes `[SubmonoidClass S M]` anyway.

I also need `[CompleteLattice S]` just to define the induced grading.
And then I need to assume `[IsConcreteLE S M]` for the lattice structure/partial order/`LE` on `S`
to be compatible with the partial order induced from the SetLike structure.
Again, I don't consider this problematic; these instances exist on submodules.

(It's easy to check whether an instance is defined for Submodules, e.g.:
   #check (inferInstance : CompleteLattice (Submodule R M))
)

With this, I can define the induced grading and prove the `one_mem` part of a
`GradedMonoid` instance.

**However, I don't see how one could possibly deduce the `mul_mem` part**
**-- this requires some compatibility between the lattice structure on `S`**
**and the multiplication on the ring `M`.**

So far, `S` knows nothing about multiplication.

*Claude*:
To make the abstract proof work, you'd need two extra assumptions on S:

- [Semigroup S] — a Mul on sub-objects, with a compatibility axiom:
  a ∈ p → b ∈ q → a * b ∈ p * q
  (This is what Submodule.mul_mem_mul gives for Submodule.)
- [IsQuantale S] — so that this Mul distributes over ⨆.

Together these would let you mimic the submodule proof verbatim.
But this combination is very unusual to assume abstractly and is
not packaged in Mathlib's SetLike hierarchy.
-/


lemma aux_mem_iSup_of_mem
  {S : Type*} {ι : Type*} {M : Type*}
  [Ring M] [SetLike S M] [CompleteLattice S] [IsConcreteLE S M]
  {b : M} {p : ι → S} (i : ι) (h : b ∈ p i) :
  b ∈ ⨆ i, p i
  := SetLike.coe_subset_coe.mpr (le_iSup p i) h


namespace SetLike
variable {S ι₁ ι₂ M : Type*} [AddMonoid ι₁] [AddMonoid ι₂] [Ring M]
  [SetLike S M] [CompleteLattice S] [IsConcreteLE S M]
  [AddSubmonoidClass S M]

example (s₁ s₂ : S) (h : s₁ ≤ s₂) : (s₁ : Set M) ⊆  s₂ := by
  exact IsConcreteLE.coe_subset_coe'.mpr h

variable (grad : ι₁ → S) [SetLike.GradedMonoid grad]
variable (f : ι₁ →+ ι₂)

def induced_grad (i : ι₂) : S :=  ⨆ j :  { i₁ : ι₁ // f i₁ = i}, (grad j)  -- this works

instance ind_gm : SetLike.GradedMonoid (induced_grad grad f) where
  one_mem := aux_mem_iSup_of_mem ⟨0, AddMonoidHom.map_zero f⟩ (SetLike.GradedOne.one_mem)
  mul_mem _i _j _p _q hp hq := by
    sorry
end SetLike

end MULTIPLICATIVE
