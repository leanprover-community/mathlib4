/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public meta import Lean.LabelAttribute -- TODO: `registerLabelAttr` should be marked `meta`
public meta import Lean.Meta.Tactic.Simp.Attr
import Lean.LabelAttribute
import Lean.Meta.Tactic.Simp.RegisterCommand
import Mathlib.Init

/-!
# Attributes used in `Mathlib`

In this file we define all `simp`-like and `label`-like attributes used in `Mathlib`. We declare all
of them in one file for two reasons:

- in Lean 4, one cannot use an attribute in the same file where it was declared;
- this way it is easy to see which simp sets contain a given lemma.
-/

public meta section

/-- Simp set for `functor_norm` -/
register_simp_attr functor_norm

-- Porting note:
-- in mathlib3 we declared `monad_norm` using:
--   mk_simp_attribute monad_norm none with functor_norm
-- This syntax is not supported by mathlib4's `register_simp_attr`.
-- See https://github.com/leanprover-community/mathlib4/issues/802
-- TODO: add `@[monad_norm]` to all `@[functor_norm] lemmas

/-- Simp set for `functor_norm` -/
register_simp_attr monad_norm

/-- Simp attribute for lemmas about `Even` -/
register_simp_attr parity_simps

/-- "Simp attribute for lemmas about `RCLike`" -/
register_simp_attr rclike_simps

/-- The simpset `rify_simps` is used by the tactic `rify` to move expressions from `ℕ`, `ℤ`, or
`ℚ` to `ℝ`. -/
register_simp_attr rify_simps

/-- The simpset `qify_simps` is used by the tactic `qify` to move expressions from `ℕ` or `ℤ` to `ℚ`
which gives a well-behaved division. -/
register_simp_attr qify_simps

/-- The simpset `zify_simps` is used by the tactic `zify` to move expressions from `ℕ` to `ℤ`
which gives a well-behaved subtraction. -/
register_simp_attr zify_simps

/--
The simpset `mfld_simps` records several simp lemmas that are
especially useful in manifolds. It is a subset of the whole set of simp lemmas, but it makes it
possible to have quicker proofs (when used with `squeeze_simp` or `simp only`) while retaining
readability.

The typical use case is the following, in a file on manifolds:
If `simp [foo, bar]` is slow, replace it with `squeeze_simp [foo, bar, mfld_simps]` and paste
its output. The list of lemmas should be reasonable (contrary to the output of
`squeeze_simp [foo, bar]` which might contain tens of lemmas), and the outcome should be quick
enough.
-/
register_simp_attr mfld_simps

/-- Simp set for integral rules. -/
register_simp_attr integral_simps

/-- simp set for the manipulation of typevec and arrow expressions -/
register_simp_attr typevec

/-- Simplification rules for ghost equations. -/
register_simp_attr ghost_simps

/-- The `@[nontriviality]` simp set is used by the `nontriviality` tactic to automatically
discharge theorems about the trivial case (where we know `Subsingleton α` and many theorems
in e.g. groups are trivially true). -/
register_simp_attr nontriviality

/-- A stub attribute for `is_poly`. -/
register_label_attr is_poly

/-- A simp set for the `fin_omega` wrapper around `omega`. -/
register_simp_attr fin_omega

/-- A simp set for simplifying expressions involving `⊤` in `enat_to_nat`. -/
register_simp_attr enat_to_nat_top

/-- A simp set for pushing coercions from `ℕ` to `ℕ∞` in `enat_to_nat`. -/
register_simp_attr enat_to_nat_coe

/-- A simp set for the `pnat_to_nat` tactic. -/
register_simp_attr pnat_to_nat_coe

/-- `mon_tauto` is a simp set to prove tautologies about morphisms from some (tensor) power of `M`
to `M`, where `M` is a (commutative) monoid object in a (braided) monoidal category.

**This `simp` set is incompatible with the standard simp set.**
If you want to use it, make sure to add the following to your simp call to disable the problematic
default simp lemmas:
```
-MonoidalCategory.whiskerLeft_id, -MonoidalCategory.id_whiskerRight,
-MonoidalCategory.tensor_comp, -MonoidalCategory.tensor_comp_assoc,
-MonObj.mul_assoc, -MonObj.mul_assoc_assoc
```

The general algorithm it follows is to push the associators `α_` and commutators `β_` inwards until
they cancel against the right sequence of multiplications.

This approach is justified by the fact that a tautology in the language of (commutative) monoid
objects "remembers" how it was proved: Every use of a (commutative) monoid object axiom inserts a
unitor, associator or commutator, and proving a tautology simply amounts to undoing those moves as
prescribed by the presence of unitors, associators and commutators in its expression.

This simp set is opinionated about its normal form, which is why it cannot be used concurrently with
some of the simp lemmas in the standard simp set:
* It eliminates all mentions of whiskers by rewriting them to tensored homs,
  which goes against `whiskerLeft_id` and `id_whiskerRight`:
  `X ◁ f = 𝟙 X ⊗ₘ f`, `f ▷ X = 𝟙 X ⊗ₘ f`.
  This goes against `whiskerLeft_id` and `id_whiskerRight` in the standard simp set.
* It collapses compositions of tensored homs to the tensored hom of the compositions,
  which goes against `tensor_comp`:
  `(f₁ ⊗ₘ g₁) ≫ (f₂ ⊗ₘ g₂) = (f₁ ≫ f₂) ⊗ₘ (g₁ ≫ g₂)`. TODO: Isn't this direction Just Better?
* It cancels the associators against multiplications,
  which goes against `mul_assoc`:
  `(α_ M M M).hom ≫ (𝟙 M ⊗ₘ μ) ≫ μ = (μ ⊗ₘ 𝟙 M) ≫ μ`,
  `(α_ M M M).inv ≫ (μ ⊗ₘ 𝟙 M) ≫ μ = (𝟙 M ⊗ₘ μ) ≫ μ`
* It unfolds non-primitive coherence isomorphisms, like the tensor strengths `tensorμ`, `tensorδ`.
-/
register_simp_attr mon_tauto

/--
`coassoc_simps` is a simp set useful to prove tautologies on coalgebras.

The general algorithm it follows is to push the associators `TensorProduct.assoc` and
commutators `TensorProduct.comm` inwards (to the right) until they cancel against
co-multiplications.

The simp set makes the following choice of normal form
* It regards `TensorProduct.map`, `TensorProduct.assoc`, `TensorProduct.comm` as the primitive
  constructions and rewrites everything else such as `lTensor`, `leftComm` using them.
* It rewrites both sides into a right associated composition of linear maps.
  In particular `LinearMap.comp_assoc` and `LinearEquiv.coe_trans` are tagged.
* It rewrites `(f₂ ⊗ g₂) ∘ (f₁ ⊗ g₁)` into `(f₂ ∘ f₁) ⊗ (g₂ ∘ g₁)`.

## Notes

- It is not confluent with `(ε ⊗ₘ id) ∘ₗ δ = λ⁻¹`.
  It is often useful to `trans` (or `calc`) with a term containing
  `(ε ⊗ₘ _) ∘ₗ δ` or `(_ ⊗ₘ ε) ∘ₗ δ`,
  and use one of `map_counit_comp_comul_left` `map_counit_comp_comul_right`
  `map_counit_comp_comul_left_assoc` `map_counit_comp_comul_right_assoc` to continue.

- Some lemmas (e.g. `lid_comp_map : λ ∘ₗ (f ⊗ₘ g) = g ∘ₗ λ ∘ₗ (f ⊗ₘ id)`) loops when tagged as simp,
  so we wrap it inside a rudimentary simproc that only fires when `g ≠ id`.
-/
register_simp_attr coassoc_simps
