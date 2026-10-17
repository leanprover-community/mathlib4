import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

open NormedSpace ContinuousLinearMap
open scoped Manifold

set_option warn.sorry false
set_option linter.style.longLine false

-- Experiments: localisation arguments in differential geometry
-- in Utrecht (June 10), Christian Merten, Edward van de Meent, Michael Rothgang
-- first file, very rough prototypes

namespace demo

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] {f : M → 𝕜} {g : M → V} {s : Set M} {x : M}

-- ContMDiff.sumElim: give a better proof that
-- ContMDiff is local on an open cover {inl '' M, inr '' N} of M ⊕ N

-- lemma: a property P on morphisms M → N is local on the source iff
-- for all all

variable (I J) in
def IsOpenImmersion (f : M → N) : Prop := sorry

-- TODO: make 𝕜 configurable!

-- science fiction: everything is in Type
-- cannot do this because universes!
-- given two manifolds, models with corners between them and a map, Prop sth

def ManifoldFunctionProperty : Type _ :=
  ∀ {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type _} [TopologicalSpace H] [ChartedSpace H M]
    {M : Type _} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {H' : Type _} [TopologicalSpace H']
    {N : Type _} [TopologicalSpace N] [ChartedSpace H' N]
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F H')
    (f : M → N),
    Prop

#exit
-- morally, P : ∀ M N manifold, (M → N) → Prop


-- In this case (open immersions), things work fine: can restrict to the universe of M
-- in the definition (because in practice, that's all you'll need).
-- i.e., for "P is local on the source", there will be no issue

-- for "this is stable under composition", there would be universe issues
-- To really preserve universe properties, this gets not fun.
-- Several different universe properties with matching universe levels,
-- need to lift...
-- Don't need this in DG as much, but fun_prop instead? Just the local-to-global passage will be annoying.


-- locality on the target... need to pull back. But can do so w.r.t. open immersions.
-- f: M→ N open immersion, W⊆ N open then f⁻¹' W ⊆ M is an open subset, i.e. a manifold


#exit





#exit
structure LocalPropertyOnSource (P : (M → N) → Prop) where
  postcomp (f : M → N) : P f ↔
    ∀ ι : V → M, IsOpenImmersion /-I J-/ ι → P (f ∘ ι)




#check' mfderiv
#check' mfderiv_add
#check' fderiv

#check' fderiv_add

lemma mvfderiv_add {f g : M → 𝕜} {z : M} (hf : MDiffAt f z) (hg : MDiffAt g z) :
    d% (f + g) z = d% f z + d% g z := sorry

-- def. "U ⊆ M is Euclidean" if it is diffeo to some open subset of E

-- step 1: wlog M is Euclidean
-- lemma: md is local, if md_x f = md_x (f.restrict U) for any open U ∋ x ⊆ M

-- choose an open subset U ⊆ E and a diffeo φ from M ≃ U
-- induces an equivalence φ_*: (f: M → ℝ) ≃ (f': U → ℝ)

-- step 2: M = U
-- i.e., replace M by U everywhere in our local context

-- so, the goal becomes about φ_* f, φ_* g and multiplication of these
-- and rewrite by the lemma lemma: md_φ x  (φ_* f) = fd_x f
-- then simp can hopefully chime in :-)

/-
variable {U : Set E} {V : Set M} (hU : IsOpen U) (hV : IsOpen V)

-- def foo (φ : V ≃ U) : (V → ℝ) ≃ (U → ℝ) where

#check Equiv.piCongrLeft
def foo (φ : PartialEquiv V U) : (V → ℝ) ≃ (U → ℝ) where
  toFun f := φ.symm ∘ f
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

-- make a PartialEquiv version of this?

-/

/-
Def. md is *local* if md_x f = md_x (f ∘ ι) for any manifold `V` and smooth open embedding `ι : V → M` (i.e., smooth embedding with open range)

lemma. `V → M` is an open embedding iff it factors as V ≃ W ↪ M, where W is an open subset of M with the induced manifold structure, with a diffeo


open immersion, for any manifold V
is the correct statement of "md is local" ---
  because it is quantifying over open embeddings, not subsets


-/

lemma mvfderiv_add' {f g : M → 𝕜} {z : M} (hf : MDiffAt f z) (hg : MDiffAt g z) :
    d% (f + g) z = d% f z + d% g z := sorry



/- old

-- def. "U ⊆ M is Euclidean" if it is diffeo to some open subset of E

-- step 1: wlog M is Euclidean
-- lemma: md is local, if md_x f = md_x (f.restrict U) for any open U ∋ x ⊆ M

-- choose an open subset U ⊆ E and a diffeo φ from M ≃ U
-- induces an equivalence φ_*: (f: M → ℝ) ≃ (f': U → ℝ)

-- step 2: M = U
-- i.e., replace M by U everywhere in our local context

-- so, the goal becomes about φ_* f, φ_* g and multiplication of these
-- and rewrite by the lemma lemma: md_φ x  (φ_* f) = fd_x f
-- then simp can hopefully chime in :-)

-/





end demo



-- being a manifold is a local property, and every local property is preserved by gluing
