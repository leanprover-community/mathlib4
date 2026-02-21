/-
Copyright (c) 2024 Colva Roney-Dougal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colva Roney-Dougal, Inna Capdeboscq, Susanna Fishel, Kim Morrison,
Spekto\R (2026)
-/
module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Order.Radical
/-
New added 2026,for further theories.
-/
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Sylow

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Order.Atoms.Finite
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type

import Mathlib.Tactic.Group
import Mathlib.Tactic.Abel
import Mathlib.Tactic.order
import Aesop

/-!
# The Frattini subgroup

We give the definition of the Frattini subgroup of a group, and three elementary results:
* The Frattini subgroup is characteristic.
* If every subgroup of a group is contained in a maximal subgroup, then
  the Frattini subgroup consists of the non-generating elements of the group.
* The Frattini subgroup of a finite group is nilpotent.

New contents in 2026 are
* (convenient lemma)A subgroup contained in all maximal subgroup is contained in
  the FRattini subgroup
* A subgroup (say H) has a proper complement (meaning for some proper subgroup K,
  K and H generate the whole group)if and only if it is not contained
  in the Frattini subgroup.
* A group is cyclic iff its Frattini factor(the quotient group wrt Frattini subgroup)
  is cyclic.
* The Frattini factor of a finite p-group is elementary abelian(that is,an abelian
  group G with Gᵖ={1})
* A finite p-group has trivial Frattini subgroup iff the group is elementary abelian.
* Burnside theorem of Frattini factor of finite p-group.
-/


@[expose] public section

set_option backward.isDefEq.respectTransparency false in
/-- The Frattini subgroup of a group is the intersection of the maximal subgroups. -/
def frattini (G : Type*) [Group G] : Subgroup G :=
  Order.radical (Subgroup G)

variable {G H : Type*} [Group G] [Group H] {φ : G →* H}

set_option backward.isDefEq.respectTransparency false in
lemma frattini_le_coatom {K : Subgroup G} (h : IsCoatom K) : frattini G ≤ K :=
  Order.radical_le_coatom h

open Subgroup

set_option backward.isDefEq.respectTransparency false in
lemma frattini_le_comap_frattini_of_surjective (hφ : Function.Surjective φ) :
    frattini G ≤ (frattini H).comap φ := by
  simp_rw [frattini, Order.radical, comap_iInf, le_iInf_iff]
  intro M hM
  apply biInf_le
  exact isCoatom_comap_of_surjective hφ hM

/-- The Frattini subgroup is characteristic. -/
instance frattini_characteristic : (frattini G).Characteristic := by
  rw [characteristic_iff_comap_eq]
  intro φ
  apply φ.comapSubgroup.map_radical

set_option backward.isDefEq.respectTransparency false in
/--
The Frattini subgroup consists of "non-generating" elements in the following sense:

If a subgroup together with the Frattini subgroup generates the whole group,
then the subgroup is already the whole group.
-/
theorem frattini_nongenerating [IsCoatomic (Subgroup G)] {K : Subgroup G}
    (h : K ⊔ frattini G = ⊤) : K = ⊤ :=
  Order.radical_nongenerating h

/-- When `G` is finite, the Frattini subgroup is nilpotent. -/
theorem frattini_nilpotent [Finite G] : Group.IsNilpotent (frattini G) := by
  -- We use the characterisation of nilpotency in terms of all Sylow subgroups being normal.
  have q := (isNilpotent_of_finite_tfae (G := frattini G)).out 0 3
  rw [q]; clear q
  -- Consider each prime `p` and Sylow `p`-subgroup `P` of `frattini G`.
  intro p p_prime P
  -- The Frattini argument shows that the normalizer of `P` in `G`
  -- together with `frattini G` generates `G`.
  have frattini_argument := Sylow.normalizer_sup_eq_top P
  -- and hence by the nongenerating property of the Frattini subgroup that
  -- the normalizer of `P` in `G` is `G`.
  have normalizer_P := frattini_nongenerating frattini_argument
  -- This means that `P` is normal as a subgroup of `G`
  have P_normal_in_G : (map (frattini G).subtype P).Normal := normalizer_eq_top_iff.mp normalizer_P
  -- and hence also as a subgroup of `frattini G`, which was the remaining goal.
  exact P_normal_in_G.of_map_subtype

/-
Added 2026.
-/

/--
According to the definition, a subgroup that is less than or equal to all coatoms
is less than or equal to the Frattini subgroup.
-/
theorem le_frattini_of_le_Coatom {G : Type*} [Group G]
(H : Subgroup G)
(hle : ∀ K : Subgroup G, IsCoatom K → H ≤ K) :
    H ≤ frattini G := by
  -- Track the definition of the Frattini subgroup
  have : frattini G = Order.radical (Subgroup G) := by rfl
  rw[this]
  have :Order.radical (Subgroup G)
  = ⨅ a ∈ {H : Subgroup G | IsCoatom H}, a := by rfl
  rw[this]
  -- From aesop?
  simp_all only [Set.mem_setOf_eq, le_iInf_iff, implies_true]

/--
Theorem: A subgroup has a proper complement if and only if it is not contained
in the Frattini subgroup (we assume that every proper subgroup is contained
in a maximal subgroup, without invoking the Axiom of Choice).
-/
theorem partial_complement_exists_iff_notin_frattini {G : Type*}
 [Group G] (H : Subgroup G) [IsCoatomic (Subgroup G)] :
    (∃ K : Subgroup G, (H ⊔ K = ⊤) ∧ (K < ⊤)) ↔ ¬(H ≤ frattini G)
     := by
  constructor
  · -- Left to right: if H ≤ frattini G, H ⊔ K = ⊤ implies frattini G ⊔ K = ⊤.
    -- Then by the non-generating property of the Frattini subgroup,
    -- K = ⊤, contradiction.
    intro h_exists
    rcases h_exists with ⟨K, h_sup, h_lt⟩
    by_contra h_le
    have gen : K ⊔ frattini G = ⊤ := by
      order
    have : K = ⊤ := by
      exact frattini_nongenerating gen
    order
  · -- Right to left: if H is not contained in frattini G, then there exists a
    -- maximal subgroup L such that H is not contained in L.
    -- Then by maximality, H ⊔ L = ⊤.
    intro h_not_le
    by_contra
    have a_fact : ∃ L : Subgroup G, (IsCoatom L) ∧ (¬(H ≤ L)) := by
      by_contra h_contra
      push_neg at h_contra
      have : H ≤ frattini G := by
        exact le_frattini_of_le_Coatom H h_contra
      contradiction
    rcases a_fact with ⟨L, h_coatom, h_not_le⟩
    have supeq : H ⊔ L = ⊤ := by
      rw[←IsCoatom.lt_iff h_coatom]
      order
    have : L < ⊤ := by
      exact IsCoatom.lt_top h_coatom
    have : ∃ K : Subgroup G, (H ⊔ K = ⊤) ∧ (K < ⊤) := by
      use L
    contradiction

-- Corollary: If the Frattini factor is cyclic, then the original group is also cyclic.
theorem cyclic_of_frattini_factor_cyclic {G : Type*} [Group G]
[IsCoatomic (Subgroup G)] :
    IsCyclic (G ⧸ frattini G) → IsCyclic (G) := by
  intro h_cyclic
  -- Take the generator x of the quotient group and its preimage g.
  rcases h_cyclic with ⟨x, hx⟩
  have : ∃ g : G, QuotientGroup.mk' (frattini G) g = x := by
    apply QuotientGroup.mk'_surjective
  rcases this with ⟨g, hg⟩
  -- Prove that the subgroup K generated by g and the Frattini subgroup generate G.
  let K := Subgroup.closure ({g} : Set G)
  have : K ⊔ frattini G = ⊤ := by
    ext y
    constructor
    · intro hy
      trivial
    · intro hy
      -- First project to the quotient group; the image of y is a power of x.
      obtain ⟨n, hn⟩ := hx (QuotientGroup.mk' (frattini G) y)
      have : QuotientGroup.mk' (frattini G) y = x^n := by
        rw[←hn]
      -- Rewrite the expression as yg⁻ⁿ ∈ frattini G.
      have : QuotientGroup.mk' ( frattini G) (y * g^(-n)) = 1 := by
        calc
          QuotientGroup.mk' (frattini G) (y * g^(-n))
          = QuotientGroup.mk' (frattini G) y
          * QuotientGroup.mk' (frattini G) g^(-n) := by rfl
          _ = (x^n)*((QuotientGroup.mk' (frattini G) g)^(-n)) := by
            rw[this]
          _ = (x^n)*((x)^(-n)) := by rw[hg]
          _ = 1 := by group
      -- Thus yg⁻ⁿ ∈ frattini ≤ K ⊔ frattini G.
      have : y * g^(-n) ∈ frattini G := by
        rw [← QuotientGroup.ker_mk' (frattini G), MonoidHom.mem_ker]
        exact this
      have in1: y * g^(-n) ∈ K ⊔ (frattini G) := by
        have le : (frattini G) ≤ K ⊔ (frattini G) := by
          apply le_sup_right
        apply le
        exact this
      -- Also g^n ∈ K ≤ K ⊔ frattini G.
      have : g^n ∈ K := by
        rw [Subgroup.mem_closure_singleton]
        use n
      have in2: g^n ∈ K ⊔ (frattini G) := by
        have le : K ≤ K ⊔ (frattini G) := by
          apply le_sup_left
        apply le
        exact this
      -- Therefore y ∈ K ⊔ frattini G.
      have : y = (y * g^(-n)) * g^n := by group
      rw[this]
      exact Subgroup.mul_mem _ in1 in2
  -- By the non-generating property of the Frattini subgroup, K = ⊤, so G is cyclic.
  have : K = ⊤ := by
    exact frattini_nongenerating this
  -- Finished.
  have : ⊤ = Subgroup.closure ({g} : Set G) := by
    rw[←this]
  -- Some fluff at the end to connect 'this' to the definition of IsCyclic.
  refine ⟨g, ?_⟩
  intro y
  have hy : y ∈ Subgroup.closure ({g} : Set G) := by
    rw[←this]
    trivial
  rw [Subgroup.mem_closure_singleton] at hy
  exact hy

-- Theorem: (Finite) p-group → Nilpotent group → Normalizer condition
-- → Coatom is a normal subgroup.
-- This just requires finding the interface.
theorem normal_of_Coatom_PGroup {P : Type*} [Group P] [Finite P]
  {p : ℕ} [hp : Fact (Nat.Prime p)]
  (hP : IsPGroup p P) (H : Subgroup P)
  (hMax : IsCoatom H) : H.Normal := by
  -- Register nilpotent group instance.
  haveI : Group.IsNilpotent P := IsPGroup.isNilpotent hP
  -- Get the normalizer condition.
  have hNC : NormalizerCondition P := normalizerCondition_of_isNilpotent
  -- Prove that the Coatom is normal using the normalizer condition.
  exact Subgroup.NormalizerCondition.normal_of_coatom H hNC hMax

-- Theorem: Coatoms of finite p-groups have index p.
theorem index_of_Coatom_PGroup {P : Type*} [Group P] [Finite P]
  {p : ℕ} [hp : Fact (Nat.Prime p)]
  (hP : IsPGroup p P) (H : Subgroup P)
  (hMax : IsCoatom H) : H.index = p := by
  -- Register the normal subgroup instance to take the quotient group.
  have h_normal : H.Normal := normal_of_Coatom_PGroup hP H hMax
  haveI := h_normal
  -- The order of the quotient group divides the order of P = power of p,
  -- and the quotient group is non-trivial; hence, the order is divisible by p.
  have Porder : ∃ (n : ℕ), Nat.card P = p ^ n := by
    rw [← IsPGroup.iff_card]
    exact hP
  rcases Porder with ⟨n, Porder'⟩
  have pdv: p ∣ Nat.card (P ⧸ H) := by
    have div:Nat.card (P ⧸ H) ∣ Nat.card P := by
      exact Subgroup.card_quotient_dvd_card H
    rw [Porder'] at div
    have nont: Nat.card (P ⧸ H)>1 := by
      have : H < ⊤ := IsCoatom.lt_top hMax
      have : H ≠ ⊤ := by
        exact ne_of_lt this
      have : 1< H.index := Subgroup.one_lt_index_of_ne_top this
      rw[Subgroup.index_eq_card H] at this
      exact this
    rw[Nat.dvd_prime_pow hp.out] at div
    rcases div with ⟨k, hk1,hk2⟩
    rw[hk2]
    have ntv:k≠0 := by
      by_contra h_contra
      have : Nat.card (P ⧸ H) = 1 := by
        rw[hk2,h_contra,pow_zero]
      rw[this] at nont
      contradiction
    exact dvd_pow_self p ntv
  -- Use Sylow's theorem on the quotient group; use p = p^1 for the interface.
  have :p = p ^ 1 := by rw [pow_one]
  rw[this] at pdv
  have : ∃ X : Subgroup (P ⧸ H), Nat.card X = p^1
  := Sylow.exists_subgroup_card_pow_prime p pdv
  rcases this with ⟨X, hX⟩
  rw[←this] at hX
  let Q := X.comap (QuotientGroup.mk' H)
  -- Next, by the correspondence theorem, |Q/H| = |X| = p.
  -- First, prove Q/H = X.
  have : Subgroup.map (QuotientGroup.mk' H)
   (Subgroup.comap (QuotientGroup.mk' H) X) = X := by
    exact Subgroup.map_comap_eq_self_of_surjective
     (QuotientGroup.mk'_surjective H) X
  have : Subgroup.map (QuotientGroup.mk' H)
   (Q) = X := by
    rw[←this]
  -- Call the theorem stating that the relative index of ker(π) in Q equals |f(Q)|.
  have equation: (QuotientGroup.mk' H).ker.relIndex Q
  = Nat.card ↥(Subgroup.map (QuotientGroup.mk' H) Q) := by
    exact Subgroup.relIndex_ker Q (QuotientGroup.mk' H)
  rw[this,hX] at equation
  have ker_eq: (QuotientGroup.mk' H).ker = H := by
    rw [QuotientGroup.ker_mk' H]
  rw[ker_eq] at equation
  -- At this point, it has been rewritten as the relative index of H in Q being p.
  have neone : p ≠ 1 := by
    exact Nat.Prime.ne_one hp.out
  rw[←equation] at neone
  -- Thus Q cannot be ≤ H.
  have consequence: ¬(Q≤ H) := by
    by_contra
    rw[← Subgroup.relIndex_eq_one] at this
    contradiction
  -- Also H ≤ Q.
  have but: H ≤ Q := by
    rw[← (QuotientGroup.ker_mk' H)]
    exact Subgroup.ker_le_comap (QuotientGroup.mk' H) X
  have :H<Q := by order
  -- By maximality Q = ⊤, so the index of H is p.
  rw[IsCoatom.lt_iff hMax] at this
  rw[this] at equation
  rw[← Subgroup.relIndex_top_right H]
  exact equation

-- Theorem: The Frattini factor of a p-group is elementary abelian.
theorem frattini_factor_elementary_abelian_of_PGroup
{P : Type*} [Group P] [Finite P]
{p : ℕ} [hp : Fact (Nat.Prime p)]
(hP : IsPGroup p P) :
    (∀ g : (P ⧸ frattini P), g ^ p = 1)∧
     (IsMulCommutative (P ⧸ frattini P)) := by
  -- Get the coatomic property first.
  haveI : IsCoatomic (Subgroup P) := Finite.to_isCoatomic
  constructor
  · intro g
    -- Take the preimage.
    have : ∃ g' : P, QuotientGroup.mk' (frattini P) g' = g := by
      apply QuotientGroup.mk'_surjective
    rcases this with ⟨g', hg'⟩
    -- Next, prove g'^p ∈ frattini P.
    -- To do this, first prove g'^p is in all coatoms.
    have critical: ∀ K : Subgroup P, IsCoatom K → g'^p ∈ K := by
      intro K hK
      -- Thus K is a normal subgroup of index p.
      haveI : K.Normal := normal_of_Coatom_PGroup hP K hK
      have indexeqp: K.index = p := index_of_Coatom_PGroup hP K hK
      rw[← QuotientGroup.ker_mk' K]
      rw[MonoidHom.mem_ker]
      have : QuotientGroup.mk' K (g'^p) = (QuotientGroup.mk' K g')^p := by rfl
      rw[this]
        -- The order of the quotient group = p.
      have : Nat.card (P ⧸ K) = p := by
        rw[← Subgroup.index_eq_card K]
        exact indexeqp
      rw[← this]
      exact pow_card_eq_one'
    -- From this, prove g'^p ∈ frattini P.
    have theend: g'^p ∈ frattini P := by
      -- Rewrite the definition; Gemini find the interface.
      have : frattini P = Order.radical (Subgroup P) := by rfl
      rw[this]
      have :Order.radical (Subgroup P)
       = ⨅ a ∈ {H : Subgroup P | IsCoatom H}, a := by rfl
      rw[this]
      simp_rw[Subgroup.mem_iInf]
      exact critical
    -- The image of g^p is g'^p; thus, finish.
    have : QuotientGroup.mk' (frattini P) (g'^p)
    = (QuotientGroup.mk' (frattini P) g')^p := by rfl
    rw[hg'] at this
    rw[← this,← MonoidHom.mem_ker, QuotientGroup.ker_mk' (frattini P)]
    exact theend
  · constructor
    constructor
    intro g h
    -- Follow the same process as above.
    -- Take the preimage.
    have : ∃ g' : P, QuotientGroup.mk' (frattini P) g' = g := by
      apply QuotientGroup.mk'_surjective
    rcases this with ⟨g', hg'⟩
    -- Take the preimage.
    have : ∃ g' : P, QuotientGroup.mk' (frattini P) g' = g := by
      apply QuotientGroup.mk'_surjective
    rcases this with ⟨g', hg'⟩
    have : ∃ h' : P, QuotientGroup.mk' (frattini P) h' = h := by
      apply QuotientGroup.mk'_surjective
    rcases this with ⟨h', hh'⟩
    -- Next, prove g'h'(g')⁻¹(h')⁻¹ ∈ frattini P.
    -- To do this, first prove g'h'(g')⁻¹(h')⁻¹ is in all coatoms.
    have critical2: ∀ K : Subgroup P, IsCoatom K →
     g'*h'*(g')⁻¹*(h')⁻¹ ∈ K := by
      intro K hK
      -- Thus K is a normal subgroup of index p.
      haveI : K.Normal := normal_of_Coatom_PGroup hP K hK
      have indexeqp: K.index = p := index_of_Coatom_PGroup hP K hK
      rw[← QuotientGroup.ker_mk' K]
      rw[MonoidHom.mem_ker]
      have : QuotientGroup.mk' K (g'*h'*(g')⁻¹*(h')⁻¹)
      = (QuotientGroup.mk' K g')*(QuotientGroup.mk' K h')
       *(QuotientGroup.mk' K g')⁻¹*(QuotientGroup.mk' K h')⁻¹ := by rfl
      rw[this]
        -- The order of the quotient group = p.
      have : Nat.card (P ⧸ K) = p := by
        rw[← Subgroup.index_eq_card K]
        exact indexeqp
      have : IsCyclic (P ⧸ K) := isCyclic_of_prime_card this
      have : Std.Commutative fun (x1 x2 : (P ⧸ K)) => x1 * x2 :=
        IsCyclic.commutative
      rcases this with ⟨comm⟩
      have :
        (QuotientGroup.mk' K h')
         *(QuotientGroup.mk' K g')⁻¹
         = (QuotientGroup.mk' K g')⁻¹
          *(QuotientGroup.mk' K h') := by
           rw[comm]
      calc
         (QuotientGroup.mk' K g')*(QuotientGroup.mk' K h')
         *(QuotientGroup.mk' K g')⁻¹*(QuotientGroup.mk' K h')⁻¹
        _ = (QuotientGroup.mk' K g')*((QuotientGroup.mk' K h')
         *(QuotientGroup.mk' K g')⁻¹)*(QuotientGroup.mk' K h')⁻¹ := by group
        _ = (QuotientGroup.mk' K g')*((QuotientGroup.mk' K g')⁻¹
         *(QuotientGroup.mk' K h'))*(QuotientGroup.mk' K h')⁻¹ := by rw[this]
        _ = 1 := by group
    -- Thus g'h'(g')⁻¹(h')⁻¹ falls into frattini P.
    have theend2: g'*h'*(g')⁻¹*(h')⁻¹ ∈ frattini P := by
      -- Rewrite the definition; Gemini find the interface.
      have : frattini P = Order.radical (Subgroup P) := by rfl
      rw[this]
      have :Order.radical (Subgroup P)
       = ⨅ a ∈ {H : Subgroup P | IsCoatom H}, a := by rfl
      rw[this]
      simp_rw[Subgroup.mem_iInf]
      exact critical2
    -- The image of g'h'(g')⁻¹(h')⁻¹ is 1; thus, finish.
    rw[← QuotientGroup.ker_mk' (frattini P),MonoidHom.mem_ker] at theend2
    have : QuotientGroup.mk' (frattini P) (g'*h'*(g')⁻¹*(h')⁻¹)
      = (QuotientGroup.mk' (frattini P) g')
       *(QuotientGroup.mk' (frattini P) h')
       *(QuotientGroup.mk' (frattini P) g')⁻¹
       *(QuotientGroup.mk' (frattini P) h')⁻¹ := by rfl
    rw[this,hg',hh'] at theend2
    calc
      g*h
       = (g*h*g⁻¹*h⁻¹)*(h * g) := by group
      _ = 1*(h*g) := by rw[theend2]
      _ = h*g := by rw[one_mul]

-- Auxiliary Lemma: For a non-zero element x in a finite ZMod p-module,
-- there exists a coatom H not containing x.
lemma exist_coatom_of_nonzero_element
{P : Type*} {p : ℕ} [AddCommGroup P] [Module (ZMod p) P] [Finite P]
 [hp : Fact (Nat.Prime p)] :
(∀ x : P,x ≠ 0 →
 (∃ H : (Submodule (ZMod p) P),(IsCoatom H)∧(x ∉ H))) := by
  intro x xnezero
  -- K=⟨x⟩
  let K := Submodule.span (ZMod p) {x}
  have xinK : x ∈ K := Submodule.mem_span_singleton_self x
  -- Use the complement theorem to obtain the complement space M of K.
  obtain ⟨M, h_compl⟩ := Submodule.exists_isCompl K
  use M
  constructor
  · -- Prove M is a coatom.
    constructor
    · -- Prove M ≠ ⊤.
      by_contra
      rw[this] at h_compl
      have infeq : K ⊓ ⊤ = ⊥ := h_compl.inf_eq_bot
      have : K ⊓ ⊤ = K := by order
      rw[this] at infeq
      rw[infeq] at xinK
      rw[Submodule.mem_bot] at xinK
      contradiction
    · -- Prove the maximality of M.
      -- Assume M < N; need to prove N = ⊤.
      intro N h_lt
      have h_le:M ≤ N := le_of_lt h_lt
      have h_nle:¬(N≤M) := by order
      rw[SetLike.le_def] at h_nle
      push_neg at h_nle
      -- Take y ∈ N, y ∉ M.
      rcases h_nle with ⟨y,hy⟩
      rcases hy with ⟨hy1,hy2⟩
      have h_sup : K ⊔ M = ⊤ := h_compl.sup_eq_top
      have h_mem : y ∈ K ⊔ M := by rw [h_sup]; exact Submodule.mem_top
      -- y = a + b, a ∈ K, b ∈ M ⊆ N, so a ∈ N; also y ∉ M implies a ≠ 0.
      rcases Submodule.mem_sup.mp h_mem with ⟨a, ha, b, hb, yeqapb⟩
      have hb':b ∈ N := by
        rw[SetLike.le_def] at h_le
        exact h_le hb
      have :a=y-b := by rw[←yeqapb];abel
      have ainN: a ∈ N := by rw[this];exact N.sub_mem hy1 hb'
      have anez: a≠ 0:= by
        by_contra
        rw[this,zero_add] at yeqapb
        rw[yeqapb] at hb
        contradiction
      -- A non-zero 'a' in N naturally generates the entire K.
      rw[Submodule.mem_span_singleton] at ha
      rcases ha with ⟨r,hr⟩
      have : r ≠ 0 := by
        by_contra
        rw[this] at hr
        apply anez
        rw[←hr]
        exact Module.zero_smul x
      have : x = r⁻¹ • a := by
        rw[← hr]
        rw[← mul_smul (r⁻¹) r x]
        rw[inv_mul_cancel₀ this]
        rw[one_smul]
      have: x∈ N := by rw[this];exact N.smul_mem (r⁻¹) ainN
      have: K ≤ N := by rw[Submodule.span_singleton_le_iff_mem x N];exact this
      order
  · intro hxM
    have hxK : x ∈ K := Submodule.mem_span_singleton_self x
    obtain ⟨h_disj, _⟩ := h_compl
    have h_zero : x = 0 := Submodule.disjoint_def.mp h_disj x hxK hxM
    exact xnezero h_zero


-- Theorem: The Frattini subgroup of a p-group is trivial if and only if
-- the original group is elementary abelian.
theorem frattini_eq_bot_iff_elementary_abelian_of_PGroup
{P : Type*} [Group P] [Finite P]
{p : ℕ} [hp : Fact (Nat.Prime p)]
(hP : IsPGroup p P) :
    frattini P = ⊥ ↔ ((∀ g : P, g ^ p = 1)∧(IsMulCommutative P)) := by
  constructor
  · intro h_frattini_bot
    rcases frattini_factor_elementary_abelian_of_PGroup
       hP with ⟨ele,ab⟩
    constructor
    · intro g
      have usingtheorem : (QuotientGroup.mk' (frattini P) g)^p=1 := by
        exact ele g
      have :(QuotientGroup.mk' (frattini P) g)^p
      = QuotientGroup.mk' (frattini P) (g^p) := by rfl
      rw[this] at usingtheorem
      rw[← MonoidHom.mem_ker,QuotientGroup.ker_mk' (frattini P)
      ,h_frattini_bot]
      at usingtheorem
      rw[Subgroup.mem_bot] at usingtheorem
      exact usingtheorem
    · constructor
      constructor
      intro a b
      -- For commutativity, follow the approach used previously.
      let a' := (QuotientGroup.mk' (frattini P) a)
      let b' := (QuotientGroup.mk' (frattini P) b)
      have usingtheorem' :
       a'*b'
       = b'*a'
       := ab.is_comm.comm a' b'
      have : a'*b'*a'⁻¹*b'⁻¹=1 := by
        rw[usingtheorem']
        group
      have muleq : (QuotientGroup.mk' (frattini P) (a*b*a⁻¹*b⁻¹))
       = a'*b'*a'⁻¹*b'⁻¹ := by rfl
      have : (QuotientGroup.mk' (frattini P) (a*b*a⁻¹*b⁻¹))=1 := by
        rw[muleq]
        exact this
      rw[← MonoidHom.mem_ker, QuotientGroup.ker_mk' (frattini P),
       h_frattini_bot,Subgroup.mem_bot] at this
      calc
        a*b = (a*b*a⁻¹*b⁻¹)*b*a := by group
        _ = 1*b*a := by rw[this]
        _ = b*a := by group
  · rintro ⟨h_exp, h_comm⟩
    -- Reduce to proving that for any g ≠ 1, g ∉ frattini P.
    rw [eq_bot_iff]
    rw[SetLike.le_def]
    intro g h_g_fra
    rw[Subgroup.mem_bot]
    by_contra h_g_ne_one
    -- (1) Obtain the ZMod p-module structure.
    -- Utilize commutativity to upgrade P to CommGroup.
    letI : CommGroup P :=
     { ‹Group P› with mul_comm := h_comm.is_comm.comm }
    let A := Additive P
    -- pA = 0 ← Pᵖ = e.
    have h_nsmul : ∀ x : A, p • x = 0 := by
      intro x
      exact h_exp (Additive.toMul x)
    -- Obtain the ZMod p-module structure using AddCommGroup.zmodModule.
    -- According to Gemini's suggestion, the explicit parameter n := p was added here,
    -- which mysteriously solved a seemingly unrelated issue later on.
    letI := AddCommGroup.zmodModule (n := p) h_nsmul
    -- (2) Corresponding x ≠ 0 in the module structure for g.
    let x : A := Additive.ofMul g
    have h_x_ne_zero : x ≠ 0 := by
      intro h
      apply h_g_ne_one
      exact (Equiv.apply_eq_iff_eq Additive.ofMul).mp h
    -- (3) According to the auxiliary lemma, obtain a coatom H_mod not containing x.
    -- Note: explicitly specify the variable p, otherwise inference will fail.
    obtain ⟨H_mod, h_coatom_H_mod, h_x_not_in_H⟩ :=
     exist_coatom_of_nonzero_element (p := p) x h_x_ne_zero
    -- Convert the maximal submodule H_mod of the ZMod p-module to a multiplicative
    -- subgroup H_sub of P.
    let H_sub : Subgroup P := H_mod.toAddSubgroup.toSubgroup
    -- Prove the corresponding coatom.
    have h_coatom_H_sub : IsCoatom H_sub := by
      -- Expand the equivalent definition of IsCoatom: not the entire ⊤ and
      -- has no proper super-subgroups.
      constructor
      · -- Prove H_sub ≠ ⊤.
        intro h_top
        apply h_coatom_H_mod.ne_top
        -- If the subgroup is the entire set, then the submodule must also be
        -- the entire set.
        ext x
        constructor
        · intro _
          exact Submodule.mem_top
        · intro
          have h_mem : Additive.toMul x ∈ H_sub := by
            rw [h_top]
            exact Subgroup.mem_top (Additive.toMul x)
          exact h_mem
      · -- Prove maximality: if there is a subgroup K such that H_sub < K, then K = ⊤.
        intro K h_lt
        -- A subgroup K larger than H_sub is also a ZMod p-submodule K_mod.
        let K_mod : Submodule (ZMod p) A := {
          carrier := K.toAddSubgroup.carrier
          add_mem' := K.toAddSubgroup.add_mem'
          zero_mem' := K.toAddSubgroup.zero_mem'
          smul_mem' := by
            -- Going from a subgroup to a ZMod p-submodule is algebraically
            -- not completely trivial.
            intro c y hy
            -- To prove that y in some submodule implies c • y is in that
            -- submodule, first lift c to z ∈ ℤ.
            obtain ⟨z, rfl⟩ := ZMod.intCast_surjective c
            -- c • y = [z] • y = z • y.
            have h_smul_eq : (z : ZMod p) • y = z • y :=
              Int.cast_smul_eq_zsmul (ZMod p) z y
            rw [h_smul_eq]
            -- Subgroups are naturally closed under integer scalar multiplication (zsmul).
            exact AddSubgroup.zsmul_mem K.toAddSubgroup hy z
        }
        -- Strictly increasing relationship persists at the submodule level.
        have h_mod_lt : H_mod < K_mod := h_lt
        -- Using the maximality of H_mod as a submodule, conclude that
        -- K_mod must be the entire set ⊤.
        rcases h_coatom_H_mod with ⟨_,h_H_mod2⟩
        have K_mod_eq_top: K_mod = ⊤
         := h_H_mod2 K_mod h_mod_lt
        -- Return to K = ⊤.
        apply le_antisymm
        · exact le_top
        · rw[SetLike.le_def]
          intro g _
          have hg : Additive.ofMul g ∈ K_mod := by
            rw [K_mod_eq_top]
            exact AddSubgroup.mem_top (Additive.ofMul g)
          exact hg
    -- (4) Finish.
    have h_g_in_H_sub : g ∈ H_sub := by
      have :frattini P≤ H_sub := frattini_le_coatom h_coatom_H_sub
      apply this
      exact h_g_fra
    -- g ∈ H_sub is equivalent to x ∈ H_mod.
    have h_x_in_H_mod : x ∈ H_mod := by
      -- Gemini: Force Lean to expand the 'let' definitions of subgroups
      -- and elements at the kernel level to recognize they are the same set.
      change x ∈ H_mod at h_g_in_H_sub
      exact h_g_in_H_sub
    exact h_x_not_in_H h_x_in_H_mod

/--
The next theorem (Burnside theorem) proof is given by copilot Claude Opus 4.6.
-/
-- Auxiliary lemma: ψ^n also induces the identity map on the Frattini factor.
lemma MulAut_pow_trivial_on_frattini_factor
    {P : Type*} [Group P] (ψ : MulAut P)
    (h_id_induced : ∀ x : P, QuotientGroup.mk (s := frattini P) (ψ x)
      = QuotientGroup.mk (s := frattini P) x)
    (n : ℕ) :
    ∀ x : P, QuotientGroup.mk (s := frattini P) ((ψ ^ n) x)
      = QuotientGroup.mk (s := frattini P) x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; aesop

-- Auxiliary lemma: Fixed points of an automorphism form a subgroup.
def MulAut.fixedSubgroup {G : Type*} [Group G] (φ : MulAut G) : Subgroup G where
  carrier := {x : G | φ x = x}
  one_mem' := by simp
  mul_mem' := by aesop
  inv_mem' := by aesop

-- Auxiliary lemma: A q-order automorphism has a fixed point in a p^k size coset
-- (where q ≠ p are primes).
lemma exists_fixed_point_in_coset
    {P : Type*} [Group P] [Finite P] {p q : ℕ}
    [hp : Fact (Nat.Prime p)] [hq : Fact (Nat.Prime q)]
    (hP : IsPGroup p P) (hpq : p ≠ q)
    (b : MulAut P) (hb_order : orderOf b = q)
    (hb_triv : ∀ x : P, QuotientGroup.mk (s := frattini P) (b x)
      = QuotientGroup.mk (s := frattini P) x)
    (y : P ⧸ frattini P) :
    ∃ x : P, b x = x ∧ QuotientGroup.mk (s := frattini P) x = y := by
  obtain ⟨g, hg⟩ := Quotient.exists_rep y
  let Fiber := {x : P // QuotientGroup.mk (s := frattini P) x = y}
  -- b preserves the fiber.
  have h_b_preserves : ∀ x : Fiber, QuotientGroup.mk (s := frattini P) (b x.val) = y :=
    fun ⟨x, hx⟩ => by rw [hb_triv x, hx]
  let b_action : Fiber → Fiber := fun ⟨x, hx⟩ => ⟨b x, h_b_preserves ⟨x, hx⟩⟩
  -- Fiber ≃ frattini P, so |Fiber| = p^k.
  haveI : Finite (frattini P) := Subgroup.instFiniteSubtypeMem (frattini P)
  have h_equiv : Fiber ≃ (frattini P) := by
    refine {
      toFun := fun ⟨x, hx⟩ => ⟨g⁻¹ * x, ?_⟩
      invFun := fun ⟨f, hf⟩ => ⟨g * f, ?_⟩
      left_inv := fun ⟨x, hx⟩ => by group
      right_inv := fun ⟨f, hf⟩ => by group
    }
    · rw [← QuotientGroup.eq]; aesop
    · rw [← hg]; change ⟦g * f⟧ = ⟦g⟧; rw [QuotientGroup.eq]; simpa
  haveI : Finite Fiber := Finite.of_equiv _ h_equiv.symm
  have h_fiber_card : ∃ k : ℕ, Nat.card Fiber = p ^ k := by
    rw [Nat.card_congr h_equiv]
    exact (IsPGroup.iff_card (p := p)).mp (IsPGroup.to_subgroup hP (frattini P))
  have h_b_pow_iter : ∀ n : ℕ, ∀ x : Fiber,
      QuotientGroup.mk (s := frattini P) ((b ^ n) x.val) = y :=
    fun n ⟨x, hx⟩ => by rw [MulAut_pow_trivial_on_frattini_factor b hb_triv n x, hx]
  obtain ⟨k, hk⟩ := h_fiber_card
  -- q ∤ p^k.
  have h_not_dvd : ¬ (q ∣ Nat.card Fiber) := by
    rw [hk]; intro h_dvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).mp
      (Nat.Prime.dvd_of_dvd_pow hq.out h_dvd)).symm
  -- Proof by contradiction: assume no fixed points; then all orbit sizes are q,
  -- so q | |Fiber|, contradiction.
  by_contra! h_no_fixed
  have h_no_fixed' : ∀ x : Fiber, b x.val ≠ x.val :=
    fun ⟨x, hx⟩ h_eq => h_no_fixed x h_eq hx
  let b_perm : Equiv.Perm Fiber := {
    toFun := b_action
    invFun := fun ⟨x, hx⟩ => ⟨b⁻¹ x, by rw [← hb_triv (b⁻¹ x), MulAut.apply_inv_self, hx]⟩
    left_inv := by intro ⟨x, hx⟩; aesop
    right_inv := by intro ⟨x, hx⟩; aesop
  }
  have h_bperm_pow_q : b_perm ^ q = 1 := by
    ext ⟨x, hx⟩
    simp only [Equiv.Perm.coe_one, id_eq, Equiv.Perm.coe_pow]
    have h_iter : ∀ n : ℕ, (b_perm^[n]) ⟨x, hx⟩ = ⟨(b^n) x, h_b_pow_iter n ⟨x, hx⟩⟩ := by
      intro n; induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ', Function.comp_apply, ih]
        simp [b_perm, b_action, pow_succ']
    rw [h_iter q]; simp [← hb_order]
  -- Fixed point counting: |Fiber| ≡ 0 [MOD q], contradiction.
  haveI : Fintype Fiber := Fintype.ofFinite Fiber
  haveI : Fintype (Function.fixedPoints b_perm) :=
    Set.Finite.fintype (Set.Finite.subset (Set.toFinite _) (Set.subset_univ _))
  have h_fixed_eq_zero : Fintype.card (Function.fixedPoints b_perm) = 0 :=
    Fintype.card_eq_zero_iff.mpr ⟨fun ⟨x, hx⟩ => h_no_fixed' x (congr_arg Subtype.val hx)⟩
  have h_mod : Fintype.card Fiber ≡ Fintype.card (Function.fixedPoints b_perm) [MOD q] := by
    classical
    let f : Function.End Fiber := ⇑b_perm
    have hf : f ^ (q ^ 1) = 1 := by
      rw [pow_one]; funext x
      have : (b_perm ^ q) x = x := by rw [h_bperm_pow_q]; rfl
      exact this
    convert Equiv.Perm.card_fixedPoints_modEq hf
  rw [h_fixed_eq_zero, Nat.modEq_zero_iff_dvd] at h_mod
  exact h_not_dvd (by rwa [Nat.card_eq_fintype_card])

/--
Burnside's Theorem: If a p'-automorphism of a p-group induces the identity map
on the Frattini factor, then it is the identity map.
By definition, a p'-automorphism is an automorphism whose order
is coprime to p.
-/
theorem PGroup_p'automorphism_id_of_id_on_frattini_factor
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact (Nat.Prime p)]
    (hP : IsPGroup p P) (ψ : MulAut P) (h_order : (orderOf ψ).Coprime p)
    (h_id_induced : ∀ x : P, QuotientGroup.mk (s := frattini P) (ψ x)
    = QuotientGroup.mk (s := frattini P) x) :
    ψ = 1 := by
  -- Proof by contradiction: assume ψ ≠ 1.
  by_contra h_ne
  have h_ord_pos : 0 < orderOf ψ := orderOf_pos ψ
  have h_ord_ne_one : orderOf ψ ≠ 1 := mt orderOf_eq_one_iff.mp h_ne
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd h_ord_ne_one
  have hq_ne_p : q ≠ p := by
    intro h_eq; rw [h_eq] at hq_dvd
    exact absurd h_order (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp.out, hq_dvd, dvd_refl p⟩)
  set m := orderOf ψ / q with hm_def
  have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd h_ord_pos hq_dvd) hq_prime.pos
  have h_ord_eq : orderOf ψ = q * m := by rw [hm_def, Nat.mul_div_cancel' hq_dvd]
  set b := ψ ^ m with hb_def
  have hb_order : orderOf b = q := by
    rw [hb_def, orderOf_pow ψ, h_ord_eq]; simp [Nat.mul_div_left q hm_pos]
  haveI : Fact (Nat.Prime q) := ⟨hq_prime⟩
  have hb_triv : ∀ x : P, QuotientGroup.mk (s := frattini P) (b x)
      = QuotientGroup.mk (s := frattini P) x :=
    MulAut_pow_trivial_on_frattini_factor ψ h_id_induced m
  let C := MulAut.fixedSubgroup b
  have h_sup : C ⊔ frattini P = ⊤ := by
    rw [eq_top_iff]; intro g _
    obtain ⟨c, hc_fixed, hc_coset⟩ :=
      exists_fixed_point_in_coset hP hq_ne_p.symm b hb_order hb_triv
        (QuotientGroup.mk (s := frattini P) g)
    have h_diff : g⁻¹ * c ∈ frattini P := by
      rw [← QuotientGroup.eq]; exact hc_coset.symm
    rw [show g = c * (c⁻¹ * g) by group]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left hc_fixed)
      (Subgroup.mem_sup_right (by rw [show c⁻¹ * g = (g⁻¹ * c)⁻¹ by group]
                                  exact Subgroup.inv_mem _ h_diff))
  -- By the non-generating property of the Frattini subgroup, C = ⊤.
  have hb_eq_one : b = 1 := by
    ext x; change x ∈ C; simp [frattini_nongenerating h_sup]
  -- But orderOf b = q > 1, contradiction.
  apply hq_prime.one_lt.ne
  simpa [hb_eq_one, orderOf_one] using hb_order
