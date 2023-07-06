/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module model_theory.fraisse
! leanprover-community/mathlib commit 0602c59878ff3d5f71dea69c2d32ccf2e93e5398
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.ModelTheory.FinitelyGenerated
import Mathbin.ModelTheory.DirectLimit
import Mathbin.ModelTheory.Bundled

/-!
# Fraïssé Classes and Fraïssé Limits

This file pertains to the ages of countable first-order structures. The age of a structure is the
class of all finitely-generated structures that embed into it.

Of particular interest are Fraïssé classes, which are exactly the ages of countable
ultrahomogeneous structures. To each is associated a unique (up to nonunique isomorphism)
Fraïssé limit - the countable ultrahomogeneous structure with that age.

## Main Definitions
* `first_order.language.age` is the class of finitely-generated structures that embed into a
particular structure.
* A class `K` has the `first_order.language.hereditary` when all finitely-generated
structures that embed into structures in `K` are also in `K`.
* A class `K` has the `first_order.language.joint_embedding` when for every `M`, `N` in
`K`, there is another structure in `K` into which both `M` and `N` embed.
* A class `K` has the `first_order.language.amalgamation` when for any pair of embeddings
of a structure `M` in `K` into other structures in `K`, those two structures can be embedded into a
fourth structure in `K` such that the resulting square of embeddings commutes.
* `first_order.language.is_fraisse` indicates that a class is nonempty, isomorphism-invariant,
essentially countable, and satisfies the hereditary, joint embedding, and amalgamation properties.
* `first_order.language.is_fraisse_limit` indicates that a structure is a Fraïssé limit for a given
class.

## Main Results
* We show that the age of any structure is isomorphism-invariant and satisfies the hereditary and
joint-embedding properties.
* `first_order.language.age.countable_quotient` shows that the age of any countable structure is
essentially countable.
* `first_order.language.exists_countable_is_age_of_iff` gives necessary and sufficient conditions
for a class to be the age of a countable structure in a language with countably many functions.

## Implementation Notes
* Classes of structures are formalized with `set (bundled L.Structure)`.
* Some results pertain to countable limit structures, others to countably-generated limit
structures. In the case of a language with countably many function symbols, these are equivalent.

## References
- [W. Hodges, *A Shorter Model Theory*][Hodges97]
- [K. Tent, M. Ziegler, *A Course in Model Theory*][Tent_Ziegler]

## TODO
* Show existence and uniqueness of Fraïssé limits

-/


universe u v w w'

open scoped FirstOrder

open Set CategoryTheory

namespace FirstOrder

namespace Language

open Structure Substructure

variable (L : Language.{u, v})

/-! ### The Age of a Structure and Fraïssé Classes-/


/-- The age of a structure `M` is the class of finitely-generated structures that embed into it. -/
def age (M : Type w) [L.Structure M] : Set (Bundled.{w} L.Structure) :=
  {N | Structure.FG L N ∧ Nonempty (N ↪[L] M)}
#align first_order.language.age FirstOrder.Language.age

variable {L} (K : Set (Bundled.{w} L.Structure))

/-- A class `K` has the hereditary property when all finitely-generated structures that embed into
  structures in `K` are also in `K`.  -/
def Hereditary : Prop :=
  ∀ M : Bundled.{w} L.Structure, M ∈ K → L.age M ⊆ K
#align first_order.language.hereditary FirstOrder.Language.Hereditary

/-- A class `K` has the joint embedding property when for every `M`, `N` in `K`, there is another
  structure in `K` into which both `M` and `N` embed. -/
def JointEmbedding : Prop :=
  DirectedOn (fun M N : Bundled.{w} L.Structure => Nonempty (M ↪[L] N)) K
#align first_order.language.joint_embedding FirstOrder.Language.JointEmbedding

/-- A class `K` has the amalgamation property when for any pair of embeddings of a structure `M` in
  `K` into other structures in `K`, those two structures can be embedded into a fourth structure in
  `K` such that the resulting square of embeddings commutes. -/
def Amalgamation : Prop :=
  ∀ (M N P : Bundled.{w} L.Structure) (MN : M ↪[L] N) (MP : M ↪[L] P),
    M ∈ K →
      N ∈ K →
        P ∈ K →
          ∃ (Q : Bundled.{w} L.Structure) (NQ : N ↪[L] Q) (PQ : P ↪[L] Q),
            Q ∈ K ∧ NQ.comp MN = PQ.comp MP
#align first_order.language.amalgamation FirstOrder.Language.Amalgamation

/-- A Fraïssé class is a nonempty, isomorphism-invariant, essentially countable class of structures
satisfying the hereditary, joint embedding, and amalgamation properties. -/
class IsFraisse : Prop where
  is_nonempty : K.Nonempty
  FG : ∀ M : Bundled.{w} L.Structure, M ∈ K → Structure.FG L M
  is_equiv_invariant : ∀ M N : Bundled.{w} L.Structure, Nonempty (M ≃[L] N) → (M ∈ K ↔ N ∈ K)
  is_essentially_countable : (Quotient.mk' '' K).Countable
  Hereditary : Hereditary K
  JointEmbedding : JointEmbedding K
  Amalgamation : Amalgamation K
#align first_order.language.is_fraisse FirstOrder.Language.IsFraisse

variable {K} (L) (M : Type w) [L.Structure M]

theorem age.is_equiv_invariant (N P : Bundled.{w} L.Structure) (h : Nonempty (N ≃[L] P)) :
    N ∈ L.age M ↔ P ∈ L.age M :=
  and_congr h.some.fg_iff
    ⟨Nonempty.map fun x => Embedding.comp x h.some.symm.toEmbedding,
      Nonempty.map fun x => Embedding.comp x h.some.toEmbedding⟩
#align first_order.language.age.is_equiv_invariant FirstOrder.Language.age.is_equiv_invariant

variable {L} {M} {N : Type w} [L.Structure N]

theorem Embedding.age_subset_age (MN : M ↪[L] N) : L.age M ⊆ L.age N := fun _ =>
  And.imp_right (Nonempty.map MN.comp)
#align first_order.language.embedding.age_subset_age FirstOrder.Language.Embedding.age_subset_age

theorem Equiv.age_eq_age (MN : M ≃[L] N) : L.age M = L.age N :=
  le_antisymm MN.toEmbedding.age_subset_age MN.symm.toEmbedding.age_subset_age
#align first_order.language.equiv.age_eq_age FirstOrder.Language.Equiv.age_eq_age

theorem Structure.FG.mem_age_of_equiv {M N : Bundled L.Structure} (h : Structure.FG L M)
    (MN : Nonempty (M ≃[L] N)) : N ∈ L.age M :=
  ⟨MN.some.fg_iff.1 h, ⟨MN.some.symm.toEmbedding⟩⟩
#align first_order.language.Structure.fg.mem_age_of_equiv FirstOrder.Language.Structure.FG.mem_age_of_equiv

theorem Hereditary.is_equiv_invariant_of_fG (h : Hereditary K)
    (fg : ∀ M : Bundled.{w} L.Structure, M ∈ K → Structure.FG L M) (M N : Bundled.{w} L.Structure)
    (hn : Nonempty (M ≃[L] N)) : M ∈ K ↔ N ∈ K :=
  ⟨fun MK => h M MK ((fg M MK).mem_age_of_equiv hn), fun NK =>
    h N NK ((fg N NK).mem_age_of_equiv ⟨hn.some.symm⟩)⟩
#align first_order.language.hereditary.is_equiv_invariant_of_fg FirstOrder.Language.Hereditary.is_equiv_invariant_of_fG

variable (M)

theorem age.nonempty : (L.age M).Nonempty :=
  ⟨Bundled.of (Substructure.closure L (∅ : Set M)),
    (fg_iff_structure_fg _).1 (fg_closure Set.finite_empty), ⟨Substructure.subtype _⟩⟩
#align first_order.language.age.nonempty FirstOrder.Language.age.nonempty

theorem age.hereditary : Hereditary (L.age M) := fun N hN P hP => hN.2.some.age_subset_age hP
#align first_order.language.age.hereditary FirstOrder.Language.age.hereditary

theorem age.jointEmbedding : JointEmbedding (L.age M) := fun N hN P hP =>
  ⟨Bundled.of ↥(hN.2.some.toHom.range ⊔ hP.2.some.toHom.range),
    ⟨(fg_iff_structure_fg _).1 ((hN.1.range hN.2.some.toHom).sup (hP.1.range hP.2.some.toHom)),
      ⟨Subtype _⟩⟩,
    ⟨Embedding.comp (inclusion le_sup_left) hN.2.some.equivRange.toEmbedding⟩,
    ⟨Embedding.comp (inclusion le_sup_right) hP.2.some.equivRange.toEmbedding⟩⟩
#align first_order.language.age.joint_embedding FirstOrder.Language.age.jointEmbedding

/-- The age of a countable structure is essentially countable (has countably many isomorphism
classes). -/
theorem age.countable_quotient [h : Countable M] : (Quotient.mk' '' L.age M).Countable := by
  classical
  refine'
    (congr_arg _ (Set.ext <| forall_quotient_iff.2 fun N => _)).mp
      (countable_range fun s : Finset M => ⟦⟨closure L (s : Set M), inferInstance⟩⟧)
  simp only [mem_image, mem_range, mem_set_of_eq, Quotient.eq']
  constructor
  · rintro ⟨s, hs⟩
    use bundled.of ↥(closure L (s : Set M))
    exact ⟨⟨(fg_iff_Structure_fg _).1 (fg_closure s.finite_to_set), ⟨Subtype _⟩⟩, hs⟩
  · rintro ⟨P, ⟨⟨s, hs⟩, ⟨PM⟩⟩, hP2⟩
    refine' ⟨s.image PM, Setoid.trans _ hP2⟩
    rw [← embedding.coe_to_hom, Finset.coe_image, closure_image PM.to_hom, hs, ← hom.range_eq_map]
    exact ⟨PM.equiv_range.symm⟩
#align first_order.language.age.countable_quotient FirstOrder.Language.age.countable_quotient

/-- The age of a direct limit of structures is the union of the ages of the structures. -/
@[simp]
theorem age_directLimit {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type max w w') [∀ i, L.Structure (G i)] (f : ∀ i j, i ≤ j → G i ↪[L] G j)
    [DirectedSystem G fun i j h => f i j h] : L.age (DirectLimit G f) = ⋃ i : ι, L.age (G i) := by
  classical
  ext M
  simp only [mem_Union]
  constructor
  · rintro ⟨Mfg, ⟨e⟩⟩
    obtain ⟨s, hs⟩ := Mfg.range e.to_hom
    let out := @Quotient.out _ (direct_limit.setoid G f)
    obtain ⟨i, hi⟩ := Finset.exists_le (s.image (Sigma.fst ∘ out))
    have e' := (direct_limit.of L ι G f i).equivRange.symm.toEmbedding
    refine' ⟨i, Mfg, ⟨e'.comp ((substructure.inclusion _).comp e.equiv_range.to_embedding)⟩⟩
    rw [← hs, closure_le]
    intro x hx
    refine' ⟨f (out x).1 i (hi (out x).1 (Finset.mem_image_of_mem _ hx)) (out x).2, _⟩
    rw [embedding.coe_to_hom, direct_limit.of_apply, Quotient.mk_eq_iff_out,
      direct_limit.equiv_iff G f _ (hi (out x).1 (Finset.mem_image_of_mem _ hx)),
      DirectedSystem.map_self]
    rfl
  · rintro ⟨i, Mfg, ⟨e⟩⟩
    exact ⟨Mfg, ⟨Embedding.comp (direct_limit.of L ι G f i) e⟩⟩
#align first_order.language.age_direct_limit FirstOrder.Language.age_directLimit

/-- Sufficient conditions for a class to be the age of a countably-generated structure. -/
theorem exists_cG_is_age_of (hn : K.Nonempty)
    (h : ∀ M N : Bundled.{w} L.Structure, Nonempty (M ≃[L] N) → (M ∈ K ↔ N ∈ K))
    (hc : (Quotient.mk' '' K).Countable)
    (fg : ∀ M : Bundled.{w} L.Structure, M ∈ K → Structure.FG L M) (hp : Hereditary K)
    (jep : JointEmbedding K) : ∃ M : Bundled.{w} L.Structure, Structure.CG L M ∧ L.age M = K :=
  by
  obtain ⟨F, hF⟩ := hc.exists_eq_range (hn.image _)
  simp only [Set.ext_iff, forall_quotient_iff, mem_image, mem_range, Quotient.eq'] at hF 
  simp_rw [Quotient.eq_mk_iff_out] at hF 
  have hF' : ∀ n : ℕ, (F n).out ∈ K := by
    intro n
    obtain ⟨P, hP1, hP2⟩ := (hF (F n).out).2 ⟨n, Setoid.refl _⟩
    exact (h _ _ hP2).1 hP1
  choose P hPK hP hFP using fun (N : K) (n : ℕ) => jep N N.2 (F (n + 1)).out (hF' _)
  let G : ℕ → K := @Nat.rec (fun _ => K) ⟨(F 0).out, hF' 0⟩ fun n N => ⟨P N n, hPK N n⟩
  let f : ∀ i j, i ≤ j → G i ↪[L] G j := directed_system.nat_le_rec fun n => (hP _ n).some
  refine'
    ⟨bundled.of (direct_limit (fun n => G n) f), direct_limit.cg _ fun n => (fg _ (G n).2).CG,
      (age_direct_limit _ _).trans
        (subset_antisymm (Union_subset fun n N hN => hp (G n) (G n).2 hN) fun N KN => _)⟩
  obtain ⟨n, ⟨e⟩⟩ := (hF N).1 ⟨N, KN, Setoid.refl _⟩
  refine' mem_Union_of_mem n ⟨fg _ KN, ⟨Embedding.comp _ e.symm.to_embedding⟩⟩
  cases n
  · exact embedding.refl _ _
  · exact (hFP _ n).some
#align first_order.language.exists_cg_is_age_of FirstOrder.Language.exists_cG_is_age_of

theorem exists_countable_is_age_of_iff [Countable (Σ l, L.Functions l)] :
    (∃ M : Bundled.{w} L.Structure, Countable M ∧ L.age M = K) ↔
      K.Nonempty ∧
        (∀ M N : Bundled.{w} L.Structure, Nonempty (M ≃[L] N) → (M ∈ K ↔ N ∈ K)) ∧
          (Quotient.mk' '' K).Countable ∧
            (∀ M : Bundled.{w} L.Structure, M ∈ K → Structure.FG L M) ∧
              Hereditary K ∧ JointEmbedding K :=
  by
  constructor
  · rintro ⟨M, h1, h2, rfl⟩
    skip
    refine'
      ⟨age.nonempty M, age.is_equiv_invariant L M, age.countable_quotient M, fun N hN => hN.1,
        age.hereditary M, age.joint_embedding M⟩
  · rintro ⟨Kn, eqinv, cq, hfg, hp, jep⟩
    obtain ⟨M, hM, rfl⟩ := exists_cg_is_age_of Kn eqinv cq hfg hp jep
    exact ⟨M, Structure.cg_iff_countable.1 hM, rfl⟩
#align first_order.language.exists_countable_is_age_of_iff FirstOrder.Language.exists_countable_is_age_of_iff

variable {K} (L) (M)

/-- A structure `M` is ultrahomogeneous if every embedding of a finitely generated substructure
into `M` extends to an automorphism of `M`. -/
def IsUltrahomogeneous : Prop :=
  ∀ (S : L.Substructure M) (hs : S.FG) (f : S ↪[L] M),
    ∃ g : M ≃[L] M, f = g.toEmbedding.comp S.Subtype
#align first_order.language.is_ultrahomogeneous FirstOrder.Language.IsUltrahomogeneous

variable {L} (K)

/-- A structure `M` is a Fraïssé limit for a class `K` if it is countably generated,
ultrahomogeneous, and has age `K`. -/
@[protect_proj]
structure IsFraisseLimit [Countable (Σ l, L.Functions l)] [Countable M] : Prop where
  ultrahomogeneous : IsUltrahomogeneous L M
  age : L.age M = K
#align first_order.language.is_fraisse_limit FirstOrder.Language.IsFraisseLimit

variable {L} {M}

theorem IsUltrahomogeneous.amalgamation_age (h : L.IsUltrahomogeneous M) : Amalgamation (L.age M) :=
  by
  rintro N P Q NP NQ ⟨Nfg, ⟨NM⟩⟩ ⟨Pfg, ⟨PM⟩⟩ ⟨Qfg, ⟨QM⟩⟩
  obtain ⟨g, hg⟩ :=
    h (PM.comp NP).toHom.range (Nfg.range _)
      ((QM.comp NQ).comp (PM.comp NP).equivRange.symm.toEmbedding)
  let s := (g.to_hom.comp PM.to_hom).range ⊔ QM.to_hom.range
  refine'
    ⟨bundled.of s,
      Embedding.comp (substructure.inclusion le_sup_left)
        (g.to_embedding.comp PM).equivRange.toEmbedding,
      Embedding.comp (substructure.inclusion le_sup_right) QM.equiv_range.to_embedding,
      ⟨(fg_iff_Structure_fg _).1 (fg.sup (Pfg.range _) (Qfg.range _)), ⟨substructure.subtype _⟩⟩, _⟩
  ext n
  have hgn := (embedding.ext_iff.1 hg) ((PM.comp NP).equivRange n)
  simp only [embedding.comp_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply,
    substructure.coe_subtype, embedding.equiv_range_apply] at hgn 
  simp only [embedding.comp_apply, Equiv.coe_toEmbedding, substructure.coe_inclusion,
    Set.coe_inclusion, embedding.equiv_range_apply, hgn]
#align first_order.language.is_ultrahomogeneous.amalgamation_age FirstOrder.Language.IsUltrahomogeneous.amalgamation_age

theorem IsUltrahomogeneous.age_isFraisse [Countable M] (h : L.IsUltrahomogeneous M) :
    IsFraisse (L.age M) :=
  ⟨age.nonempty M, fun _ hN => hN.1, age.is_equiv_invariant L M, age.countable_quotient M,
    age.hereditary M, age.jointEmbedding M, h.amalgamation_age⟩
#align first_order.language.is_ultrahomogeneous.age_is_fraisse FirstOrder.Language.IsUltrahomogeneous.age_isFraisse

namespace IsFraisseLimit

/-- If a class has a Fraïssé limit, it must be Fraïssé. -/
theorem isFraisse [Countable (Σ l, L.Functions l)] [Countable M] (h : IsFraisseLimit K M) :
    IsFraisse K :=
  (congr rfl h.age).mp h.ultrahomogeneous.age_isFraisse
#align first_order.language.is_fraisse_limit.is_fraisse FirstOrder.Language.IsFraisseLimit.isFraisse

end IsFraisseLimit

end Language

end FirstOrder

