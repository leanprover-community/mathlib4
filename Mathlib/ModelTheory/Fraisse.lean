/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Gabin Kolly
-/
import Mathlib.ModelTheory.FinitelyGenerated
import Mathlib.ModelTheory.PartialEquiv
import Mathlib.ModelTheory.Bundled
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Fraïssé Classes and Fraïssé Limits

This file pertains to the ages of countable first-order structures. The age of a structure is the
class of all finitely-generated structures that embed into it.

Of particular interest are Fraïssé classes, which are exactly the ages of countable
ultrahomogeneous structures. To each is associated a unique (up to nonunique isomorphism)
Fraïssé limit - the countable ultrahomogeneous structure with that age.

## Main Definitions

- `FirstOrder.Language.age` is the class of finitely-generated structures that embed into a
  particular structure.
- A class `K` is `FirstOrder.Language.Hereditary` when all finitely-generated
  structures that embed into structures in `K` are also in `K`.
- A class `K` has `FirstOrder.Language.JointEmbedding` when for every `M`, `N` in
  `K`, there is another structure in `K` into which both `M` and `N` embed.
- A class `K` has `FirstOrder.Language.Amalgamation` when for any pair of embeddings
  of a structure `M` in `K` into other structures in `K`, those two structures can be embedded into
  a fourth structure in `K` such that the resulting square of embeddings commutes.
- `FirstOrder.Language.IsFraisse` indicates that a class is nonempty, essentially countable,
  and satisfies the hereditary, joint embedding, and amalgamation properties.
- `FirstOrder.Language.IsFraisseLimit` indicates that a structure is a Fraïssé limit for a given
  class.

## Main Results

- We show that the age of any structure is isomorphism-invariant and satisfies the hereditary and
  joint-embedding properties.
- `FirstOrder.Language.age.countable_quotient` shows that the age of any countable structure is
  essentially countable.
- `FirstOrder.Language.exists_countable_is_age_of_iff` gives necessary and sufficient conditions
  for a class to be the age of a countable structure in a language with countably many functions.
- `FirstOrder.Language.IsFraisseLimit.nonempty_equiv` shows that any class which is Fraïssé has
  at most one Fraïssé limit up to equivalence.
- `FirstOrder.Language.empty.isFraisseLimit_of_countable_infinite` shows that any countably infinite
  structure in the empty language is a Fraïssé limit of the class of finite structures.
- `FirstOrder.Language.empty.isFraisse_finite` shows that the class of finite structures in the
  empty language is Fraïssé.

## Implementation Notes

- Classes of structures are formalized with `Set (Bundled L.Structure)`.
- Some results pertain to countable limit structures, others to countably-generated limit
  structures. In the case of a language with countably many function symbols, these are equivalent.

## References

- [W. Hodges, *A Shorter Model Theory*][Hodges97]
- [K. Tent, M. Ziegler, *A Course in Model Theory*][Tent_Ziegler]

## TODO

- Show existence of Fraïssé limits

-/


universe u v w w'

open scoped FirstOrder

open Set CategoryTheory

namespace FirstOrder

namespace Language

open Structure Substructure

variable (L : Language.{u, v})

/-! ### The Age of a Structure and Fraïssé Classes -/


/-- The age of a structure `M` is the class of finitely-generated structures that embed into it. -/
def age (M : Type w) [L.Structure M] : Set (Bundled.{w} L.Structure) :=
  {N | Structure.FG L N ∧ Nonempty (N ↪[L] M)}

variable {L}
variable (K : Set (Bundled.{w} L.Structure))

/-- A class `K` has the hereditary property when all finitely-generated structures that embed into
  structures in `K` are also in `K`. -/
def Hereditary : Prop :=
  ∀ M : Bundled.{w} L.Structure, M ∈ K → L.age M ⊆ K

/-- A class `K` has the joint embedding property when for every `M`, `N` in `K`, there is another
  structure in `K` into which both `M` and `N` embed. -/
def JointEmbedding : Prop :=
  DirectedOn (fun M N : Bundled.{w} L.Structure => Nonempty (M ↪[L] N)) K

/-- A class `K` has the amalgamation property when for any pair of embeddings of a structure `M` in
  `K` into other structures in `K`, those two structures can be embedded into a fourth structure in
  `K` such that the resulting square of embeddings commutes. -/
def Amalgamation : Prop :=
  ∀ (M N P : Bundled.{w} L.Structure) (MN : M ↪[L] N) (MP : M ↪[L] P),
    M ∈ K → N ∈ K → P ∈ K → ∃ (Q : Bundled.{w} L.Structure) (NQ : N ↪[L] Q) (PQ : P ↪[L] Q),
      Q ∈ K ∧ NQ.comp MN = PQ.comp MP

/-- A Fraïssé class is a nonempty, essentially countable class of structures satisfying the
hereditary, joint embedding, and amalgamation properties. -/
class IsFraisse : Prop where
  is_nonempty : K.Nonempty
  FG : ∀ M : Bundled.{w} L.Structure, M ∈ K → Structure.FG L M
  is_essentially_countable : (Quotient.mk' '' K).Countable
  hereditary : Hereditary K
  jointEmbedding : JointEmbedding K
  amalgamation : Amalgamation K

variable {K} (L) (M : Type w) [Structure L M]

theorem age.is_equiv_invariant (N P : Bundled.{w} L.Structure) (h : Nonempty (N ≃[L] P)) :
    N ∈ L.age M ↔ P ∈ L.age M :=
  and_congr h.some.fg_iff
    ⟨Nonempty.map fun x => Embedding.comp x h.some.symm.toEmbedding,
      Nonempty.map fun x => Embedding.comp x h.some.toEmbedding⟩

variable {L} {M} {N : Type w} [Structure L N]

theorem Embedding.age_subset_age (MN : M ↪[L] N) : L.age M ⊆ L.age N := fun _ =>
  And.imp_right (Nonempty.map MN.comp)

theorem Equiv.age_eq_age (MN : M ≃[L] N) : L.age M = L.age N :=
  le_antisymm MN.toEmbedding.age_subset_age MN.symm.toEmbedding.age_subset_age

theorem Structure.FG.mem_age_of_equiv {M N : Bundled L.Structure} (h : Structure.FG L M)
    (MN : Nonempty (M ≃[L] N)) : N ∈ L.age M :=
  ⟨MN.some.fg_iff.1 h, ⟨MN.some.symm.toEmbedding⟩⟩

theorem Hereditary.is_equiv_invariant_of_fg (h : Hereditary K)
    (fg : ∀ M : Bundled.{w} L.Structure, M ∈ K → Structure.FG L M) (M N : Bundled.{w} L.Structure)
    (hn : Nonempty (M ≃[L] N)) : M ∈ K ↔ N ∈ K :=
  ⟨fun MK => h M MK ((fg M MK).mem_age_of_equiv hn),
   fun NK => h N NK ((fg N NK).mem_age_of_equiv ⟨hn.some.symm⟩)⟩

theorem IsFraisse.is_equiv_invariant [h : IsFraisse K] {M N : Bundled.{w} L.Structure}
    (hn : Nonempty (M ≃[L] N)) : M ∈ K ↔ N ∈ K :=
  h.hereditary.is_equiv_invariant_of_fg h.FG M N hn

variable (M)

theorem age.nonempty : (L.age M).Nonempty :=
  ⟨Bundled.of (Substructure.closure L (∅ : Set M)),
    (fg_iff_structure_fg _).1 (fg_closure Set.finite_empty), ⟨Substructure.subtype _⟩⟩

theorem age.hereditary : Hereditary (L.age M) := fun _ hN _ hP => hN.2.some.age_subset_age hP

theorem age.jointEmbedding : JointEmbedding (L.age M) := fun _ hN _ hP =>
  ⟨Bundled.of (↥(hN.2.some.toHom.range ⊔ hP.2.some.toHom.range)),
    ⟨(fg_iff_structure_fg _).1 ((hN.1.range hN.2.some.toHom).sup (hP.1.range hP.2.some.toHom)),
      ⟨Substructure.subtype _⟩⟩,
    ⟨Embedding.comp (inclusion le_sup_left) hN.2.some.equivRange.toEmbedding⟩,
    ⟨Embedding.comp (inclusion le_sup_right) hP.2.some.equivRange.toEmbedding⟩⟩

variable {M} in
theorem age.fg_substructure {S : L.Substructure M} (fg : S.FG) : Bundled.mk S ∈ L.age M := by
  exact ⟨(Substructure.fg_iff_structure_fg _).1 fg, ⟨subtype _⟩⟩

/-- Any class in the age of a structure has a representative which is a finitely generated
substructure. -/
theorem age.has_representative_as_substructure :
    ∀ C ∈ Quotient.mk' '' L.age M, ∃ V : {V : L.Substructure M // FG V},
      ⟦Bundled.mk V⟧ = C := by
  rintro _ ⟨N, ⟨N_fg, ⟨N_incl⟩⟩, N_eq⟩
  refine N_eq.symm ▸ ⟨⟨N_incl.toHom.range, ?_⟩, Quotient.sound ⟨N_incl.equivRange.symm⟩⟩
  exact FG.range N_fg (Embedding.toHom N_incl)

/-- The age of a countable structure is essentially countable (has countably many isomorphism
classes). -/
theorem age.countable_quotient [h : Countable M] : (Quotient.mk' '' L.age M).Countable := by
  classical
  refine (congr_arg _ (Set.ext <| Quotient.forall.2 fun N => ?_)).mp
    (countable_range fun s : Finset M => ⟦⟨closure L (s : Set M), inferInstance⟩⟧)
  constructor
  · rintro ⟨s, hs⟩
    use Bundled.of (closure L (s : Set M))
    exact ⟨⟨(fg_iff_structure_fg _).1 (fg_closure s.finite_toSet), ⟨Substructure.subtype _⟩⟩, hs⟩
  · simp only [mem_range, Quotient.eq]
    rintro ⟨P, ⟨⟨s, hs⟩, ⟨PM⟩⟩, hP2⟩
    refine ⟨s.image PM, Setoid.trans (b := P) ?_ <| Quotient.exact hP2⟩
    rw [← Embedding.coe_toHom, Finset.coe_image, closure_image PM.toHom, hs, ← Hom.range_eq_map]
    exact ⟨PM.equivRange.symm⟩

-- This is not a simp-lemma because it does not apply to itself.
/-- The age of a direct limit of structures is the union of the ages of the structures. -/
theorem age_directLimit {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (G : ι → Type max w w') [∀ i, L.Structure (G i)] (f : ∀ i j, i ≤ j → G i ↪[L] G j)
    [DirectedSystem G fun i j h => f i j h] : L.age (DirectLimit G f) = ⋃ i : ι, L.age (G i) := by
  classical
  ext M
  simp only [mem_iUnion]
  constructor
  · rintro ⟨Mfg, ⟨e⟩⟩
    obtain ⟨s, hs⟩ := Mfg.range e.toHom
    let out := @Quotient.out _ (DirectLimit.setoid G f)
    obtain ⟨i, hi⟩ := Finset.exists_le (s.image (Sigma.fst ∘ out))
    have e' := (DirectLimit.of L ι G f i).equivRange.symm.toEmbedding
    refine ⟨i, Mfg, ⟨e'.comp ((Substructure.inclusion ?_).comp e.equivRange.toEmbedding)⟩⟩
    rw [← hs, closure_le]
    intro x hx
    refine ⟨f (out x).1 i (hi (out x).1 (Finset.mem_image_of_mem _ hx)) (out x).2, ?_⟩
    rw [Embedding.coe_toHom, DirectLimit.of_apply, @Quotient.mk_eq_iff_out _ (_),
      DirectLimit.equiv_iff G f (le_refl _) (hi (out x).1 (Finset.mem_image_of_mem _ hx)),
      DirectedSystem.map_self]
  · rintro ⟨i, Mfg, ⟨e⟩⟩
    exact ⟨Mfg, ⟨Embedding.comp (DirectLimit.of L ι G f i) e⟩⟩

/-- Sufficient conditions for a class to be the age of a countably-generated structure. -/
theorem exists_cg_is_age_of (hn : K.Nonempty)
    (hc : (Quotient.mk' '' K).Countable)
    (fg : ∀ M : Bundled.{w} L.Structure, M ∈ K → Structure.FG L M) (hp : Hereditary K)
    (jep : JointEmbedding K) : ∃ M : Bundled.{w} L.Structure, Structure.CG L M ∧ L.age M = K := by
  obtain ⟨F, hF⟩ := hc.exists_eq_range (hn.image _)
  simp only [Set.ext_iff, Quotient.forall, mem_image, mem_range] at hF
  simp_rw [Quotient.eq_mk_iff_out] at hF
  have hF' : ∀ n : ℕ, (F n).out ∈ K := by
    intro n
    obtain ⟨P, hP1, hP2⟩ := (hF (F n).out).2 ⟨n, Setoid.refl _⟩
    -- Porting note: fix hP2 because `Quotient.out (Quotient.mk' x) ≈ a` was not simplified
    -- to `x ≈ a` in hF
    replace hP2 := Setoid.trans (Setoid.symm (Quotient.mk_out P)) hP2
    exact (hp.is_equiv_invariant_of_fg fg _ _ hP2).1 hP1
  choose P hPK hP hFP using fun (N : K) (n : ℕ) => jep N N.2 (F (n + 1)).out (hF' _)
  let G : ℕ → K := @Nat.rec (fun _ => K) ⟨(F 0).out, hF' 0⟩ fun n N => ⟨P N n, hPK N n⟩
  -- Porting note: was
  -- let f : ∀ i j, i ≤ j → G i ↪[L] G j := DirectedSystem.natLeRec fun n => (hP _ n).some
  let f : ∀ (i j : ℕ), i ≤ j → (G i).val ↪[L] (G j).val := by
    refine DirectedSystem.natLERec (G' := fun i => (G i).val) (L := L) ?_
    dsimp only [G]
    exact fun n => (hP _ n).some
  have : DirectedSystem (fun n ↦ (G n).val) fun i j h ↦ ↑(f i j h) := by
    dsimp [f, G]; infer_instance
  refine ⟨Bundled.of (@DirectLimit L _ _ (fun n ↦ (G n).val) _ f _ _), ?_, ?_⟩
  · exact DirectLimit.cg _ (fun n => (fg _ (G n).2).cg)
  · refine (age_directLimit (fun n ↦ (G n).val) f).trans
      (subset_antisymm (iUnion_subset fun n N hN => hp (G n).val (G n).2 hN) fun N KN => ?_)
    have : Quotient.out (Quotient.mk' N) ≈ N := Quotient.eq_mk_iff_out.mp rfl
    obtain ⟨n, ⟨e⟩⟩ := (hF N).1 ⟨N, KN, this⟩
    refine mem_iUnion_of_mem n ⟨fg _ KN, ⟨Embedding.comp ?_ e.symm.toEmbedding⟩⟩
    rcases n with - | n
    · dsimp [G]; exact Embedding.refl _ _
    · dsimp [G]; exact (hFP _ n).some

theorem exists_countable_is_age_of_iff [Countable (Σ l, L.Functions l)] :
    (∃ M : Bundled.{w} L.Structure, Countable M ∧ L.age M = K) ↔
      K.Nonempty ∧ (∀ M N : Bundled.{w} L.Structure, Nonempty (M ≃[L] N) → (M ∈ K ↔ N ∈ K)) ∧
      (Quotient.mk' '' K).Countable ∧ (∀ M : Bundled.{w} L.Structure, M ∈ K → Structure.FG L M) ∧
      Hereditary K ∧ JointEmbedding K := by
  constructor
  · rintro ⟨M, h1, h2, rfl⟩
    refine ⟨age.nonempty M, age.is_equiv_invariant L M, age.countable_quotient M, fun N hN => hN.1,
      age.hereditary M, age.jointEmbedding M⟩
  · rintro ⟨Kn, _, cq, hfg, hp, jep⟩
    obtain ⟨M, hM, rfl⟩ := exists_cg_is_age_of Kn cq hfg hp jep
    exact ⟨M, Structure.cg_iff_countable.1 hM, rfl⟩

variable (L)

/-- A structure `M` is ultrahomogeneous if every embedding of a finitely generated substructure
into `M` extends to an automorphism of `M`. -/
def IsUltrahomogeneous : Prop :=
  ∀ (S : L.Substructure M) (_ : S.FG) (f : S ↪[L] M),
    ∃ g : M ≃[L] M, f = g.toEmbedding.comp S.subtype

variable {L} (K)

/-- A structure `M` is a Fraïssé limit for a class `K` if it is countably generated,
ultrahomogeneous, and has age `K`. -/
structure IsFraisseLimit [Countable (Σ l, L.Functions l)] [Countable M] : Prop where
  protected ultrahomogeneous : IsUltrahomogeneous L M
  protected age : L.age M = K

variable {M}

/-- Any embedding from a finitely generated `S` to an ultrahomogeneous structure `M`
can be extended to an embedding from any structure with an embedding to `M`. -/
theorem IsUltrahomogeneous.extend_embedding (M_homog : L.IsUltrahomogeneous M) {S : Type*}
    [L.Structure S] (S_FG : FG L S) {T : Type*} [L.Structure T] [h : Nonempty (T ↪[L] M)]
    (f : S ↪[L] M) (g : S ↪[L] T) :
    ∃ f' : T ↪[L] M, f = f'.comp g := by
  let ⟨r⟩ := h
  let s := r.comp g
  let ⟨t, eq⟩ := M_homog s.toHom.range (S_FG.range s.toHom) (f.comp s.equivRange.symm.toEmbedding)
  use t.toEmbedding.comp r
  change _ = t.toEmbedding.comp s
  ext x
  have eq' := congr_fun (congr_arg DFunLike.coe eq) ⟨s x, Hom.mem_range.2 ⟨x, rfl⟩⟩
  simp only [Embedding.comp_apply,
    coe_subtype] at eq'
  simp only [Embedding.comp_apply, ← eq', Equiv.coe_toEmbedding, EmbeddingLike.apply_eq_iff_eq]
  apply (Embedding.equivRange (Embedding.comp r g)).injective
  ext
  simp only [Equiv.apply_symm_apply, Embedding.equivRange_apply, s]

/-- A countably generated structure is ultrahomogeneous if and only if any equivalence between
finitely generated substructures can be extended to any element in the domain. -/
theorem isUltrahomogeneous_iff_IsExtensionPair (M_CG : CG L M) : L.IsUltrahomogeneous M ↔
    L.IsExtensionPair M M := by
  constructor
  · intro M_homog ⟨f, f_FG⟩ m
    let S := f.dom ⊔ closure L {m}
    have dom_le_S : f.dom ≤ S := le_sup_left
    let ⟨f', eq_f'⟩ := M_homog.extend_embedding (f.dom.fg_iff_structure_fg.1 f_FG)
      ((subtype _).comp f.toEquiv.toEmbedding) (inclusion dom_le_S) (h := ⟨subtype _⟩)
    refine ⟨⟨⟨S, f'.toHom.range, f'.equivRange⟩, f_FG.sup (fg_closure_singleton _)⟩,
      subset_closure.trans (le_sup_right : _ ≤ S) (mem_singleton m), ⟨dom_le_S, ?_⟩⟩
    ext
    simp only [Embedding.comp_apply, Equiv.coe_toEmbedding, coe_subtype, eq_f',
      Embedding.equivRange_apply, Substructure.coe_inclusion]
  · intro h S S_FG f
    let ⟨g, ⟨dom_le_dom, eq⟩⟩ :=
      equiv_between_cg M_CG M_CG ⟨⟨S, f.toHom.range, f.equivRange⟩, S_FG⟩ h h
    use g
    simp only [Embedding.subtype_equivRange] at eq
    rw [← eq]
    ext
    rfl

theorem IsUltrahomogeneous.amalgamation_age (h : L.IsUltrahomogeneous M) :
    Amalgamation (L.age M) := by
  rintro N P Q NP NQ ⟨Nfg, ⟨-⟩⟩ ⟨Pfg, ⟨PM⟩⟩ ⟨Qfg, ⟨QM⟩⟩
  obtain ⟨g, hg⟩ := h (PM.comp NP).toHom.range (Nfg.range _)
    ((QM.comp NQ).comp (PM.comp NP).equivRange.symm.toEmbedding)
  let s := (g.toHom.comp PM.toHom).range ⊔ QM.toHom.range
  refine ⟨Bundled.of s,
    Embedding.comp (Substructure.inclusion le_sup_left)
      (g.toEmbedding.comp PM).equivRange.toEmbedding,
    Embedding.comp (Substructure.inclusion le_sup_right) QM.equivRange.toEmbedding,
    ⟨(fg_iff_structure_fg _).1 (FG.sup (Pfg.range _) (Qfg.range _)), ⟨Substructure.subtype _⟩⟩, ?_⟩
  ext n
  apply Subtype.ext
  have hgn := (Embedding.ext_iff.1 hg) ((PM.comp NP).equivRange n)
  simp only [Embedding.comp_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply,
    Substructure.coe_subtype, Embedding.equivRange_apply] at hgn
  simp only [Embedding.comp_apply, Equiv.coe_toEmbedding]
  erw [Substructure.coe_inclusion, Substructure.coe_inclusion]
  simp only [Embedding.equivRange_apply, hgn]
  -- This used to be `simp only [...]` before https://github.com/leanprover/lean4/pull/2644
  erw [Embedding.comp_apply, Equiv.coe_toEmbedding,
    Embedding.equivRange_apply]
  simp

theorem IsUltrahomogeneous.age_isFraisse [Countable M] (h : L.IsUltrahomogeneous M) :
    IsFraisse (L.age M) :=
  ⟨age.nonempty M, fun _ hN => hN.1, age.countable_quotient M,
    age.hereditary M, age.jointEmbedding M, h.amalgamation_age⟩

namespace IsFraisseLimit

/-- If a class has a Fraïssé limit, it must be Fraïssé. -/
theorem isFraisse [Countable (Σ l, L.Functions l)] [Countable M] (h : IsFraisseLimit K M) :
    IsFraisse K :=
  (congr rfl h.age).mp h.ultrahomogeneous.age_isFraisse

variable {K} {N : Type w} [L.Structure N]
variable [Countable (Σ l, L.Functions l)] [Countable M] [Countable N]
variable (hM : IsFraisseLimit K M) (hN : IsFraisseLimit K N)

include hM hN

protected theorem isExtensionPair : L.IsExtensionPair M N := by
  intro ⟨f, f_FG⟩ m
  let S := f.dom ⊔ closure L {m}
  have S_FG : S.FG := f_FG.sup (Substructure.fg_closure_singleton _)
  have S_in_age_N : ⟨S, inferInstance⟩ ∈ L.age N := by
    rw [hN.age, ← hM.age]
    exact ⟨(fg_iff_structure_fg S).1 S_FG, ⟨subtype _⟩⟩
  haveI nonempty_S_N : Nonempty (S ↪[L] N) := S_in_age_N.2
  let ⟨g, g_eq⟩ := hN.ultrahomogeneous.extend_embedding (f.dom.fg_iff_structure_fg.1 f_FG)
    ((subtype f.cod).comp f.toEquiv.toEmbedding) (inclusion (le_sup_left : _ ≤ S))
  refine ⟨⟨⟨S, g.toHom.range, g.equivRange⟩, S_FG⟩,
    subset_closure.trans (le_sup_right : _ ≤ S) (mem_singleton m), ⟨le_sup_left, ?_⟩⟩
  ext
  simp [S, g_eq]

/-- The Fraïssé limit of a class is unique, in that any two Fraïssé limits are isomorphic. -/
theorem nonempty_equiv : Nonempty (M ≃[L] N) := by
  let S : L.Substructure M := ⊥
  have S_fg : FG L S := (fg_iff_structure_fg _).1 Substructure.fg_bot
  obtain ⟨_, ⟨emb_S : S ↪[L] N⟩⟩ : ⟨S, inferInstance⟩ ∈ L.age N := by
    rw [hN.age, ← hM.age]
    exact ⟨S_fg, ⟨subtype _⟩⟩
  let v : M ≃ₚ[L] N := {
    dom := S
    cod := emb_S.toHom.range
    toEquiv := emb_S.equivRange
  }
  exact ⟨Exists.choose (equiv_between_cg cg_of_countable cg_of_countable
    ⟨v, ((Substructure.fg_iff_structure_fg _).2 S_fg)⟩ (hM.isExtensionPair hN)
      (hN.isExtensionPair hM))⟩

end IsFraisseLimit

namespace empty

/-- Any countable infinite structure in the empty language is a Fraïssé limit of the class of finite
structures. -/
theorem isFraisseLimit_of_countable_infinite
    (M : Type*) [Countable M] [Infinite M] [Language.empty.Structure M] :
    IsFraisseLimit { S : Bundled Language.empty.Structure | Finite S } M where
  age := by
    ext S
    simp only [age, Structure.fg_iff_finite, mem_setOf_eq, and_iff_left_iff_imp]
    intro hS
    simp
  ultrahomogeneous S hS f := by
    classical
    have : Finite S := hS.finite
    have : Infinite { x // x ∉ S } := ((Set.toFinite _).infinite_compl).to_subtype
    have : Finite f.toHom.range := (((Substructure.fg_iff_structure_fg S).1 hS).range _).finite
    have : Infinite { x // x ∉ f.toHom.range } := ((Set.toFinite _).infinite_compl).to_subtype
    refine ⟨StrongHomClass.toEquiv (f.equivRange.subtypeCongr nonempty_equiv_of_countable.some), ?_⟩
    ext x
    simp [Equiv.subtypeCongr]

/-- The class of finite structures in the empty language is Fraïssé. -/
theorem isFraisse_finite : IsFraisse { S : Bundled.{w} Language.empty.Structure | Finite S } := by
  have : Language.empty.Structure (ULift ℕ : Type w) := emptyStructure
  exact (isFraisseLimit_of_countable_infinite (ULift ℕ)).isFraisse

end empty

end Language

end FirstOrder
