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
- `FirstOrder.Language.IsFraisse` indicates that a class is nonempty, isomorphism-invariant,
  essentially countable, and satisfies the hereditary, joint embedding, and amalgamation properties.
- `FirstOrder.Language.IsFraisseLimit` indicates that a structure is a Fraïssé limit for a given
  class.

## Main Results

- We show that the age of any structure is isomorphism-invariant and satisfies the hereditary and
  joint-embedding properties.
- `FirstOrder.Language.age.countable_quotient` shows that the age of any countable structure is
  essentially countable.
- `FirstOrder.Language.exists_countable_is_age_of_iff` gives necessary and sufficient conditions
  for a class to be the age of a countable structure in a language with countably many functions.
- `FirstOrder.Language.IsFraisseLimit.nonempty_equiv` shows that any class which is Fraïsse has
  at most one Fraïsse limit up to equivalence.

## Implementation Notes

- Classes of structures are formalized with `Set (Bundled L.Structure)`.
- Some results pertain to countable limit structures, others to countably-generated limit
  structures. In the case of a language with countably many function symbols, these are equivalent.

## References

- [W. Hodges, *A Shorter Model Theory*][Hodges97]
- [K. Tent, M. Ziegler, *A Course in Model Theory*][Tent_Ziegler]

## TODO

- Show existence and uniqueness of Fraïssé limits

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

variable {L}
variable (K : Set (Bundled.{w} L.Structure))

/-- A class `K` has the hereditary property when all finitely-generated structures that embed into
  structures in `K` are also in `K`.  -/
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

/-- A Fraïssé class is a nonempty, isomorphism-invariant, essentially countable class of structures
satisfying the hereditary, joint embedding, and amalgamation properties. -/
class IsFraisse : Prop where
  is_nonempty : K.Nonempty
  FG : ∀ M : Bundled.{w} L.Structure, M ∈ K → Structure.FG L M
  is_equiv_invariant : ∀ M N : Bundled.{w} L.Structure, Nonempty (M ≃[L] N) → (M ∈ K ↔ N ∈ K)
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

variable {M}

theorem age.fg_substructure {S : L.Substructure M} (fg : S.FG) : Bundled.mk S ∈ L.age M := by
  exact ⟨(Substructure.fg_iff_structure_fg _).1 fg, ⟨subtype _⟩⟩

variable (M)

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
    have : P ≈ N := by apply Quotient.eq'.mp; rw [hP2]; rfl -- Porting note: added
    refine ⟨s.image PM, Setoid.trans (b := P) ?_ this⟩
    rw [← Embedding.coe_toHom, Finset.coe_image, closure_image PM.toHom, hs, ← Hom.range_eq_map]
    exact ⟨PM.equivRange.symm⟩

/-- The age of a direct limit of structures is the union of the ages of the structures. -/
-- @[simp] -- Porting note: cannot simplify itself
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
      DirectLimit.equiv_iff G f _ (hi (out x).1 (Finset.mem_image_of_mem _ hx)),
      DirectedSystem.map_self]
    rfl
  · rintro ⟨i, Mfg, ⟨e⟩⟩
    exact ⟨Mfg, ⟨Embedding.comp (DirectLimit.of L ι G f i) e⟩⟩

/-- Sufficient conditions for a class to be the age of a countably-generated structure. -/
theorem exists_cg_is_age_of (hn : K.Nonempty)
    (h : ∀ M N : Bundled.{w} L.Structure, Nonempty (M ≃[L] N) → (M ∈ K ↔ N ∈ K))
    (hc : (Quotient.mk' '' K).Countable)
    (fg : ∀ M : Bundled.{w} L.Structure, M ∈ K → Structure.FG L M) (hp : Hereditary K)
    (jep : JointEmbedding K) : ∃ M : Bundled.{w} L.Structure, Structure.CG L M ∧ L.age M = K := by
  obtain ⟨F, hF⟩ := hc.exists_eq_range (hn.image _)
  simp only [Set.ext_iff, Quotient.forall, mem_image, mem_range, Quotient.eq'] at hF
  simp_rw [Quotient.eq_mk_iff_out] at hF
  have hF' : ∀ n : ℕ, (F n).out ∈ K := by
    intro n
    obtain ⟨P, hP1, hP2⟩ := (hF (F n).out).2 ⟨n, Setoid.refl _⟩
    -- Porting note: fix hP2 because `Quotient.out (Quotient.mk' x) ≈ a` was not simplified
    -- to `x ≈ a` in hF
    replace hP2 := Setoid.trans (Setoid.symm (Quotient.mk_out P)) hP2
    exact (h _ _ hP2).1 hP1
  choose P hPK hP hFP using fun (N : K) (n : ℕ) => jep N N.2 (F (n + 1)).out (hF' _)
  let G : ℕ → K := @Nat.rec (fun _ => K) ⟨(F 0).out, hF' 0⟩ fun n N => ⟨P N n, hPK N n⟩
  -- Poting note: was
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
    cases' n with n
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
  · rintro ⟨Kn, eqinv, cq, hfg, hp, jep⟩
    obtain ⟨M, hM, rfl⟩ := exists_cg_is_age_of Kn eqinv cq hfg hp jep
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
  simp only [Embedding.comp_apply, Hom.comp_apply,
    Equiv.coe_toHom, Embedding.coe_toHom, coeSubtype] at eq'
  simp only [Embedding.comp_apply, ← eq', Equiv.coe_toEmbedding, EmbeddingLike.apply_eq_iff_eq]
  apply (Embedding.equivRange (Embedding.comp r g)).injective
  ext
  simp only [Equiv.apply_symm_apply, Embedding.equivRange_apply, s]

/-- A countably generated structure is ultrahomogeneous if and only if any equivalence between
finitely generated substructures can be extended to any element in the domain.-/
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
    simp only [Embedding.comp_apply, Equiv.coe_toEmbedding, coeSubtype, eq_f',
      Embedding.equivRange_apply, Substructure.coe_inclusion, EmbeddingLike.apply_eq_iff_eq]
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
    Substructure.coeSubtype, Embedding.equivRange_apply] at hgn
  simp only [Embedding.comp_apply, Equiv.coe_toEmbedding]
  erw [Substructure.coe_inclusion, Substructure.coe_inclusion]
  simp only [Embedding.comp_apply, Equiv.coe_toEmbedding, Set.coe_inclusion,
    Embedding.equivRange_apply, hgn]
  -- This used to be `simp only [...]` before leanprover/lean4#2644
  erw [Embedding.comp_apply, Equiv.coe_toEmbedding,
    Embedding.equivRange_apply]
  simp

theorem IsUltrahomogeneous.age_isFraisse [Countable M] (h : L.IsUltrahomogeneous M) :
    IsFraisse (L.age M) :=
  ⟨age.nonempty M, fun _ hN => hN.1, age.is_equiv_invariant L M, age.countable_quotient M,
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
  simp [Subtype.mk_le_mk, PartialEquiv.le_def, g_eq]

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

variable {K} {N : Type w} [L.Structure N]
variable [Countable (Σ l, L.Functions l)] [Countable M] [Countable N]

instance [K_fraisse : IsFraisse K] : Nonempty ↑(Quotient.mk' '' K) :=
  (K_fraisse.is_nonempty.image Quotient.mk').coe_sort

instance [K_fraisse : IsFraisse K] : ∀ S : K, Countable S :=
  fun S ↦ Structure.cg_iff_countable.mp (K_fraisse.FG _ S.prop).cg

variable (K_fraisse : IsFraisse K)

/-- An essentially surjective sequence of L.structures in a Fraisse class. -/
noncomputable def ess_surj_sequence : ℕ → K := by
  intro n
  let l' n := (countable_iff_exists_surjective.1
    (countable_coe_iff.2 K_fraisse.is_essentially_countable)).choose n
  let A := (Quot.out (l' n).1)
  have A_in_K : A ∈ K := by
    let ⟨V, V_in_K, quot_V⟩ := (mem_image Quotient.mk' K _).1 (l' n).2
    have : Nonempty (V ≃[L] A) := by
      show V ≈ A
      apply Quotient.exact
      convert quot_V
      apply Quot.out_eq
    exact (K_fraisse.is_equiv_invariant _ _ this).1 V_in_K
  exact ⟨A, A_in_K⟩

theorem ess_surj_sequence_spec : ∀ V : K, ∃ n,
    Nonempty (V ≃[L] ess_surj_sequence K_fraisse n) := by
  rintro ⟨V, V_in_K⟩
  simp only
  let ⟨n, n_prop⟩ := (countable_iff_exists_surjective.1
    (countable_coe_iff.2 K_fraisse.is_essentially_countable)).choose_spec
      ⟨Quotient.mk' V, mem_image_of_mem _ V_in_K⟩
  use n
  show V ≈ (ess_surj_sequence K_fraisse n)
  apply Quotient.exact
  convert (congr_arg (Subtype.val) n_prop).symm
  apply Quot.out_eq

noncomputable def sequence_FGEquiv (A : K) (n : ℕ) : FGEquiv L A A :=
  (countable_iff_exists_surjective.1 (countable_self_fgequiv_of_countable (L := L))).choose n

theorem sequence_FGEquiv_spec {A : K} (f : FGEquiv L A A) :
    ∃ n, f = sequence_FGEquiv K_fraisse A n := by
  let ⟨m, hm⟩ := (countable_iff_exists_surjective.1
    (countable_self_fgequiv_of_countable (L := L))).choose_spec f
  use m
  exact hm.symm

include K_fraisse in

theorem can_extend_finiteEquiv_in_class : ∀ S : K, ∀ f : S ≃ₚ[L] S, ∀ _ : f.dom.FG,
    ∃ T : K, ∃ incl : S ↪[L] T, ∃ g : T ≃ₚ[L] T,
    f.map incl ≤ g ∧ incl.toHom.range ≤ g.dom := by
  rintro ⟨S, S_in_K⟩ f f_fg
  obtain ⟨R, g₁, g₂, R_in_K, eq⟩ := K_fraisse.amalgamation (Bundled.mk f.dom) S S
    (subtype _) ((subtype _).comp f.toEquiv.toEmbedding) (K_fraisse.hereditary S S_in_K
      (age.fg_substructure f_fg)) S_in_K S_in_K
  use ⟨R, R_in_K⟩
  use g₂
  use ⟨g₂.toHom.range, g₁.toHom.range, g₁.equivRange.comp g₂.equivRange.symm⟩
  simp only [le_refl, and_true, PartialEquiv.le_def, PartialEquiv.map_dom]
  use Hom.map_le_range
  ext ⟨x, x_prop⟩
  let ⟨y, y_in_dom_f, eq_xy⟩ := Substructure.mem_map.1 x_prop
  apply_fun (fun f ↦ f ⟨y, y_in_dom_f⟩) at eq
  simp only [Embedding.comp_apply, coeSubtype, Equiv.coe_toEmbedding] at eq
  cases eq_xy
  change g₁ ((g₂.equivRange.symm (g₂.equivRange y))) = _
  simp only [Equiv.symm_apply_apply, eq, PartialEquiv.map_cod, Embedding.coe_toHom,
    Embedding.comp_apply, Equiv.coe_toEmbedding, coeSubtype, map_coe]
  have := PartialEquiv.map_commutes_apply g₂ f ⟨y, y_in_dom_f⟩
  simp only [PartialEquiv.map_cod, PartialEquiv.map_dom] at this
  rw [this]

noncomputable def extend_finiteEquiv_in_class (S : K) (f : S ≃ₚ[L] S) (f_fg : f.dom.FG) :
    (T : K) × (incl : S ↪[L] T) × (g : T ≃ₚ[L] T) ×'
    f.map incl ≤ g ∧ incl.toHom.range ≤ g.dom := by
  choose a b c d using can_extend_finiteEquiv_in_class K_fraisse
  exact ⟨a S f f_fg, b .., c .., d ..⟩

noncomputable def join (S : K) (T : K) : (U : K) × (S ↪[L] U) × (T ↪[L] U) := by
  let h := K_fraisse.jointEmbedding S S.prop T T.prop
  exact ⟨⟨h.choose, h.choose_spec.1⟩, Classical.choice h.choose_spec.2.1,
    Classical.choice h.choose_spec.2.2⟩

noncomputable def extend_and_join (B : K) {A : K} {f : A ≃ₚ[L] A} (f_fg : f.dom.FG) :
    (C : K) × (A ↪[L] C) := by
  let ⟨C', A_to_C', _, _⟩ := extend_finiteEquiv_in_class K_fraisse A f f_fg
  let ⟨C, C'_to_C, _⟩ := join K_fraisse C' B
  exact ⟨C, C'_to_C.comp A_to_C'⟩

theorem extend_and_join_spec_1 {A : K} (B : K) {f : A ≃ₚ[L] A} (f_fg : f.dom.FG) :
    f.is_extended_by (extend_and_join K_fraisse B f_fg).2 := by
  apply PartialEquiv.is_extended_by_comp
  show f.is_extended_by (extend_finiteEquiv_in_class K_fraisse A f f_fg).2.1
  let ⟨C, A_to_C, g, le_g, le_g_dom⟩ := extend_finiteEquiv_in_class K_fraisse A f f_fg
  exact ⟨g, le_g, le_g_dom⟩

theorem extend_and_join_spec_2 (A B : K) {f : A ≃ₚ[L] A} (f_fg : f.dom.FG) :
    Nonempty (B ↪[L] (extend_and_join K_fraisse B f_fg).1) := ⟨(join K_fraisse _ B).2.2⟩

noncomputable def init_system : (n : ℕ) →
    (A : K) × (ℕ → (B : K) × (B ↪[L] A))
  | 0 => ⟨ess_surj_sequence K_fraisse 0,
    fun _ => ⟨_, Embedding.refl L _⟩⟩
  | n + 1 => by
    let m1 := (Nat.unpair n).1
    let m2 := (Nat.unpair n).2
    let An := (init_system n).1
    let Sn := (init_system n).2
    let Am1 := (Sn m1).1
    let Am1_to_An : Am1 ↪[L] An := (Sn m1).2
    let ⟨f, f_fg⟩ := sequence_FGEquiv K_fraisse Am1 m2
    let ⟨A, An_to_A⟩ := extend_and_join K_fraisse
      (A := An) (B := ess_surj_sequence K_fraisse (n+1))
        (f := f.map Am1_to_An) (PartialEquiv.map_dom Am1_to_An f ▸ FG.map _ f_fg)
    exact ⟨A, fun m ↦ if m ≤ n then ⟨(Sn m).1, An_to_A.comp ((Sn m).2)⟩
                        else ⟨_, Embedding.eq_embed (rfl)⟩⟩

noncomputable def system : ℕ → K :=
  fun n ↦ (init_system K_fraisse n).1

theorem system_eq {n : ℕ} {m : ℕ} (h : m ≤ n) :
    system K_fraisse m = ((init_system K_fraisse n).2 m).1 := by
  match n with
    | 0 =>
        cases h
        rfl'
    | n + 1 =>
          rw [init_system]
          simp only
          split
          · apply system_eq
            assumption
          · cases h
            rfl'
            contradiction

theorem system_eq' {n : ℕ} {m : ℕ} (h : m ≤ n) :
    (system K_fraisse m : Bundled.{w} L.Structure) = ((init_system K_fraisse n).2 m).1 :=
    congr_arg _ (system_eq K_fraisse h)

noncomputable def maps_system {m n : ℕ} (h : m ≤ n): system K_fraisse m ↪[L] system K_fraisse n :=
  ((init_system K_fraisse n).2 m).2.comp (Embedding.eq_embed (system_eq' K_fraisse h))

theorem map_from_eq_dep_pair {C : K} {P Q : (B : K) × (B ↪[L] C)} (h : P = Q) :
    P.2 = Q.2.comp (Embedding.eq_embed (congr_arg _ (congr_arg Sigma.fst h))) := by
  cases h
  rfl

theorem if_then_else_left_struct {A B C: K} {P : Prop} [Decidable P] (f : A ↪[L] C)
    (g : B ↪[L] C) (h : P = True) :
      (if P then (⟨A, f⟩ : (B : K) × (B ↪[L] C)) else ⟨B, g⟩).1 = A := by
  simp only [h, ↓reduceIte]

theorem if_then_else_left {A B C: K} {P : Prop} [Decidable P] (f : A ↪[L] C)
    (g : B ↪[L] C) (h : P = True) :
      (if P then (⟨A, f⟩ : (B : K) × (B ↪[L] C)) else ⟨B, g⟩).2 =
        f.comp (Embedding.eq_embed (congr_arg _ (if_then_else_left_struct f g h))):= by
  have h' : (if P then (⟨A, f⟩ : (B : K) × (B ↪[L] C)) else ⟨B, g⟩) = ⟨A, f⟩ := by
    simp [h]
  apply map_from_eq_dep_pair h'

theorem if_then_else_right_struct {A B C: K} {P : Prop} [Decidable P] (f : A ↪[L] C)
    (g : B ↪[L] C) (h : P = False) :
      (if P then (⟨A, f⟩ : (B : K) × (B ↪[L] C)) else ⟨B, g⟩).1 = B := by
  simp only [h, ↓reduceIte]

theorem if_then_else_right {A B C: K} {P : Prop} [Decidable P] (f : A ↪[L] C)
    (g : B ↪[L] C) (h : P = False) :
      (if P then (⟨A, f⟩ : (B : K) × (B ↪[L] C)) else ⟨B, g⟩).2 =
        g.comp (Embedding.eq_embed (congr_arg _ (if_then_else_right_struct f g h))):= by
  have h' : (if P then (⟨A, f⟩ : (B : K) × (B ↪[L] C)) else ⟨B, g⟩) = ⟨B, g⟩ := by
    simp [h]
  apply map_from_eq_dep_pair h'

theorem maps_system_same_step (m : ℕ) : maps_system K_fraisse (le_refl m)
    = Embedding.refl L _ := by
  cases m
  rfl'
  rename_i m
  unfold maps_system
  simp_rw [init_system]
  have u : ∀ (n : ℕ), ((n+1 ≤ n) = False) := by intro n; simp
  conv =>
    lhs
    congr
    rw [if_then_else_right]
    simp
    · skip
    · exact u m
  simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero,
    Embedding.eq_embed_trans]
  rfl

theorem maps_system_same_step' (m : ℕ) : ((init_system K_fraisse m).2 m).2 =
    Embedding.eq_embed (system_eq' K_fraisse (le_refl m)).symm := by
  cases m
  rfl
  rename_i m
  simp_rw [init_system]
  have u : ∀ (n : ℕ), ((n+1 ≤ n) = False) := by intro n; simp
  conv =>
    lhs
    rw [if_then_else_right]
    simp
    · skip
    · exact u m

noncomputable def FGEquiv_extended (n : ℕ) :
    FGEquiv L ((init_system K_fraisse n).2 (Nat.unpair n).1).1
      ((init_system K_fraisse n).2 (Nat.unpair n).1).1 :=
  sequence_FGEquiv K_fraisse ((init_system K_fraisse n).2 (Nat.unpair n).1).1 (Nat.unpair n).2

theorem init_system_map_decomposition {k r : ℕ} (h : k ≤ r) :
    ((init_system K_fraisse (r+1)).2 k).2 =
    ((extend_and_join K_fraisse (ess_surj_sequence K_fraisse (r+1))
      (f := ((FGEquiv_extended K_fraisse r).1.map
        ((init_system K_fraisse r).2 (Nat.unpair r).1).2))
      (PartialEquiv.map_dom (((init_system K_fraisse r).2
        (Nat.unpair r).1).2) _ ▸ FG.map _ (FGEquiv_extended K_fraisse r).2)).2
    ).comp
      (((init_system K_fraisse r).2 k).2.comp
        (Embedding.eq_embed ((system_eq' K_fraisse (h.trans (Nat.le_add_right r 1))).symm.trans
          (system_eq' K_fraisse h)))) := by
  apply if_then_else_left
  simp only [h]

noncomputable def map_step (m : ℕ) : system K_fraisse m ↪[L] system K_fraisse (m+1) :=
  maps_system K_fraisse (Nat.le_add_right m 1)

theorem factorize_with_map_step {m n : ℕ} (h : m ≤ n) :
    maps_system K_fraisse (h.trans (Nat.le_add_right n 1)) =
      (map_step K_fraisse n).comp (maps_system K_fraisse h) := by
  rw [map_step]
  simp only [maps_system]
  rw [init_system_map_decomposition, init_system_map_decomposition]
  case h => trivial
  case h => assumption
  rw [maps_system_same_step', Embedding.eq_embed_trans]
  simp only [PartialEquiv.map_dom, Embedding.comp_assoc, Embedding.eq_embed_trans,
    Embedding.refl_eq_embed, Embedding.comp_refl]

theorem transitive_maps_system {m n k : ℕ} (h : m ≤ n) (h' : n ≤ k) :
    (maps_system K_fraisse h').comp (maps_system K_fraisse h) =
      maps_system K_fraisse (h.trans h') := by
  match k with
  | 0 =>
      cases h'
      cases h
      rfl
  | k+1 =>
      cases h'
      · simp [maps_system_same_step]
      · rename_i h'
        rw [factorize_with_map_step, map_step, Embedding.comp_assoc,
            transitive_maps_system h h', ←map_step, ←factorize_with_map_step]

theorem map_step_is_extend_and_join (r : ℕ) :
    map_step K_fraisse r = ((extend_and_join K_fraisse (ess_surj_sequence K_fraisse (r+1))
      (f := ((FGEquiv_extended K_fraisse r).1.map
        ((init_system K_fraisse r).2 (Nat.unpair r).1).2))
      (PartialEquiv.map_dom (((init_system K_fraisse r).2
        (Nat.unpair r).1).2) _ ▸ FG.map _ (FGEquiv_extended K_fraisse r).2)).2) := by
  rw [map_step, maps_system, init_system_map_decomposition]
  simp [Embedding.comp_assoc]
  rw [←maps_system, maps_system_same_step, Embedding.comp_refl]
  rfl

theorem all_fgequiv_extend {m : ℕ} : ∀ f : L.FGEquiv (system _ m) (system _ m),
    ∃ n, ∃ h : m ≤ n, f.val.is_extended_by (maps_system K_fraisse h) := by
  intro f
  let ⟨n, hn⟩ := sequence_FGEquiv_spec K_fraisse f
  let r := Nat.pair m n
  have h_unpair_m : m = (Nat.unpair r).1 := by simp [r]
  have h_unpair_n : n = (Nat.unpair r).2 := by simp [r]
  let f'' := FGEquiv_extended K_fraisse r
  clear_value r
  cases h_unpair_m
  let f' := f.1.map (Embedding.eq_embed (system_eq' K_fraisse (Nat.unpair_left_le r)))
  have f'_fg : f'.dom.FG := f.1.map_fg _ f.2
  cases h_unpair_n
  cases hn
  have h_f'_f'' : f' = f'' := by
    have H : ∀ (A B : K), ∀ (h : A = B),
        (sequence_FGEquiv K_fraisse A (Nat.unpair r).2).val.map
          (Embedding.eq_embed (congr_arg Subtype.val h)) =
        (sequence_FGEquiv K_fraisse B (Nat.unpair r).2).val := by
      intro A B h
      cases h
      simp
    exact H _ _ (system_eq K_fraisse (Nat.unpair_left_le r))
  use r+1
  use (Nat.unpair_left_le r).trans (Nat.le_add_right r 1)
  rw [←transitive_maps_system K_fraisse (Nat.unpair_left_le r) (Nat.le_add_right r 1)]
  apply PartialEquiv.comp_is_extended_by
  have H : f'.map ((init_system _ r).2 (Nat.unpair r).1).2 =
      (sequence_FGEquiv K_fraisse (system K_fraisse (Nat.unpair r).1) (Nat.unpair r).2).1.map
        (maps_system _ (Nat.unpair_left_le r)) := by
      unfold_let f'
      rw [PartialEquiv.map_map]
      rfl
  rw [←H, h_f'_f'', ←map_step, map_step_is_extend_and_join]
  unfold_let f''
  apply extend_and_join_spec_1

theorem contains_K : ∀ M ∈ K, ∃ n, Nonempty (M ↪[L] system K_fraisse n) := by
  intro A h
  let ⟨n, ⟨g⟩⟩ := ess_surj_sequence_spec K_fraisse ⟨A, h⟩
  use n
  refine ⟨?_⟩
  apply fun f ↦ Embedding.comp f g.toEmbedding
  cases n
  · trivial
  · simp [system, init_system]
    apply Classical.choice
    apply extend_and_join_spec_2

include K_fraisse in

theorem exists_fraisse_limit : ∃ M : Bundled.{w} L.Structure, ∃ _ : Countable M,
    IsFraisseLimit K M := by
  let _ : (i : ℕ) → L.Structure ((Bundled.α ∘ Subtype.val ∘ system K_fraisse) i) :=
    fun i => Bundled.str _
  have _ : DirectedSystem (Bundled.α ∘ Subtype.val ∘ system K_fraisse)
      fun i j h ↦ ⇑(maps_system K_fraisse h) := by
    constructor
    intro _ _ _
    simp [maps_system_same_step]
    intro i j k hij hjk x
    simp [←Embedding.comp_apply, transitive_maps_system]
  let M := DirectLimit (L := L) (Bundled.α ∘ Subtype.val ∘ system K_fraisse)
    (@maps_system _ _ _ K_fraisse)
  use ⟨M, DirectLimit.instStructureDirectLimit ..⟩
  have M_c : Countable M := by
    rw [←Structure.cg_iff_countable (L := L)]
    apply DirectLimit.cg
    simp [Function.comp_apply, Structure.cg_of_countable, implies_true]
  use M_c
  let of : (n : ℕ) → (system K_fraisse n ↪[L] M) :=
    fun n ↦ DirectLimit.of L ℕ (Bundled.α ∘ Subtype.val ∘ system K_fraisse) _ n
  refine ⟨?_, ?_⟩
  · rw [isUltrahomogeneous_iff_IsExtensionPair]
    simp
    unfold IsExtensionPair
    intro ⟨f, f_fg⟩ m
    let A := f.dom ⊔ f.cod ⊔ (closure L {m})
    let A_fg : A.FG := FG.sup (FG.sup f_fg (f.dom_fg_iff_cod_fg.1 f_fg)) (fg_closure_singleton m)
    let ⟨n, A', hA'⟩ := DirectLimit.exists_fg_substructure_in_Sigma A A_fg
    have in_range : f.dom ⊔ f.cod ⊔ (closure L {m}) ≤ (of n).toHom.range := by
      show A ≤ _
      rw [←hA']
      exact Hom.map_le_range
    let ⟨f',f'_map⟩ := (PartialEquiv.exists_preimage_map_iff (of n) f).2
      (le_sup_left.trans in_range)
    have f'_fg : f'.dom.FG := by
      apply FG.of_map_embedding (of n)
      rwa [←PartialEquiv.map_dom, f'_map]
    have H : f'.is_extended_by (of n) := by
      let ⟨m, hnm, f'_extended⟩ := all_fgequiv_extend K_fraisse ⟨f', f'_fg⟩
      unfold_let of
      simp
      rw [←DirectLimit.of_comp_f (hij := hnm)]
      exact PartialEquiv.is_extended_by_comp _ _ _ f'_extended
    let ⟨g', map_f'_le, range_le_g'⟩ := H
    let g := g'.domRestrict (in_range.trans range_le_g')
    have g_fg : g.dom.FG := by
      unfold_let g
      unfold PartialEquiv.domRestrict
      simpa
    have f_le_g : (⟨f, f_fg⟩ : FGEquiv L M M) ≤ ⟨g, g_fg⟩ := by
      rw [Subtype.mk_le_mk]
      apply PartialEquiv.le_domRestrict
      exact le_sup_left.trans le_sup_left
      rw [f'_map] at map_f'_le
      exact map_f'_le
    have m_in_dom : m ∈ g.dom := by
      unfold_let g
      unfold PartialEquiv.domRestrict
      simp
      rw [←closure_eq f.dom, ←closure_eq f.cod, ←closure_union, ←closure_union]
      apply subset_closure
      exact mem_union_right (f.dom ∪ (f.cod : Set M)) rfl
    use ⟨g, g_fg⟩
    exact Structure.cg_of_countable
  · rw [age_directLimit]
    apply Set.ext
    intro S
    rw [mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨i, S_in_age⟩
      exact K_fraisse.hereditary ((Subtype.val ∘ system K_fraisse) i)
        (by simp only [Function.comp_apply, Subtype.coe_prop]) S_in_age
    · intro S_in_K
      let ⟨n, ⟨inc_S⟩⟩ := contains_K K_fraisse S S_in_K
      use n
      simp only [age, Function.comp_apply, mem_setOf_eq]
      refine ⟨IsFraisse.FG S S_in_K, ⟨inc_S⟩⟩

end Language

end FirstOrder
