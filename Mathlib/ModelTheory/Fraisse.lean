/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Gabin Kolly
-/
import Mathlib.ModelTheory.FinitelyGenerated
import Mathlib.ModelTheory.DirectLimit
import Mathlib.ModelTheory.Bundled

#align_import model_theory.fraisse from "leanprover-community/mathlib"@"0602c59878ff3d5f71dea69c2d32ccf2e93e5398"

/-!
# Fraïssé Classes and Fraïssé Limits

This file pertains to the ages of countable first-order structures. The age of a structure is the
class of all finitely-generated structures that embed into it.

Of particular interest are Fraïssé classes, which are exactly the ages of countable
ultrahomogeneous structures. To each is associated a unique (up to nonunique isomorphism)
Fraïssé limit - the countable ultrahomogeneous structure with that age.

## Main Definitions
* `FirstOrder.Language.age` is the class of finitely-generated structures that embed into a
particular structure.
* A class `K` is `FirstOrder.Language.Hereditary` when all finitely-generated
structures that embed into structures in `K` are also in `K`.
* A class `K` has `FirstOrder.Language.JointEmbedding` when for every `M`, `N` in
`K`, there is another structure in `K` into which both `M` and `N` embed.
* A class `K` has `FirstOrder.Language.Amalgamation` when for any pair of embeddings
of a structure `M` in `K` into other structures in `K`, those two structures can be embedded into a
fourth structure in `K` such that the resulting square of embeddings commutes.
* `FirstOrder.Language.IsFraisse` indicates that a class is nonempty, isomorphism-invariant,
essentially countable, and satisfies the hereditary, joint embedding, and amalgamation properties.
* `FirstOrder.Language.IsFraisseLimit` indicates that a structure is a Fraïssé limit for a given
class.

## Main Results
* We show that the age of any structure is isomorphism-invariant and satisfies the hereditary and
joint-embedding properties.
* `FirstOrder.Language.age.countable_quotient` shows that the age of any countable structure is
essentially countable.
* `FirstOrder.Language.exists_countable_is_age_of_iff` gives necessary and sufficient conditions
for a class to be the age of a countable structure in a language with countably many functions.
* `FirstOrder.Language.IsFraisseLimit.unique_FraisseLimit` shows that any class which is Fraïsse has
  at most one Fraïsse limit up to equivalence.

## Implementation Notes
* Classes of structures are formalized with `Set (Bundled L.Structure)`.
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
    M ∈ K → N ∈ K → P ∈ K → ∃ (Q : Bundled.{w} L.Structure) (NQ : N ↪[L] Q) (PQ : P ↪[L] Q),
      Q ∈ K ∧ NQ.comp MN = PQ.comp MP
#align first_order.language.amalgamation FirstOrder.Language.Amalgamation

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
#align first_order.language.is_fraisse FirstOrder.Language.IsFraisse

variable {K} (L) (M : Type w) [Structure L M]

theorem age.is_equiv_invariant (N P : Bundled.{w} L.Structure) (h : Nonempty (N ≃[L] P)) :
    N ∈ L.age M ↔ P ∈ L.age M :=
  and_congr h.some.fg_iff
    ⟨Nonempty.map fun x => Embedding.comp x h.some.symm.toEmbedding,
      Nonempty.map fun x => Embedding.comp x h.some.toEmbedding⟩
#align first_order.language.age.is_equiv_invariant FirstOrder.Language.age.is_equiv_invariant

variable {L} {M} {N : Type w} [Structure L N]

theorem Embedding.age_subset_age (MN : M ↪[L] N) : L.age M ⊆ L.age N := fun _ =>
  And.imp_right (Nonempty.map MN.comp)
#align first_order.language.embedding.age_subset_age FirstOrder.Language.Embedding.age_subset_age

theorem Equiv.age_eq_age (MN : M ≃[L] N) : L.age M = L.age N :=
  le_antisymm MN.toEmbedding.age_subset_age MN.symm.toEmbedding.age_subset_age
#align first_order.language.equiv.age_eq_age FirstOrder.Language.Equiv.age_eq_age

theorem Structure.FG.mem_age_of_equiv {M N : Bundled L.Structure} (h : Structure.FG L M)
    (MN : Nonempty (M ≃[L] N)) : N ∈ L.age M :=
  ⟨MN.some.fg_iff.1 h, ⟨MN.some.symm.toEmbedding⟩⟩
set_option linter.uppercaseLean3 false in
#align first_order.language.Structure.fg.mem_age_of_equiv FirstOrder.Language.Structure.FG.mem_age_of_equiv

theorem Hereditary.is_equiv_invariant_of_fg (h : Hereditary K)
    (fg : ∀ M : Bundled.{w} L.Structure, M ∈ K → Structure.FG L M) (M N : Bundled.{w} L.Structure)
    (hn : Nonempty (M ≃[L] N)) : M ∈ K ↔ N ∈ K :=
  ⟨fun MK => h M MK ((fg M MK).mem_age_of_equiv hn),
   fun NK => h N NK ((fg N NK).mem_age_of_equiv ⟨hn.some.symm⟩)⟩
#align first_order.language.hereditary.is_equiv_invariant_of_fg FirstOrder.Language.Hereditary.is_equiv_invariant_of_fg

variable (M)

theorem age.nonempty : (L.age M).Nonempty :=
  ⟨Bundled.of (Substructure.closure L (∅ : Set M)),
    (fg_iff_structure_fg _).1 (fg_closure Set.finite_empty), ⟨Substructure.subtype _⟩⟩
#align first_order.language.age.nonempty FirstOrder.Language.age.nonempty

theorem age.hereditary : Hereditary (L.age M) := fun _ hN _ hP => hN.2.some.age_subset_age hP
#align first_order.language.age.hereditary FirstOrder.Language.age.hereditary

theorem age.jointEmbedding : JointEmbedding (L.age M) := fun _ hN _ hP =>
  ⟨Bundled.of (↥(hN.2.some.toHom.range ⊔ hP.2.some.toHom.range)),
    ⟨(fg_iff_structure_fg _).1 ((hN.1.range hN.2.some.toHom).sup (hP.1.range hP.2.some.toHom)),
      ⟨Substructure.subtype _⟩⟩,
    ⟨Embedding.comp (inclusion le_sup_left) hN.2.some.equivRange.toEmbedding⟩,
    ⟨Embedding.comp (inclusion le_sup_right) hP.2.some.equivRange.toEmbedding⟩⟩
#align first_order.language.age.joint_embedding FirstOrder.Language.age.jointEmbedding

variable {M}

theorem age.fg_substructure {S : L.Substructure M} (fg : S.FG) : Bundled.mk S ∈ L.age M := by
  exact ⟨(Substructure.fg_iff_structure_fg _).1 fg, ⟨subtype _⟩⟩

variable (M)

/-- Any class in the age of a structure has a representant which is a finitely generated
substructure. -/
theorem age.has_representant_as_substructure :
    ∀ C ∈ Quotient.mk' '' L.age M, ∃ V : {V : L.Substructure M // FG V},
      ⟦Bundled.mk V⟧ = C := by
  rintro _ ⟨N, ⟨N_fg, ⟨N_incl⟩⟩, N_eq⟩
  refine N_eq.symm ▸ ⟨⟨N_incl.toHom.range, ?_⟩, Quotient.sound ⟨N_incl.equivRange.symm⟩⟩
  exact FG.range N_fg (Embedding.toHom N_incl)

/-- The age of a countable structure is essentially countable (has countably many isomorphism
classes). -/
theorem age.countable_quotient [h : Countable M] : (Quotient.mk' '' L.age M).Countable := by
  rw [← countable_coe_iff]
  let f : Quotient.mk' '' L.age M → {V : L.Substructure M // FG V} :=
    fun ⟨C, C_in⟩ ↦ (age.has_representant_as_substructure M C C_in).choose
  have f_inj : Function.Injective f := by
    intro C C' h
    ext
    simp only at h
    exact (age.has_representant_as_substructure M C.1 C.2).choose_spec.symm.trans <|
      (by rw [h] : _ = _).trans (age.has_representant_as_substructure M C'.1 C'.2).choose_spec
  exact Function.Embedding.countable ⟨f, f_inj⟩
#align first_order.language.age.countable_quotient FirstOrder.Language.age.countable_quotient

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
    refine' ⟨i, Mfg, ⟨e'.comp ((Substructure.inclusion _).comp e.equivRange.toEmbedding)⟩⟩
    rw [← hs, closure_le]
    intro x hx
    refine' ⟨f (out x).1 i (hi (out x).1 (Finset.mem_image_of_mem _ hx)) (out x).2, _⟩
    rw [Embedding.coe_toHom, DirectLimit.of_apply, @Quotient.mk_eq_iff_out _ (_),
      DirectLimit.equiv_iff G f _ (hi (out x).1 (Finset.mem_image_of_mem _ hx)),
      DirectedSystem.map_self]
    rfl
  · rintro ⟨i, Mfg, ⟨e⟩⟩
    exact ⟨Mfg, ⟨Embedding.comp (DirectLimit.of L ι G f i) e⟩⟩
#align first_order.language.age_direct_limit FirstOrder.Language.age_directLimit

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
    exact (fun n => (hP _ n).some)
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
#align first_order.language.exists_cg_is_age_of FirstOrder.Language.exists_cg_is_age_of

theorem exists_countable_is_age_of_iff [Countable (Σ l, L.Functions l)] :
    (∃ M : Bundled.{w} L.Structure, Countable M ∧ L.age M = K) ↔
      K.Nonempty ∧ (∀ M N : Bundled.{w} L.Structure, Nonempty (M ≃[L] N) → (M ∈ K ↔ N ∈ K)) ∧
      (Quotient.mk' '' K).Countable ∧ (∀ M : Bundled.{w} L.Structure, M ∈ K → Structure.FG L M) ∧
      Hereditary K ∧ JointEmbedding K := by
  constructor
  · rintro ⟨M, h1, h2, rfl⟩
    refine' ⟨age.nonempty M, age.is_equiv_invariant L M, age.countable_quotient M, fun N hN => hN.1,
      age.hereditary M, age.jointEmbedding M⟩
  · rintro ⟨Kn, eqinv, cq, hfg, hp, jep⟩
    obtain ⟨M, hM, rfl⟩ := exists_cg_is_age_of Kn eqinv cq hfg hp jep
    exact ⟨M, Structure.cg_iff_countable.1 hM, rfl⟩
#align first_order.language.exists_countable_is_age_of_iff FirstOrder.Language.exists_countable_is_age_of_iff

variable (L)

/-- A structure `M` is ultrahomogeneous if every embedding of a finitely generated substructure
into `M` extends to an automorphism of `M`. -/
def IsUltrahomogeneous : Prop :=
  ∀ (S : L.Substructure M) (_ : S.FG) (f : S ↪[L] M),
    ∃ g : M ≃[L] M, f = g.toEmbedding.comp S.subtype
#align first_order.language.is_ultrahomogeneous FirstOrder.Language.IsUltrahomogeneous

variable {L} (K)

/-- A structure `M` is a Fraïssé limit for a class `K` if it is countably generated,
ultrahomogeneous, and has age `K`. -/
structure IsFraisseLimit [Countable (Σ l, L.Functions l)] [Countable M] : Prop where
  protected ultrahomogeneous : IsUltrahomogeneous L M
  protected age : L.age M = K
#align first_order.language.is_fraisse_limit FirstOrder.Language.IsFraisseLimit

variable {M}

/-- Any embedding from a finitely generated `S` to an ultrahomogeneous structure `M`
can be extended to an embedding from any structure with an embedding to `M`.-/
theorem IsUltrahomogeneous.extend_embedding (M_homog : L.IsUltrahomogeneous M) {S : Type*}
    [L.Structure S] (S_FG : FG L S) {T : Type*} [L.Structure T] [h : Nonempty (T ↪[L] M)]
    (f : S ↪[L] M) (g : S ↪[L] T) :
    ∃ f' : T ↪[L] M, f = f'.comp g := by
  let ⟨r⟩ := h
  let s := (r.comp g)
  let S'' := s.toHom.range
  let ⟨t, eq⟩ := M_homog S'' (S_FG.range s.toHom) (f.comp s.equivRange.symm.toEmbedding)
  use t.toEmbedding.comp r
  change _ = t.toEmbedding.comp s
  ext x
  have eq' := congr_fun (congr_arg DFunLike.coe eq) ⟨s x, Hom.mem_range.2 ⟨x, rfl⟩⟩
  simp only [Embedding.comp_apply, Hom.comp_apply,
    Equiv.coe_toHom, Embedding.coe_toHom, coeSubtype] at eq'
  simp only [Embedding.comp_apply, ← eq', Equiv.coe_toEmbedding, EmbeddingLike.apply_eq_iff_eq]
  apply (Embedding.equivRange (Embedding.comp r g)).injective
  simp only [Equiv.apply_symm_apply]
  rfl

/-- A countably generated structure is ultrahomogeneous if and only if any equivalence between
finitely generated substructures can be extended to any element in the domain.-/
theorem isUltrahomogeneous_iff_extend_finite_equiv (M_CG : CG L M) : L.IsUltrahomogeneous M ↔
    ∀ f : (M ≃ₚ[L] M), ∀ _ : f.sub_dom.FG, ∀ m : M, ∃ g : (M ≃ₚ[L] M), f ≤ g ∧ m ∈ g.sub_dom := by
  constructor
  · intro M_homog f f_FG m
    let S := closure L (f.sub_dom ∪ {m})
    have dom_le_S : f.sub_dom ≤ S := by
      simp only [closure_union, closure_eq, ge_iff_le, le_sup_left]
    let ⟨f', eq_f'⟩ := M_homog.extend_embedding (f.sub_dom.fg_iff_structure_fg.1 f_FG)
      ((subtype _).comp f.equiv.toEmbedding) (inclusion dom_le_S) (h := ⟨subtype _⟩)
    use ⟨S, f'.toHom.range, f'.equivRange⟩
    refine ⟨⟨dom_le_S, ?_⟩, by
      simp only [union_singleton]
      exact Substructure.subset_closure <| mem_insert_iff.2 <| Or.inl <| refl m⟩
    simp only
    rw [← Embedding.comp_assoc, Embedding.subtype_equivRange f', ← eq_f']
  · intro h S S_FG f
    let ⟨g, ⟨le_dom, eq⟩⟩ := BackAndForth.equiv_between_cg M_CG M_CG
      ⟨S, f.toHom.range, f.equivRange⟩ S_FG h (BackAndForth.back_iff_symm_of_forth.2 h)
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
  refine' ⟨Bundled.of s,
    Embedding.comp (Substructure.inclusion le_sup_left)
      (g.toEmbedding.comp PM).equivRange.toEmbedding,
    Embedding.comp (Substructure.inclusion le_sup_right) QM.equivRange.toEmbedding,
    ⟨(fg_iff_structure_fg _).1 (FG.sup (Pfg.range _) (Qfg.range _)), ⟨Substructure.subtype _⟩⟩, _⟩
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

variable {K} {N : Type w} [L.Structure N]
variable [Countable (Σ l, L.Functions l)] [Countable M] [Countable N]
variable (hM : IsFraisseLimit K M) (hN : IsFraisseLimit K N)

theorem extend_finite_SubEquiv :
    ∀ f : M ≃ₚ[L] N, ∀ _ : f.sub_dom.FG, ∀ m : M, ∃ g : (M ≃ₚ[L] N), f ≤ g ∧ m ∈ g.sub_dom := by
  intro f f_FG m
  let S := closure L (f.sub_dom ∪ {m})
  have dom_le_S : f.sub_dom ≤ S :=
    by simp only [closure_union, closure_eq, ge_iff_le, le_sup_left]
  have S_FG : FG L (closure L (f.sub_dom ∪ {m})) := by
    rw [← fg_iff_structure_fg, closure_union, closure_eq]
    exact Substructure.FG.sup f_FG (Substructure.fg_closure_singleton _)
  have S_in_age_N : ⟨S, inferInstance⟩ ∈ L.age N := by
    rw [hN.age, ← hM.age]
    exact ⟨S_FG, ⟨subtype _⟩⟩
  let nonempty_S_N : Nonempty (S ↪[L] N) := by
    let ⟨_, this⟩ := S_in_age_N
    exact this
  let ⟨g, eq⟩ := hN.ultrahomogeneous.extend_embedding (f.sub_dom.fg_iff_structure_fg.1 f_FG)
    ((subtype f.sub_cod).comp f.equiv.toEmbedding) (inclusion dom_le_S)
  refine ⟨⟨S, g.toHom.range, g.equivRange⟩, ?_, ?_⟩
  · rw [SubEquivalence.le_def]
    use dom_le_S
    rw [eq]
    rfl
  · simp only [union_singleton]
    exact Substructure.subset_closure <| mem_insert_iff.2 <| Or.inl <| refl m

theorem unique_FraisseLimit : Nonempty (M ≃[L] N) := by
  let S := closure L (∅ : Set M)
  have S_fg : FG L S := by
    simp [← fg_iff_structure_fg, Substructure.closure_empty]
    exact Substructure.fg_bot
  obtain ⟨_, ⟨emb_S : S ↪[L] N⟩⟩ : ⟨S, inferInstance⟩ ∈ L.age N := by
    rw [hN.age, ← hM.age]
    exact ⟨S_fg, ⟨subtype _⟩⟩
  let v : M ≃ₚ[L] N := {
    sub_dom := S
    sub_cod := emb_S.toHom.range
    equiv := emb_S.equivRange
  }
  exact ⟨Exists.choose (BackAndForth.equiv_between_cg (cg_of_countable) (cg_of_countable) v
    ((Substructure.fg_iff_structure_fg _).2 S_fg) (extend_finite_SubEquiv hM hN)
      (BackAndForth.back_iff_symm_of_forth.2 (extend_finite_SubEquiv hN hM)))⟩

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

theorem ess_surj_sequence_is_ess_surj : ∀ V : K, ∃ n,
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

theorem can_extend_finiteEquiv_in_class : ∀ S : K, ∀ f : S ≃ₚ[L] S, ∀ _ : f.sub_dom.FG,
    ∃ T : K, ∃ incl : S ↪[L] T, ∃ g : T ≃ₚ[L] T,
    f.map incl ≤ g ∧ incl.toHom.range ≤ g.sub_dom := by
  rintro ⟨S, S_in_K⟩ f f_fg
  obtain ⟨R, g₁, g₂, R_in_K, eq⟩ := K_fraisse.amalgamation (Bundled.mk f.sub_dom) S S
    (subtype _) ((subtype _).comp f.equiv.toEmbedding) (K_fraisse.hereditary S S_in_K
      (age.fg_substructure f_fg)) S_in_K S_in_K
  use ⟨R, R_in_K⟩
  use g₂
  use ⟨g₂.toHom.range, g₁.toHom.range, g₁.equivRange.comp g₂.equivRange.symm⟩
  simp only [le_refl, and_true, SubEquivalence.le_def, SubEquivalence.map_dom]
  use Hom.map_le_range
  ext ⟨x, x_prop⟩
  let ⟨y, y_in_dom_f, eq_xy⟩ := Substructure.mem_map.1 x_prop
  apply_fun (fun f ↦ f ⟨y, y_in_dom_f⟩) at eq
  simp only [Embedding.comp_apply, coeSubtype, Equiv.coe_toEmbedding] at eq
  cases eq_xy
  change g₁ ((g₂.equivRange.symm (g₂.equivRange y))) = _
  simp only [Equiv.symm_apply_apply, eq, SubEquivalence.map_cod, Embedding.coe_toHom,
    Embedding.comp_apply, Equiv.coe_toEmbedding, coeSubtype, map_coe]
  have := SubEquivalence.map_commutes_apply g₂ f ⟨y, y_in_dom_f⟩
  simp only [SubEquivalence.map_cod, SubEquivalence.map_dom] at this
  rw [this]

noncomputable def extend_finiteEquiv_in_class (S : K) (f : S ≃ₚ[L] S) (f_fg : f.sub_dom.FG) :
    (T : K) × (incl : S ↪[L] T) × (g : T ≃ₚ[L] T) ×'
    f.map incl ≤ g ∧ incl.toHom.range ≤ g.sub_dom := by
  choose a b c d using can_extend_finiteEquiv_in_class K_fraisse
  exact ⟨a S f f_fg, b .., c .., d ..⟩

noncomputable def join (S : K) (T : K) : (U : K) × (S ↪[L] U) × (T ↪[L] U) := by
  let h := K_fraisse.jointEmbedding S S.prop T T.prop
  exact ⟨⟨h.choose, h.choose_spec.1⟩, Classical.choice h.choose_spec.2.1,
    Classical.choice h.choose_spec.2.2⟩

noncomputable def init_system : ℕ →
    (A : K) × (ℕ → (B : K) × (B ↪[L] A))
  | 0 => ⟨ess_surj_sequence K_fraisse 0,
    fun _ => ⟨_, Embedding.refl L _⟩⟩
  | n + 1 => by
    let ⟨m1, m2⟩ := Nat.unpair n
    let ⟨An, Sn⟩ := init_system n
    let ⟨B, B_to_An⟩ := Sn m1
    let ⟨f, f_fg⟩ := (countable_iff_exists_surjective.1
      (Substructure.countable_self_finiteEquiv_of_countable (L := L) (M := B))).choose m2
    let ⟨A, An_to_A, _, _⟩ := extend_finiteEquiv_in_class K_fraisse An (f.map B_to_An)
      (SubEquivalence.map_dom B_to_An f ▸ FG.map _ f_fg)
    let ⟨A', A_to_A', _⟩ := join K_fraisse A (ess_surj_sequence K_fraisse (n+1))
    exact ⟨A', fun m ↦
      if m ≤ n then ⟨(Sn m).1, A_to_A'.comp (An_to_A.comp (Sn m).2)⟩
        else ⟨A', Embedding.refl L A'⟩⟩

noncomputable def system : ℕ → K :=
  fun n ↦ (init_system K_fraisse n).1

  theorem system_eq {m n} (h : m ≤ n) : ((init_system K_fraisse n).2 m).1 = system K_fraisse m := by
  match n with
  | 0 => cases h; rfl
  | n+1 =>
    simp [init_system]; split <;> simp <;> rename_i h'
    · apply system_eq h'
    · cases (Nat.le_or_eq_of_le_succ h).resolve_left h'
      rfl

theorem init_system_succ (n : ℕ) :
    ((init_system K_fraisse n).2 n).2.comp
      (system_eq K_fraisse (le_refl n) ▸ Embedding.refl L _) =
      Embedding.refl L (system K_fraisse n) := by
  match n with
  | 0 => rfl
  | n+1 =>
    simp [init_system]; split <;> simp
    · sorry
    · sorry

  have : (n + 1 ≤ n) = False := by simp only [eq_iff_iff, iff_false, not_le,
        Nat.lt_succ_self]
  let ⟨m1, m2⟩ := Nat.unpair n
  let ⟨An, Sn⟩ := init_system K_fraisse n
  let ⟨B, B_to_An⟩ := Sn m1
  let ⟨f, f_fg⟩ := (countable_iff_exists_surjective.1
    (Substructure.countable_self_finiteEquiv_if_countable (L := L) (M := B))).choose m2
  let ⟨A, An_to_A, _, _⟩ := extend_finiteEquiv_in_class K_fraisse An (f.map B_to_An)
    (SubEquivalence.map_dom B_to_An f ▸ FG.map _ f_fg)
  let ⟨A', A_to_A', _⟩ := join K_fraisse A (ess_surj_sequence K_fraisse (n+1))
  have eq1 : ((init_system K_fraisse (n + 1)).2 (n + 1)) =
    if n + 1 ≤ n then ⟨(Sn (n + 1)).1, A_to_A'.comp (An_to_A.comp (Sn (n + 1)).2)⟩
      else ⟨A', Embedding.refl L A'⟩

noncomputable def maps_system {m n : ℕ} (h : m ≤ n): system K_fraisse m ↪[L] system K_fraisse n :=
  system_eq K_fraisse h ▸ ((init_system K_fraisse n).2 m).2

theorem transitive_maps_system {m n k : ℕ} (h : m ≤ n) (h' : n ≤ k) :
    (maps_system K_fraisse h').comp (maps_system K_fraisse h) =
      maps_system K_fraisse (h.trans h') := by
  classical
  let r := (Nat.exists_eq_add_of_le h').choose
  have : k = n + r := (Nat.exists_eq_add_of_le h').choose_spec
  match r_eq : r with
  | 0 =>
    have : k = n := by simp only [this, add_zero]
    cases this
    cases n with
    | zero => rfl
    | succ n =>
      have truc : (Nat.succ n ≤ n) = False := by simp only [eq_iff_iff, iff_false, not_le,
        Nat.lt_succ_self]
      have {α : Type*} (t e : α) : (if (Nat.succ n ≤ n) then t else e) = e := by
        convert (congr_arg (fun x ↦ if x then t else e) truc).trans (if_false _ _)
        infer_instance
        exact t

theorem exists_fraisse_limit : ∃ M : Bundled.{w} L.Structure, ∃ _ : Countable M,
    IsFraisseLimit K M := by
  let l : ℕ → Bundled.{w} L.Structure :=
    ess_surj_sequence K_fraisse
  have l_image_in_K : ∀ n, l n ∈ K :=
    ess_surj_sequence_in_fraisse_class K_fraisse
  have l_ess_surj : ∀ V : K, ∃ n, Nonempty (V ≃[L] l n) :=
    ess_surj_sequence_is_ess_surj K_fraisse
  let rec V : (n : ℕ) → Σ f : Fin (n + 1) → Bundled.{w} L.Structure, (k : Fin (n + 1)) →
      (f k ↪[L] f n)
    | 0 => ⟨fun _ ↦ l 0, fun k ↦ Embedding.refl _ _⟩
    | n + 1 => by
      have : ℕ ≃ ℕ × ℕ := by exact Denumerable.equiv₂ ℕ (ℕ × ℕ)



end IsFraisseLimit

end Language

end FirstOrder
