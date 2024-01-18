/- Copyright here.-/
import Mathlib.Order.PFilter
import Mathlib.Combinatorics.AbstractSimplicialComplex.Basic

/-! Documentation here.-/

universe u v

variable {α : Type u} {β : Type v}

variable {K : AbstractSimplicialComplex α} {L : AbstractSimplicialComplex β}

open Finset

variable (K)

/-- Partial order instance on the type of faces of an abstract simplicial complex:
this is the order induced by the inclusion on finsets.-/
instance FacePoset : _root_.PartialOrder K.faces :=
  PartialOrder.lift (fun s => (s.1 : Finset α)) (fun _ _ hst => SetCoe.ext hst)

namespace SimplicialMap

variable [DecidableEq α] [DecidableEq β]
variable {K : AbstractSimplicialComplex α} {L : AbstractSimplicialComplex β}

/-- If `f : K →ₛ L` is a simplicial map, then its face map is an order homomorphism.-/
noncomputable def toOrderHom_faces (f : K →ₛ L) : OrderHom K.faces L.faces where
  toFun := f.face_map
  monotone' s t hst _ := by rw [f.face_vertex, f.face_vertex]
                            exact fun ⟨a, has, hab⟩ ↦ ⟨a, (hst has), hab⟩

end SimplicialMap

/-! Finset `α` is a `LocallyFiniteOrder` and a `LocallyFiniteOrderBot`.-/
--TODO : move this to another file.

namespace Finset

/-- If `s` is a finset of `α`, then the interval `Set.Iic s` in `Finset α` is finite.-/
lemma Iic_finite (s : Finset α) : (Set.Iic s).Finite := by
  rw [← Set.finite_coe_iff]
  apply Finite.of_injective (fun (t : Set.Iic s) => ({a : s | a.1 ∈ t.1} : Set s))
  intro t u htu
  simp only at htu
  revert htu
  rw [← SetCoe.ext_iff, le_antisymm_iff (a := t.1), imp_and]
  constructor
  rw [eq_comm]
  all_goals (intro heq a ha)
  set a' := (⟨a, Set.mem_Iic.mp t.2 ha⟩ : {a : α | a ∈ s})
  swap
  set a' := (⟨a, Set.mem_Iic.mp u.2 ha⟩ : {a : α | a ∈ s})
  all_goals
  rw [Set.ext_iff] at heq
  have : a = a'.1 := by simp only
  erw [this, heq a']
  exact ha

/-- of `s` and `t` are finsets of `α`, then the closed interval `Set.Icc s t` in `Finset α`
is finite.-/
lemma Icc_finite (s t : Finset α) : (Set.Icc s t).Finite :=
  Set.Finite.subset (Iic_finite t) (by rw [Set.subset_def]; simp only [ge_iff_le, gt_iff_lt,
  Set.mem_Icc, Set.mem_Iic, and_imp, imp_self, implies_true, Subtype.forall, forall_const])

/- `LocallyFiniteOrderBot` instance on `Finset α`.-/
noncomputable instance instLocallyFiniteOrderBot [DecidableEq α]:
    LocallyFiniteOrderBot (Finset α) :=
  LocallyFiniteOrderTop.ofIic (Finset α) (fun s => Set.Finite.toFinset (Iic_finite s))
  (fun a s => by simp only [Set.Finite.mem_toFinset, Set.mem_Iic])

/- `LocallyFiniteOrder` instance on `Finset α`.-/
noncomputable instance instLocallyFiniteOrder [DecidableEq α]: LocallyFiniteOrder (Finset α) :=
  LocallyFiniteOrder.ofIcc (Finset α) (fun s t => Set.Finite.toFinset (Icc_finite s t))
  (fun a s t => by simp only [ge_iff_le, gt_iff_lt, Set.Finite.mem_toFinset, Set.mem_Icc])

end Finset

/-! The face poset of an abstract simplicial complex is a `LocallyFiniteOrder` and a
`LocallyFiniteOrderBot`.-/

namespace AbstractSimplicalComplex

/-- If `s` is a finset of `α`, then the intersection of the interval `Set.Iic s` in `Finset α`
and of the set of faces of `K` is finite.-/
lemma FinsetIic_finite (s : Finset α) : {u : K.faces | u ≤ s}.Finite := by
  refine Set.Finite.of_finite_image (f := fun u ↦ u.1) (Set.Finite.subset (Finset.Iic_finite s)
    ?_) (fun _ _ _ _ ↦ by rw [← SetCoe.ext_iff]; simp only [imp_self])
  intro u
  simp only [le_eq_subset, Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_left,
    exists_prop, exists_eq_right_right, Set.mem_Iic, and_imp]
  exact fun h _ ↦ h

/-- If `s` and `t` are finsets of `α`, then the intersection of the interval `Set.Icc s t`
in `Finset α` and of the set of faces of `K` is finite.-/
lemma FinsetIcc_finite (s t : Finset α) : {u : K.faces | s ≤ u ∧ u ≤ t}.Finite :=
  Set.Finite.subset (FinsetIic_finite K t)
    (fun _ ↦ by simp only [le_eq_subset, Set.mem_setOf_eq, and_imp, imp_self, implies_true])

/-- Left-infinite right-closed intervals of the face poset of an abstract simplicial complex
are finite.-/
lemma Iic_finite (s : K.faces) : (Set.Iic s).Finite := by
  rw [← Set.Iic_def]
  exact FinsetIic_finite K s.1

/-- Closed intervals of the face poset of an abstract simplicial complex are finite.-/
lemma Icc_finite (s t : K.faces) : (Set.Icc s t).Finite := by
  rw [← Set.Icc_def]
  exact FinsetIcc_finite K s.1 t.1

/-- `LocallyFiniteOrderBot` instance on the face poset of an abstract simplicial complex.-/
noncomputable instance instLocallyFiniteOrderBot [DecidableEq α] :
    LocallyFiniteOrderBot (K.faces) :=
  LocallyFiniteOrderTop.ofIic K.faces (fun s => Set.Finite.toFinset (Iic_finite K s))
  (fun a s => by simp only [Set.Finite.mem_toFinset, Set.mem_Iic])

/-- `LocallyFiniteOrder` instance on the face poset of an abstract simplicial complex.-/
noncomputable instance instLocallyFiniteOrder [DecidableEq α] : LocallyFiniteOrder (K.faces) :=
  LocallyFiniteOrder.ofFiniteIcc (Icc_finite K)

-- TODO : move the next two lemmas somewhere else.
/-- If an order ideal has a maximal element, then this element generates the ideal.-/
lemma Order.Ideal.generated_by_maximal_element {α : Type*} [Preorder α] (I : Order.Ideal α)
    {a : α} (ha : a ∈ I ∧ ∀ (b : α), b ∈ I → a ≤ b → b ≤ a) : I = Order.Ideal.principal a := by
  rw [← Order.Ideal.principal_le_iff] at ha
  refine le_antisymm ?_ ha.1
  intro b hbI
  erw [Order.Ideal.mem_principal]
  let ⟨c, hc⟩ := I.directed a (by rw [Order.Ideal.principal_le_iff] at ha; exact ha.1) b hbI
  exact le_trans hc.2.2 (ha.2 c hc.1 hc.2.1)

/-- If an order filter has a minimal element, then this element generates the filter.-/
lemma Order.PFilter.generated_by_minimal_element {α : Type*} [Preorder α] (F : Order.PFilter α)
    {a : α} (ha : a ∈ F ∧ ∀ (b : α), b ∈ F → b ≤ a → a ≤ b) : F = Order.PFilter.principal a := by
  suffices hdual : F.dual = @Order.Ideal.principal αᵒᵈ _ a by
    unfold Order.PFilter.principal
    erw [←hdual]
  apply Order.Ideal.generated_by_maximal_element F.dual
  change a ∈ F.dual ∧ _ at ha
  rw [and_iff_right ha.1]
  exact fun b hbF hab => ha.2 b hbF hab
-- end of stuff to move

/-! Order filters and order ideals of the face poset.-/

variable {K}

/-- Every filter of the face poset of an abstract simplicial complex is principal, generated
by a minimal element.-/
lemma isPrincipal_filter_facePoset [DecidableEq α] (F : Order.PFilter K.faces) :
    ∃ (s : K.faces), F = Order.PFilter.principal s := by
  let ⟨t, ht⟩ := F.nonempty
  have hfin : ({s : K.faces | s ≤ t ∧ s ∈ F}).Finite :=
    Set.finite_coe_iff.mp (Finite.Set.subset (Set.Iic t) (fun s hs ↦ hs.1))
  let ⟨s, hs⟩ := Finset.exists_minimal (Set.Finite.toFinset hfin)
    ⟨t, by simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, le_refl, true_and]; exact ht⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, and_imp, Subtype.forall] at hs
  existsi s
  apply Order.PFilter.generated_by_minimal_element
  rw [and_iff_right hs.1.2]
  intro b hbF hbs
  have hsb := hs.2 b.1 b.2 (le_trans hbs hs.1.1) hbF
  rw [lt_iff_le_not_le] at hsb
  push_neg at hsb
  exact hsb hbs

#exit

/- Note that every ideal is principal if and only if the face poset of K is a Noetherian poset,
this is a general fact (see Noetherian_iff_every_ideal_is_principal from GeneralPreorderStuff.lean).-/

/- Support of an ideal of the face poset: this is the union of all the faces in the ideal.-/
def SupportIdeal (I : Order.Ideal K.faces) : Set α := ⋃ (s : I), (s : Set α)

/- If S is a subset of α, this is the set of faces of K contained in S (it is not always an ideal).-/
def IdealFromSet (S : Set α) : Set K.faces := {s : K.faces | (s : Set α) ⊆ S}

/- An element of α is in the support of an ideal I if and only if there exists a face s ∈ I such that a ∈ s.-/
lemma SupportIdeal_def (I : Order.Ideal K.faces) (a : α) : a ∈ SupportIdeal I ↔ ∃ (s : K.faces), s ∈ I ∧ a ∈ s.1 := by
  unfold SupportIdeal
  rw [Set.mem_iUnion]
  constructor
  . intro haI
    cases haI with
    | intro s hs => exact ⟨s.1, s.2, hs⟩
  . intro haI
    cases haI with
    | intro s hs => exists ⟨s, hs.1⟩; exact hs.2

/- An element of α is in the support of an ideal I if and only if a is a vertex of K and {a} ∈ I.-/
lemma SupportIdeal_eq (I : Order.Ideal K.faces) (a : α) : a ∈ SupportIdeal I ↔ ∃ (hav : a ∈ K.vertices), ⟨{a},hav⟩ ∈ I := by
  rw [SupportIdeal_def]
  constructor
  . intro haI
    cases haI with
    | intro s hs => exists (K.down_closed s.2 (Finset.singleton_subset_iff.mpr hs.2) (Finset.singleton_nonempty _))
                    exact Order.Ideal.lower I (Finset.singleton_subset_iff.mpr hs.2) hs.1
  . intro haI
    cases haI with
    | intro hav ha => exists ⟨{a}, hav⟩
                      rw [and_iff_right ha]
                      exact Finset.mem_singleton_self _

/- Every face s ∈ I is contained in the support of I.-/
lemma SupportIdeal_contains_faces (I : Order.Ideal K.faces) {s : K.faces} (hsI : s ∈ I) : (s : Set α) ⊆ SupportIdeal I := by
  intro a has
  rw [SupportIdeal_def]
  exists s

/- If I ⊆ J are ideals, then the support of I is contained in the support of J.-/
lemma SupportIdeal_monotone {I J : Order.Ideal K.faces} (hIJ : (↑I : Set K.faces) ⊆ (↑J : Set K.faces)) : SupportIdeal I ⊆ SupportIdeal J := by
  intro a haI
  rw [SupportIdeal_eq] at haI ⊢
  cases haI with
  | intro hav ha => exists hav; exact hIJ ha

/- The support of an ideal is nonempty.-/
lemma SupportIdeal_nonempty (I : Order.Ideal K.faces) : (SupportIdeal I).Nonempty := by
  cases Order.Ideal.nonempty I with
  | intro s hs => cases K.nonempty_of_mem s.2 with
                  | intro a ha => exists a
                                  rw [SupportIdeal_eq]
                                  exists (K.down_closed s.2 (Finset.singleton_subset_iff.mpr ha) (Finset.singleton_nonempty a))
                                  exact Order.Ideal.lower I (Finset.singleton_subset_iff.mpr ha) hs

lemma Finset_SupportIdeal_aux : ∀ (n : ℕ) (I : Order.Ideal K.faces) (s : Finset α), s.Nonempty → ↑s ⊆ SupportIdeal I → Finset.card s = n →
∃ (hsf :s ∈ K.faces), ⟨s,hsf⟩ ∈ I := by
  intro n
  induction n with
    | zero => intro I s hsne hsI hscard
              exfalso
              rw [←Finset.card_pos, hscard] at hsne
              exact ne_of_lt hsne rfl
    | succ m hrec => intro I s hsne hsI hscard
                     cases hsne with
                     | intro a ha => have haI : a ∈ SupportIdeal I := Set.mem_of_mem_of_subset ha hsI
                                     rw [SupportIdeal_eq] at haI
                                     cases haI with
                                     | intro hav haI => by_cases hsa : s = {a}
                                                        . rw [hsa]; exists hav
                                                        . set t := s \ {a}
                                                          have htne : t.Nonempty := by rw [Finset.sdiff_nonempty]
                                                                                       by_contra habs
                                                                                       rw [Finset.Nonempty.subset_singleton_iff ⟨a, ha⟩] at habs
                                                                                       exact hsa habs
                                                          have htcard : Finset.card t = m := by
                                                            have hcard := Finset.card_sdiff (Finset.singleton_subset_iff.mpr ha)
                                                            rw [hscard, Finset.card_singleton, Nat.succ_sub_one] at hcard
                                                            exact hcard
                                                          have htI := hrec I t htne (le_trans (Finset.sdiff_subset s {a}) hsI) htcard
                                                          cases htI with
                                                          | intro htf htI => cases Order.Ideal.directed I ⟨{a},hav⟩ haI ⟨t, htf⟩ htI with
                                                                             | intro u huI => have hsu : s ⊆ u.1 := by
                                                                                                intro b hbs
                                                                                                by_cases hba : b = a
                                                                                                . rw [hba]
                                                                                                  rw [←Finset.singleton_subset_iff]
                                                                                                  exact huI.2.1
                                                                                                . have hbt : b ∈ t := by
                                                                                                    rw [Finset.mem_sdiff]
                                                                                                    rw [←Finset.mem_singleton] at hba
                                                                                                    exact ⟨hbs, hba⟩
                                                                                                  exact huI.2.2 hbt
                                                                                              exists (K.down_closed u.2 hsu ⟨a, ha⟩)
                                                                                              exact Order.Ideal.lower I hsu huI.1




/- If I is an ideal, then any nonempty finset of α contained in the support of I is a face of K and an element of I.-/
lemma Finset_SupportIdeal (I : Order.Ideal K.faces) {s : Finset α} (hne : s.Nonempty) (hsI : ↑s ⊆ SupportIdeal I) :
∃ (hsf : s ∈ K.faces), ⟨s, hsf⟩ ∈ I :=
Finset_SupportIdeal_aux (Finset.card s) I s hne hsI rfl

/- A face of K is an element of I if and only if it is contained in the support of I.-/
lemma MemIdeal_iff_subset_SupportIdeal (I : Order.Ideal K.faces) (s : K.faces) : s ∈ I ↔ (s : Set α) ⊆ SupportIdeal I := by
  constructor
  . exact fun hsI => SupportIdeal_contains_faces I hsI
  . intro hssupp
    cases Finset_SupportIdeal I (K.nonempty_of_mem s.2) hssupp with
    | intro hsf hsI => exact hsI

/- If I is the principal ideal generated by a face s, then the support of I is equal to s.-/
lemma SupportIdeal_principalIdeal (s : K.faces) : SupportIdeal (Order.Ideal.principal s) = (s : Set α) := by
  ext a
  rw [SupportIdeal_def]
  constructor
  . intro ha
    cases ha with
    | intro t ht => rw [Order.Ideal.mem_principal] at ht
                    have has := ht.1 ht.2
                    simp only [Finset.mem_coe]
                    exact has
  . exact fun has => by exists s
                        rw [Finset.mem_coe] at has
                        rw [Order.Ideal.mem_principal]
                        exact ⟨le_refl _, has⟩

/- If the ideal of I is equal to the set of all faces of K, then its support is equal to the set of vertices of K.-/
lemma SupportIdeal_top {I : Order.Ideal K.faces} (htop : I.carrier = Set.univ) : SupportIdeal I = K.vertices := by
  ext a
  rw [AbstractSimplicialComplex.mem_vertices_iff, SupportIdeal_def]
  constructor
  . exact fun ⟨s, ⟨_, has⟩⟩ => ⟨s, has⟩
  . exact fun ⟨s, has⟩ => by exists s; rw [and_iff_left has]; change s ∈ I.carrier; rw [htop]; exact Set.mem_univ _

/- If S is set of α, then IdealFromSet of S is equal to IdealFromSet of the intersection of S with the set of vertices of K.-/
lemma IdealFromSet_only_depends_on_vertices (S : Set α) : IdealFromSet S = @IdealFromSet α K (S ∩ K.vertices) := by
  ext s
  constructor
  . intro hs
    change (s : Set α) ⊆ S ∩ K.vertices
    rw [Set.subset_inter_iff]
    exact ⟨hs, face_subset_vertices K s⟩
  . intro hs
    refine subset_trans ?_ (Set.inter_subset_left S K.vertices)
    exact hs

/- If S is a set of α, then IdealFromSet of S is a lower set of the face poset.-/
lemma IdealFromSet.IsLowerSet (S : Set α) : @IsLowerSet K.faces (inferInstance) (IdealFromSet S) := by
  intro s t hts hsI
  exact le_trans (Finset.coe_subset.mpr hts) hsI

/- If I is an ideal, then it is equal to IdealFromSet of its support.-/
lemma IdealFromSupport (I : Order.Ideal K.faces) : (I : Set K.faces) = IdealFromSet (SupportIdeal I) := by
  ext s
  exact MemIdeal_iff_subset_SupportIdeal I s

lemma IdealFromSet_DirectOn_iff_aux {S : Set α} (hS : @DirectedOn K.faces (fun s t => s ≤ t) (IdealFromSet S)) (hSK : S ⊆ K.vertices) :
∀ (n : ℕ) (s : Finset α), s.Nonempty → (s : Set α) ⊆ S → Finset.card s = n → s ∈ K.faces := by
  intro n
  induction n with
    | zero => intro s hsne hsS hscard
              exfalso
              rw [←Finset.card_pos, hscard] at hsne
              exact ne_of_lt hsne rfl
    | succ m hrec => intro s hsne hsS hscard
                     cases hsne with
                     | intro a ha => have haS : a ∈ S := Set.mem_of_mem_of_subset ha hsS
                                     by_cases hsa : s = {a}
                                     . rw [hsa]; exact hSK haS
                                     . set t := s \ {a}
                                       have htne : t.Nonempty := by rw [Finset.sdiff_nonempty]
                                                                    by_contra habs
                                                                    rw [Finset.Nonempty.subset_singleton_iff ⟨a, ha⟩] at habs
                                                                    exact hsa habs
                                       have htcard : Finset.card t = m := by
                                         have hcard := Finset.card_sdiff (Finset.singleton_subset_iff.mpr ha)
                                         rw [hscard, Finset.card_singleton, Nat.succ_sub_one] at hcard
                                         exact hcard
                                       have htf := hrec t htne (le_trans (Finset.sdiff_subset s {a}) hsS) htcard
                                       have haS' : ⟨{a}, hSK haS⟩ ∈ IdealFromSet S := by
                                         unfold IdealFromSet
                                         simp only [Set.mem_setOf_eq, Finset.coe_singleton, Set.singleton_subset_iff]
                                         exact haS
                                       have htS : ⟨t, htf⟩ ∈ IdealFromSet S := by
                                         unfold IdealFromSet
                                         simp only [Set.mem_setOf_eq, Finset.coe_sdiff, Finset.coe_singleton, Finset.mem_coe]
                                         exact subset_trans (Set.diff_subset ↑s {a}) hsS
                                       cases (hS ⟨{a}, hSK haS⟩ haS' ⟨t, htf⟩ htS) with
                                       | intro u huS => have hsu : s ⊆ u.1 := by
                                                          intro b hbs
                                                          by_cases hba : b = a
                                                          . rw [hba]
                                                            rw [←Finset.singleton_subset_iff]
                                                            exact huS.2.1
                                                          . have hbt : b ∈ t := by
                                                              rw [Finset.mem_sdiff]
                                                              rw [←Finset.mem_singleton] at hba
                                                              exact ⟨hbs, hba⟩
                                                            exact huS.2.2 hbt
                                                        exact (K.down_closed u.2 hsu ⟨a, ha⟩)


/- If S is a subset of the set of vertices of K, then IdealFromSet of S is a directed subset of the face poset if and only
if every nonempty finset contained in S is a face.-/
lemma IdealFromSet_DirectedOn_iff {S : Set α} (hSK : S ⊆ K.vertices) : @DirectedOn K.faces (fun s t => s ≤ t) (IdealFromSet S) ↔
∀ (s : Finset α), s.Nonempty → (s : Set α) ⊆ S → s ∈ K.faces := by
  constructor
  . exact fun hS s hsne hsS => IdealFromSet_DirectOn_iff_aux hS hSK (Finset.card s) s hsne hsS rfl
  . intro hS s hs t ht
    set u : Finset α := s.1 ∪ t.1
    have huS : (u : Set α) ⊆ S := by rw [Finset.coe_union, Set.union_subset_iff]; exact ⟨hs, ht⟩
    have huf := hS u ?_ huS
    exists ⟨u, huf⟩
    constructor
    . exact huS
    . exact ⟨Finset.subset_union_left _ _, Finset.subset_union_right _ _⟩
    rw [←Finset.coe_nonempty, Finset.coe_union, Set.union_nonempty]
    apply Or.inl
    rw [Finset.coe_nonempty]
    exact K.nonempty_of_mem s.2


/- If I is an ideal, then it is principal if and only if its support is finite.-/
lemma PrincipalIdeal_iff (I : Order.Ideal K.faces) : (∃ (s : K.faces), I = Order.Ideal.principal s) ↔ (SupportIdeal I).Finite := by
  constructor
  . intro hI
    cases hI with
    | intro s hs => rw [hs, SupportIdeal_principalIdeal]; simp only [Finset.finite_toSet]
  . intro hfin
    cases @Finset_SupportIdeal α _ K I (Set.Finite.toFinset hfin) (by rw [Set.Finite.toFinset_nonempty]; exact SupportIdeal_nonempty I)
      (by rw [←Set.Finite.subset_toFinset]) with
    | intro hf h => exists ⟨Set.Finite.toFinset hfin, hf⟩
                    apply Order.Ideal.generated_by_maximal_element
                    rw [and_iff_right h]
                    intro b hbI hb
                    change b.1 ⊆ Set.Finite.toFinset hfin
                    rw [Set.Finite.subset_toFinset]
                    rw [MemIdeal_iff_subset_SupportIdeal] at hbI
                    exact hbI

/- If I ⊆ J are ideals and J is principal, then I is principal.-/
lemma Subideal_of_Principal_is_Principal {I J : Order.Ideal K.faces} (hIJ : I ≤ J) (hJprin : ∃ (s : K.faces), J = Order.Ideal.principal s) :
∃ (s : K.faces), I = Order.Ideal.principal s := by
  rw [PrincipalIdeal_iff] at hJprin ⊢
  exact Set.Finite.subset hJprin (SupportIdeal_monotone hIJ)

/- Every ideal of the face poset is principal if and only if every maximal nonproper ideal of the face poset is principal.
(Where "maximal nonproper" means "maximal in the set of not necessarily proper ideal".)-/
lemma AllIdealsPrincipal_iff_AllMaximalNonProperIdealsPrincipal : (∀ (I : Order.Ideal K.faces), ∃ (s : K.faces), I = Order.Ideal.principal s) ↔
(∀ (I : Order.Ideal K.faces), Order.Ideal.IsMaximalNonProper I → (∃ (s : K.faces), I = Order.Ideal.principal s)) := by
  constructor
  . exact fun hp => fun I _ => hp I
  . intro hp I
    cases Order.Ideal.contained_in_maximal_nonproper I with
    | intro J hJ => exact Subideal_of_Principal_is_Principal hJ.2 (hp J hJ.1)


/- A face of K is a facet if and only if the principal ideal it generates is maximal nonproper.-/
lemma Facet_iff_principal_ideal_maximal (s : K.faces) : s.1 ∈ K.facets ↔ Order.Ideal.IsMaximalNonProper (Order.Ideal.principal s) := by
  rw [AbstractSimplicialComplex.mem_facets_iff]
  simp only [Subtype.coe_prop, Finset.le_eq_subset, true_and]
  constructor
  . intro hsmax
    rw [Order.Ideal.IsMaximalNonProper_iff]
    intro J hsJ
    refine le_antisymm hsJ ?_
    intro t htJ
    cases J.directed s (by rw [Order.Ideal.principal_le_iff] at hsJ; exact hsJ) t htJ with
    | intro u hu => have hsu := hsmax u.2 hu.2.1
                    rw [SetCoe.ext_iff] at hsu
                    erw [hsu, Order.Ideal.mem_principal]
                    exact hu.2.2
  . intro hImax t htf hst
    change s ≤ t at hst
    have hst' : Order.Ideal.principal s ≤ Order.Ideal.principal ⟨t,htf⟩ := by
      simp only [Order.Ideal.principal_le_iff, Order.Ideal.mem_principal]
      exact hst
    rw [Order.Ideal.IsMaximalNonProper_iff] at hImax
    have h := Elements_to_Ideal.injective (hImax hst')
    rw [←SetCoe.ext_iff] at h
    exact h




/- The set of all faces of K is an ideal if and only every nonempty finite set of vertices is a face. (This means that K is an
"infinite simplex" on its set of vertices.)-/

lemma Top_ideal_iff_simplex (hne : Nonempty K.faces) : Order.IsIdeal (@Set.univ K.faces) ↔ ∀ (s : Finset α), s.Nonempty → ↑s ⊆ K.vertices → s ∈ K.faces := by
  constructor
  . intro huniv s hsne hsK
    rw [←(@SupportIdeal_top α K (Order.IsIdeal.toIdeal huniv) rfl)] at hsK
    cases Finset_SupportIdeal _ hsne hsK with
    | intro hsf _ => exact hsf
  . intro huniv
    refine {Nonempty := ?_, IsLowerSet := ?_, Directed := ?_}
    exact fun _ _ _ _ => Set.mem_univ _
    exact @Set.univ_nonempty _ hne
    intro s _ t _
    have hstf : s.1 ∪ t.1 ∈ K.faces := huniv (s.1 ∪ t.1) (by cases K.nonempty_of_mem s.2 with
                                                             | intro a has => exists a; exact Finset.mem_union_left _ has)
                                                         (by rw [Finset.coe_union, Set.union_subset_iff]
                                                             exact ⟨AbstractSimplicialComplex.face_subset_vertices K s,
                                                                    AbstractSimplicialComplex.face_subset_vertices K t⟩)
    exists ⟨s.1 ∪ t.1, hstf⟩
    rw [and_iff_right (Set.mem_univ _)]
    exact ⟨Finset.subset_union_left _ _, Finset.subset_union_right _ _⟩


/- If the face poset of K is Noetherian, then every face is contained in a facet.-/
lemma Noetherian_implies_every_face_contained_in_facet (hnoeth : IsNoetherianPoset K.faces) (s : K.faces) :
∃ (t : K.faces), t.1 ∈ K.facets ∧ s ≤ t := by
  exists WellFounded.min hnoeth {t : K.faces | s ≤ t}  ⟨s, le_refl s⟩
  have hst := WellFounded.min_mem hnoeth {t : K.faces | s ≤ t} ⟨s, le_refl s⟩
  simp only [Set.mem_setOf_eq] at hst
  erw [and_iff_left hst]
  rw [mem_facets_iff, and_iff_right (WellFounded.min hnoeth {t : K.faces | s ≤ t}  ⟨s, le_refl s⟩).2]
  intro u huf htu
  have h := @WellFounded.not_lt_min _ _ hnoeth {t : K.faces | s ≤ t}  ⟨s, le_refl s⟩ ⟨u, huf⟩ (le_trans hst htu)
  rw [lt_iff_le_not_le] at h
  push_neg at h
  exact le_antisymm htu (h htu)

/- A Noetherian nonempty simplicial complex has facets.-/
lemma Noetherian_nonempty_implies_facets_exist (hnoeth : IsNoetherianPoset K.faces) (hne : K.faces.Nonempty) :
K.facets.Nonempty := by
  match hne with
  | ⟨s, hs⟩ => cases (Noetherian_implies_every_face_contained_in_facet hnoeth ⟨s, hs⟩) with
              | intro t htf => exact ⟨t, htf.1⟩



open Classical

/- A finite-dimensional simplicial complex has a Noetherian face poset.-/
lemma Finite_dimensional_implies_Noetherian (hdim : dimension K ≠ ⊤) : IsNoetherianPoset K.faces := by
  rw [WithTop.ne_top_iff_exists] at hdim
  cases hdim with
  | intro n hn => unfold dimension at hn
                  have hboun : ∀ (s : K.faces), Finset.card s.1 ≤ n + 1 := by
                    intro s
                    have h := le_iSup (fun (s : K.faces) => (Finset.card s.1 : ENat)) s
                    rw [←WithTop.coe_le_coe]
                    apply le_trans h
                    simp only [ENat.some_eq_coe, Nat.cast_add, Nat.cast_one]
                    rw [←ENat.some_eq_coe, hn]
                    exact le_tsub_add
                  unfold IsNoetherianPoset
                  rw [WellFounded.wellFounded_iff_has_min]
                  intro S hSne
                  set f : S → Set.Iic (n+1) := fun s => ⟨Finset.card s.1.1, hboun s⟩
                  set t:= @Function.argmin S (Set.Iic (n+1))ᵒᵈ f _ (Finite.to_wellFoundedLT).wf (Set.Nonempty.to_subtype hSne)
                  exists t.1
                  rw [and_iff_right t.2]
                  intro u huS
                  have htu := @Function.not_lt_argmin S (Set.Iic (n+1))ᵒᵈ f _ (Finite.to_wellFoundedLT).wf (Set.Nonempty.to_subtype hSne) ⟨u, huS⟩
                  change  ¬(Finset.card t.1.1 < Finset.card u.1) at htu
                  rw [lt_iff_le_not_le, not_and, not_not] at htu
                  by_contra habs
                  have h := Finset.eq_of_subset_of_card_le (le_of_lt habs) (htu (Finset.card_le_of_subset (le_of_lt habs)))
                  have h' : t.1.1 = u.1 := by simp only [h]
                  rw [SetCoe.ext_iff] at h'
                  exact (ne_of_lt habs) h'




/- A finite complex has a Noetherian face poset (this follows from the previous lemma and from
AbstractSimplicialComplex.Finite_implies_finite_dimensional, but the direct proof is simpler.). -/
lemma Finite_implies_Noetherian {K : AbstractSimplicialComplex α} (hfin : FiniteComplex K) : IsNoetherianPoset K.faces :=
(@Finite.to_wellFoundedGT K.faces hfin _).wf



/- If K has a Noetherian face poset and all its facets have the same cardinality, then K is pure. -/
lemma Dimension_of_Noetherian_pure {K : AbstractSimplicialComplex α} (hnoeth : IsNoetherianPoset K.faces)
(hpure : ∀ (s t  : Finset α), s ∈ K.facets → t ∈ K.facets → Finset.card s = Finset.card t) : Pure K := by
  intro s hsf
  have hboun := @iSup_le ENat K.faces _ (fun t => (Finset.card t.1 : ENat)) (Finset.card s : ENat)
    (by intro t; cases Noetherian_implies_every_face_contained_in_facet hnoeth t with
                 | intro u hu => erw [hpure s u hsf hu.1, WithTop.some_le_some, Nat.cast_le]
                                 exact Finset.card_le_of_subset hu.2)
  have hboun' : dimension K ≤ Finset.card s - 1 := by
    unfold dimension
    simp only [ge_iff_le, Nat.cast_le_one, tsub_le_iff_right]
    refine le_trans hboun ?_
    exact le_tsub_add
  refine le_antisymm ?_ hboun'
  unfold dimension
  simp only [ge_iff_le, ENat.coe_sub, Nat.cast_one, Nat.cast_le_one, iSup_le_iff, Subtype.forall, tsub_le_iff_right]
  have h : Finset.card s = Finset.card s -1 + 1 := by
    rw [←Nat.succ_eq_add_one, ←Nat.pred_eq_sub_one, Nat.succ_pred (face_card_nonzero (facets_subset hsf))]
  rw [h]
  simp only [ge_iff_le, Nat.cast_add, ENat.coe_sub, Nat.cast_one, Nat.cast_le_one, iSup_le_iff, Subtype.forall]
  apply add_le_add_right
  apply tsub_le_tsub_right
  exact le_iSup (fun (t : K.faces) => (Finset.card t.1 : ENat)) (⟨s, facets_subset hsf⟩ : K.faces)



end AbstractSimplicialComplex
