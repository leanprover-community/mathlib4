import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Nucleus

variable {α β : Type*} [PartialOrder β] {l : α → β} {u : β → α}

def GaloisInsertion.toNucleus [CompleteLattice α] (gi : GaloisInsertion l u) : Nucleus α where
  toFun x := u (l x)
  idempotent' x := by rw [gi.l_u_eq]

  map_inf' a b := by

    let y (b1 b2 : β):=  @GaloisConnection.u_inf α β b1 b2 _ (by exact gi.liftSemilatticeInf) _ _ gi.gc
    rw [← y]
    apply le_antisymm
    . sorry --trivial
    .
      have h : (a ⊓ b) = sSup (lowerBounds {a, b})  := by
        rw [← sInf_pair]
        rw [← sSup_lowerBounds_eq_sInf]


      --rw [h]
      let z := @GaloisConnection.l_sSup α β _ (by exact gi.liftCompleteLattice) l u gi.gc
      --rw [z]
      simp [lowerBounds_insert, lowerBounds_singleton, Set.Iic_inter_Iic, Set.mem_Iic,
        le_inf_iff] at h
      rw [h]
      rw [z]



      sorry



    let z := @GaloisInsertion.l_inf_u α β l u _ (by exact gi.liftSemilatticeInf) gi
    rw [← z]





  le_apply' a := gi.gc.le_u (by rfl)




abbrev liftFrameMinimalAxioms [Order.Frame α] (gi : GaloisInsertion l u) : Order.Frame.MinimalAxioms β :=
  { gi.liftCompleteLattice with
inf_sSup_le_iSup_inf a s := by
  --- f_obenstern surjektiv
  --- f_untenstern injectiv
  ---- f_untenstern( f_obenstern x) = n x
  --- > f_obenstern l, f_untenstern u
  --- l : α → β
  --- u : β → α
  --- l (u (x)) = x
  --- u (l (x)) = Nucleus
  --- u_inf
  --- beim Nukleus:
  --- α : E
  --- β : img
  --- Nukleus (coe x) = x
  --- coe/u : img → E
  --- Nukleus/l : E → img
  rw [← gi.u_le_u_iff]
  rw [ @iSup_subtype']
  simp_rw [iSup, sSup]

  have h (a : β) : u a = u (l (u a)) := by
    rw [gi.l_u_eq]

  rw [← gi.l_u_eq (u a ⊓ _)]














  simp_rw [sSup]
  rw [@iSup_subtype']
  simp_rw [iSup, sSup]



  --

  apply gi.gc.monotone_l
  let x:= @GaloisConnection.l_sSup α β _ ( gi.liftCompleteLattice) _ _ gi.gc (u '' s)
  rw [x]


  let y (b1 b2 : β):=  @GaloisConnection.u_inf α β b1 b2 _ gi.liftCompleteLattice.toSemilatticeInf
  rw [← y]








 }
