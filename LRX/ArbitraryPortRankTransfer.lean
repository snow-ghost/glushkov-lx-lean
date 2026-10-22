import LRX.ForwardFiniteRankTransfer

namespace LRX.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem renamed_base_window (p : State n) (base : Configuration n)
    (hbt : base.physical.tokens=1) (hbp : ∀ i, base.position i=(i : ℤ)) :
    FiniteWindowState (rename p (fun _ => 0) base) 0 := by
  intro i
  simp only [rename,hbt,hbp,mul_one,Equiv.symm_symm,zero_add,add_zero]

theorem renamed_base_aligned (p : State n) (base : Configuration n)
    (hbt : base.physical.tokens=1) (hbp : ∀ i, base.position i=(i : ℤ)) (ha : Aligned base) :
    Aligned (rename p (fun _ => 0) base) := by
  constructor
  · exact ha.1
  · intro i
    simp only [rename,hbt,hbp,mul_one,Equiv.symm_symm,add_zero]
    simp

theorem forward_finite_rank_transfer_from (hn : 2 ≤ n) (w : List Letter) (p q : State n)
    (base : Configuration n) (hbt : base.physical.tokens=1)
    (hbp : ∀ i, base.position i=(i : ℤ)) (hba : Aligned base)
    (hpq : FiniteRankOrder.Below p q)
    (hqt : (run w base).physical.tokens=q)
    (hqp : ∀ i, (run w base).position i=(q.symm i : ℤ)) :
    ∃ v : List Letter, rotationLetters v=rotationLetters w ∧
      (run v base).cursor=(run w base).cursor ∧
      (run v base).physical.tokens=p ∧
      (∀ i, (run v base).position i=(p.symm i : ℤ)) ∧
      BufferProgram.exchanges v=FiniteCuts.inversionNumber p ∧
      v.length=FiniteCuts.inversionNumber p+BufferProgram.rotations w := by
  let s := rename p (fun _ => 0) base
  let t := rename q (fun _ => 0) base
  have hs : s.physical.tokens=p.symm := by simp [s,rename,hbt]
  have ht : t.physical.tokens=q.symm := by simp [t,rename,hbt]
  have hbelow : FiniteRankOrder.Below s.physical.tokens t.physical.tokens := by
    rw [hs,ht]
    exact (FiniteRankOrder.below_inverse_iff p q).mpr hpq
  have htt : (run w t).physical.tokens=1 := by
    rw [show t=rename q (fun _ => 0) base from rfl,← rename_run]
    simp only [rename,hqt,← Equiv.Perm.inv_def,inv_mul_cancel]
  have htp : ∀ i, (run w t).position i=(i : ℤ) := by
    intro i
    rw [show t=rename q (fun _ => 0) base from rfl,← rename_run]
    simp only [rename,hqp,Equiv.symm_apply_apply,add_zero]
  have htw : FiniteWindowState (run w t) 0 := by
    intro i
    rw [htp,htt]
    simp only [← Equiv.Perm.inv_def,inv_one,Equiv.Perm.one_apply,zero_add]
  obtain ⟨v,hrot,hcursor,hpos,htokens,hx,hlen⟩ := finite_service_rank_transfer hn w s t 0
    hbelow rfl rfl (renamed_base_aligned q base hbt hbp hba) (renamed_base_window q base hbt hbp) htw htt
      (renamed_base_window p base hbt hbp)
  have hpout : (run v base).physical.tokens=p := by
    change (run v (rename p (fun _ => 0) base)).physical.tokens=1 at htokens
    rw [← rename_run] at htokens
    change p.symm*(run v base).physical.tokens=1 at htokens
    have he := congrArg (fun z => p*z) htokens
    simpa only [← Equiv.Perm.inv_def,← mul_assoc,mul_inv_cancel,one_mul,mul_one] using he
  have hpositions : ∀ i, (run v base).position i=(p.symm i : ℤ) := by
    intro i
    have he := hpos (p.symm i)
    change (run v (rename p (fun _ => 0) base)).position (p.symm i)=0+(p.symm i : ℤ) at he
    rw [← rename_run] at he
    simpa only [rename,Equiv.apply_symm_apply,add_zero,zero_add] using he
  have hcur : (run v base).cursor=(run w base).cursor := by
    change (run v (rename p (fun _ => 0) base)).cursor=
      (run w (rename q (fun _ => 0) base)).cursor at hcursor
    rw [← rename_run,← rename_run] at hcursor
    exact hcursor
  rw [hs,show FiniteCuts.inversionNumber p.symm=FiniteCuts.inversionNumber p from
    FiniteCuts.inversion_number_inverse p] at hx hlen
  exact ⟨v,hrot,hcur,hpout,hpositions,hx,hlen⟩

#print axioms forward_finite_rank_transfer_from
end LRX.LiftedModel
