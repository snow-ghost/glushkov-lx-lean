import LRX.FiniteServiceRankTransfer

namespace LRX.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem renamed_initial_window (p : State n) :
    FiniteWindowState (rename p (fun _ => 0) initial) 0 := by
  intro i
  simp only [rename,initial,PhysicalModel.initial,mul_one,Equiv.symm_symm,zero_add,add_zero]

theorem renamed_initial_aligned (p : State n) : Aligned (rename p (fun _ => 0) initial) := by
  constructor
  · simp [rename,initial,PhysicalModel.initial]
  · intro i
    simp only [rename,initial,PhysicalModel.initial,mul_one,Equiv.symm_symm,add_zero]
    simp

/-- Direct transfer of a finite service from the identity to an upper target.
No descending-word or seam-exclusion hypothesis is imposed on the service.
The complete integer target and rotation subsequence are preserved for the
lower target, and the exact price is its own inversion count plus old rotations. -/
theorem forward_finite_rank_transfer (hn : 2 ≤ n) (w : List Letter) (p q : State n)
    (hpq : FiniteRankOrder.Below p q)
    (hqt : (run w (initial (n:=n))).physical.tokens=q)
    (hqp : ∀ i, (run w (initial (n:=n))).position i=(q.symm i : ℤ)) :
    ∃ v : List Letter, rotationLetters v=rotationLetters w ∧
      (run v (initial (n:=n))).cursor=(run w (initial (n:=n))).cursor ∧
      (run v (initial (n:=n))).physical.tokens=p ∧
      (∀ i, (run v (initial (n:=n))).position i=(p.symm i : ℤ)) ∧
      BufferProgram.exchanges v=FiniteCuts.inversionNumber p ∧
      v.length=FiniteCuts.inversionNumber p+BufferProgram.rotations w := by
  let s := rename p (fun _ => 0) (initial (n:=n))
  let t := rename q (fun _ => 0) (initial (n:=n))
  have hs : s.physical.tokens=p.symm := by simp [s,rename,initial,PhysicalModel.initial]
  have ht : t.physical.tokens=q.symm := by simp [t,rename,initial,PhysicalModel.initial]
  have hbelow : FiniteRankOrder.Below s.physical.tokens t.physical.tokens := by
    rw [hs,ht]
    exact (FiniteRankOrder.below_inverse_iff p q).mpr hpq
  have htt : (run w t).physical.tokens=1 := by
    rw [show t=rename q (fun _ => 0) initial from rfl,← rename_run]
    simp only [rename,hqt,← Equiv.Perm.inv_def,inv_mul_cancel]
  have htp : ∀ i, (run w t).position i=(i : ℤ) := by
    intro i
    rw [show t=rename q (fun _ => 0) initial from rfl,← rename_run]
    simp only [rename,hqp,Equiv.symm_apply_apply,add_zero]
  have htw : FiniteWindowState (run w t) 0 := by
    intro i
    rw [htp,htt]
    simp only [← Equiv.Perm.inv_def,inv_one,Equiv.Perm.one_apply,zero_add]
  obtain ⟨v,hrot,hcursor,hpos,htokens,hx,hlen⟩ := finite_service_rank_transfer hn w s t 0
    hbelow rfl rfl (renamed_initial_aligned q) (renamed_initial_window q) htw htt
      (renamed_initial_window p)
  have hpout : (run v (initial (n:=n))).physical.tokens=p := by
    change (run v (rename p (fun _ => 0) initial)).physical.tokens=1 at htokens
    rw [← rename_run] at htokens
    change p.symm*(run v (initial (n:=n))).physical.tokens=1 at htokens
    have he := congrArg (fun z => p*z) htokens
    simpa only [← Equiv.Perm.inv_def,← mul_assoc,mul_inv_cancel,one_mul,mul_one] using he
  have hpositions : ∀ i, (run v (initial (n:=n))).position i=(p.symm i : ℤ) := by
    intro i
    have he := hpos (p.symm i)
    change (run v (rename p (fun _ => 0) initial)).position (p.symm i)=0+(p.symm i : ℤ) at he
    rw [← rename_run] at he
    simpa only [rename,Equiv.apply_symm_apply,add_zero,zero_add] using he
  have hcur : (run v (initial (n:=n))).cursor=(run w (initial (n:=n))).cursor := by
    change (run v (rename p (fun _ => 0) initial)).cursor=
      (run w (rename q (fun _ => 0) initial)).cursor at hcursor
    rw [← rename_run,← rename_run] at hcursor
    exact hcursor
  rw [hs,show FiniteCuts.inversionNumber p.symm=FiniteCuts.inversionNumber p from
    FiniteCuts.inversion_number_inverse p] at hx hlen
  exact ⟨v,hrot,hcur,hpout,hpositions,hx,hlen⟩

#print axioms forward_finite_rank_transfer
end LRX.LiftedModel
