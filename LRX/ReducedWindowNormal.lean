import LRX.NonwrappingRankTransfer
import LRX.TraceInversions

namespace LRX.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem window_large_shift_order (s t : Configuration n) (H : ℤ)
    (hs : FiniteWindowState s H) (ht : FiniteWindowState t H)
    (key : PairKey n) (hk : (n : ℤ) ≤ |key.shift|) : key.Before s ↔ key.Before t := by
  have hsa := (s.physical.tokens.symm key.first).isLt
  have hsb := (s.physical.tokens.symm key.second).isLt
  have hta := (t.physical.tokens.symm key.first).isLt
  have htb := (t.physical.tokens.symm key.second).isLt
  unfold PairKey.Before
  rw [hs,hs,ht,ht]
  simp only [abs_eq_max_neg] at hk
  omega

theorem seam_event_shift (hn : 2 ≤ n) (s : Configuration n) (H : ℤ)
    (hs : FiniteWindowState s H)
    (hbad : (s.physical.cursor+1).val ≠ s.physical.cursor.val+1) :
    |(eventKey s).shift|=(n : ℤ) := by
  let c := s.physical.cursor
  have he : (c+1).val=(c.val+1)%n := by
    rw [Fin.val_add]
    have h1 : (1 : Fin n).val=1 := by simp [Fin.val_one,Nat.mod_eq_of_lt (by omega : 1 < n)]
    rw [h1]
  have hc := c.isLt
  have hcn : c.val+1=n := by
    by_contra h
    have hlt : c.val+1 < n := by omega
    have ha : (c+1).val=c.val+1 := by rw [he,Nat.mod_eq_of_lt hlt]
    exact hbad ha
  have hz : (c+1).val=0 := by rw [he,hcn,Nat.mod_self]
  have hshift : s.position (s.physical.tokens c)+1-s.position (s.physical.tokens (c+1))=(n : ℤ) := by
    rw [hs,hs]
    simp only [Equiv.symm_apply_apply]
    omega
  dsimp [c] at hshift
  unfold eventKey normalizePair
  change |(if s.physical.tokens c ≤ s.physical.tokens (c+1) then
    {first:=s.physical.tokens c,second:=s.physical.tokens (c+1),shift:=_} else
    {first:=s.physical.tokens (c+1),second:=s.physical.tokens c,shift:=_} : PairKey n).shift|=_
  split_ifs <;> simp only [hshift,abs_neg,abs_of_nonneg (by positivity : (0 : ℤ) ≤ n)]

theorem reduced_window_nonwrapping (hn : 2 ≤ n) (w : List Letter) (s : Configuration n) (H : ℤ)
    (ha : Aligned s) (hs : FiniteWindowState s H)
    (ht : FiniteWindowState (run w s) H) (hnd : (events w s).Nodup) :
    PhysicalModel.NonwrappingWord w s.physical := by
  induction w generalizing s with
  | nil => trivial
  | cons a w ih =>
    cases a with
    | l =>
      exact ih (step .l s) (step_aligned hn .l ha)
        (finite_window_step .l s H hs (by simp)) ht hnd
    | r =>
      exact ih (step .r s) (step_aligned hn .r ha)
        (finite_window_step .r s H hs (by simp)) ht hnd
    | x =>
      have hadj : (s.physical.cursor+1).val=s.physical.cursor.val+1 := by
        by_contra hbad
        have hshift := seam_event_shift hn s H hs hbad
        have horder := window_large_shift_order s (run (.x::w) s) H hs ht (eventKey s) (by omega)
        have hchange := (reduced_trace_inversions hn (.x::w) ha hnd (eventKey s)).mp
          (by simp [events])
        exact hchange.2 horder
      exact ⟨hadj,ih (step .x s) (step_aligned hn .x ha)
        (finite_window_step .x s H hs (fun _ => hadj)) ht (List.nodup_cons.mp hnd).2⟩

#print axioms reduced_window_nonwrapping
end LRX.LiftedModel
