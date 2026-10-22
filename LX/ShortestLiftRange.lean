import LX.FinitePairReduction
import LX.GreedyWordNormalForm

namespace LX.FinitePairReduction
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.LiftedModel
variable {n : ℕ} [NeZero n]

theorem position_step_partner_bound (s : Configuration n) (a : Letter) (i : Fin n) :
    |(step a.toLRX s).position i-s.position i| ≤
      (if a=.x then ((headPartners i (LiftedScan.visible s)).length : ℤ) else 0) := by
  have h0 : s.physical.tokens s.physical.cursor=LiftedScan.visible s 0 := by
    simp [LiftedScan.visible,LRX.PhysicalModel.visible_apply]
  have h1 : s.physical.tokens (s.physical.cursor+1)=LiftedScan.visible s 1 := by
    simp [LiftedScan.visible,LRX.PhysicalModel.visible_apply,add_comm]
  cases a with
  | l => simp [Letter.toLRX,step]
  | x =>
    simp only [Letter.toLRX,step,h0,h1,headPartners,ite_true,abs_le]
    split_ifs <;> simp only [List.length_singleton,List.length_nil,Nat.cast_one,Nat.cast_zero] <;> omega

/-- Integer displacement is charged to the actual partners of this token,
including seam crossings; no winding is discarded. -/
theorem position_run_partner_bound (w : List Letter) (s : Configuration n) (i : Fin n) :
    |(run (w.map Letter.toLRX) s).position i-s.position i| ≤
      ((partners i w (LiftedScan.visible s)).length : ℤ) := by
  induction w generalizing s with
  | nil => simp [run,partners]
  | cons a w ih =>
    have ht := ih (step a.toLRX s)
    have hh := position_step_partner_bound s a i
    have hlen : (partners i (a::w) (LiftedScan.visible s)).length=
        (partners i w (LiftedScan.visible (step a.toLRX s))).length+
          (if a=.x then (headPartners i (LiftedScan.visible s)).length else 0) := by
      rw [LiftedScan.visible_step]
      cases a <;> simp [partners,Nat.add_comm]
    have hleni : ((partners i (a::w) (LiftedScan.visible s)).length : ℤ)=
        ((partners i w (LiftedScan.visible (step a.toLRX s))).length : ℤ)+
          (if a=.x then ((headPartners i (LiftedScan.visible s)).length : ℤ) else 0) := by
      exact_mod_cast hlen
    have ha := abs_add_le
      ((run (w.map Letter.toLRX) (step a.toLRX s)).position i-(step a.toLRX s).position i)
      ((step a.toLRX s).position i-s.position i)
    have he : (run (w.map Letter.toLRX) (step a.toLRX s)).position i-(step a.toLRX s).position i+
        ((step a.toLRX s).position i-s.position i)=
        (run (w.map Letter.toLRX) (step a.toLRX s)).position i-s.position i := by ring
    rw [he] at ha
    change |(run (w.map Letter.toLRX) (step a.toLRX s)).position i-s.position i| ≤ _
    omega

/-- Every shortest directed word moves each named token by fewer than n
integer positions, because its exchange partners cannot repeat. -/
theorem shortest_displacement_bound (hn : 2 ≤ n) (w : List Letter)
    (hw : w.length=length (eval (n := n) w)) (i : Fin n) :
    |(run (w.map Letter.toLRX) (initial (n := n))).position i-(i : ℤ)| ≤ (n : ℤ)-1 := by
  have hc := shortest_partner_count hn i w 1 (shortest_from_of_length 1 w hw)
  have hb := position_run_partner_bound w (initial (n := n)) i
  simp only [initial,LiftedScan.visible,LRX.PhysicalModel.visible_initial] at hb
  have hci : ((partners i w 1).length : ℤ) ≤ (n : ℤ)-1 := by omega
  exact hb.trans hci

#print axioms position_run_partner_bound
#print axioms shortest_displacement_bound
end LX.FinitePairReduction
