import LRX.JoinedOuterPorts
import LRX.ExteriorCursorWord

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem external_port_costs (hn : 2 ≤ n) (l r x : Fin n) (hlr : l.val < r.val)
    (hx : r.val ≤ x.val ∨ x.val < l.val) :
    min ((r-1)-x).val (n-((r-1)-x).val) ≤ (x-r).val+1 ∧
    min (x-(r-1)).val (n-(x-(r-1)).val) ≤ (x-r).val+1 ∧
    min (l-x).val (n-(l-x).val) ≤ (l-r).val-(x-r).val ∧
    min (x-l).val (n-(x-l).val) ≤ (l-r).val-(x-r).val := by
  have hlt : l < r := hlr
  have hg : (l-r).val=n+l.val-r.val := Fin.coe_sub_iff_lt.mpr hlt
  have hz : (x-r).val < (l-r).val := by
    rcases hx with hx | hx
    · rw [Fin.sub_val_of_le hx,hg]
      have := x.isLt
      omega
    · have hxr : x < r := by change x.val < r.val; omega
      rw [Fin.coe_sub_iff_lt.mpr hxr,hg]
      omega
  have hz' : (x-r).val+1 < n := by have := (l-r).isLt; omega
  have hleft := short_neg_one_costs hn (x-r) hz'
  have hright := short_move_le_difference (x-r) (l-r) (le_of_lt hz)
  have hback := short_move_le_backward_difference (l-r) (x-r) (le_of_lt hz)
  have he1 : (r-1)-x=(-1)-(x-r) := by ring
  have he2 : x-(r-1)=(x-r)-(-1) := by ring
  have he3 : l-x=(l-r)-(x-r) := by ring
  have he4 : x-l=(x-r)-(l-r) := by ring
  exact ⟨by simpa only [he1] using hleft.1,by simpa only [he2] using hleft.2,
    by simpa only [he3] using hright,by simpa only [he4] using hback⟩

#print axioms external_port_costs
end LRX.FiniteCuts
