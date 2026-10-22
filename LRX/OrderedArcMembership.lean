import LRX.JoinedLoadInterval

namespace LRX.FiniteCuts
open RotationWords
variable {n : ℕ} [NeZero n]

theorem ordered_arc_between (s t port : Fin n) (hs : s.val ≤ port.val) (ht : port.val ≤ t.val) :
    (arcCoordinate true s port).val ≤ (arcCoordinate true s t).val ∧
    (arcCoordinate false t port).val ≤ (arcCoordinate false t s).val := by
  have hst : s.val ≤ t.val := by omega
  constructor
  · simp only [arcCoordinate,ite_true,Fin.sub_val_of_le hs,Fin.sub_val_of_le hst]
    omega
  · simp only [arcCoordinate,Bool.false_eq_true,ite_false,Fin.sub_val_of_le ht,Fin.sub_val_of_le hst]
    omega

theorem ordered_arc_outside (s t port : Fin n) (hst : s.val < t.val)
    (hout : port.val ≤ s.val ∨ t.val ≤ port.val) :
    (arcCoordinate false s port).val ≤ (arcCoordinate false s t).val ∧
    (arcCoordinate true t port).val ≤ (arcCoordinate true t s).val := by
  have hst' : s < t := hst
  rcases hout with hp | hp
  · have hpt : port < t := by change port.val < t.val; omega
    constructor
    · simp only [arcCoordinate,Bool.false_eq_true,ite_false,Fin.sub_val_of_le hp,Fin.coe_sub_iff_lt.mpr hst']
      have := t.isLt
      omega
    · simp only [arcCoordinate,ite_true,Fin.coe_sub_iff_lt.mpr hpt,Fin.coe_sub_iff_lt.mpr hst']
      omega
  · have hsp : s < port := by change s.val < port.val; omega
    constructor
    · simp only [arcCoordinate,Bool.false_eq_true,ite_false,Fin.coe_sub_iff_lt.mpr hsp,Fin.coe_sub_iff_lt.mpr hst']
      omega
    · simp only [arcCoordinate,ite_true,Fin.sub_val_of_le hp,Fin.coe_sub_iff_lt.mpr hst']
      have := port.isLt
      omega

#print axioms ordered_arc_between
#print axioms ordered_arc_outside
end LRX.FiniteCuts
