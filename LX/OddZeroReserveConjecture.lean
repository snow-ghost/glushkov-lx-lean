import LX.OddReflectionSharpChoice
import LX.OddUnitPayment
import LX.OddZeroReserveExceptions
import LX.OddZeroReserveGeometry
import LX.OddZeroReserveSeven
import LX.SharpScanDeletion
import LX.Small5
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- The odd zero strip-reserve branch meets the conjectured constant 9/4.
The actual matching geometry supplies the adjacent swap; the only two failed
crossing choices are paid separately, with size seven kernel-checked. -/
theorem odd_zero_reserve_conjecture_word (p : State n) (a : Fin n)
    (hn4 : 4 ≤ n) (ha : GlobalMinimum p a)
    (hn : n=2*height p a+3) (hz : anchorReserve p a=0) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9 := by
  by_cases hsmall : n < 7
  · have hn5 : n=5 := by omega
    subst n
    obtain ⟨w,hw,hprice⟩ := LX.Small5.sharp_words p⁻¹
    exact ⟨w,by rw [hw,mul_inv_cancel],by norm_num; omega⟩
  let m := height p a+1
  have hm : 3 ≤ m := by omega
  have hn' : n=2*m+1 := by omega
  obtain ⟨u,hu,hv⟩ := odd_zero_reserve_adjacent_fixed p a (by omega) hn (global_minimum_majorized ha) hz
  obtain ⟨r,href⟩ := odd_zero_strip_join_reflection hn4 p a hn (global_minimum_majorized ha) hz u hu hv
  rcases odd_reflection_sharp_crossing_choice (p*Equiv.swap u (u+1)) r u href m hn' hm with
    ⟨b,hb,hforward,hcorner,hcross⟩ | hcase
  · obtain ⟨w,hw,hprice⟩ := odd_reflection_crossing_conjecture_word
      (p*Equiv.swap u (u+1)) r b u href m hn' hm hb hforward hcorner hcross
    refine ⟨w,?_,hprice⟩
    simpa [mul_assoc] using hw
  · by_cases hm4 : 4 ≤ m
    · exact odd_zero_reserve_exception_large p a r u ha hz m hn' rfl hm4 hu href hcase
    · have hm3 : m=3 := by omega
      have hn7 : n=7 := by omega
      clear_value m
      subst m
      subst n
      obtain ⟨w,hw,hprice⟩ := odd_zero_reserve_exception_seven p r u href hcase
      exact ⟨w,hw,by norm_num; omega⟩

#print axioms odd_zero_reserve_conjecture_word
end LX.AnchoredPhases
