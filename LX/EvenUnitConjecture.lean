import LX.EvenReflectionSharpChoice
import LX.EvenUnitSharpExceptions

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- Every even input one exchange below the dimension-wide capacity meets
the conjectured additive constant three. -/
theorem even_unit_conjecture_word (p : State n) (a : Fin n)
    (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hunit : (inversions (displacement p a) : ℤ)+1=(m : ℤ)*(m-1)) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12 := by
  by_cases hsmall : n < 8
  · have hc : n=4 ∨ n=6 := by omega
    rcases hc with rfl | rfl
    · obtain ⟨w,hw,hprice⟩ := LX.Small4.sharp_words p⁻¹
      exact ⟨w,by rw [hw,mul_inv_cancel],by norm_num; omega⟩
    · obtain ⟨w,hw,hprice⟩ := LX.Small6.sharp_words p⁻¹
      exact ⟨w,by rw [hw,mul_inv_cancel],by norm_num; omega⟩
  obtain ⟨u,r,hr⟩ := even_unit_reflection_neighbor hn4 m hn ha hunit
  rcases even_reflection_sharp_crossing_choice (p*Equiv.swap u (u+1)) r u hr m hn (by omega) with
    ⟨b,hb,hfinish,hcross⟩ | ⟨hr0,hu⟩
  · obtain ⟨w,hw,hzero,hprice⟩ := even_reflection_sharp_zero_word
      (p*Equiv.swap u (u+1)) r b hr m hn (by omega) hb hfinish
    obtain ⟨v,hv,hlen,_⟩ := LX.LiftedScan.delete_adjacent_descent (by omega)
      (p*Equiv.swap u (u+1)) (displacement (p*Equiv.swap u (u+1)) b) w hw hzero u
      (reflection_neighbor_descent hn4 (p*Equiv.swap u (u+1)) r hr b u hcross)
    refine ⟨v,?_,by omega⟩
    simpa [mul_assoc] using hv
  · have hp : ∀ i,(p*Equiv.swap u (u+1)) i= -i := by simpa [hr0] using hr
    exact even_unit_sharp_exception p a u ha m hn (by omega) hunit hp hu

/-- Strip-reserve formulation at the critical even height. -/
theorem even_one_reserve_conjecture_word (p : State n) (a : Fin n)
    (hn4 : 4 ≤ n) (ha : GlobalMinimum p a)
    (hn : n=2*height p a+2) (hr : anchorReserve p a=1) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12 := by
  have hunit : (inversions (displacement p a) : ℤ)+1=
      ((height p a : ℤ)+1)*((height p a : ℤ)+1-1) := by
    unfold anchorReserve at hr
    have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by exact_mod_cast hn
    nlinarith only [hr,hn']
  apply even_unit_conjecture_word p a hn4 (height p a+1) (by omega) ha
  simpa only [Nat.cast_add,Nat.cast_one] using hunit

#print axioms even_unit_conjecture_word
#print axioms even_one_reserve_conjecture_word
end LX.AnchoredPhases
