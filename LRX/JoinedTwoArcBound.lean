import LRX.FillingPeakArcFamilies

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n k : ℕ} [NeZero n]

/-- The actual original-map word in the positive-port two-arc case, with
research bound (20). This is a route bound, prior to the M3 sharp payment. -/
theorem joined_two_arc_word_bound (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k)
    (start finish : Fin n) (hne : start ≠ finish)
    (hboth : ∀ dir : Bool, ∃ r ∈ sourcePackets p, ∃ port : Fin n,
      (port=r ∨ port+1=r) ∧
      (arcCoordinate dir start port).val ≤ (arcCoordinate dir start finish).val ∧
      0 < portLoad (displacement (joinedComponents p hc).symm) port) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
        2*(bridgeBudget (componentBridges p hc) : ℤ)+((n/2 : ℕ) : ℤ)-
        (sourceHalfPeak p : ℤ)-fillingHalfPeakSum p-1 := by
  obtain ⟨roots,ports,hroots,hinc,hrange,hrootload⟩ := joined_peak_arc_ports p hc hk start finish hne hboth
  obtain ⟨cycles,services,hdis,hout,hst,hcan,hprice,hports,hsaving⟩ :=
    filling_peak_arc_families hn p start finish hne
  have hw (dir : Bool) : ∃ w : List Letter,
      eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
        2*(bridgeBudget (componentBridges p hc) : ℤ)-
        portLoad (displacement (joinedComponents p hc).symm) (ports dir)-
        ((cycles dir).map (fun q => 2*(leftPeak q n : ℤ))).sum+
        ((arcCoordinate dir start finish).val : ℤ) :=
    joined_peak_arc_word hn p hc hk (roots dir) (ports dir) (hroots dir) (hinc dir)
      (cycles dir) (hdis dir) (hout dir) (services dir) (hst dir) (hcan dir) (hprice dir)
      dir start finish (hrange dir) (hports dir)
  obtain ⟨left,hle,hll⟩ := hw true
  obtain ⟨right,hre,hrl⟩ := hw false
  have harcs : ((arcCoordinate true start finish).val : ℤ)+
      ((arcCoordinate false start finish).val : ℤ)=(n : ℤ) := by
    exact_mod_cast complementary_arc_lengths start finish hne
  have hn' : (n : ℤ) ≤ 2*((n/2 : ℕ) : ℤ)+1 := by omega
  by_cases hl : (left.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
      2*(bridgeBudget (componentBridges p hc) : ℤ)+((n/2 : ℕ) : ℤ)-
      (sourceHalfPeak p : ℤ)-fillingHalfPeakSum p-1
  · exact ⟨left,hle,hl⟩
  · exact ⟨right,hre,by omega⟩

#print axioms joined_two_arc_word_bound
end LRX.FiniteCuts
