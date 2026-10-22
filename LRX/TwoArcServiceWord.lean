import LRX.CircularOrderedRoute
import LRX.PacketCycleBudget

/-! Two actual service decompositions on complementary arcs give a sharp
word once their combined rotation saving is supplied. -/
namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem complementary_arc_lengths (start finish : Fin n) (hne : start ≠ finish) :
    (arcCoordinate true start finish).val+(arcCoordinate false start finish).val=n := by
  have hneval : start.val ≠ finish.val := fun h => hne (Fin.ext h)
  simp only [arcCoordinate,Bool.false_eq_true,ite_false,ite_true]
  rcases lt_or_gt_of_ne hneval with h | h
  · rw [Fin.sub_val_of_le (le_of_lt h),Fin.coe_sub_iff_lt.mpr h]
    have hs := start.isLt
    have ht := finish.isLt
    omega
  · rw [Fin.coe_sub_iff_lt.mpr h,Fin.sub_val_of_le (le_of_lt h)]
    have hs := start.isLt
    have ht := finish.isLt
    omega

theorem two_arc_service_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (root start finish : Fin n)
    (hne : start ≠ finish) (services : Bool → List (ExactService n))
    (hdis : ∀ dir, (services dir).Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (htarget : ∀ dir, ((services dir).map (fun a => a.service.target)).prod=p)
    (hdisp : ∀ dir i, ((services dir).map (fun a => a.displacement i)).sum=d i)
    (hrange : ∀ dir a, a ∈ services dir → (arcCoordinate dir start a.service.port).val ≤
      (arcCoordinate dir start finish).val)
    (hsaving : (((services true).map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ)+
      (((services false).map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ) ≤
      2*(∑ i : Fin n, |d i|)-2*((ZeroGap.outsideCycles p d root).card : ℤ)-2) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  obtain ⟨left,hle,hll⟩ := circular_reduced_route hn hd true start finish (services true)
    (hdis true) (htarget true) (hdisp true) (hrange true)
  obtain ⟨right,hre,hrl⟩ := circular_reduced_route hn hd false start finish (services false)
    (hdis false) (htarget false) (hdisp false) (hrange false)
  have harcs := complementary_arc_lengths start finish hne
  have hbudget := FiniteGaps.packet_two_arc_price hd hm root
  have hleft : (left.length : ℤ) ≤
      (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
      (((services true).map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ)+
      ((arcCoordinate true start finish).val : ℤ) := by exact_mod_cast hll
  have hright : (right.length : ℤ) ≤
      (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
      (((services false).map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ)+
      ((arcCoordinate false start finish).val : ℤ) := by exact_mod_cast hrl
  have hn' : (n : ℤ)=2*(n/2 : ℕ)+(n%2 : ℕ) := by omega
  by_cases hl : left.length ≤ n.choose 2
  · exact ⟨left,hle,hl⟩
  · exact ⟨right,hre,by omega⟩

#print axioms complementary_arc_lengths
#print axioms two_arc_service_word
end LRX.RotationWords
