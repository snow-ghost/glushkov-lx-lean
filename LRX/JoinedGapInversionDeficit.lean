import LRX.JoinedInternalGapWord
import LRX.GapCostInversionDeficit

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n k : ℕ} [NeZero n]

theorem joined_gap_inversion_deficit_word (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k)
    (u v : Fin n) (huv : u.val < v.val) (hu : u ∈ sourcePackets p) (hv : v ∈ sourcePackets p)
    (hgap : ∀ z : Fin n, u.val < z.val → z.val < v.val → z ∉ sourcePackets p)
    (start finish : Fin n) (hsu : u.val ≤ start.val) (hsv : start.val < v.val)
    (hfu : u.val ≤ finish.val) (hfv : finish.val < v.val) :
    ∃ (filling : State (v.val-u.val-1)) (w : List Letter),
      (∀ i, p.symm (FiniteWindow.embed (sourceGapWindow u v huv) i)=
        FiniteWindow.embed (sourceGapWindow u v huv) (filling i)) ∧
      eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
        2*(bridgeBudget (componentBridges p hc) : ℤ)+
        ((v.val-u.val-1).choose 2 : ℤ)-(inversionNumber filling : ℤ)+1-
        portLoad (displacement p.symm) u := by
  obtain ⟨filling,w,hmatch,he,hl⟩ := joined_internal_gap_word hn p hc hk u v huv hu hv hgap start finish hsu hsv hfu hfv
  have hK := gapCost_le_inversion_deficit filling
  exact ⟨filling,w,hmatch,he,by omega⟩

theorem joined_positive_gap_deficit_word (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k)
    (u v : Fin n) (huv : u.val < v.val) (hu : u ∈ sourcePackets p) (hv : v ∈ sourcePackets p)
    (hgap : ∀ z : Fin n, u.val < z.val → z.val < v.val → z ∉ sourcePackets p)
    (hpos : 0 < portLoad (displacement p.symm) u)
    (start finish : Fin n) (hsu : u.val ≤ start.val) (hsv : start.val < v.val)
    (hfu : u.val ≤ finish.val) (hfv : finish.val < v.val) :
    ∃ (filling : State (v.val-u.val-1)) (w : List Letter),
      (∀ i, p.symm (FiniteWindow.embed (sourceGapWindow u v huv) i)=
        FiniteWindow.embed (sourceGapWindow u v huv) (filling i)) ∧
      eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
        2*(bridgeBudget (componentBridges p hc) : ℤ)+
        ((v.val-u.val-1).choose 2 : ℤ)-(inversionNumber filling : ℤ)-1 := by
  obtain ⟨filling,w,hmatch,he,hl⟩ := joined_gap_inversion_deficit_word hn p hc hk u v huv hu hv hgap start finish hsu hsv hfu hfv
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hload := positive_port_load_ge_two hd u hpos
  exact ⟨filling,w,hmatch,he,by omega⟩

#print axioms joined_positive_gap_deficit_word
end LRX.FiniteCuts
