import LRX.JoinedSourcePeak
import LRX.PeakServiceArcPartition

namespace LRX.FiniteCuts
open RotationWords
variable {n k : ℕ} [NeZero n]

/-- In the positive-port two-arc case, preserve a positive port on one arc and
use an original source peak on the other. Zero-load incident ports do not
satisfy the hypothesis. -/
theorem joined_peak_arc_ports (p : State n) (hc : (componentRoots p).card=k+1) (hk : 0 < k)
    (start finish : Fin n) (hne : start ≠ finish)
    (hboth : ∀ dir : Bool, ∃ r ∈ sourcePackets p, ∃ port : Fin n,
      (port=r ∨ port+1=r) ∧
      (arcCoordinate dir start port).val ≤ (arcCoordinate dir start finish).val ∧
      0 < portLoad (displacement (joinedComponents p hc).symm) port) :
    ∃ roots ports : Bool → Fin n,
      (∀ dir, roots dir ∈ sourcePackets p) ∧
      (∀ dir, ports dir=roots dir ∨ ports dir+1=roots dir) ∧
      (∀ dir, (arcCoordinate dir start (ports dir)).val ≤ (arcCoordinate dir start finish).val) ∧
      2*(sourceHalfPeak p : ℤ)+2 ≤
        portLoad (displacement (joinedComponents p hc).symm) (ports true)+
        portLoad (displacement (joinedComponents p hc).symm) (ports false) := by
  classical
  choose roots hroots ports hinc hrange hpos using hboth
  obtain ⟨good,hgood,hpeak⟩ := joined_source_peak_port p hc hk
  have hd : AffineLift.IsLift (joinedComponents p hc) 0 (displacement (joinedComponents p hc).symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift (joinedComponents p hc).symm
  have hbase (dir : Bool) : 2 ≤ portLoad (displacement (joinedComponents p hc).symm) (ports dir) :=
    positive_port_load_ge_two hd (ports dir) (hpos dir)
  by_cases hg : (arcCoordinate true start good).val ≤ (arcCoordinate true start finish).val
  · refine ⟨(fun dir => if dir then good else roots false),
      (fun dir => if dir then good else ports false),?_,?_,?_,?_⟩
    · intro dir; cases dir
      · exact hroots false
      · exact hgood
    · intro dir; cases dir
      · exact hinc false
      · exact Or.inl rfl
    · intro dir; cases dir
      · exact hrange false
      · exact hg
    · have hb := hbase false
      simp only [ite_true,Bool.false_eq_true,ite_false]
      omega
  · have hg' := arc_not_forward_is_reverse start finish good hne hg
    refine ⟨(fun dir => if dir then roots true else good),
      (fun dir => if dir then ports true else good),?_,?_,?_,?_⟩
    · intro dir; cases dir
      · exact hgood
      · exact hroots true
    · intro dir; cases dir
      · exact Or.inl rfl
      · exact hinc true
    · intro dir; cases dir
      · exact hg'
      · exact hrange true
    · have hb := hbase true
      simp only [ite_true,Bool.false_eq_true,ite_false]
      omega

#print axioms joined_peak_arc_ports
end LRX.FiniteCuts
