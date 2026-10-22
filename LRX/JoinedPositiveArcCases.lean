import LRX.FiniteMarkedGap

namespace LRX.FiniteCuts
open RotationWords
variable {n k : ℕ} [NeZero n]

def JoinedPositiveArcs (p : State n) (hc : (componentRoots p).card=k+1) (s t : Fin n) : Prop :=
  ∀ dir : Bool, ∃ r ∈ sourcePackets p, ∃ port : Fin n,
    (port=r ∨ port+1=r) ∧
    (arcCoordinate dir s port).val ≤ (arcCoordinate dir s t).val ∧
    0 < portLoad (displacement (joinedComponents p hc).symm) port

def SourceCursorGap (p : State n) (s t : Fin n) : Prop :=
  ∃ u ∈ sourcePackets p, ∃ v ∈ sourcePackets p, u.val < v.val ∧
    (∀ z : Fin n, u.val < z.val → z.val < v.val → z ∉ sourcePackets p) ∧
    u.val ≤ s.val ∧ s.val < v.val ∧ u.val ≤ t.val ∧ t.val < v.val

def OuterCursorPair (p : State n) (hc : (componentRoots p).card=k+1) (s t : Fin n) : Prop :=
  ((outerRight p hc).val ≤ s.val ∨ s.val < (outerLeft p hc).val) ∧
  ((outerRight p hc).val ≤ t.val ∨ t.val < (outerLeft p hc).val)

theorem positive_arcs_from_between_outside (p : State n) (hc : (componentRoots p).card=k+1)
    (s t : Fin n) (hst : s.val < t.val) (ri pi ro po : Fin n)
    (hri : ri ∈ sourcePackets p) (hro : ro ∈ sourcePackets p)
    (hpi : pi=ri ∨ pi+1=ri) (hpo : po=ro ∨ po+1=ro)
    (hi : s.val ≤ pi.val ∧ pi.val ≤ t.val) (ho : po.val ≤ s.val ∨ t.val ≤ po.val)
    (hloadi : 0 < portLoad (displacement (joinedComponents p hc).symm) pi)
    (hloado : 0 < portLoad (displacement (joinedComponents p hc).symm) po) :
    JoinedPositiveArcs p hc s t ∧ JoinedPositiveArcs p hc t s := by
  have hbetween := ordered_arc_between s t pi hi.1 hi.2
  have houtside := ordered_arc_outside s t po hst ho
  constructor
  · intro dir
    cases dir
    · exact ⟨ro,hro,po,hpo,houtside.1,hloado⟩
    · exact ⟨ri,hri,pi,hpi,hbetween.1,hloadi⟩
  · intro dir
    cases dir
    · exact ⟨ri,hri,pi,hpi,hbetween.2,hloadi⟩
    · exact ⟨ro,hro,po,hpo,houtside.2,hloado⟩

#print axioms positive_arcs_from_between_outside
end LRX.FiniteCuts
