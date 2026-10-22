import LRX.OrderedArcMembership

namespace LRX.FiniteCuts
variable {n : ℕ}

theorem finite_marked_gap (S : Finset (Fin n)) (L R s t : Fin n)
    (hL : L ∈ S) (hR : R ∈ S) (hLs : L.val ≤ s.val) (hsR : s.val < R.val)
    (hst : s.val ≤ t.val)
    (hnone : ∀ z ∈ S, ¬(s.val < z.val ∧ z.val ≤ t.val)) :
    ∃ u ∈ S, ∃ v ∈ S, u.val < v.val ∧
      (∀ z : Fin n, u.val < z.val → z.val < v.val → z ∉ S) ∧
      u.val ≤ s.val ∧ s.val < v.val ∧ u.val ≤ t.val ∧ t.val < v.val := by
  classical
  let A := S.filter (fun z => z.val ≤ s.val)
  let B := S.filter (fun z => s.val < z.val)
  have hA : A.Nonempty := ⟨L,Finset.mem_filter.mpr ⟨hL,hLs⟩⟩
  have hB : B.Nonempty := ⟨R,Finset.mem_filter.mpr ⟨hR,hsR⟩⟩
  let u := A.max' hA
  let v := B.min' hB
  obtain ⟨hu,hus⟩ := Finset.mem_filter.mp (Finset.max'_mem A hA)
  obtain ⟨hv,hsv⟩ := Finset.mem_filter.mp (Finset.min'_mem B hB)
  change u ∈ S at hu
  change v ∈ S at hv
  change u.val ≤ s.val at hus
  change s.val < v.val at hsv
  have htv : t.val < v.val := by have hh := hnone v hv; omega
  refine ⟨u,hu,v,hv,by omega,?_,hus,hsv,by omega,htv⟩
  intro z huz hzv hz
  by_cases hzs : z.val ≤ s.val
  · have hh : z ≤ u := Finset.le_max' A z (Finset.mem_filter.mpr ⟨hz,hzs⟩)
    change z.val ≤ u.val at hh
    omega
  · have hh : v ≤ z := Finset.min'_le B z (Finset.mem_filter.mpr ⟨hz,by omega⟩)
    change v.val ≤ z.val at hh
    omega

#print axioms finite_marked_gap
end LRX.FiniteCuts
