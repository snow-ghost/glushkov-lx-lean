import LX.DeadlinePrice
import LX.DepthCrowding
import LX.FirstLapFormula
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- A prefix consisting entirely of high-depth tokens cannot exceed the total
number of such tokens in the original permutation. -/
theorem prefix_depth_count (d : Fin n → ℤ) (j k : ℕ) (hj : j ≤ n)
    (hp : ∀ i < j, k ≤ atDepth d i) : j ≤ depthCount d k := by
  let f : Fin j → {i : Fin n // k ≤ backwardDepth d i} := fun i =>
    ⟨⟨i.val,by have := i.isLt; omega⟩, by
      have hh := hp i.val i.isLt
      simpa only [atDepth, Fin.natCast_eq_mk (by have := i.isLt; omega : i.val < n)] using hh⟩
  have hf : Function.Injective f := by
    intro i l he
    apply Fin.ext
    exact congrArg (fun z => z.val.val) he
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fin,Fintype.card_subtype,depthCount] using hc

/-- After one lap, all entries at the highest remaining depth occur either
at an original maximum-depth position or in a bounded initial prefix. -/
theorem emitted_depth_top_positions (d : Fin n → ℤ) (h M K : ℕ)
    (hpos : 2 ≤ h) (hmax : ∀ i, backwardDepth d i ≤ h)
    (hhead : backwardDepth d 0 < h)
    (hpositions : ∀ i, backwardDepth d i=h → i.val ≤ M)
    (hcount : depthCount d (h-1) ≤ K)
    (j : ℕ) (hj : 0 < j) (hjn : j < n) :
    emittedDepth d j ≤ h-1 ∧
      (emittedDepth d j=h-1 → j ≤ max M K) := by
  have hval : (j : Fin n).val=j := by simp [Nat.mod_eq_of_lt hjn]
  unfold emittedDepth
  split_ifs with hdesc
  · have hb := hmax (j : Fin n)
    change atDepth d j ≤ h at hb
    constructor
    · omega
    · intro he
      have hh : backwardDepth d (j : Fin n)=h := by
        change atDepth d j=h
        omega
      have hh' := hpositions (j : Fin n) hh
      rw [hval] at hh'
      exact hh'.trans (le_max_left _ _)
  · have hb : prefixMinimum (atDepth d) (j-1) ≤ backwardDepth d 0 := by
      have hh := (prefix_minimum_le_iff (atDepth d) (j-1)
        (prefixMinimum (atDepth d) (j-1))).mp le_rfl 0 (by omega)
      exact hh
    constructor
    · omega
    · intro he
      have hp : ∀ i < j, h-1 ≤ atDepth d i := by
        have hh := (prefix_minimum_le_iff (atDepth d) (j-1) (h-1)).mp (by omega)
        intro i hi
        exact hh i (by omega)
      exact ((prefix_depth_count d j (h-1) (by omega) hp).trans hcount).trans (le_max_right _ _)

/-- The loss from late prefix records is bounded by K, independently of n.
The other possible last event belongs to an original maximum-depth token. -/
theorem scan_deadline_of_crowding (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (h M K : ℕ) (hpos : 2 ≤ h)
    (hmax : ∀ i, backwardDepth d i ≤ h) (hhead : backwardDepth d 0 < h)
    (hpositions : ∀ i, backwardDepth d i=h → i.val ≤ M)
    (hcount : depthCount d (h-1) ≤ K) :
    scanDeadline d ≤ (h-1)*(n-1)+max M K-1 := by
  have hqueue : queueDeadline (sweep d (n-1)) ≤ (n-1)*(h-2)+max M K := by
    unfold queueDeadline
    apply Finset.sup_le
    intro i _
    rw [first_lap_depth_formula hn d hi i]
    by_cases hi0 : i=0
    · subst i
      simp
    · simp only [ite_eq_right hi0]
      have hip : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi0
      have hb := emitted_depth_top_positions d h M K (by omega) hmax hhead hpositions hcount
        i.val hip i.isLt
      by_cases hz : emittedDepth d i.val=0
      · simp only [ite_eq_left hz]
        omega
      · rw [ite_eq_right hz]
        by_cases ht : emittedDepth d i.val=h-1
        · rw [ht]
          have hj := hb.2 ht
          have he : h-1-1=h-2 := by omega
          rw [he]
          omega
        · have hh : emittedDepth d i.val ≤ h-2 := by omega
          have hmul := Nat.mul_le_mul_left (n-1) hh
          have he : emittedDepth d i.val-1+1=emittedDepth d i.val := by omega
          rw [← he,Nat.mul_add,Nat.mul_one] at hmul
          have hj := i.isLt
          omega
  have he : (n-1)+(n-1)*(h-2)=(h-1)*(n-1) := by
    have hh : h-2+1=h-1 := by omega
    calc
      _ = (h-2+1)*(n-1) := by ring
      _ = _ := by rw [hh]
  unfold scanDeadline
  omega


#print axioms scan_deadline_of_crowding
end LX.AffineScan
