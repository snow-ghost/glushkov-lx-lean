import LRX.LargeComponentBridgeReserve
import LRX.JoinedGapInversionDeficit

namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow RotationWords
variable {n k : ℕ} [NeZero n]

theorem filling_deficit_le_family_sum (As : List (FillingWindow n)) (A : FillingWindow n)
    (hA : A ∈ As) : A.deficit ≤ (As.map FillingWindow.deficit).sum := by
  apply List.single_le_sum
  · intro x hx
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hx
    exact inversion_deficit_nonneg B.filling
  · exact List.mem_map.mpr ⟨A,hA,rfl⟩

/-- The filling in the literal gap word equals the filling chosen in the
extracted source family. Its deficit is therefore charged to that same sum. -/
theorem selected_source_gap_word (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card = k+1) (hk : 0 < k)
    (u : {u // u ∈ positiveSourceGapStarts p n})
    (start finish : Fin n)
    (hsu : u.val.val ≤ start.val) (hsv : start.val < FiniteGaps.next (sourcePackets p) u.val)
    (hfu : u.val.val ≤ finish.val) (hfv : finish.val < FiniteGaps.next (sourcePackets p) u.val) :
    ∃ w : List Letter, eval w = (rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
        2*(bridgeBudget (componentBridges p hc) : ℤ)+
        ((positiveSourceFamily p n).map FillingWindow.deficit).sum-1 := by
  classical
  have hu := (mem_positive_source_gap_starts p n u.val).mp u.property
  let v : Fin n := ⟨FiniteGaps.next (sourcePackets p) u.val,hu.2.1⟩
  have hv : v ∈ sourcePackets p := by
    obtain ⟨j,hj,hje⟩ := FiniteGaps.next_is_member (sourcePackets p) u.val hu.2.1
    have he : j = v := Fin.ext hje
    exact he ▸ hj
  have huv : u.val.val < v.val := FiniteGaps.lt_next (sourcePackets p) u.val
  have hgap (x : Fin n) (hx : u.val.val < x.val) (hx' : x.val < v.val) : x ∉ sourcePackets p :=
    FiniteGaps.gap_avoids_marks (sourcePackets p) u.val x ((FiniteGaps.mem_positions _ _ _).mpr ⟨hx,hx'⟩)
  obtain ⟨f,w,hmatch,he,hl⟩ := joined_positive_gap_deficit_word hn p hc hk
    u.val v huv hu.1 hv hgap hu.2.2.2 start finish hsu hsv hfu hfv
  let A := positiveSourceFilling p n u
  have hf : f = A.filling := by
    apply Equiv.ext
    intro i
    apply embed_injective (sourceGapWindow u.val v huv)
    exact (hmatch i).symm.trans (Classical.choose_spec (positive_source_gap_filling_exists p n u) i)
  rw [hf] at hl
  have hA : A ∈ positiveSourceFamily p n := by
    apply List.mem_map.mpr
    exact ⟨u,by simp,rfl⟩
  have hsum := filling_deficit_le_family_sum (positiveSourceFamily p n) A hA
  have hdef : A.deficit = ((v.val-u.val.val-1).choose 2 : ℤ)-(inversionNumber A.filling : ℤ) := rfl
  change (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
    2*(bridgeBudget (componentBridges p hc) : ℤ)+(A.size.choose 2 : ℤ)-
    (inversionNumber A.filling : ℤ)-1 at hl
  have hprice : (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
      2*(bridgeBudget (componentBridges p hc) : ℤ)+A.deficit-1 := by
    change (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
      2*(bridgeBudget (componentBridges p hc) : ℤ)+
      ((A.size.choose 2 : ℤ)-(inversionNumber A.filling : ℤ))-1
    omega
  exact ⟨w,he,by omega⟩

#print axioms selected_source_gap_word
end LRX.FiniteCuts
