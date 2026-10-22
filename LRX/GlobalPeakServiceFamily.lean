import LRX.WeightedPacketAssembly
import LRX.FiniteExactAvailability
import LRX.OutsideCyclePositivePort

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

theorem cycle_global_peak_positive (q : State n) (hq : q.IsCycle) : 0 < leftPeak q n := by
  have hl := ZeroGap.cycle_root_load_ge_two hq
  rw [port_load_eq_twice_half] at hl
  have hb : halfLoad q ((ZeroGap.cycleRoot q).val+1) ≤ leftPeak q n :=
    Finset.le_sup (Finset.mem_range.mpr (by have := (ZeroGap.cycleRoot q).isLt; omega))
  omega

/-- Every cycle gets its full global peak discount, with canonical integer
endpoints. The target list records the correspondence without reordering. -/
theorem global_peak_service_family (hn : 2 ≤ n) (cycles : List (State n))
    (hc : ∀ q ∈ cycles, q.IsCycle) :
    ∃ ss : List (ExactService n),
      ss.map (fun a => a.service.target)=cycles.map (fun q => q⁻¹) ∧
      CanonicalFamily ss ∧
      (∀ a ∈ ss, (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i, |a.displacement i|)-2*(leftPeak a.service.target⁻¹ n : ℤ)) := by
  induction cycles with
  | nil => exact ⟨[],rfl,by simp [CanonicalFamily],by simp⟩
  | cons q rest ih =>
    have hq := hc q (by simp)
    obtain ⟨a,_,ht,hd,hr⟩ := left_peak_exact_service hn q hq n le_rfl (cycle_global_peak_positive q hq)
    obtain ⟨ss,hst,hcan,hprice⟩ := ih (fun t ht => hc t (List.mem_cons_of_mem _ ht))
    refine ⟨a::ss,by simp [ht,hst],?_,?_⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · rw [hd,ht]
        rfl
      · exact hcan b hb
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · simpa only [hd,ht,inv_inv,displacement] using hr
      · exact hprice b hb

/-- Summing peak services preserves the entire peak sum, not merely one unit
per cycle. -/
theorem global_peak_family_price (ss : List (ExactService n))
    (hdis : ss.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hcan : CanonicalFamily ss)
    (hp : ∀ a ∈ ss, (BufferProgram.rotations a.service.word : ℤ)=
      (∑ i, |a.displacement i|)-2*(leftPeak a.service.target⁻¹ n : ℤ)) :
    (ss.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum=
      (∑ i : Fin n, |(((ss.map (fun a : ExactService n => a.service.target)).prod).symm i : ℤ)-(i : ℤ)|)-
        (ss.map (fun a => 2*(leftPeak a.service.target⁻¹ n : ℤ))).sum := by
  rw [← canonical_family_mass ss hdis hcan]
  clear hdis hcan
  induction ss with
  | nil => simp
  | cons a rest ih =>
    have ha := hp a (by simp)
    have hr := ih (fun b hb => hp b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons,List.sum_cons]
    omega

#print axioms global_peak_service_family
#print axioms global_peak_family_price
end LRX.FiniteCuts
