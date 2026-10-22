import LRX.CanonicalWindowPacketData
import LRX.SpanRankTransfer

namespace LRX.FiniteWindow
open scoped BigOperators
open RotationWords
variable {n b : ℕ} [NeZero n]

theorem canonical_window_left_rank_route (hn : 2 ≤ n) (p G : State n)
    (hbelow : FiniteRankOrder.Below p G) (r : Fin n) (hr : G.symm r ≠ r)
    (hcover : PrunedLift.PacketCover G (FiniteCuts.displacement G.symm) r)
    (W : Window n b) (hoff : W.offset=r.val+1) (filling : State b)
    (hmatch : ∀ i, G.symm (embed W i)=embed W (filling i))
    (l : List (State b)) (hcycles : ∀ q ∈ l, q.IsCycle)
    (hdis : l.Pairwise Equiv.Perm.Disjoint) (hparts : ∀ q ∈ l, CyclePart.IsPart q filling)
    (y : ℕ) (hy : y ≤ b) (hpos : ∀ q ∈ l, 0 < FiniteCuts.leftPeak q y)
    (start finish : Fin n) (hstart : r.val ≤ start.val) (hfin : r.val ≤ finish.val)
    (hfinish : W.offset+y ≤ max start.val finish.val+1) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (FiniteCuts.inversionNumber p : ℤ)+
        (∑ i, |FiniteCuts.displacement G.symm i|)-portLoad (FiniteCuts.displacement G.symm) r-
        2*(l.map (fun q => (FiniteCuts.leftPeak q y : ℤ))).sum+
        (start.val : ℤ)+(finish.val : ℤ)-2*(r.val : ℤ) := by
  let selected := (l.map (fun q => (permutation W q)⁻¹)).prod
  have hrootoutside : ¬Contains W r := by unfold Contains; omega
  obtain ⟨hpart,hkeep⟩ := canonical_window_packet_data G W filling hmatch l hdis hparts r hrootoutside
  obtain ⟨ss,ht,hdisp,hports,hprice⟩ := left_window_family hn W l hcycles y hy hpos
  have hcan := window_family_canonical W l ss ht hdisp
  have hsdis := window_family_disjoint W l hdis ss ht
  have hprod : (ss.map (fun a => a.service.target)).prod=selected := by rw [ht]
  have hm : (∑ i, |FiniteCuts.displacement selected.symm i|)=
      (l.map (fun q => ∑ i : Fin b, |FiniteCuts.displacement q i|)).sum := by
    have hh := canonical_family_mass ss hsdis hcan
    rw [hprod] at hh
    exact hh.symm.trans (window_family_mass W l ss hdisp)
  have hp : (ss.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum ≤
      (∑ i, |FiniteCuts.displacement selected.symm i|)-
        2*(l.map (fun q => (FiniteCuts.leftPeak q y : ℤ))).sum := by
    rw [hprice,sum_price,hm]
  obtain ⟨a,ha,hcanonical,hpair,hfull,hrot⟩ := FiniteCuts.finite_aggregate_packet_family hn G selected
    r r hr (Or.inl rfl) hcover hpart hkeep ss hsdis hcan hprod _ hp
  have hb : FiniteRankOrder.Below p (((a::ss).map (fun a => a.service.target)).prod) := by
    rw [hfull]
    exact hbelow
  have hrange : ∀ s ∈ a::ss, r.val ≤ s.service.port.val ∧ s.service.port.val ≤ max start.val finish.val := by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · rw [ha]
      exact ⟨le_rfl,hfin.trans (le_max_right _ _)⟩
    · have hp := hports s hs
      constructor <;> omega
  obtain ⟨w,he,hl⟩ := FiniteCuts.left_span_rank_transfer hn p r start finish hstart hfin
    (a::ss) hpair hcanonical hb hrange
  exact ⟨w,he,by omega⟩

#print axioms canonical_window_left_rank_route
end LRX.FiniteWindow
