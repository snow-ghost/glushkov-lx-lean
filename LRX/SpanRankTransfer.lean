import LRX.LinearRankTransfer

namespace LRX.FiniteCuts
open RotationWords
variable {n : ℕ} [NeZero n]

theorem left_span_rank_transfer (hn : 2 ≤ n) (p : State n)
    (anchor start finish : Fin n) (has : anchor.val ≤ start.val) (haf : anchor.val ≤ finish.val)
    (ss : List (ExactService n))
    (hdis : ss.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hcan : CanonicalFamily ss)
    (hbelow : FiniteRankOrder.Below p ((ss.map (fun a => a.service.target)).prod))
    (hrange : ∀ a ∈ ss, anchor.val ≤ a.service.port.val ∧ a.service.port.val ≤ max start.val finish.val) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+
        ((ss.map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ)+
        (start.val : ℤ)+(finish.val : ℤ)-2*(anchor.val : ℤ) := by
  by_cases hsf : start.val ≤ finish.val
  · apply left_linear_rank_transfer hn p anchor start finish has haf ss hdis hcan hbelow
    intro a ha
    simpa only [max_eq_right hsf] using hrange a ha
  · have hfs : finish.val ≤ start.val := by omega
    have hr : ∀ a ∈ ss, (arcCoordinate false start a.service.port).val ≤ (arcCoordinate false start anchor).val := by
      intro a ha
      obtain ⟨hlo,hhi⟩ := hrange a ha
      rw [max_eq_left hfs] at hhi
      simp only [arcCoordinate,Bool.false_eq_true,ite_false,Fin.sub_val_of_le hhi,Fin.sub_val_of_le has]
      omega
    obtain ⟨w,he,hl⟩ := circular_rank_transfer_route hn p false start anchor ss hdis hcan hbelow hr
    simp only [arcCoordinate,Bool.false_eq_true,ite_false,Fin.sub_val_of_le has] at hl
    have hm := short_move_le_difference anchor finish haf
    refine ⟨w++toPort (finish-anchor),?_,?_⟩
    · rw [eval_append,toPort_eval_rotation,rotation_sub,he]
      group
    · rw [List.length_append,toPort_length,Nat.cast_add]
      have hh : (w.length : ℤ) ≤ (inversionNumber p : ℤ)+
          ((ss.map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ)+
          ((start.val-anchor.val : ℕ) : ℤ) := by exact_mod_cast hl
      omega

theorem right_span_rank_transfer (hn : 2 ≤ n) (p : State n)
    (anchor start finish : Fin n) (has : start.val ≤ anchor.val) (haf : finish.val ≤ anchor.val)
    (ss : List (ExactService n))
    (hdis : ss.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hcan : CanonicalFamily ss)
    (hbelow : FiniteRankOrder.Below p ((ss.map (fun a => a.service.target)).prod))
    (hrange : ∀ a ∈ ss, min start.val finish.val ≤ a.service.port.val ∧ a.service.port.val ≤ anchor.val) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+
        ((ss.map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ)+
        2*(anchor.val : ℤ)-(start.val : ℤ)-(finish.val : ℤ) := by
  by_cases hsf : start.val ≤ finish.val
  · apply right_linear_rank_transfer hn p anchor start finish has haf ss hdis hcan hbelow
    intro a ha
    simpa only [min_eq_left hsf] using hrange a ha
  · have hfs : finish.val ≤ start.val := by omega
    have hr : ∀ a ∈ ss, (arcCoordinate false anchor a.service.port).val ≤ (arcCoordinate false anchor finish).val := by
      intro a ha
      obtain ⟨hlo,hhi⟩ := hrange a ha
      rw [min_eq_right hfs] at hlo
      simp only [arcCoordinate,Bool.false_eq_true,ite_false,Fin.sub_val_of_le hhi,Fin.sub_val_of_le haf]
      omega
    obtain ⟨w,he,hl⟩ := approached_circular_rank_transfer hn p false anchor start finish ss hdis hcan hbelow hr
    simp only [arcCoordinate,Bool.false_eq_true,ite_false,Fin.sub_val_of_le haf] at hl
    have hm := short_move_le_difference start anchor has
    refine ⟨w,he,?_⟩
    have hh : (w.length : ℤ) ≤ (inversionNumber p : ℤ)+
        ((ss.map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ)+
        ((anchor.val-finish.val : ℕ) : ℤ)+(min (anchor-start).val (n-(anchor-start).val) : ℕ) := by exact_mod_cast hl
    omega

#print axioms left_span_rank_transfer
#print axioms right_span_rank_transfer
end LRX.FiniteCuts
