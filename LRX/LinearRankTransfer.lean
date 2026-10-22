import LRX.CircularRankTransfer

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

theorem approached_circular_rank_transfer (hn : 2 ≤ n) (p : State n)
    (dir : Bool) (anchor start finish : Fin n) (ss : List (ExactService n))
    (hdis : ss.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hcan : CanonicalFamily ss)
    (hbelow : FiniteRankOrder.Below p ((ss.map (fun a => a.service.target)).prod))
    (hrange : ∀ a ∈ ss, (arcCoordinate dir anchor a.service.port).val ≤
      (arcCoordinate dir anchor finish).val) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      w.length ≤ inversionNumber p+(ss.map (fun a => BufferProgram.rotations a.service.word)).sum+
        (arcCoordinate dir anchor finish).val+min (anchor-start).val (n-(anchor-start).val) := by
  obtain ⟨w,he,hl⟩ := circular_rank_transfer_route hn p dir anchor finish ss hdis hcan hbelow hrange
  refine ⟨toPort (anchor-start)++w,?_,?_⟩
  · rw [eval_append,toPort_eval_rotation,rotation_sub,he]
    group
  · rw [List.length_append,toPort_length]
    omega

theorem left_linear_rank_transfer (hn : 2 ≤ n) (p : State n)
    (anchor start finish : Fin n) (has : anchor.val ≤ start.val) (haf : anchor.val ≤ finish.val)
    (ss : List (ExactService n))
    (hdis : ss.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hcan : CanonicalFamily ss)
    (hbelow : FiniteRankOrder.Below p ((ss.map (fun a => a.service.target)).prod))
    (hrange : ∀ a ∈ ss, anchor.val ≤ a.service.port.val ∧ a.service.port.val ≤ finish.val) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+
        ((ss.map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ)+
        (start.val : ℤ)+(finish.val : ℤ)-2*(anchor.val : ℤ) := by
  have hr : ∀ a ∈ ss, (arcCoordinate true anchor a.service.port).val ≤ (arcCoordinate true anchor finish).val := by
    intro a ha
    obtain ⟨hlo,hhi⟩ := hrange a ha
    simp only [arcCoordinate,ite_true,Fin.sub_val_of_le hlo,Fin.sub_val_of_le haf]
    omega
  obtain ⟨w,he,hl⟩ := approached_circular_rank_transfer hn p true anchor start finish ss hdis hcan hbelow hr
  simp only [arcCoordinate,ite_true,Fin.sub_val_of_le haf] at hl
  have hm := short_move_le_backward_difference start anchor has
  refine ⟨w,he,?_⟩
  have hh : (w.length : ℤ) ≤ (inversionNumber p : ℤ)+
      ((ss.map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ)+
      ((finish.val-anchor.val : ℕ) : ℤ)+(min (anchor-start).val (n-(anchor-start).val) : ℕ) := by exact_mod_cast hl
  omega

theorem right_linear_rank_transfer (hn : 2 ≤ n) (p : State n)
    (anchor start finish : Fin n) (has : start.val ≤ anchor.val) (haf : finish.val ≤ anchor.val)
    (ss : List (ExactService n))
    (hdis : ss.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hcan : CanonicalFamily ss)
    (hbelow : FiniteRankOrder.Below p ((ss.map (fun a => a.service.target)).prod))
    (hrange : ∀ a ∈ ss, start.val ≤ a.service.port.val ∧ a.service.port.val ≤ anchor.val) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+
        ((ss.map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ)+
        2*(anchor.val : ℤ)-(start.val : ℤ)-(finish.val : ℤ) := by
  have hr : ∀ a ∈ ss, (arcCoordinate true start a.service.port).val ≤ (arcCoordinate true start anchor).val := by
    intro a ha
    obtain ⟨hlo,hhi⟩ := hrange a ha
    simp only [arcCoordinate,ite_true,Fin.sub_val_of_le hlo,Fin.sub_val_of_le has]
    omega
  obtain ⟨w,he,hl⟩ := circular_rank_transfer_route hn p true start anchor ss hdis hcan hbelow hr
  simp only [arcCoordinate,ite_true,Fin.sub_val_of_le has] at hl
  have hm := short_move_le_backward_difference anchor finish haf
  refine ⟨w++toPort (finish-anchor),?_,?_⟩
  · rw [eval_append,toPort_eval_rotation,rotation_sub,he]
    group
  · rw [List.length_append,toPort_length,Nat.cast_add]
    have hh : (w.length : ℤ) ≤ (inversionNumber p : ℤ)+
        ((ss.map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ)+
        ((anchor.val-start.val : ℕ) : ℤ) := by exact_mod_cast hl
    omega

#print axioms left_linear_rank_transfer
#print axioms right_linear_rank_transfer
end LRX.FiniteCuts
