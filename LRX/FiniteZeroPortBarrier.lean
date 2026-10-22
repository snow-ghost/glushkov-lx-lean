import LRX.JoinedInternalGapWord

namespace LRX.FiniteCuts
open RotationWords
variable {n : ℕ} [NeZero n]

theorem zero_port_step_side (p : State n) (port : Fin n)
    (hz : portLoad (displacement p.symm) port=0) {a b : Fin n}
    (he : CycleFootprint.LoadedStep (displacement p.symm) a b) :
    a.val ≤ port.val ↔ b.val ≤ port.val := by
  rcases he with ⟨he,hpos⟩ | ⟨he,hpos⟩
  · have hab : a.val+1=b.val := by
      rw [he,Fin.val_add_one_of_lt' (finite_positive_port_before_end p a hpos)]
    have hne : a.val ≠ port.val := by
      intro hh
      have h := Fin.ext hh
      rw [h,hz] at hpos
      omega
    omega
  · have hab : b.val+1=a.val := by
      rw [he,Fin.val_add_one_of_lt' (finite_positive_port_before_end p b hpos)]
    have hne : b.val ≠ port.val := by
      intro hh
      have h := Fin.ext hh
      rw [h,hz] at hpos
      omega
    omega

theorem zero_port_path_side (p : State n) (port : Fin n)
    (hz : portLoad (displacement p.symm) port=0) {a b : Fin n}
    (hp : CycleFootprint.LoadPath (displacement p.symm) a b) :
    a.val ≤ port.val ↔ b.val ≤ port.val := by
  induction hp with
  | refl => rfl
  | tail hp he ih => exact ih.trans (zero_port_step_side p port hz he)

theorem load_path_crossed_port_positive (p : State n) {a b : Fin n}
    (hp : CycleFootprint.LoadPath (displacement p.symm) a b) (port : Fin n)
    (ha : a.val ≤ port.val) (hb : port.val < b.val) :
    0 < portLoad (displacement p.symm) port := by
  have hnon := port_load_nonneg (displacement p.symm) port
  by_contra h
  have hz : portLoad (displacement p.symm) port=0 := by omega
  have he := (zero_port_path_side p port hz hp).mp ha
  omega

#print axioms zero_port_path_side
#print axioms load_path_crossed_port_positive
end LRX.FiniteCuts
