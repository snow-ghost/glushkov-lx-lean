import LRX.FiniteWindowLoad
import LRX.ReflectedExactService

/-! Local peak discounts are realized by exact services in the ambient graph.
The mass and discount use the window width, while the literal word uses n. -/
namespace LRX.FiniteWindow
open scoped BigOperators
open RotationWords
variable {n b : ℕ} [NeZero n]

theorem left_peak_ambient_service (hn : 2 ≤ n) (W : Window n b) (p : State b)
    (hp : p.IsCycle) (y : ℕ) (hy : y ≤ b) (hpos : 0 < FiniteCuts.leftPeak p y) :
    ∃ a : ExactService n, W.offset ≤ a.service.port.val ∧ a.service.port.val+1 ≤ W.offset+y ∧
      a.service.target=(permutation W p)⁻¹ ∧
      a.displacement=FiniteCuts.displacement (permutation W p) ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin b, |FiniteCuts.displacement p i|)-2*(FiniteCuts.leftPeak p y : ℤ) := by
  obtain ⟨i,hi,hiy,hload⟩ := FiniteCuts.left_peak_port p y hy hpos
  have hm : permutation W p (embed W i) ≠ embed W i := by
    rw [permutation_embed]
    exact fun h => hi (embed_injective W h)
  obtain ⟨a,ha,ht,hd,hprice⟩ := single_cycle_exact_service (p := (permutation W p)⁻¹) hn
    (permutation_is_cycle W p hp).inv (FiniteCuts.canonical_lift (permutation W p))
    (FiniteCuts.displacement_short (permutation W p)) (embed W i)
    (FiniteCuts.displacement_ne_of_moved (permutation W p) (embed W i) hm)
  rw [displacement_mass, FiniteCuts.port_load_eq_twice_half] at hprice
  have hc : (embed W i).val+1=W.offset+(i.val+1) := by simp [embed]; omega
  rw [hc,half_load_window,hload] at hprice
  refine ⟨a,?_,?_,ht,hd,hprice⟩
  · rw [ha]; dsimp [embed]; omega
  · rw [ha,hc]; omega

theorem right_peak_ambient_service (hn : 2 ≤ n) (W : Window n b) (p : State b)
    (hp : p.IsCycle) (x : ℕ) (hx : x ≤ b) (hpos : 0 < FiniteCuts.rightPeak p x) :
    ∃ a : ExactService n, W.offset+x ≤ a.service.port.val+1 ∧ a.service.port.val+1 < W.offset+b ∧
      a.service.target=(permutation W p)⁻¹ ∧
      a.displacement=FiniteCuts.displacement (permutation W p) ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin b, |FiniteCuts.displacement p i|)-2*(FiniteCuts.rightPeak p x : ℤ) := by
  obtain ⟨i,hi,hxi,hload⟩ := FiniteCuts.right_peak_port p x hx hpos
  have hi0 : i.val ≠ 0 := by
    intro h
    rw [h,FiniteCuts.half_load_zero] at hload
    omega
  have hr0 : embed W i ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp only [embed,Fin.val_zero] at this
    omega
  have hv : (embed W i-1 : Fin n).val+1=W.offset+i.val := by
    rw [Fin.val_sub_one_of_ne_zero hr0]
    dsimp [embed]
    omega
  have hm : permutation W p (embed W i) ≠ embed W i := by
    rw [permutation_embed]
    exact fun h => hi (embed_injective W h)
  obtain ⟨a,ha,ht,hd,hprice⟩ := WordReflection.single_cycle_exact_left_service
    (p := (permutation W p)⁻¹) hn (permutation_is_cycle W p hp).inv
    (FiniteCuts.canonical_lift (permutation W p)) (FiniteCuts.displacement_short (permutation W p))
    (embed W i) (FiniteCuts.displacement_ne_of_moved (permutation W p) (embed W i) hm)
  rw [displacement_mass,FiniteCuts.port_load_eq_twice_half,hv,half_load_window,hload] at hprice
  refine ⟨a,?_,?_,ht,hd,hprice⟩
  · rw [ha,hv]; omega
  · rw [ha,hv]; have := i.isLt; omega

#print axioms left_peak_ambient_service
#print axioms right_peak_ambient_service
end LRX.FiniteWindow
