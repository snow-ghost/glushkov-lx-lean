import LRX.CanonicalWindowTwoBoundary
import LRX.OuterSupportBudget
import LRX.FiniteWindowRestriction

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem source_gap_inverse_inside (p : State n) (u v x : Fin n)
    (hu : u ∈ sourcePackets p) (hv : v ∈ sourcePackets p)
    (hx : x ∉ sourcePackets p) (hux : u.val < x.val) (hxv : x.val < v.val) :
    u.val < (p.symm x).val ∧ (p.symm x).val < v.val := by
  have hum := ((mem_source_packets p u).mp hu).1
  have hvm := ((mem_source_packets p v).mp hv).1
  constructor
  · by_contra h
    have he : BufferProgram.ServiceEdge p (displacement p.symm) x u := by
      right
      refine ⟨hum,0,?_,?_⟩ <;> simp only [displacement,zero_mul,add_zero] <;> omega
    exact hx (source_packets_predecessor_closed p x u he hu)
  · by_contra h
    have he : BufferProgram.ServiceEdge p (displacement p.symm) x v := by
      right
      refine ⟨hvm,0,?_,?_⟩ <;> simp only [displacement,zero_mul,add_zero] <;> omega
    exact hx (source_packets_predecessor_closed p x v he hv)

def sourceGapWindow (u v : Fin n) (huv : u.val < v.val) :
    FiniteWindow.Window n (v.val-u.val-1) where
  offset := u.val+1
  fits := by have := v.isLt; omega

theorem source_gap_filling (p : State n) (u v : Fin n) (huv : u.val < v.val)
    (hu : u ∈ sourcePackets p) (hv : v ∈ sourcePackets p)
    (hgap : ∀ x : Fin n, u.val < x.val → x.val < v.val → x ∉ sourcePackets p) :
    ∃ filling : State (v.val-u.val-1),
      (∀ i, p.symm (FiniteWindow.embed (sourceGapWindow u v huv) i)=
        FiniteWindow.embed (sourceGapWindow u v huv) (filling i)) ∧
      (∀ i, FiniteWindow.embed (sourceGapWindow u v huv) i ∉ sourcePackets p) := by
  let W := sourceGapWindow u v huv
  have hb : W.offset+(v.val-u.val-1)=v.val := by dsimp [W,sourceGapWindow]; omega
  have hout (x : Fin n) (hx : FiniteWindow.Contains W x) : x ∉ sourcePackets p := by
    unfold FiniteWindow.Contains at hx
    have hoff : W.offset=u.val+1 := rfl
    exact hgap x (by omega) (by omega)
  have hclosed (x : Fin n) (hx : FiniteWindow.Contains W x) : FiniteWindow.Contains W (p.symm x) := by
    have hxnot := hout x hx
    unfold FiniteWindow.Contains at hx ⊢
    have hoff : W.offset=u.val+1 := rfl
    have hh := source_gap_inverse_inside p u v x hu hv hxnot (by omega) (by omega)
    constructor <;> omega
  obtain ⟨filling,hmatch⟩ := FiniteWindow.exists_restriction_of_inverse_closed W p hclosed
  exact ⟨filling,hmatch,fun i => hout _ (FiniteWindow.contains_embed W i)⟩

#print axioms source_gap_filling
end LRX.FiniteCuts
