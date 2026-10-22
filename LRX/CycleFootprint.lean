import LRX.FootprintPacket
import LRX.PeriodicTouches

/-! Actual finite footprints of lifted permutation cycles. Boundary vertices
belong to the cycle support; internal vertices contain both circle neighbors. -/
namespace LRX.CycleFootprint
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def Adjacent (x y : Fin n) : Prop := y=x+1 ∨ x=y+1

theorem adjacent_symm {x y : Fin n} (h : Adjacent x y) : Adjacent y x := h.symm

noncomputable def footprint (p : State n) (d : Fin n → ℤ) (a : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun x => ∃ i ∈ BufferProgram.orbitLabels p a,
    BufferProgram.Touches (n : ℤ) (i : ℤ) (d i) (x : ℤ))

theorem mem_footprint (p : State n) (d : Fin n → ℤ) (a x : Fin n) :
    x ∈ footprint p d a ↔ ∃ i ∈ BufferProgram.orbitLabels p a,
      BufferProgram.Touches (n : ℤ) (i : ℤ) (d i) (x : ℤ) := by
  classical
  simp [footprint]

theorem support_subset (p : State n) (d : Fin n → ℤ) (a : Fin n) :
    BufferProgram.orbitLabels p a ⊆ footprint p d a := by
  intro i hi
  apply (mem_footprint p d a i).mpr
  exact ⟨i,hi,0,by simp,by simp⟩

theorem support_inverse (p : State n) (a i : Fin n) (hi : i ∈ BufferProgram.orbitLabels p a) :
    p.symm i ∈ BufferProgram.orbitLabels p a := by
  obtain ⟨hc,ha⟩ := (BufferProgram.mem_orbitLabels p a i).mp hi
  exact (BufferProgram.mem_orbitLabels p a (p.symm i)).mpr ⟨hc.apply_right,ha⟩

theorem copy_cast (x : Fin n) (k : ℤ) : (((x : ℤ)+k*(n : ℤ) : ℤ) : Fin n)=x := by simp

theorem arrow_point_mem (p : State n) (d : Fin n → ℤ) (a i : Fin n)
    (hi : i ∈ BufferProgram.orbitLabels p a) (z : ℤ)
    (hz : min (i : ℤ) ((i : ℤ)+d i) ≤ z ∧ z ≤ max (i : ℤ) ((i : ℤ)+d i)) :
    (z : Fin n) ∈ footprint p d a := by
  have hm : Int.ModEq (n : ℤ) ((z : Fin n) : ℤ) z := by
    apply (LiftedModel.cast_eq_iff_modEq _ _).mp
    simp only [Int.cast_natCast,Fin.cast_val_eq_self]
  obtain ⟨k,hk⟩ := Int.modEq_iff_dvd.mp hm
  have he : ((z : Fin n) : ℤ)+k*(n : ℤ)=z := by nlinarith [hk]
  exact (mem_footprint p d a _).mpr ⟨i,hi,k,by rw [he]; exact hz.1,by rw [he]; exact hz.2⟩

theorem strict_touch {p : State n} {d : Fin n → ℤ} (hd : AffineLift.IsLift p 0 d)
    (a i x : Fin n) (hi : i ∈ BufferProgram.orbitLabels p a)
    (hx : x ∉ BufferProgram.orbitLabels p a)
    (ht : BufferProgram.Touches (n : ℤ) (i : ℤ) (d i) (x : ℤ)) :
    ∃ k : ℤ, min (i : ℤ) ((i : ℤ)+d i) < (x : ℤ)+k*(n : ℤ) ∧
      (x : ℤ)+k*(n : ℤ) < max (i : ℤ) ((i : ℤ)+d i) := by
  obtain ⟨k,hlo,hhi⟩ := ht
  have hs : (x : ℤ)+k*(n : ℤ) ≠ (i : ℤ) := by
    intro he
    have h := congrArg (fun z : ℤ => (z : Fin n)) he
    have hxi : x=i := by simpa using h
    exact hx (hxi ▸ hi)
  have he : (x : ℤ)+k*(n : ℤ) ≠ (i : ℤ)+d i := by
    intro he
    have h := congrArg (fun z : ℤ => (z : Fin n)) he
    have hres := AffineLift.lift_residue hd i
    have hxi : x=p.symm i := by
      have hc : x=i+(d i : Fin n) := by simpa using h
      simpa using hc.trans hres
    exact hx (hxi ▸ support_inverse p a i hi)
  exact ⟨k,by omega,by omega⟩

theorem strict_touch_neighbor (i x y : Fin n) (d : ℤ) (k : ℤ)
    (hlo : min (i : ℤ) ((i : ℤ)+d) < (x : ℤ)+k*(n : ℤ))
    (hhi : (x : ℤ)+k*(n : ℤ) < max (i : ℤ) ((i : ℤ)+d)) (hadj : Adjacent x y) :
    BufferProgram.Touches (n : ℤ) (i : ℤ) d (y : ℤ) := by
  rcases hadj with hy | hy
  · have ht : BufferProgram.Touches (n : ℤ) (i : ℤ) d ((x : ℤ)+1) := ⟨k,by omega,by omega⟩
    apply BufferProgram.touches_of_modEq (d := d) (a := (i : ℤ)) (a' := (i : ℤ)) ?_ ht
    apply (LiftedModel.cast_eq_iff_modEq _ _).mp
    simp only [Int.cast_sub,Int.cast_add,Int.cast_one,Int.cast_natCast,Fin.cast_val_eq_self]
    rw [hy]
  · have ht : BufferProgram.Touches (n : ℤ) (i : ℤ) d ((x : ℤ)-1) := ⟨k,by omega,by omega⟩
    apply BufferProgram.touches_of_modEq (d := d) (a := (i : ℤ)) (a' := (i : ℤ)) ?_ ht
    apply (LiftedModel.cast_eq_iff_modEq _ _).mp
    simp only [Int.cast_sub,Int.cast_one,Int.cast_natCast,Fin.cast_val_eq_self]
    rw [hy]
    abel

theorem boundary_in_support {p : State n} {d : Fin n → ℤ} (hd : AffineLift.IsLift p 0 d)
    (a x : Fin n) (hx : x ∈ footprint p d a) (hnot : x ∉ BufferProgram.orbitLabels p a)
    (y : Fin n) (hy : Adjacent x y) : y ∈ footprint p d a := by
  obtain ⟨i,hi,ht⟩ := (mem_footprint p d a x).mp hx
  obtain ⟨k,hlo,hhi⟩ := strict_touch hd a i x hi hnot ht
  exact (mem_footprint p d a y).mpr ⟨i,hi,strict_touch_neighbor i x y (d i) k hlo hhi hy⟩

#print axioms support_subset
#print axioms boundary_in_support
end LRX.CycleFootprint
