import LRX.CircleIntervalPaths

/-! The footprint of an actual lifted cycle is connected: follow the cycle
arrows to a supporting vertex, then follow its integer interval. -/
namespace LRX.CycleFootprint
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem arrow_touch_path (p : State n) (d : Fin n → ℤ) (a i x : Fin n)
    (hi : i ∈ BufferProgram.orbitLabels p a)
    (ht : BufferProgram.Touches (n : ℤ) (i : ℤ) (d i) (x : ℤ)) :
    InsidePath (footprint p d a) i x := by
  obtain ⟨k,hlo,hhi⟩ := ht
  have h := segment_path (footprint p d a) (i : ℤ) ((i : ℤ)+d i) ((x : ℤ)+k*(n : ℤ))
    ⟨hlo,hhi⟩ (fun z hz hz' => arrow_point_mem p d a i hi z ⟨hz,hz'⟩)
  simpa only [Int.cast_natCast,Fin.cast_val_eq_self,copy_cast] using h

theorem arrow_target_path {p : State n} {d : Fin n → ℤ} (hd : AffineLift.IsLift p 0 d)
    (a i : Fin n) (hi : i ∈ BufferProgram.orbitLabels p a) :
    InsidePath (footprint p d a) i (p.symm i) := by
  have h := segment_path (footprint p d a) (i : ℤ) ((i : ℤ)+d i) ((i : ℤ)+d i)
    ⟨by simp,by simp⟩ (fun z hz hz' => arrow_point_mem p d a i hi z ⟨hz,hz'⟩)
  have he : (((i : ℤ)+d i : ℤ) : Fin n)=p.symm i := by
    simpa using AffineLift.lift_residue hd i
  simpa only [Int.cast_natCast,Fin.cast_val_eq_self,he] using h

theorem support_path {p : State n} {d : Fin n → ℤ} (hd : AffineLift.IsLift p 0 d)
    (a i : Fin n) (ha : p⁻¹ a ≠ a) (hi : i ∈ BufferProgram.orbitLabels p a) :
    InsidePath (footprint p d a) a i := by
  have hc := ((BufferProgram.mem_orbitLabels p a i).mp hi).1
  obtain ⟨k,rfl⟩ := hc.exists_nat_pow_eq
  have hiter (m : ℕ) : InsidePath (footprint p d a) a (((p⁻¹)^m) a) := by
    induction m with
    | zero => exact Relation.ReflTransGen.refl
    | succ m ih =>
      have hm : ((p⁻¹)^m) a ∈ BufferProgram.orbitLabels p a :=
        (BufferProgram.mem_orbitLabels p a _).mpr
          ⟨Equiv.Perm.SameCycle.pow_right (Equiv.Perm.SameCycle.refl _ _),ha⟩
      have ht := arrow_target_path hd a _ hm
      simpa only [pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.inv_def] using ih.trans ht
  exact hiter k

theorem root_path {p : State n} {d : Fin n → ℤ} (hd : AffineLift.IsLift p 0 d)
    (a : Fin n) (ha : p⁻¹ a ≠ a) (x : Fin n) (hx : x ∈ footprint p d a) :
    InsidePath (footprint p d a) a x := by
  obtain ⟨i,hi,ht⟩ := (mem_footprint p d a x).mp hx
  exact (support_path hd a i ha hi).trans (arrow_touch_path p d a i x hi ht)

theorem connected {p : State n} {d : Fin n → ℤ} (hd : AffineLift.IsLift p 0 d)
    (a : Fin n) (ha : p⁻¹ a ≠ a) (x : Fin n) (hx : x ∈ footprint p d a)
    (y : Fin n) (hy : y ∈ footprint p d a) : InsidePath (footprint p d a) x y := by
  exact (inside_path_symm _ (root_path hd a ha x hx)).trans (root_path hd a ha y hy)

#print axioms support_path
#print axioms connected
end LRX.CycleFootprint
