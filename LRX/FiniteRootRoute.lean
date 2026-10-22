import LRX.SelectedRootScan

/-! A complete finite-root route directly from a permutation, using its
canonical cycle factorization and an automatic choice of child services. -/
namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {b : ℕ}

noncomputable def factorList (p : State b) : List (State b) := p.cycleFactorsFinset.toList

theorem factor_list_spec (p : State b) :
    (∀ q ∈ factorList p, q.IsCycle) ∧
      (factorList p).Pairwise Equiv.Perm.Disjoint ∧ (factorList p).prod=p := by
  classical
  apply (Equiv.Perm.cycleFactorsFinset_eq_list_toFinset (Finset.nodup_toList _)).mp
  simp

variable [NeZero b]

theorem finite_root_route (hb : 2 ≤ b) (p : State b) (hroot : p 0 ≠ 0)
    (u v : Fin b) (hu : p.SameCycle 0 u) (hv : p.SameCycle 0 v)
    (hinside : ∀ i, p i ≠ i → u.val ≤ i.val ∧ i.val ≤ v.val) (finish : Fin b) :
    ∃ w : List Letter, eval w=p⁻¹*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin b => (p i : ℤ)) : ℤ)+
        (∑ i : Fin b, |displacement p i|)-portLoad (displacement p) 0-
        2*((selectedCycles (factorList p) (finish.val+1)).map
          (fun q => (leftPeak q (finish.val+1) : ℤ))).sum+(finish.val : ℤ) := by
  obtain ⟨hc,hd,hp⟩ := factor_list_spec p
  have h := selected_root_scan hb (factorList p) hc hd
    (by rw [hp]; exact hroot) u v (by rw [hp]; exact hu) (by rw [hp]; exact hv)
    (by rw [hp]; exact hinside) finish
  simpa only [hp] using h

/-- Paid left-boundary line for arbitrary starting and finishing cursors. -/
theorem finite_root_left_line (hb : 2 ≤ b) (p : State b) (hroot : p 0 ≠ 0)
    (u v : Fin b) (hu : p.SameCycle 0 u) (hv : p.SameCycle 0 v)
    (hinside : ∀ i, p i ≠ i → u.val ≤ i.val ∧ i.val ≤ v.val) (start finish : Fin b) :
    ∃ w : List Letter,
      eval w=(RotationWords.rotation start)⁻¹*p⁻¹*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin b => (p i : ℤ)) : ℤ)+
        (∑ i : Fin b, |displacement p i|)-portLoad (displacement p) 0-
        2*((selectedCycles (factorList p) (finish.val+1)).map
          (fun q => (leftPeak q (finish.val+1) : ℤ))).sum+
        (start.val : ℤ)+(finish.val : ℤ) := by
  obtain ⟨w,he,hl⟩ := finite_root_route hb p hroot u v hu hv hinside finish
  refine ⟨spin (-(start.val : ℤ)) ++ w, ?_, ?_⟩
  · rw [eval_append,spin_eval,he]
    simp [RotationWords.rotation,mul_assoc]
  · simp only [List.length_append,spin_length,Int.natAbs_neg,Int.natAbs_natCast,Nat.cast_add]
    linarith

#print axioms finite_root_route
#print axioms finite_root_left_line
end LRX.FiniteCuts
