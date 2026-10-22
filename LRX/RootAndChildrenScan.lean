import LRX.RemainingRootService
import LRX.FiniteReducedScan

/-! Assemble the retained root factor and separately served finite cycles.
The resulting literal word has the full target and both root and child discounts. -/
namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {b : ℕ} [NeZero b]

theorem root_and_children_scan (hb : 2 ≤ b) (root : State b) (l : List (State b))
    (hcycles : ∀ q ∈ l, q.IsCycle)
    (hd : ((root⁻¹)::l).Pairwise Equiv.Perm.Disjoint) (hroot : root 0 ≠ 0)
    (u v : Fin b) (hu : ((root⁻¹)::l).prod.SameCycle 0 u)
    (hv : ((root⁻¹)::l).prod.SameCycle 0 v)
    (hinside : ∀ i, ((root⁻¹)::l).prod i ≠ i → u.val ≤ i.val ∧ i.val ≤ v.val)
    (finish : Fin b) (hpos : ∀ q ∈ l, 0 < leftPeak q (finish.val+1)) :
    ∃ w : List Letter, eval w=((root⁻¹)::l).prod⁻¹*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin b => (((root⁻¹)::l).prod i : ℤ)) : ℤ)+
        (∑ i : Fin b, |displacement ((root⁻¹)::l).prod i|)-
        portLoad (displacement ((root⁻¹)::l).prod) 0-
        2*(l.map (fun q => (leftPeak q (finish.val+1) : ℤ))).sum+(finish.val : ℤ) := by
  obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hd
  have hdis : root.Disjoint l.prod⁻¹ := by
    have h := Equiv.Perm.disjoint_prod_right l hhead
    exact h.inv_left.inv_right
  have hfull : ((root⁻¹)::l).prod⁻¹=root*l.prod⁻¹ := by
    rw [← inverse_cycle_product ((root⁻¹)::l) hd, ← inverse_cycle_product l htail]
    simp
  have hinv : (root*l.prod⁻¹)⁻¹=((root⁻¹)::l).prod := by rw [← hfull]; simp
  obtain ⟨a,ha,hat,had,har⟩ := PrunedLift.remaining_root_service hb root l.prod⁻¹ hdis hroot
    u v (by rw [hinv]; exact hu) (by rw [hinv]; exact hv) (by rw [hinv]; exact hinside)
  have har' : (BufferProgram.rotations a.service.word : ℤ)=
      (∑ i : Fin b, |displacement (root⁻¹) i|)-portLoad (displacement ((root⁻¹)::l).prod) 0 := by
    unfold displacement
    simpa only [← Equiv.Perm.inv_def, hinv] using har
  obtain ⟨ss,ht,hdisp,hp,hc⟩ := left_peak_exact_family hb l hcycles (finish.val+1) (by omega) hpos
  have htargets : (a::ss).map (fun c => c.service.target)=((root⁻¹)::l).map (fun q => q⁻¹) := by
    simp [hat,ht]
  have hdisps : (a::ss).map ExactService.displacement=((root⁻¹)::l).map displacement := by
    simp only [List.map_cons,had,hdisp]
    rfl
  have hdisall : (a::ss).Pairwise (fun c d => c.service.target.Disjoint d.service.target) := by
    apply List.pairwise_map.mp
    rw [htargets]
    exact inverse_targets_disjoint _ hd
  have hsum (i : Fin b) : ((a::ss).map (fun c => c.displacement i)).sum=
      (((root⁻¹)::l).map (fun q => displacement q i)).sum := by
    have h := congrArg (fun fs : List (Fin b → ℤ) => (fs.map (fun f => f i)).sum) hdisps
    simpa [List.map_map,Function.comp_def] using h
  have hend : (fun i : Fin b => (i : ℤ)+((a::ss).map (fun c => c.displacement i)).sum)=
      (fun i => (((root⁻¹)::l).prod i : ℤ)) := by
    funext i
    rw [hsum, ← displacement_list_prod _ hd]
    simp [displacement]
  obtain ⟨w,he,hl⟩ := ordered_reduced_route hb (a::ss) hdisall finish (by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · simp [ha]
    · have := hp c hc; omega)
  refine ⟨w, ?_, ?_⟩
  · rw [htargets,inverse_cycle_product _ hd] at he
    exact he
  · rw [hend] at hl
    have hcast : ((((a::ss).map (fun c => BufferProgram.rotations c.service.word)).sum : ℕ) : ℤ)=
        ((a::ss).map (fun c => (BufferProgram.rotations c.service.word : ℤ))).sum := by simp [Function.comp_def]
    have hl' : (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin b => (((root⁻¹)::l).prod i : ℤ)) : ℤ)+
        ((((a::ss).map (fun c => BufferProgram.rotations c.service.word)).sum : ℕ) : ℤ)+
        (finish.val : ℤ) := by exact_mod_cast hl
    rw [hcast,List.map_cons,List.sum_cons,har',hc] at hl'
    have hsplit :
        (l.map (fun q => (∑ i : Fin b, |displacement q i|)-2*(leftPeak q (finish.val+1) : ℤ))).sum=
        (l.map (fun q => ∑ i : Fin b, |displacement q i|)).sum-
          2*(l.map (fun q => (leftPeak q (finish.val+1) : ℤ))).sum := by
      clear har hcycles hd hhead htail hdis hfull hinv hu hv hinside hpos har' ht hdisp hp hc htargets hdisps hdisall hsum hend he hl hl'
      induction l with
      | nil => simp
      | cons q rest ih => simp only [List.map_cons,List.sum_cons]; rw [ih]; ring
    rw [hsplit] at hl'
    have hm := displacement_mass_list_prod ((root⁻¹)::l) hd
    simp only [List.map_cons,List.sum_cons] at hm
    linarith

#print axioms root_and_children_scan
end LRX.FiniteCuts
