import LRX.ServiceExtension

/-! Finite saturation of real service certificates. Maximality is over finite
sets of labels, not over arbitrary programs. Every reachable cycle is covered. -/
namespace LRX.BufferProgram
variable {n : ℕ} [NeZero n]

def Saturated {p : State n} {d : Fin n → ℤ} (C : ServiceCertificate p d) : Prop :=
  ∀ a : Fin n, (p⁻¹) a ≠ a →
    Visits C.program initialLogical (PeriodicBuffer.contract (n : ℤ) (a : ℤ)) → a ∈ C.labels

theorem exists_saturated_service {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hroot : (p⁻¹) 0 ≠ 0) :
    ∃ C : ServiceCertificate p d, Saturated C := by
  classical
  let candidates : Finset (Finset (Fin n)) := Finset.univ.filter
    (fun S => ∃ C : ServiceCertificate p d, C.labels=S)
  obtain ⟨seed⟩ := root_service_certificate hd hroot
  have hn : candidates.Nonempty := by
    exact ⟨seed.labels, Finset.mem_filter.mpr ⟨Finset.mem_univ _, seed, rfl⟩⟩
  obtain ⟨S, hS, hmax⟩ := candidates.exists_max_image Finset.card hn
  obtain ⟨C, hC⟩ := (Finset.mem_filter.mp hS).2
  refine ⟨C, ?_⟩
  intro a ha hv
  by_contra hnew
  obtain ⟨D, hD⟩ := extend_service hd C a ha hnew hv
  have hDmem : D.labels ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, D, rfl⟩
  have hle : D.labels.card ≤ C.labels.card := by simpa only [← hC] using hmax D.labels hDmem
  have hsub : C.labels ⊂ D.labels := by
    rw [hD]
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_union_left, ?_⟩
    intro he
    have hm : a ∈ C.labels ∪ orbitLabels p a := Finset.mem_union_right _ (mem_own_orbit p a ha)
    rw [← he] at hm
    exact hnew hm
  have hlt := Finset.card_lt_card hsub
  omega

/-- Edges are either within a target cycle, or a lifted arrow passing through
a periodic copy of a vertex of a nontrivial target cycle. -/
def ServiceEdge (p : State n) (d : Fin n → ℤ) (i j : Fin n) : Prop :=
  (p⁻¹).SameCycle i j ∨ ((p⁻¹) j ≠ j ∧ ∃ k : ℤ,
    min (i : ℤ) ((i : ℤ)+d i) ≤ (j : ℤ)+k*(n : ℤ) ∧
    (j : ℤ)+k*(n : ℤ) ≤ max (i : ℤ) ((i : ℤ)+d i))

theorem saturated_edge_closed {p : State n} {d : Fin n → ℤ}
    (C : ServiceCertificate p d) (hs : Saturated C) {i j : Fin n}
    (hi : i ∈ C.labels) (he : ServiceEdge p d i j) : j ∈ C.labels := by
  rcases he with he | ⟨hj, k, hseg⟩
  · exact invariant_sameCycle p C.labels C.invariant hi he
  · apply hs j hj
    have hv := C.ports i hi ((j : ℤ)+k*(n : ℤ)) hseg
    apply visits_modEq _ _ hv
    have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-k, ?_⟩
    rw [PeriodicBuffer.contract_period hn]
    simp only [BufferMachine.slots]
    ring

theorem saturated_reachable {p : State n} {d : Fin n → ℤ}
    (C : ServiceCertificate p d) (hs : Saturated C) {i : Fin n}
    (hi : Relation.ReflTransGen (ServiceEdge p d) 0 i) : i ∈ C.labels := by
  induction hi with
  | refl => exact C.root_mem
  | tail hpath hedge ih => exact saturated_edge_closed C hs ih hedge

#print axioms exists_saturated_service
#print axioms saturated_reachable
end LRX.BufferProgram
