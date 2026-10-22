import LRX.SourceGapComponent
import LRX.WindowReversalComponentEquality

namespace LRX.FiniteWindow
open FiniteCuts RotationWords
variable {n : ℕ} [NeZero n]

/-- A whole disjoint family of internally loaded windows preserves positive ports. -/
theorem reverse_windows_positive_port_iff (As : List (FillingWindow n)) (p : State n)
    (hmatch : ∀ A ∈ As, A.Matches p) (hapart : As.Pairwise FillingWindow.Apart)
    (hloaded : ∀ A ∈ As, ∀ r : Fin n,
      A.window.offset < r.val+1 → r.val+1 < A.window.offset+A.size →
      0 < portLoad (displacement p) r) (r : Fin n) :
    0 < portLoad (displacement (reverseWindows As p)) r ↔
      0 < portLoad (displacement p) r := by
  induction As generalizing p with
  | nil => rfl
  | cons A As ih =>
    have hm := hmatch A (List.mem_cons_self ..)
    obtain ⟨hA,hAs⟩ := List.pairwise_cons.mp hapart
    have hstep (s : Fin n) := replace_reversal_positive_port_iff A.window p A.filling hm
      (hloaded A (List.mem_cons_self ..)) s
    have hmAs : ∀ B ∈ As, B.Matches (A.reverseIn p) := by
      intro B hB
      exact FillingWindow.matches_after_apart A B p (hA B hB)
        (hmatch B (List.mem_cons_of_mem _ hB))
    have hlAs : ∀ B ∈ As, ∀ s : Fin n,
        B.window.offset < s.val+1 → s.val+1 < B.window.offset+B.size →
        0 < portLoad (displacement (A.reverseIn p)) s := by
      intro B hB s hs hs'
      exact (hstep s).mpr (hloaded B (List.mem_cons_of_mem _ hB) s hs hs')
    exact (ih (A.reverseIn p) hmAs hAs hlAs).trans (hstep r)

/-- Positive-port equality determines the full load-path relation. -/
theorem load_path_iff_of_positive_ports (d e : Fin n → ℤ)
    (hports : ∀ r, 0 < portLoad d r ↔ 0 < portLoad e r) (a b : Fin n) :
    CycleFootprint.LoadPath d a b ↔ CycleFootprint.LoadPath e a b := by
  have hdir (d e : Fin n → ℤ) (hh : ∀ r, 0 < portLoad d r → 0 < portLoad e r)
      (a b : Fin n) (hp : CycleFootprint.LoadPath d a b) : CycleFootprint.LoadPath e a b := by
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | @tail x y hp he ih =>
      apply ih.tail
      rcases he with ⟨he,hp⟩ | ⟨he,hp⟩
      · exact Or.inl ⟨he,hh x hp⟩
      · exact Or.inr ⟨he,hh y hp⟩
  exact ⟨hdir d e (fun r => (hports r).mp) a b,
    hdir e d (fun r => (hports r).mpr) a b⟩
end LRX.FiniteWindow

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
variable {n : ℕ} [NeZero n]

theorem positive_source_family_internal_ports (p : State n) (L : ℕ)
    (A : FillingWindow n) (hA : A ∈ positiveSourceFamily p L) (r : Fin n)
    (hr : A.window.offset < r.val+1) (hr' : r.val+1 < A.window.offset+A.size) :
    0 < portLoad (displacement p.symm) r := by
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hA
  change u.val.val+1 < r.val+1 at hr
  change r.val+1 < u.val.val+1+(FiniteGaps.next (sourcePackets p) u.val-u.val.val-1) at hr'
  have hn := FiniteGaps.lt_next (sourcePackets p) u.val
  exact selected_source_gap_ports_positive p L u r (by omega) (by omega)

/-- Reversing all extracted source gaps preserves every component exactly. -/
theorem source_reversal_component_eq (p : State n) (L : ℕ) (a : Fin n) :
    CycleFootprint.component (displacement (reverseWindows (positiveSourceFamily p L) p.symm)) a =
      componentSet p a := by
  obtain ⟨hm,hd,_,_⟩ := positive_source_family_spec p L
  have hports := reverse_windows_positive_port_iff (positiveSourceFamily p L) p.symm hm hd
    (positive_source_family_internal_ports p L)
  ext b
  change b ∈ CycleFootprint.component _ a ↔ b ∈ CycleFootprint.component _ a
  simp only [CycleFootprint.mem_component]
  exact load_path_iff_of_positive_ports _ _ hports a b

#print axioms source_reversal_component_eq
end LRX.FiniteCuts
