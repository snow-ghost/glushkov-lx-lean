import LRX.MaximalEventSupport
import LRX.LinearEventComponents

namespace LRX.ZeroGap
variable {n : ℕ} [NeZero n]

theorem maximal_event_pair_mem (events : List (Event n))
    (hcard : (events.map eventSwap).prod.support.card=2*events.length)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val)
    (a b : Fin n) (hab : a.val < b.val)
    (hp : (events.map eventSwap).prod a=b) : (a,b) ∈ events := by
  have ha : a ∈ (events.map eventSwap).prod.support := by
    apply Equiv.Perm.mem_support.mpr
    rw [hp]
    intro heq
    have := congrArg Fin.val heq
    omega
  have hm := event_product_support_subset_endpoints events ha
  obtain ⟨e,he,hor⟩ := (mem_endpoints events a).mp hm
  obtain ⟨_,hl,hr⟩ := maximal_event_support_pair events hcard e he
  have hel := hlinear e he
  rcases hor with rfl | rfl
  · have hb : e.2=b := hl.symm.trans hp
    have heq : e=(e.1,b) := by rw [← hb]
    rwa [heq] at he
  · have hb : e.1=b := hr.symm.trans hp
    have := congrArg Fin.val hb
    omega

/-- LaterOutside for a minimal matching trace excludes alternating actual pairs. -/
theorem maximal_event_pairs_noncrossing (events : List (Event n))
    (hcard : (events.map eventSwap).prod.support.card=2*events.length)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val)
    (hsep : events.Pairwise LaterOutside)
    (a b c d : Fin n) (hab : a.val < b.val) (hbc : b.val < c.val) (hcd : c.val < d.val)
    (hac : (events.map eventSwap).prod a=c) : (events.map eventSwap).prod b ≠ d := by
  intro hbd
  have he := maximal_event_pair_mem events hcard hlinear a c (by omega) hac
  have hf := maximal_event_pair_mem events hcard hlinear b d (by omega) hbd
  rcases event_pair_order events hsep he hf with h | h | h
  · have hh := congrArg (fun e : Event n => e.1.val) h
    change a.val=b.val at hh
    omega
  · exact h.1 ((inside_linear_iff (a,c) (by dsimp; omega) b).mpr ⟨hab,hbc⟩)
  · exact h.2 ((inside_linear_iff (b,d) (by dsimp; omega) c).mpr ⟨hbc,hcd⟩)

#print axioms maximal_event_pairs_noncrossing
end LRX.ZeroGap
