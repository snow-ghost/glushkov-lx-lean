import LRX.ProtectedHoleLengths

namespace LRX.ContractionBlocks.System
open scoped BigOperators
variable {m : ℕ}

theorem full_cycle_crosses_cut (P : State (m+1)) (hp : P.IsCycle)
    (hf : P.support=Finset.univ) (gap : Fin m) :
    ∃ x, x.val ≤ gap.val ∧ gap.val < (P x).val := by
  by_contra hn
  have hclosed : ∀ x : Fin (m+1), x.val ≤ gap.val → (P x).val ≤ gap.val := by
    intro x hx
    by_contra h
    exact hn ⟨x,hx,by omega⟩
  have h0 : P 0 ≠ 0 := Equiv.Perm.mem_support.mp (by simp [hf])
  have hlast : P (Fin.last m) ≠ Fin.last m := Equiv.Perm.mem_support.mp (by simp [hf])
  obtain ⟨t,ht⟩ := (hp.sameCycle h0 hlast).exists_nat_pow_eq
  have hc : ∀ t : ℕ, ((P^t) 0).val ≤ gap.val := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ']
      exact hclosed _ ih
  have hh := hc t
  rw [ht] at hh
  have hg := gap.isLt
  simp only [Fin.val_last] at hh
  omega

theorem internal_hole_short (P : State (m+1)) (hp : P.IsCycle)
    (hfull : P.support=Finset.univ) (gap : Fin m)
    (f : Fin (m+1) → ℤ) (hf : StrictMono f) (h : ℤ)
    (hshort : ∀ x, |f (P x)-f x| ≤ h) : f gap.succ-f gap.castSucc ≤ h := by
  obtain ⟨x,hx,hpx⟩ := full_cycle_crosses_cut P hp hfull gap
  have hl := hf.monotone (show x ≤ gap.castSucc by exact hx)
  have hr := hf.monotone (show gap.succ ≤ P x by change gap.val+1 ≤ (P x).val; omega)
  have hs := hshort x
  have hab := le_abs_self (f (P x)-f x)
  omega

/-- The hypotheses used in §9.3 imply both the threshold size condition and
the strict geometric inequality needed throughout protected contractions. -/
theorem dominant_hole_threshold_conditions (P : State (m+1)) (hp : P.IsCycle)
    (hfull : P.support=Finset.univ) (gap : Fin m)
    (f : Fin (m+1) → ℤ) (hf : StrictMono f) (h : ℤ)
    (hshort : ∀ x, |f (P x)-f x| ≤ h)
    (n s a z : ℕ) (hn : n=m+1+s) (hhalf : 2*h < n)
    (hthreshold : (a : ℤ)+z ≤ 2*(f gap.succ-f gap.castSucc-1)-s) :
    a+z < m+1 ∧ h < (m : ℤ)+2-a-z+(f gap.succ-f gap.castSucc-1) := by
  have hb := internal_hole_short P hp hfull gap f hf h hshort
  constructor <;> omega

/-- Protected form of (29) under the ambient parameters of the dominant
internal-hole case. No stepwise absence-of-extreme-arrow hypothesis remains. -/
theorem dominant_hole_selected_bound (P : State (m+1)) (hp : P.IsCycle)
    (hs : FiniteCuts.Shallow P) (hfull : P.support=Finset.univ)
    (f : Fin (m+1) → ℤ) (hf : StrictMono f) (h : ℤ)
    (hshort : ∀ x, |f (P x)-f x| ≤ h)
    (gap : Fin m) (n s a z : ℕ) (hn : n=m+1+s) (hhalf : 2*h < n)
    (ha : 0 < a) (hz : 0 < z)
    (hthreshold : (a : ℤ)+z ≤ 2*(f gap.succ-f gap.castSucc-1)-s) :
    ∃ (k : ℕ) (q : State k) (B : System P q), History P q B ∧
      B.Protected gap.val ∧ B.selected.card ≤ a+z-1 ∧
      ((B.positive.card=a ∧ physicalLength B.positive P f ≤
          (a : ℤ)*z+(min a z : ℕ)*(holeMass f-(f gap.succ-f gap.castSucc-1))) ∨
       (B.negative.card=z ∧ physicalLength B.negative P f ≤
          (a : ℤ)*z+(min a z : ℕ)*(holeMass f-(f gap.succ-f gap.castSucc-1)))) := by
  obtain ⟨hsize,hwide⟩ := dominant_hole_threshold_conditions P hp hfull gap f hf h hshort
    n s a z hn hhalf hthreshold
  exact shallow_protected_physical_bound P hp hs hfull f hf a z ha hz hsize gap h hshort hwide

#print axioms dominant_hole_selected_bound
end LRX.ContractionBlocks.System
