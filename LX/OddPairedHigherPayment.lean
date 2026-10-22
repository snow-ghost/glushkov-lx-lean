import LX.PairedAlignedPrefix

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Two aligned higher phases pay the larger terminal gap, independently
of the rank peak or the total next-depth count. -/
theorem odd_paired_higher_conjecture_word (p : State n) (a b : Fin n)
    (hn : n=2*height p a+1) (hh : 2 ≤ height p a)
    (hheight : height p b=height p a)
    (hheada : p 0 ≠ p a-a) (hheadb : p 0 ≠ p b-b)
    (hlasta : ∀ i : Fin n,p i-i=p a-a → i.val ≤ a.val)
    (hlastb : ∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val)
    (hfa : a.val+(-p a).val=(a-p a).val)
    (hfb : b.val+(-p b).val=(b-p b).val)
    (hgb : 0 < (b-p b).val) (hgap : (b-p b).val < (a-p a).val)
    (hpay : ((a-p a).val : ℤ)-anchorReserve p a ≤ (height p a : ℤ)+2) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9 := by
  obtain ⟨i,hi,hbound⟩ := paired_aligned_early_low_depth p a b hh hheight hheada hheadb
    hlasta hlastb hfa hfb hgb hgap
  obtain ⟨w,hw,_,hprice⟩ := aligned_anchor_prefix_gap_zero_word p a hh (by omega)
    hheada hlasta i hi (by omega)
  have hn' : (n : ℤ)=2*(height p a : ℤ)+1 := by exact_mod_cast hn
  have hfin : (a.val : ℤ)+((-p a).val : ℤ)=((a-p a).val : ℤ) := by exact_mod_cast hfa
  unfold anchorReserve at hpay
  refine ⟨w,hw,?_⟩
  nlinarith only [hprice,hpay,hn',hfin]

def HigherAlignedTerminal (p : State n) (h : ℕ) (a : Fin n) : Prop :=
  height p a=h+1 ∧ p 0 ≠ p a-a ∧
    (∀ i : Fin n,p i-i=p a-a → i.val ≤ a.val) ∧
    a.val+(-p a).val=(a-p a).val ∧
    0 < (a-p a).val ∧ (a-p a).val ≤ h+3

theorem odd_unpaid_aligned_terminal_unique (p : State n) (h : ℕ)
    (hn : n=2*h+3) (hh : 1 ≤ h)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9)
    (a b : Fin n) (ha : HigherAlignedTerminal p h a) (hb : HigherAlignedTerminal p h b) :
    p a-a=p b-b := by
  have hle (c d : Fin n) (hc : HigherAlignedTerminal p h c) (hd : HigherAlignedTerminal p h d) :
      (c-p c).val ≤ (d-p d).val := by
    by_contra hnot
    have hr := anchor_reserve_nonneg p c
    have hch := hc.1
    have hdh := hd.1
    exact hunpaid (odd_paired_higher_conjecture_word p c d (by omega) (by omega) (by omega)
      hc.2.1 hd.2.1 hc.2.2.1 hd.2.2.1 hc.2.2.2.1 hd.2.2.2.1
      hd.2.2.2.2.1 (by omega) (by have := hc.2.2.2.2.2; omega))
  have hab := hle a b ha hb
  have hba := hle b a hb ha
  have he : a-p a=b-p b := Fin.ext (by omega)
  linear_combination -he

theorem exists_unpaid_aligned_terminal_source (p : State n) (h : ℕ)
    (hn : n=2*h+3) (hh : 1 ≤ h)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    ∃ z : Fin n,∀ a,HigherAlignedTerminal p h a → p a-a=p z-z := by
  classical
  by_cases hex : ∃ z,HigherAlignedTerminal p h z
  · obtain ⟨z,hz⟩ := hex
    exact ⟨z,fun a ha => odd_unpaid_aligned_terminal_unique p h hn hh hunpaid a z ha hz⟩
  · exact ⟨0,fun a ha => False.elim (hex ⟨a,ha⟩)⟩

#print axioms odd_paired_higher_conjecture_word
#print axioms odd_unpaid_aligned_terminal_unique
end LX.AnchoredPhases
