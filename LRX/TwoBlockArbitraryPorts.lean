import LRX.TwoBlockOuterRoute
import LRX.PortApproachWord

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords BalancedTwoBlockPorts
variable {n : ℕ} [NeZero n]

/-- Four literal internal routes plus their shortest approaches handle arbitrary cursors. -/
theorem two_block_arbitrary_cursor_word (a : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ n-a)
    (p : State n) (hcut : ∀ i : Fin n, (p i).val < a ↔ i.val < a)
    (start finish : Fin n) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(a.choose 2 : ℤ)+((n-a).choose 2 : ℤ)+(n/2 : ℕ) := by
  let A0 : Fin n := ⟨a/2-1,by omega⟩
  let A1 : Fin n := ⟨(a-1)/2,by omega⟩
  let B0 : Fin n := ⟨a+((n-a)/2-1),by omega⟩
  let B1 : Fin n := ⟨a+(n-a-1)/2,by omega⟩
  have hN : (a : ℤ)+((n-a : ℕ) : ℤ)=(n : ℤ) := by omega
  have hA0 : (A0 : ℤ)=((a : ℤ)-2)/2 := by dsimp [A0]; omega
  have hA1 : (A1 : ℤ)=((a : ℤ)-1)/2 := by dsimp [A1]; omega
  have hB0 : (B0 : ℤ)=(a : ℤ)+(((n-a : ℕ) : ℤ)-2)/2 := by dsimp [B0]; omega
  have hB1 : (B1 : ℤ)=(a : ℤ)+(((n-a : ℕ) : ℤ)-1)/2 := by dsimp [B1]; omega
  have hhalf : (n : ℤ)/2=((n/2 : ℕ) : ℤ) := by omega
  have hs := start.isLt
  have ht := finish.isLt
  have hcover := LRX.TwoBlockPorts.four_center_cover (a : ℤ) ((n-a : ℕ) : ℤ) (start : ℤ) (finish : ℤ)
    (by omega) (by omega) (by positivity) (by omega) (by positivity) (by omega)
  rw [hN,← hA1,← hB0,← hB1,← hA0,hhalf] at hcover
  have extend (s t : Fin n) (w : List Letter)
      (he : eval w=(RotationWords.rotation s)⁻¹*p*RotationWords.rotation t)
      (hl : (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(a.choose 2 : ℤ)+((n-a).choose 2 : ℤ))
      (hc : lee (n : ℤ) (start : ℤ) (s : ℤ)+lee (n : ℤ) (finish : ℤ) (t : ℤ) ≤ (n/2 : ℕ)) :
      ∃ v : List Letter, eval v=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
        (v.length : ℤ) ≤ (inversionNumber p : ℤ)+(a.choose 2 : ℤ)+((n-a).choose 2 : ℤ)+(n/2 : ℕ) := by
    obtain ⟨v,hv,hprice⟩ := approach_word p s t start finish w he
    exact ⟨v,hv,by omega⟩
  rcases hcover with h | h | h | h
  · obtain ⟨w,he,hl⟩ := two_block_cut_internal_word a ha hb p hcut
    exact extend A1 B0 w he hl h
  · obtain ⟨w,he,hl⟩ := two_block_cut_reverse_internal_word a ha hb p hcut
    exact extend B0 A1 w he hl h
  · obtain ⟨w,he,hl⟩ := two_block_cut_outer_word a ha hb p hcut
    exact extend B1 A0 w he hl h
  · obtain ⟨w,he,hl⟩ := two_block_cut_reverse_outer_word a ha hb p hcut
    exact extend A0 B1 w he hl h

#print axioms two_block_arbitrary_cursor_word
end LRX.FiniteCuts
