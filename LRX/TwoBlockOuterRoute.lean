import LRX.TwoBlockRecenter

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- The same construction through the other boundary, restored to the original target. -/
theorem two_block_cut_outer_word (a : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ n-a)
    (p : State n) (hcut : ∀ i : Fin n, (p i).val < a ↔ i.val < a) :
    ∃ w : List Letter,
      eval w=(RotationWords.rotation (⟨a+(n-a-1)/2,by omega⟩ : Fin n))⁻¹*p*
        RotationWords.rotation (⟨a/2-1,by omega⟩ : Fin n) ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(a.choose 2 : ℤ)+((n-a).choose 2 : ℤ) := by
  let r : Fin n := ⟨a,by omega⟩
  let q := localTarget p 0 r
  obtain ⟨hqcut,hI⟩ := invariant_cut_recenter_blocks p a (by omega) (by omega) hcut
  change (∀ i : Fin n, (q i).val < n-a ↔ i.val < n-a) at hqcut
  change inversionNumber q=inversionNumber p at hI
  have hsize : n-(n-a)=a := by omega
  obtain ⟨w,he,hl⟩ := two_block_cut_internal_word (n-a) hb (by omega) q hqcut
  simp only [hsize] at he hl
  let s0 : Fin n := ⟨(n-a-1)/2,by omega⟩
  let t0 : Fin n := ⟨n-a+(a/2-1),by omega⟩
  let start : Fin n := ⟨a+(n-a-1)/2,by omega⟩
  let finish : Fin n := ⟨a/2-1,by omega⟩
  have hs : start-r=s0 := by
    apply Fin.ext
    rw [Fin.sub_val_of_le (show r ≤ start by change a ≤ a+(n-a-1)/2; omega)]
    dsimp [start,r,s0]
    omega
  have ht : finish-r=t0 := by
    apply Fin.ext
    rw [Fin.coe_sub_iff_lt.mpr (show finish < r by change a/2-1 < a; omega)]
    dsimp [finish,r,t0]
    omega
  change eval w=(RotationWords.rotation s0)⁻¹*q*RotationWords.rotation t0 at he
  have hrestore := shifted_word_target p r start finish
  rw [hs,ht] at hrestore
  refine ⟨w,he.trans hrestore,?_⟩
  rw [hI] at hl
  omega

theorem two_block_cut_reverse_outer_word (a : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ n-a)
    (p : State n) (hcut : ∀ i : Fin n, (p i).val < a ↔ i.val < a) :
    ∃ w : List Letter,
      eval w=(RotationWords.rotation (⟨a/2-1,by omega⟩ : Fin n))⁻¹*p*
        RotationWords.rotation (⟨a+(n-a-1)/2,by omega⟩ : Fin n) ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(a.choose 2 : ℤ)+((n-a).choose 2 : ℤ) := by
  have hcutInv : ∀ i : Fin n, (p⁻¹ i).val < a ↔ i.val < a := invariant_cut_inverse p a hcut
  obtain ⟨w,he,hl⟩ := two_block_cut_outer_word a ha hb p⁻¹ hcutInv
  refine ⟨w.reverse.map Letter.inverse,?_,?_⟩
  · rw [eval_inverse_word,he]
    simp only [mul_inv_rev,inv_inv,mul_assoc]
  · simp only [List.length_map,List.length_reverse]
    rwa [inversion_number_inverse] at hl

#print axioms two_block_cut_outer_word
#print axioms two_block_cut_reverse_outer_word
end LRX.FiniteCuts
