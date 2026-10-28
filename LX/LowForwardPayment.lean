import LX.CriticalPhaseWord
import LX.RankPeakCount
import LX.ReserveAwareAnchorPrice
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- A non-head forward minimum with enough finishing time pays the
quadratic part outright; no arbitrary gap cutoff is needed. -/
theorem low_forward_depth_paid (p : State n) (b : Fin n)
    (hh : 2 ≤ height p b) (hn : n=2*height p b+2 ∨ n=2*height p b+3)
    (hhead : p 0 ≠ p b-b)
    (hlast : ∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val)
    (hback : ¬(p b).val < b.val) (hgap : 0 < (b-p b).val)
    (hdepth : depthCount (displacement p b) (height p b-1) ≤ (b-p b).val) :
    ∃ w : List Letter,p*eval w=1 ∧ 4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n := by
  have hforward : b.val < (p b).val := by
    by_contra hnot
    have he : p b=b := Fin.ext (by omega)
    rw [he,sub_self,Fin.val_zero] at hgap
    omega
  have hcount : depthCount (displacement p b) (height p b-1) ≤ b.val+(-p b).val := by
    have hg : (b-p b).val ≤ b.val+(-p b).val := by
      rw [sub_eq_add_neg,Fin.val_add]
      exact Nat.mod_le _ _
    omega
  have hne : p b ≠ 0 := by intro he; rw [he,Fin.val_zero] at hforward; omega
  have hneg : (-p b).val=n-(p b).val := by simp [Fin.val_neg,hne]
  have hr := anchor_reserve_nonneg p b
  rcases hn with hn | hn
  · obtain ⟨w,hw,hprice⟩ := even_anchor_reserve_price p b hh hn hhead hlast hcount
    rw [hneg,Nat.cast_sub (Nat.le_of_lt (p b).isLt)] at hprice
    exact ⟨w,hw,by omega⟩
  · obtain ⟨w,hw,hprice⟩ := odd_lower_anchor_reserve_price p b hh hn hhead hlast hcount
    rw [hneg,Nat.cast_sub (Nat.le_of_lt (p b).isLt)] at hprice
    exact ⟨w,hw,by omega⟩

/-- Count only explicitly excepted minimum gaps and the actual low head.
All other non-backward representatives are paid by the supplied words. -/
theorem low_offset_count_of_forward_payment (p : State n) (h : ℕ) (E : Finset ℕ) {C : ℤ}
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*C)
    (hpay : ∀ b,height p b=h → (b-p b).val ∉ E → p 0 ≠ p b-b →
      (∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val) → ¬(p b).val < b.val →
      ∃ w : List Letter,p*eval w=1 ∧ 4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*C) :
    (minimumHeightOffsets p h).card ≤
      ((descendingPositions p).filter fun i => height p i=h).card+E.card+
        (if height p 0=h then 1 else 0) := by
  classical
  let B := E.image (fun k : ℕ => -(k : Fin n))
  let H : Finset (Fin n) := if height p 0=h then {p 0} else ∅
  let U := B ∪ H
  let V := ((descendingPositions p).filter fun i => height p i=h).image (fun i => p i-i)
  have hsub : minimumHeightOffsets p h ⊆ V ∪ U := by
    intro t ht
    by_cases hbad : t ∈ U
    · exact Finset.mem_union_right _ hbad
    obtain ⟨b,hb,hbt⟩ := Finset.mem_image.mp ht
    have hbh := (Finset.mem_filter.mp hb).2
    obtain ⟨c,hraw,hch,_,hlast⟩ := last_offset_source p b
    have hct : p c-c=t := hraw.trans hbt
    have hcHeight : height p c=h := hch.trans hbh
    by_cases hback : (p c).val < c.val
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨c,Finset.mem_filter.mpr
        ⟨(mem_descendingPositions _ _).mpr hback,hcHeight⟩,hct⟩
    have hgap : (c-p c).val ∉ E := by
      intro he
      apply hbad
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨(c-p c).val,he,?_⟩
      simp only [Fin.cast_val_eq_self]
      rw [← hct]
      ring
    have hhead : p 0 ≠ p c-c := by
      intro he
      apply hbad
      have ht0 : t=p 0 := hct.symm.trans he.symm
      have hperm : permutation p 0=permutation p c := by
        apply Equiv.ext
        intro i
        change p i+(0-p 0)=p i+(c-p c)
        linear_combination -he
      have hheight : height p 0=h :=
        (congrArg (fun q : State n => (descendingPositions q).card) hperm).trans hcHeight
      simp [U,H,hheight,ht0]
    exact False.elim (hunpaid (hpay c hcHeight hgap hhead hlast hback))
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le V U)
  have hV : V.card ≤ ((descendingPositions p).filter fun i => height p i=h).card := Finset.card_image_le
  have hB : B.card ≤ E.card := Finset.card_image_le
  have hH : H.card=(if height p 0=h then 1 else 0) := by dsimp [H]; split_ifs <;> simp
  have hU : U.card ≤ E.card+(if height p 0=h then 1 else 0) := by
    have hc := Finset.card_union_le B H
    rw [hH] at hc
    change U.card ≤ _ at hc
    omega
  omega

#print axioms low_forward_depth_paid
#print axioms low_offset_count_of_forward_payment
end LX.AnchoredPhases
