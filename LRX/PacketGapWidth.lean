import LRX.PacketCoreBalance
import LRX.NarrowWindowLift

/-! A packet arrow visiting an open packet gap crosses its whole width.
Majorization then bounds the size of every such internal gap. -/
namespace LRX.PrunedLift
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem core_copy_outside_gap (p : State n) (d : Fin n → ℤ) (r : Fin n)
    (hgap : ∀ i : Fin n, 0 < i.val → i.val < r.val → ¬InCore p d 0 i)
    (z : ℤ) (hz : InCore p d 0 (z : Fin n)) : z ≤ 0 ∨ (r : ℤ) ≤ z := by
  by_contra h
  push Not at h
  have hn : (r : ℤ) < (n : ℤ) := by exact_mod_cast r.isLt
  have he : ((z : Fin n) : ℤ)=z := by
    simp [Int.emod_eq_of_lt (le_of_lt h.1) (lt_trans h.2 hn),le_of_lt h.1]
  exact hgap (z : Fin n) (by exact_mod_cast (show (0 : ℤ) < ((z : Fin n) : ℤ) by omega))
    (by exact_mod_cast (show ((z : Fin n) : ℤ) < (r : ℤ) by omega)) hz

theorem core_arrow_gap_length {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (r : Fin n)
    (hgap : ∀ i : Fin n, 0 < i.val → i.val < r.val → ¬InCore p d 0 i)
    (i : Fin n) (hi : InCore p d 0 i) (x : Fin n) (hx : 0 < x.val) (hx' : x.val < r.val)
    (ht : BufferProgram.Touches (n : ℤ) (i : ℤ) (d i) (x : ℤ)) : (r : ℤ) ≤ |d i| := by
  obtain ⟨k,hlo,hhi⟩ := ht
  have hi' : InCore p d 0 (p.symm i) :=
    in_core_same_cycle p d 0 hi (Equiv.Perm.SameCycle.refl _ _).apply_right
  have hstart : (((i : ℤ)-k*(n : ℤ) : ℤ) : Fin n)=i := by simp
  have hfinish : (((i : ℤ)+d i-k*(n : ℤ) : ℤ) : Fin n)=p.symm i := by
    calc
      _ = (((i : ℤ)+d i : ℤ) : Fin n) := by simp
      _ = p.symm i := by simpa using AffineLift.lift_residue hd i
  have ha := core_copy_outside_gap p d r hgap ((i : ℤ)-k*(n : ℤ)) (by simpa only [hstart] using hi)
  have hb := core_copy_outside_gap p d r hgap ((i : ℤ)+d i-k*(n : ℤ)) (by simpa only [hfinish] using hi')
  have hxa : (0 : ℤ) < x := by exact_mod_cast hx
  have hxb : (x : ℤ) < r := by exact_mod_cast hx'
  have habs := le_abs_self (d i)
  have habs' := neg_le_abs (d i)
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega

theorem internal_gap_width {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (r : Fin n) (b : ℕ)
    (hr : r.val=b+1)
    (hgap : ∀ i : Fin n, 0 < i.val → i.val < r.val → ¬InCore p d 0 i)
    (ht : ∃ i x : Fin n, InCore p d 0 i ∧ 0 < x.val ∧ x.val < r.val ∧
      BufferProgram.Touches (n : ℤ) (i : ℤ) (d i) (x : ℤ)) : 2*(b+1) < n := by
  obtain ⟨i,x,hi,hx,hx',hvisit⟩ := ht
  have hlen := core_arrow_gap_length hd r hgap i hi x hx hx' hvisit
  have hshort := FiniteWindow.majorized_short hd hm i
  omega

#print axioms core_arrow_gap_length
#print axioms internal_gap_width
end LRX.PrunedLift
