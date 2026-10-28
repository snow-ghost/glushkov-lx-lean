import LX.LiftedRename
import Mathlib

/-! A lifted pair is a pair of finite labels together with an integer relative
copy offset. Equal pair events implement the same periodic involution. -/
namespace LX.Core.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def pairOffset (a b : Fin n) (shift : ℤ) (i : Fin n) : ℤ :=
  if i=a then shift else if i=b then -shift else 0

def pairRename (a b : Fin n) (shift : ℤ) : Configuration n → Configuration n :=
  rename (Equiv.swap a b) (pairOffset a b shift)

omit [NeZero n] in
theorem pair_offset_cancel (a b : Fin n) (shift : ℤ) (hab : a ≠ b) (i : Fin n) :
    pairOffset a b shift (Equiv.swap a b i)+pairOffset a b shift i=0 := by
  by_cases ha : i=a
  · subst i; simp [pairOffset, Ne.symm hab]
  · by_cases hb : i=b
    · subst i; simp [pairOffset, Ne.symm hab]
    · simp [pairOffset, ha, hb, Equiv.swap_apply_of_ne_of_ne ha hb]


omit [NeZero n] in
theorem configuration_ext_components {s t : Configuration n}
    (hp : s.physical=t.physical) (hz : s.position=t.position) (hc : s.cursor=t.cursor) : s=t := by
  cases s
  cases t
  cases hp
  cases hz
  cases hc
  rfl

theorem x_as_pair_rename (s : Configuration n) (a b : Fin n) (hab : a ≠ b)
    (ha : s.physical.tokens s.physical.cursor=a)
    (hb : s.physical.tokens (s.physical.cursor+1)=b) :
    step .x s=pairRename a b (s.position a+1-s.position b) s := by
  apply configuration_ext_components
  · have ht : s.physical.tokens*Equiv.swap s.physical.cursor (s.physical.cursor+1)=
        (Equiv.swap a b).symm*s.physical.tokens := by
      apply Equiv.ext
      intro i
      simpa only [Equiv.Perm.mul_apply, Equiv.symm_swap, ha, hb] using
        Function.Injective.map_swap s.physical.tokens.injective s.physical.cursor
          (s.physical.cursor+1) i
    simpa only [step, PhysicalModel.step, pairRename, rename] using
      congrArg (fun q => PhysicalModel.Configuration.mk q s.physical.cursor) ht
  · funext i
    simp only [step, pairRename, rename, ha, hb]
    by_cases hi : i=a
    · subst i
      simp [pairOffset, hab]
    · by_cases hj : i=b
      · subst i
        simp [pairOffset, Ne.symm hab]
        ring
      · simp [pairOffset, hi, hj, Equiv.swap_apply_of_ne_of_ne hi hj]
  · simp [step, increment, pairRename, rename]

omit [NeZero n] in
theorem pair_rename_reverse (a b : Fin n) (shift : ℤ) (hab : a ≠ b) :
    pairRename b a (-shift)=pairRename a b shift := by
  have ho : pairOffset b a (-shift)=pairOffset a b shift := by
    funext i
    by_cases ha : i=a
    · subst i; simp [pairOffset, hab]
    · by_cases hb : i=b
      · subst i; simp [pairOffset, Ne.symm hab]
      · simp [pairOffset, ha, hb]
  simp only [pairRename, Equiv.swap_comm b a, ho]

/-- Alignment forces the offset to be a whole number of turns. No quotient is
rounded or silently discarded in the pair-renaming representation. -/
theorem pair_offset_dvd {s : Configuration n} (hs : Aligned s)
    (a b : Fin n) (ha : s.physical.tokens s.physical.cursor=a)
    (hb : s.physical.tokens (s.physical.cursor+1)=b) :
    (n : ℤ) ∣ s.position a+1-s.position b := by
  have hcast : ((s.position a+1 : ℤ) : Fin n)=(s.position b : Fin n) := by
    rw [Int.cast_add, hs.2 a, hs.2 b, ← ha, ← hb]
    simp
  have hm := (cast_eq_iff_modEq _ _).mp hcast
  have hh := hm.sub_right (s.position b)
  apply Int.modEq_zero_iff_dvd.mp
  simpa only [sub_self] using hh

#print axioms x_as_pair_rename
#print axioms pair_offset_dvd
end LX.Core.LiftedModel
