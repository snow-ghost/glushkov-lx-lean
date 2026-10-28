import LX.ScanInversions
import Mathlib

namespace LX.LiftedScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

abbrev visible (s : LX.Core.LiftedModel.Configuration n) : State n :=
  LX.Core.PhysicalModel.visible s.physical

/-- Remaining displacement of the token currently at a relative cursor slot.
Targets and tracked positions are integers, so winding is preserved. -/
def remainder (F : Fin n → ℤ) (s : LX.Core.LiftedModel.Configuration n) (i : Fin n) : ℤ :=
  F (visible s i)-s.position (visible s i)

theorem visible_step (s : LX.Core.LiftedModel.Configuration n) (a : Letter) :
    visible (LX.Core.LiftedModel.step a.toCore s)=visible s*eval [a] := by
  change LX.Core.PhysicalModel.visible (LX.Core.PhysicalModel.step a.toCore s.physical)=_
  rw [LX.Core.PhysicalModel.visible_step]
  congr 1

theorem remainder_step (hn : 2 ≤ n) (F : Fin n → ℤ)
    (s : LX.Core.LiftedModel.Configuration n) (a : Letter) :
    remainder F (LX.Core.LiftedModel.step a.toCore s)=AffineScan.step a (remainder F s) := by
  funext i
  have h0 : s.physical.tokens s.physical.cursor=visible s 0 := by
    simp [visible,LX.Core.PhysicalModel.visible_apply]
  have h1 : s.physical.tokens (s.physical.cursor+1)=visible s 1 := by
    simp [visible,LX.Core.PhysicalModel.visible_apply,add_comm]
  have h01 : (0 : Fin n) ≠ 1 := by
    intro he
    have hh := Fin.one_eq_zero_iff.mp he.symm
    omega
  cases a with
  | l =>
    rw [remainder,visible_step]
    simp only [Letter.toCore,eval, List.map_cons,List.map_nil,LX.Core.eval_cons,LX.Core.eval_nil,
      mul_one,LX.Core.Letter.eval,Equiv.Perm.mul_apply,LX.Core.L,LX.Core.LiftedModel.step,
      AffineScan.step,AffineScan.rotate,remainder]
  | x =>
    rw [remainder,visible_step]
    simp only [Letter.toCore,eval,List.map_cons,List.map_nil,LX.Core.eval_cons,LX.Core.eval_nil,
      mul_one,LX.Core.Letter.eval,Equiv.Perm.mul_apply,LX.Core.X,LX.Core.LiftedModel.step,
      AffineScan.step,AffineScan.exchange,remainder,h0,h1]
    by_cases hi0 : i=0
    · subst i
      simp [h01,Ne.symm h01,(visible s).injective.eq_iff]
      ring
    · by_cases hi1 : i=1
      · subst i
        simp [h01,Ne.symm h01,(visible s).injective.eq_iff]
        ring
      · simp [Equiv.swap_apply_of_ne_of_ne hi0 hi1,(visible s).injective.eq_iff,hi0,hi1]

theorem remainder_run (hn : 2 ≤ n) (F : Fin n → ℤ) (w : List Letter)
    (s : LX.Core.LiftedModel.Configuration n) :
    remainder F (LX.Core.LiftedModel.run (w.map Letter.toCore) s)=AffineScan.run w (remainder F s) := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons,LX.Core.LiftedModel.run,AffineScan.run]
    rw [ih,remainder_step hn]

theorem remainder_initial (d : Fin n → ℤ) :
    remainder (AffineScan.targets d) (LX.Core.LiftedModel.initial (n := n))=d := by
  funext i
  simp [remainder,visible,LX.Core.LiftedModel.initial,LX.Core.PhysicalModel.visible_initial,
    AffineScan.targets]

/-- A zero residual board determines every named token's exact integer
endpoint. Finite evaluation alone would not imply this statement. -/
theorem exact_positions_of_zero (hn : 2 ≤ n) (d : Fin n → ℤ) (w : List Letter)
    (hz : ∀ i,AffineScan.run w d i=0) :
    ∀ i,(LX.Core.LiftedModel.run (w.map Letter.toCore) LX.Core.LiftedModel.initial).position i=
      (i : ℤ)+d i := by
  have hr := remainder_run hn (AffineScan.targets d) w LX.Core.LiftedModel.initial
  rw [remainder_initial] at hr
  intro i
  let s : LX.Core.LiftedModel.Configuration n := LX.Core.LiftedModel.run (w.map Letter.toCore) LX.Core.LiftedModel.initial
  have hh := congrFun hr ((visible s).symm i)
  rw [hz] at hh
  change AffineScan.targets d (visible s ((visible s).symm i))-
    s.position (visible s ((visible s).symm i))=0 at hh
  rw [Equiv.apply_symm_apply] at hh
  change (i : ℤ)+d i-s.position i=0 at hh
  change s.position i=(i : ℤ)+d i
  omega

theorem visible_run (w : List Letter) (s : LX.Core.LiftedModel.Configuration n) :
    visible (LX.Core.LiftedModel.run (w.map Letter.toCore) s)=visible s*eval w := by
  unfold visible
  rw [LX.Core.LiftedModel.run_physical,LX.Core.PhysicalModel.visible_run]
  rfl

theorem visible_run_initial (w : List Letter) :
    visible (LX.Core.LiftedModel.run (w.map Letter.toCore) (LX.Core.LiftedModel.initial (n := n)))=eval w := by
  rw [visible_run]
  simp [visible,LX.Core.LiftedModel.initial]

/-- The event's finite transposition is the actual conjugate of X by the
current visible configuration. The periodic shift is retained in the event key. -/
theorem event_swap_visible (hn : 2 ≤ n) (s : LX.Core.LiftedModel.Configuration n) :
    Equiv.swap (LX.Core.LiftedModel.eventKey s).first (LX.Core.LiftedModel.eventKey s).second*visible s=
      visible s*eval [.x] := by
  have hh := congrArg (fun t : LX.Core.LiftedModel.Configuration n => visible t)
    (LX.Core.LiftedModel.x_event_action hn s)
  change visible (LX.Core.LiftedModel.step Letter.x.toCore s)=_ at hh
  rw [visible_step] at hh
  simpa only [visible,LX.Core.LiftedModel.PairKey.action,LX.Core.LiftedModel.pairRename,
    LX.Core.LiftedModel.rename,LX.Core.PhysicalModel.visible,Equiv.symm_swap,mul_assoc] using hh.symm

/-- Event decomposition stays inside the LX alphabet. In particular the
deleted word cannot acquire an R from the LX.Core event infrastructure. -/
theorem mem_events (w : List Letter) (s : LX.Core.LiftedModel.Configuration n)
    (key : LX.Core.LiftedModel.PairKey n) :
    key ∈ LX.Core.LiftedModel.events (w.map Letter.toCore) s ↔
      ∃ u v : List Letter,w=u++[.x]++v ∧
        LX.Core.LiftedModel.eventKey (LX.Core.LiftedModel.run (u.map Letter.toCore) s)=key := by
  constructor
  · induction w generalizing s with
    | nil => simp [LX.Core.LiftedModel.events]
    | cons a w ih =>
      have liftTail (hh : key ∈ LX.Core.LiftedModel.events (w.map Letter.toCore)
          (LX.Core.LiftedModel.step a.toCore s)) :
          ∃ u v : List Letter,a::w=u++[.x]++v ∧
            LX.Core.LiftedModel.eventKey (LX.Core.LiftedModel.run (u.map Letter.toCore) s)=key := by
        obtain ⟨u,v,he,hk⟩ := ih _ hh
        exact ⟨a::u,v,by simp only [List.cons_append,he],hk⟩
      cases a with
      | l => exact liftTail
      | x =>
        intro hh
        rcases List.mem_cons.mp hh with he | ht
        · exact ⟨[],w,rfl,he.symm⟩
        · exact liftTail ht
  · rintro ⟨u,v,rfl,hk⟩
    simp [List.map_append,LX.Core.LiftedModel.events_append,LX.Core.LiftedModel.events,Letter.toCore,hk]

/-- Deleting an observed X sorts the input with those two original positions
transposed. Exactly one exchange is removed and all rotations are retained. -/
theorem delete_event_word (hn : 2 ≤ n) (p : State n) (w : List Letter)
    (hp : p*eval w=1) (key : LX.Core.LiftedModel.PairKey n)
    (hkey : key ∈ LX.Core.LiftedModel.events (w.map Letter.toCore) LX.Core.LiftedModel.initial) :
    ∃ v : List Letter,(p*Equiv.swap key.first key.second)*eval v=1 ∧
      v.length+1=w.length ∧ v.count .l=w.count .l := by
  obtain ⟨u,v,hw,hk⟩ := (mem_events w LX.Core.LiftedModel.initial key).mp hkey
  have hs := event_swap_visible hn (LX.Core.LiftedModel.run (u.map Letter.toCore) LX.Core.LiftedModel.initial)
  rw [hk,visible_run_initial] at hs
  rw [hw,eval_append,eval_append] at hp
  refine ⟨u++v,?_,?_,?_⟩
  · rw [eval_append]
    calc
      _ = p*((Equiv.swap key.first key.second*eval u)*eval v) := by group
      _ = p*((eval u*eval [.x])*eval v) := by rw [hs]
      _ = 1 := hp
  · simp [hw]
    omega
  · simp [hw]

/-- An inversion of periodic token copies must occur as an X event in any
zero-board execution, not only in a reduced trace. -/
theorem event_of_order_change (hn : 2 ≤ n) (d : Fin n → ℤ) (w : List Letter)
    (hz : ∀ i,AffineScan.run w d i=0) (key : LX.Core.LiftedModel.PairKey n) (hk : key.Valid)
    (hchange : ¬ ((key.first : ℤ)<(key.second : ℤ)+key.shift ↔
      (key.first : ℤ)+d key.first<(key.second : ℤ)+d key.second+key.shift)) :
    key ∈ LX.Core.LiftedModel.events (w.map Letter.toCore) LX.Core.LiftedModel.initial := by
  by_contra hnot
  have hb := LX.Core.LiftedModel.before_run_of_absent hn (w.map Letter.toCore)
    LX.Core.LiftedModel.initial_aligned key hk hnot
  simp only [LX.Core.LiftedModel.PairKey.Before] at hb
  rw [exact_positions_of_zero hn d w hz,exact_positions_of_zero hn d w hz] at hb
  exact hchange hb.symm

theorem delete_crossing_word (hn : 2 ≤ n) (p : State n) (d : Fin n → ℤ) (w : List Letter)
    (hp : p*eval w=1) (hz : ∀ i,AffineScan.run w d i=0)
    (key : LX.Core.LiftedModel.PairKey n) (hk : key.Valid)
    (hchange : ¬ ((key.first : ℤ)<(key.second : ℤ)+key.shift ↔
      (key.first : ℤ)+d key.first<(key.second : ℤ)+d key.second+key.shift)) :
    ∃ v : List Letter,(p*Equiv.swap key.first key.second)*eval v=1 ∧
      v.length+1=w.length ∧ v.count .l=w.count .l :=
  delete_event_word hn p w hp key (event_of_order_change hn d w hz key hk hchange)


#print axioms remainder_step
#print axioms exact_positions_of_zero
#print axioms delete_crossing_word
end LX.LiftedScan
