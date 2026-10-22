import LX.DeadlinePrice
import LRX.TraceInversions

namespace LX.LiftedScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

abbrev visible (s : LRX.LiftedModel.Configuration n) : State n :=
  LRX.PhysicalModel.visible s.physical

/-- Remaining displacement of the token currently at a relative cursor slot.
Targets and tracked positions are integers, so winding is preserved. -/
def remainder (F : Fin n → ℤ) (s : LRX.LiftedModel.Configuration n) (i : Fin n) : ℤ :=
  F (visible s i)-s.position (visible s i)

theorem visible_step (s : LRX.LiftedModel.Configuration n) (a : Letter) :
    visible (LRX.LiftedModel.step a.toLRX s)=visible s*eval [a] := by
  change LRX.PhysicalModel.visible (LRX.PhysicalModel.step a.toLRX s.physical)=_
  rw [LRX.PhysicalModel.visible_step]
  congr 1

theorem remainder_step (hn : 2 ≤ n) (F : Fin n → ℤ)
    (s : LRX.LiftedModel.Configuration n) (a : Letter) :
    remainder F (LRX.LiftedModel.step a.toLRX s)=AffineScan.step a (remainder F s) := by
  funext i
  have h0 : s.physical.tokens s.physical.cursor=visible s 0 := by
    simp [visible,LRX.PhysicalModel.visible_apply]
  have h1 : s.physical.tokens (s.physical.cursor+1)=visible s 1 := by
    simp [visible,LRX.PhysicalModel.visible_apply,add_comm]
  have h01 : (0 : Fin n) ≠ 1 := by
    intro he
    have hh := Fin.one_eq_zero_iff.mp he.symm
    omega
  cases a with
  | l =>
    rw [remainder,visible_step]
    simp only [Letter.toLRX,eval, List.map_cons,List.map_nil,LRX.eval_cons,LRX.eval_nil,
      mul_one,LRX.Letter.eval,Equiv.Perm.mul_apply,LRX.L,LRX.LiftedModel.step,
      AffineScan.step,AffineScan.rotate,remainder]
  | x =>
    rw [remainder,visible_step]
    simp only [Letter.toLRX,eval,List.map_cons,List.map_nil,LRX.eval_cons,LRX.eval_nil,
      mul_one,LRX.Letter.eval,Equiv.Perm.mul_apply,LRX.X,LRX.LiftedModel.step,
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
    (s : LRX.LiftedModel.Configuration n) :
    remainder F (LRX.LiftedModel.run (w.map Letter.toLRX) s)=AffineScan.run w (remainder F s) := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons,LRX.LiftedModel.run,AffineScan.run]
    rw [ih,remainder_step hn]

theorem remainder_initial (d : Fin n → ℤ) :
    remainder (AffineScan.targets d) (LRX.LiftedModel.initial (n := n))=d := by
  funext i
  simp [remainder,visible,LRX.LiftedModel.initial,LRX.PhysicalModel.visible_initial,
    AffineScan.targets]

/-- A zero residual board determines every named token's exact integer
endpoint. Finite evaluation alone would not imply this statement. -/
theorem exact_positions_of_zero (hn : 2 ≤ n) (d : Fin n → ℤ) (w : List Letter)
    (hz : ∀ i,AffineScan.run w d i=0) :
    ∀ i,(LRX.LiftedModel.run (w.map Letter.toLRX) LRX.LiftedModel.initial).position i=
      (i : ℤ)+d i := by
  have hr := remainder_run hn (AffineScan.targets d) w LRX.LiftedModel.initial
  rw [remainder_initial] at hr
  intro i
  let s : LRX.LiftedModel.Configuration n := LRX.LiftedModel.run (w.map Letter.toLRX) LRX.LiftedModel.initial
  have hh := congrFun hr ((visible s).symm i)
  rw [hz] at hh
  change AffineScan.targets d (visible s ((visible s).symm i))-
    s.position (visible s ((visible s).symm i))=0 at hh
  rw [Equiv.apply_symm_apply] at hh
  change (i : ℤ)+d i-s.position i=0 at hh
  change s.position i=(i : ℤ)+d i
  omega

theorem visible_run (w : List Letter) (s : LRX.LiftedModel.Configuration n) :
    visible (LRX.LiftedModel.run (w.map Letter.toLRX) s)=visible s*eval w := by
  unfold visible
  rw [LRX.LiftedModel.run_physical,LRX.PhysicalModel.visible_run]
  rfl

theorem visible_run_initial (w : List Letter) :
    visible (LRX.LiftedModel.run (w.map Letter.toLRX) (LRX.LiftedModel.initial (n := n)))=eval w := by
  rw [visible_run]
  simp [visible,LRX.LiftedModel.initial]

/-- The event's finite transposition is the actual conjugate of X by the
current visible configuration. The periodic shift is retained in the event key. -/
theorem event_swap_visible (hn : 2 ≤ n) (s : LRX.LiftedModel.Configuration n) :
    Equiv.swap (LRX.LiftedModel.eventKey s).first (LRX.LiftedModel.eventKey s).second*visible s=
      visible s*eval [.x] := by
  have hh := congrArg (fun t : LRX.LiftedModel.Configuration n => visible t)
    (LRX.LiftedModel.x_event_action hn s)
  change visible (LRX.LiftedModel.step Letter.x.toLRX s)=_ at hh
  rw [visible_step] at hh
  simpa only [visible,LRX.LiftedModel.PairKey.action,LRX.LiftedModel.pairRename,
    LRX.LiftedModel.rename,LRX.PhysicalModel.visible,Equiv.symm_swap,mul_assoc] using hh.symm

/-- Event decomposition stays inside the LX alphabet. In particular the
deleted word cannot acquire an R from the LRX event infrastructure. -/
theorem mem_events (w : List Letter) (s : LRX.LiftedModel.Configuration n)
    (key : LRX.LiftedModel.PairKey n) :
    key ∈ LRX.LiftedModel.events (w.map Letter.toLRX) s ↔
      ∃ u v : List Letter,w=u++[.x]++v ∧
        LRX.LiftedModel.eventKey (LRX.LiftedModel.run (u.map Letter.toLRX) s)=key := by
  constructor
  · induction w generalizing s with
    | nil => simp [LRX.LiftedModel.events]
    | cons a w ih =>
      have liftTail (hh : key ∈ LRX.LiftedModel.events (w.map Letter.toLRX)
          (LRX.LiftedModel.step a.toLRX s)) :
          ∃ u v : List Letter,a::w=u++[.x]++v ∧
            LRX.LiftedModel.eventKey (LRX.LiftedModel.run (u.map Letter.toLRX) s)=key := by
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
    simp [List.map_append,LRX.LiftedModel.events_append,LRX.LiftedModel.events,Letter.toLRX,hk]

/-- Deleting an observed X sorts the input with those two original positions
transposed. Exactly one exchange is removed and all rotations are retained. -/
theorem delete_event_word (hn : 2 ≤ n) (p : State n) (w : List Letter)
    (hp : p*eval w=1) (key : LRX.LiftedModel.PairKey n)
    (hkey : key ∈ LRX.LiftedModel.events (w.map Letter.toLRX) LRX.LiftedModel.initial) :
    ∃ v : List Letter,(p*Equiv.swap key.first key.second)*eval v=1 ∧
      v.length+1=w.length ∧ v.count .l=w.count .l := by
  obtain ⟨u,v,hw,hk⟩ := (mem_events w LRX.LiftedModel.initial key).mp hkey
  have hs := event_swap_visible hn (LRX.LiftedModel.run (u.map Letter.toLRX) LRX.LiftedModel.initial)
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
    (hz : ∀ i,AffineScan.run w d i=0) (key : LRX.LiftedModel.PairKey n) (hk : key.Valid)
    (hchange : ¬ ((key.first : ℤ)<(key.second : ℤ)+key.shift ↔
      (key.first : ℤ)+d key.first<(key.second : ℤ)+d key.second+key.shift)) :
    key ∈ LRX.LiftedModel.events (w.map Letter.toLRX) LRX.LiftedModel.initial := by
  by_contra hnot
  have hb := LRX.LiftedModel.before_run_of_absent hn (w.map Letter.toLRX)
    LRX.LiftedModel.initial_aligned key hk hnot
  simp only [LRX.LiftedModel.PairKey.Before] at hb
  rw [exact_positions_of_zero hn d w hz,exact_positions_of_zero hn d w hz] at hb
  exact hchange hb.symm

theorem delete_crossing_word (hn : 2 ≤ n) (p : State n) (d : Fin n → ℤ) (w : List Letter)
    (hp : p*eval w=1) (hz : ∀ i,AffineScan.run w d i=0)
    (key : LRX.LiftedModel.PairKey n) (hk : key.Valid)
    (hchange : ¬ ((key.first : ℤ)<(key.second : ℤ)+key.shift ↔
      (key.first : ℤ)+d key.first<(key.second : ℤ)+d key.second+key.shift)) :
    ∃ v : List Letter,(p*Equiv.swap key.first key.second)*eval v=1 ∧
      v.length+1=w.length ∧ v.count .l=w.count .l :=
  delete_event_word hn p w hp key (event_of_order_change hn d w hz key hk hchange)

theorem paid_word_zero (d : Fin n → ℤ) (w : List Letter) (c : Fin n)
    (hz : ∀ i,AffineScan.run w d i=0) :
    ∀ i,AffineScan.run (AffineScan.paidWord c w) d i=0 := by
  intro i
  simp only [AffineScan.paidWord,AffineScan.run_append,AffineScan.run_left_apply]
  exact hz _

#print axioms remainder_step
#print axioms exact_positions_of_zero
#print axioms delete_crossing_word
end LX.LiftedScan
