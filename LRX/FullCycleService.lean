import LRX.BufferItinerary
import LRX.BufferBalance

/-! An actual buffer-service word for a supplied complete cyclic order of labels.
The order follows the physical target permutation. Correctness, closed integer
cursor, every integer endpoint, and exact rotation price are proved. The raw X
count is not reduced to affine inversion length here. -/
namespace LRX.BufferProgram
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def logicalDelta (d : Fin n → ℤ) (i : Fin n) : ℤ :=
  PeriodicBuffer.contract (n : ℤ) ((i : ℤ)+d i) - PeriodicBuffer.contract (n : ℤ) (i : ℤ)

def Follows (p : State n) : List (Fin n) → Prop
  | [] => True
  | a :: rest => match rest with
    | [] => True
    | b :: _ => p.symm a=b ∧ Follows p rest

theorem follows_compatible {p : State n} {d : Fin n → ℤ} (hd : AffineLift.IsLift p 0 d)
    (path : List (Fin n)) (hp : Follows p path) :
    Compatible (initialLogical (n := n)).coord (logicalDelta d) path := by
  induction path with
  | nil => trivial
  | cons a rest ih =>
    cases rest with
    | nil => trivial
    | cons b rest =>
      refine ⟨?_, ih hp.2⟩
      have hm : Int.ModEq (n : ℤ) ((a : ℤ)+d a) (b : ℤ) := by
        simpa only [hp.1, add_zero] using hd.2 a
      have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
      have hh := PeriodicBuffer.contract_modEq hn0 hm
      change Int.ModEq (BufferMachine.slots n)
        (PeriodicBuffer.contract (n : ℤ) (a : ℤ) +
          (PeriodicBuffer.contract (n : ℤ) ((a : ℤ)+d a)-PeriodicBuffer.contract (n : ℤ) (a : ℤ)))
        (PeriodicBuffer.contract (n : ℤ) (b : ℤ))
      convert hh using 1
      ring

/-- A complete cyclic order gives a concrete closed physical service. Its raw
word has `rotations + number of commands` letters; no optimal-X claim is made. -/
theorem full_cycle_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (rest : List (Fin n))
    (hnd : ((0 : Fin n)::rest).Nodup)
    (hcover : ∀ i : Fin n, i ∈ (0 : Fin n)::rest)
    (hfollow : Follows p ((0 : Fin n)::rest))
    (hlast : p.symm (((0 : Fin n)::rest).getLast (by simp)) = 0) :
    ∃ w : List Letter,
      eval w = p ∧
      (LiftedModel.run w (LiftedModel.initial (n := n))).cursor=0 ∧
      (∀ i, (LiftedModel.run w (LiftedModel.initial (n := n))).position i = (i : ℤ)+d i) ∧
      (rotations w : ℤ) = (∑ i : Fin n, |d i|) -
        ∑ i : Fin n, PeriodicBuffer.edgePassages (n : ℤ) (i : ℤ) ((i : ℤ)+d i) ∧
      w.length=2*rotations w+n-1 := by
  let path := (0 : Fin n)::rest
  let cs := itinerary (logicalDelta d) path
  let w := compile cs
  have hc := follows_compatible hd path hfollow
  have hh : HeadReady (initialLogical (n := n)) := by
    simp [HeadReady, initialLogical, PeriodicBuffer.contract]
  have hv : Valid cs initialLogical :=
    itinerary_valid (initialLogical (n := n)).coord (logicalDelta d) 0 rest initialLogical
      hnd rfl (fun _ _ => rfl) hh hc
  have hy (i : Fin n) : (logicalRun cs initialLogical).coord i =
      PeriodicBuffer.contract (n : ℤ) ((i : ℤ)+d i) := by
    have h := itinerary_coordinates (logicalDelta d) 0 rest (initialLogical (n := n)) hnd rfl i
    rw [ite_eq_left (hcover i)] at h
    change (logicalRun cs initialLogical).coord i = _ at h
    rw [h]
    dsimp [initialLogical, logicalDelta]
    ring
  have hbuf : (((logicalRun cs initialLogical).buffer : ℤ)+
      d (logicalRun cs initialLogical).buffer)%(n : ℤ)=0 := by
    change (((logicalRun (itinerary (logicalDelta d) ((0 : Fin n)::rest)) initialLogical).buffer : ℤ)+
      d (logicalRun (itinerary (logicalDelta d) ((0 : Fin n)::rest)) initialLogical).buffer)%(n : ℤ)=0
    have hbval := itinerary_buffer (logicalDelta d) (0 : Fin n) rest (initialLogical (n := n)) rfl
    rw [hbval]
    have he := (hd.2 (path.getLast (by simp [path]))).eq
    simpa only [path, hlast, Fin.val_zero, Nat.cast_zero, add_zero, Int.zero_emod] using he
  have hhead := closed_head_of_complete_coordinates cs hd hy
  have hm := compile_correct hn cs (initial_matches hn) hv
  have hset : path.toFinset = Finset.univ := by
    ext i
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact hcover i
  have hr : rotations w = ∑ i : Fin n, (logicalDelta d i).natAbs := by
    rw [show w=compile (itinerary (logicalDelta d) path) from rfl, itinerary_rotation_price,
      ← List.sum_toFinset _ hnd, hset]
  have hlen : path.length=n := by
    have he := List.toFinset_card_of_nodup hnd
    rw [hset] at he
    simpa [path] using he.symm
  refine ⟨w, completed_service_endpoint hn cs hd hv hy hbuf, hm.1.trans hhead,
    compiled_exact_positions hn cs hd hv hhead hy hbuf, ?_, ?_⟩
  · have hn0 : (0 : ℤ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [hr]
    simp only [Nat.cast_sum, Int.natCast_natAbs]
    simpa only [logicalDelta, add_sub_cancel_left] using PeriodicBuffer.rotation_price
      (Finset.univ : Finset (Fin n)) hn0 (fun i => (i : ℤ)) (fun i => (i : ℤ)+d i)
  · have hl := itinerary_length (logicalDelta d) path
    have hrot := itinerary_rotation_price (logicalDelta d) path
    change (compile (itinerary (logicalDelta d) path)).length = _
    rw [hl, ← hrot, hlen]

#print axioms follows_compatible
#print axioms full_cycle_service
end LRX.BufferProgram
