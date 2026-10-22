import LRX.PaidPortPrice

/-! Literal composition of closed services along a paid cursor route. The
permutation product, all letters, and both ends of every move are accounted for. -/
namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def rotation (r : Fin n) : State n := L n^r.val

theorem rotation_add (a b : Fin n) : rotation (a+b)=rotation a*rotation b := by
  apply Equiv.ext
  intro i
  simp only [rotation, AffineLift.rotation_power_apply, Fin.cast_val_eq_self, Equiv.Perm.mul_apply]
  abel

theorem rotation_sub (a b : Fin n) : rotation (b-a)=(rotation a)⁻¹*rotation b := by
  have h : rotation a*rotation (b-a)=rotation b := by
    rw [← rotation_add]
    congr 1
    abel
  calc
    rotation (b-a)=(rotation a)⁻¹*(rotation a*rotation (b-a)) := by group
    _ = _ := by rw [h]

theorem toPort_eval_rotation (r : Fin n) : eval (toPort r)=rotation r := toPort_eval r

structure ClosedService (n : ℕ) [NeZero n] where
  port : Fin n
  word : List Letter
  target : State n
  correct : eval word=(rotation port)⁻¹*target*rotation port
  closed : (word.map LiftedModel.increment).sum=0

def route (s t : Fin n) : List (ClosedService n) → List Letter
  | [] => toPort (t-s)
  | service::rest => toPort (service.port-s) ++ service.word ++ route service.port t rest

def walkCost (s t : Fin n) : List (ClosedService n) → ℕ
  | [] => min (t-s).val (n-(t-s).val)
  | service::rest => min (service.port-s).val (n-(service.port-s).val)+walkCost service.port t rest

def walkOffset (s t : Fin n) : List (ClosedService n) → ℤ
  | [] => shortOffset (t-s)
  | service::rest => shortOffset (service.port-s)+walkOffset service.port t rest

theorem route_eval (s t : Fin n) (services : List (ClosedService n)) :
    eval (route s t services)=(rotation s)⁻¹*(services.map ClosedService.target).prod*rotation t := by
  induction services generalizing s with
  | nil => simp [route, toPort_eval_rotation, rotation_sub]
  | cons service rest ih =>
    simp only [route, eval_append, toPort_eval_rotation, service.correct, ih,
      rotation_sub, List.map_cons, List.prod_cons]
    group

theorem route_length (s t : Fin n) (services : List (ClosedService n)) :
    (route s t services).length=(services.map (fun a => a.word.length)).sum+walkCost s t services := by
  induction services generalizing s with
  | nil => simp [route, walkCost, toPort_length]
  | cons service rest ih =>
    simp only [route, List.length_append, toPort_length, ih, List.map_cons, List.sum_cons, walkCost]
    omega

theorem route_exchanges (s t : Fin n) (services : List (ClosedService n)) :
    BufferProgram.exchanges (route s t services)=
      (services.map (fun a => BufferProgram.exchanges a.word)).sum := by
  induction services generalizing s with
  | nil => simp [route, toPort, spin_exchanges]
  | cons service rest ih =>
    simp [route, BufferProgram.exchanges_append, toPort, spin_exchanges, ih]

theorem route_rotations (s t : Fin n) (services : List (ClosedService n)) :
    BufferProgram.rotations (route s t services)=
      (services.map (fun a => BufferProgram.rotations a.word)).sum+walkCost s t services := by
  induction services generalizing s with
  | nil => simp [route, walkCost, toPort, spin_rotations, short_offset_cost]
  | cons service rest ih =>
    simp only [route, BufferProgram.rotations_append, toPort, spin_rotations,
      short_offset_cost, ih, List.map_cons, List.sum_cons, walkCost]
    omega

theorem route_increment (s t : Fin n) (services : List (ClosedService n)) :
    ((route s t services).map LiftedModel.increment).sum=walkOffset s t services := by
  induction services generalizing s with
  | nil => exact spin_increment _
  | cons service rest ih =>
    simp only [route, List.map_append, List.sum_append, toPort, spin_increment,
      service.closed, add_zero, ih, walkOffset]

theorem walk_offset_cast (s t : Fin n) (services : List (ClosedService n)) :
    (walkOffset s t services : Fin n)=t-s := by
  induction services generalizing s with
  | nil => exact short_offset_cast _
  | cons service rest ih =>
    simp only [walkOffset, Int.cast_add, short_offset_cast, ih]
    abel

theorem route_cursor (s t : Fin n) (services : List (ClosedService n))
    (state : LiftedModel.Configuration n) (hs : (state.cursor : Fin n)=s) :
    ((LiftedModel.run (route s t services) state).cursor : Fin n)=t := by
  rw [LiftedModel.cursor_run, route_increment, Int.cast_add, hs, walk_offset_cast]
  abel

/-- Reordering complete services with disjoint physical targets preserves the
final permutation. The local words are kept in their original directions. -/
theorem route_permuted (s t : Fin n) (services other : List (ClosedService n))
    (hdis : services.Pairwise (fun a b => Disjoint a.target.support b.target.support))
    (hp : services.Perm other) : eval (n := n) (route s t services)=eval (route s t other) := by
  have hd : (services.map ClosedService.target).Pairwise Equiv.Perm.Disjoint := by
    apply List.pairwise_map.mpr
    exact hdis.imp (fun h => Equiv.Perm.disjoint_iff_disjoint_support.mpr h)
  rw [route_eval, route_eval, Equiv.Perm.disjoint_prod_perm hd (hp.map ClosedService.target)]

#print axioms route_eval
#print axioms route_length
#print axioms route_cursor
#print axioms route_permuted
end LRX.RotationWords
