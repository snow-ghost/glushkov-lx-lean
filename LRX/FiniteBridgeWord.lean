import LRX.FiniteReachableExactService
import LRX.ArbitraryFiniteRouteTransfer

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- A genuine word for the original map after joining two reachable families.
The upper bridge map is served and then transferred back by M1. The selected
original port keeps its load discount. -/
theorem component_bridge_word (hn : 2 ≤ n) (p : State n) (u v r start finish : Fin n)
    (huv : u.val < v.val) (ha : (p.symm u).val ≤ u.val) (hb : v.val ≤ (p.symm v).val)
    (hroot : p.symm r ≠ r) (hru : FiniteReach p r u)
    (hr : ∀ i, p.symm i ≠ i → FiniteReach p u i ∨ FiniteReach p v i) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
        2*((v : ℤ)-(u : ℤ))-portLoad (displacement p.symm) r+
        (min (r-start).val (n-(r-start).val)+min (finish-r).val (n-(finish-r).val) : ℕ) := by
  obtain ⟨s,hport,htarget,hdisp,hrot⟩ := component_bridge_service_at hn p u v r huv ha hb hroot hru hr
  have hcan : ∀ a ∈ [s], ∀ i, a.displacement i=(a.service.target.symm i : ℤ)-(i : ℤ) := by
    intro a ha i
    have he : a=s := by simpa using ha
    subst a
    rw [hdisp,htarget]
    rfl
  have hbelow : FiniteRankOrder.Below p ([s].map (fun a : ExactService n => a.service.target)).prod := by
    simpa only [List.map_singleton,List.prod_singleton,htarget] using
      component_bridge_rank p u v huv (by omega)
  obtain ⟨w,he,_,_,_,hlen⟩ := arbitrary_finite_route_rank_transfer hn [s] (by simp) hcan p hbelow start finish
  have hcost : BufferProgram.rotations (route start finish ([s].map ExactService.service))=
      BufferProgram.rotations s.service.word+
        (min (r-start).val (n-(r-start).val)+min (finish-r).val (n-(finish-r).val)) := by
    simp [route_rotations,walkCost,hport,Nat.add_assoc]
  rw [hcost] at hlen
  have hlen' : (w.length : ℤ)=(inversionNumber p : ℤ)+BufferProgram.rotations s.service.word+
      (min (r-start).val (n-(r-start).val)+min (finish-r).val (n-(finish-r).val) : ℕ) := by
    exact_mod_cast hlen.trans (Nat.add_assoc _ _ _).symm
  refine ⟨w,he,?_⟩
  omega

#print axioms component_bridge_word
end LRX.FiniteCuts
