import LX.ReflectionConjecture

namespace LX.AnchoredPhases
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem odd_zero_reserve_exception_seven (p : State 7) (r u : Fin 7)
    (hp : ∀ i,(p*Equiv.swap u (u+1)) i=r-i)
    (hcase : (r.val=3 ∧ u.val=4) ∨ (r.val=4 ∧ u.val=1)) :
    ∃ w : List Letter,p*eval w=1 ∧ w.length ≤ 25 := by
  have he : p=(Equiv.subLeft r)*Equiv.swap u (u+1) := by
    have hq : p*Equiv.swap u (u+1)=Equiv.subLeft r := by
      apply Equiv.ext
      exact hp
    have hh := congrArg (fun q : State 7 => q*Equiv.swap u (u+1)) hq
    simpa [mul_assoc] using hh
  rcases hcase with h | h
  · have hr : r=3 := Fin.ext h.1
    have hu : u=4 := Fin.ext h.2
    rw [hr,hu] at he
    rw [he]
    refine ⟨[.x,.l,.l,.x,.l,.x,.l,.x,.l,.l,.x,.l,.x,.l,.l,.x,.l,.x,.l],?_,?_⟩ <;> decide +kernel
  · have hr : r=4 := Fin.ext h.1
    have hu : u=1 := Fin.ext h.2
    rw [hr,hu] at he
    rw [he]
    refine ⟨[.x,.l,.x,.l,.l,.x,.l,.x,.l,.l,.x,.l,.x,.l,.x,.l,.l,.x,.l],?_,?_⟩ <;> decide +kernel

#print axioms odd_zero_reserve_exception_seven
end LX.AnchoredPhases
