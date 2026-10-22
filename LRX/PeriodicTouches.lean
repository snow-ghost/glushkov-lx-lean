import LRX.PrunedReachability
import LRX.ClosedReachableService

/-! A lifted arrow touches a periodic vertex according only to the relative
residue of that vertex. This makes root-star coverage independent of the port. -/
namespace LRX.BufferProgram

def Touches (N a d b : ℤ) : Prop :=
  ∃ k : ℤ, min a (a+d) ≤ b+k*N ∧ b+k*N ≤ max a (a+d)

theorem touches_relative (N a d b : ℤ) :
    Touches N a d b ↔ ∃ k : ℤ, min 0 d ≤ b-a+k*N ∧ b-a+k*N ≤ max 0 d := by
  have hmin : min a (a+d)=a+min 0 d := by rw [add_min]; simp
  have hmax : max a (a+d)=a+max 0 d := by rw [add_max]; simp
  unfold Touches
  rw [hmin,hmax]
  constructor <;> rintro ⟨k,hl,hh⟩ <;> refine ⟨k,?_,?_⟩ <;> omega

theorem touches_of_modEq {N a b a' b' d : ℤ}
    (hm : Int.ModEq N (b-a) (b'-a')) (ht : Touches N a d b) : Touches N a' d b' := by
  obtain ⟨k,hk⟩ := Int.modEq_iff_dvd.mp hm
  obtain ⟨j,hl,hh⟩ := (touches_relative N a d b).mp ht
  apply (touches_relative N a' d b').mpr
  have he : b'-a'+(j-k)*N=b-a+j*N := by nlinarith [hk]
  exact ⟨j-k,by rwa [he],by rwa [he]⟩

theorem touches_modEq_iff {N a b a' b' d : ℤ}
    (hm : Int.ModEq N (b-a) (b'-a')) : Touches N a d b ↔ Touches N a' d b' :=
  ⟨touches_of_modEq hm,touches_of_modEq hm.symm⟩

#print axioms touches_modEq_iff
end LRX.BufferProgram
