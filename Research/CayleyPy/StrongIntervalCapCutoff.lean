import Mathlib

/-! Phase75: exact finite-profile square capacity with a stronger interval cap.
The existence and lengths of the original invariant intervals are geometric
inputs. No assertion about all permutations is an axiom of this file. -/
namespace CayleyPy.StrongIntervalCapCutoff

theorem lower_mass_square {ι : Type*} [DecidableEq ι]
    (S A : Finset ι) (x : ι → ℤ) (b : ℤ)
    (hsub : A ⊆ S) (hb : 0 ≤ b)
    (hx : ∀ i ∈ S, 0 ≤ x i) (hA : ∀ i ∈ A, b ≤ x i) :
    ∑ i ∈ S, (x i)^2 ≤
      ((∑ i ∈ S, x i)-b*((A.card : ℤ)-1))^2+b^2*((A.card : ℤ)-1) := by
  let y : ι → ℤ := fun i => x i-if i ∈ A then b else 0
  have hy : ∀ i ∈ S, 0 ≤ y i := by
    intro i hi
    by_cases h : i ∈ A
    · simp only [y, h, ↓reduceIte]
      exact sub_nonneg.mpr (hA i h)
    · simpa only [y, h, ↓reduceIte, sub_zero] using hx i hi
  have hf : S.filter (fun i => i ∈ A)=A := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h,h⟩⟩
  have hind (c : ℤ) : (∑ i ∈ S, if i ∈ A then c else 0)=(A.card : ℤ)*c := by
    rw [← Finset.sum_filter, hf]
    simp
  have hsum : (∑ i ∈ S, y i)=(∑ i ∈ S, x i)-(A.card : ℤ)*b := by
    simp only [y, Finset.sum_sub_distrib, hind]
  have hpoint : ∀ i ∈ S,
      (x i)^2 ≤ (y i)^2+2*b*y i+(if i ∈ A then b^2 else 0) := by
    intro i hi
    by_cases h : i ∈ A
    · simp only [y, h, ↓reduceIte]
      nlinarith
    · simp only [y, h, ↓reduceIte, sub_zero, add_zero]
      nlinarith [mul_nonneg hb (hx i hi)]
  have htotal := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hind] at htotal
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg hy
  rw [hsum] at hsq htotal
  nlinarith

theorem exact_cap_envelope (V M x w C S2 : ℤ)
    (hV : 0 ≤ V) (hM : 0 ≤ M) (hw : 0 ≤ w) (hC : 0 ≤ C)
    (hcap : x ≤ M) (hVcap : V ≤ 2*M)
    (hsmall : S2 ≤ x*V) (hrest : S2 ≤ x*x+(V-x-w)^2+C) :
    S2 ≤ M*M+(V-M-w)^2+C := by
  by_cases hx : x ≤ V-M-w
  · have h1 := mul_nonneg hV (show 0 ≤ V-M-w-x by omega)
    have h2 := mul_nonneg (show 0 ≤ M+w by omega) (show 0 ≤ 2*M-V by omega)
    nlinarith [sq_nonneg w]
  · have hprod := mul_nonneg (show 0 ≤ M-x by omega)
      (show 0 ≤ x-(V-M-w) by omega)
    nlinarith

theorem finite_profile_envelope {ι : Type*} [DecidableEq ι]
    (S A : Finset ι) (x : ι → ℤ) (j : ι) (t M : ℤ)
    (hj : j ∈ S) (hsub : A ⊆ S.erase j) (hcard : (A.card : ℤ)=t-1)
    (ht : 3 ≤ t) (hM : 0 ≤ M)
    (hx : ∀ i ∈ S, 0 ≤ x i) (hA : ∀ i ∈ A, 2 ≤ x i)
    (hmax : ∀ i ∈ S, x i ≤ x j) (hcap : x j ≤ M)
    (hVcap : (∑ i ∈ S, x i) ≤ 2*M) :
    ∑ i ∈ S, (x i)^2 ≤
      M*M+((∑ i ∈ S, x i)-M-2*(t-2))^2+4*(t-2) := by
  have hrest := lower_mass_square (S.erase j) A x 2 hsub (by omega)
    (fun i hi => hx i (Finset.mem_of_mem_erase hi)) hA
  rw [hcard] at hrest
  have hs := Finset.sum_erase_add S x hj
  have hs2 := Finset.sum_erase_add S (fun i => (x i)^2) hj
  have hsmall : (∑ i ∈ S, (x i)^2) ≤ x j*(∑ i ∈ S, x i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    nlinarith [mul_nonneg (hx i hi) (sub_nonneg.mpr (hmax i hi))]
  apply exact_cap_envelope (∑ i ∈ S, x i) M (x j) (2*(t-2)) (4*(t-2))
    (∑ i ∈ S, (x i)^2) (Finset.sum_nonneg hx) hM (by omega) (by omega)
    hcap hVcap hsmall
  have hsum : (∑ i ∈ S.erase j, x i)=(∑ i ∈ S, x i)-x j := by omega
  rw [hsum] at hrest
  nlinarith

theorem cap_volume (t m p u : ℤ) (ht : 3 ≤ t) (htop : t ≤ 5)
    (hp0 : 0 ≤ p) (hu : 3 ≤ u)
    (hcubic : t^3-3*t*t+4*t+1 ≤ m)
    (hdensity : 8*(t-2)*(m-1) ≤ (u+4*t-10)^2+6*t-7) :
    2*m-u ≤ 2*(m-3+p) := by
  by_contra h
  have hu5 : u ≤ 5 := by omega
  interval_cases t <;> interval_cases u <;> norm_num at hcubic hdensity <;> omega

def width (t : ℤ) : ℤ := 2*(t-2)
def cutoff (t p : ℤ) : ℤ := if t=3 then 27+2*p else if t=4 then 43+2*p else 71
def pivot (t p : ℤ) : ℤ := if t=3 then 16-p else if t=4 then 24-p else 35-2*p
def areaGap (t p w m u : ℤ) : ℤ :=
  2*m*(m+p)-6*t-8-4*(2*t-2)*(2*m+p-4*t+2)
    -(m-3+p)^2-(m-u+3-p-w)^2-2*w

theorem strong_density (m p t u w S2 H : ℤ)
    (hH : H=(2*m-u)^2-2*S2) (hupper : H ≤ 6*t-7)
    (hsq : S2 ≤ (m-3+p)^2+(m-u+3-p-w)^2+2*w) :
    4*w*(m-3+p)+2*w*w-4*w ≤ (u+2*w-6+2*p)^2+6*t-7 := by
  nlinarith

theorem parity_preserving_area (m p t U epsilon a S2 : ℤ)
    (hp : 0 ≤ p) (ht : 2 ≤ t) (hU0 : 0 ≤ U) (hU : U ≤ 2*t-2)
    (hm : 4*t ≤ m) (ha : 0 ≤ a) (he : epsilon ≤ 3*t+4)
    (harea : 2*(m*(m+p)-epsilon) ≤ 4*U*(2*m+p-2*t-a-U)+S2) :
    2*m*(m+p)-6*t-8 ≤ 4*(2*t-2)*(2*m+p-4*t+2)+S2 := by
  have hmono := mul_nonneg (show 0 ≤ 2*t-2-U by omega)
    (show 0 ≤ 2*m+p-4*t+2-U by omega)
  have hUa := mul_nonneg hU0 ha
  nlinarith

theorem split_certificate (t p w M0 u0 umax m u : ℤ)
    (hw : 2 ≤ w) (hp : 0 ≤ p) (hu0 : 3 ≤ u0) (hu : 3 ≤ u)
    (hupper : u ≤ umax) (hm : M0 ≤ m)
    (hmonom : 8*t-8 ≤ u0+w+p)
    (hmonou : umax+u0+2*w+2*p-6 ≤ 2*M0)
    (hsplit : (u0+2*w-7+2*p)^2+6*t-7 < 4*w*(M0-3+p)+2*w*w-4*w)
    (hpoint : 0 < areaGap t p w M0 u0)
    (hdensity : 4*w*(m-3+p)+2*w*w-4*w ≤ (u+2*w-6+2*p)^2+6*t-7)
    (harea : 2*m*(m+p)-6*t-8 ≤
      4*(2*t-2)*(2*m+p-4*t+2)+(m-3+p)^2+(m-u+3-p-w)^2+2*w) : False := by
  have hthreshold : u0 ≤ u := by
    by_contra h
    have hsmall : u ≤ u0-1 := by omega
    have hs := mul_nonneg
      (show 0 ≤ (u0+2*w-7+2*p)-(u+2*w-6+2*p) by omega)
      (show 0 ≤ (u0+2*w-7+2*p)+(u+2*w-6+2*p) by omega)
    have hwm := mul_nonneg (show 0 ≤ w by omega) (show 0 ≤ m-M0 by omega)
    nlinarith only [hsplit, hs, hwm, hdensity]
  have hp1 := mul_nonneg (show 0 ≤ m-M0 by omega) (show 0 ≤ u+w+p-8*t+8 by omega)
  have hp2 := mul_nonneg (show 0 ≤ u-u0 by omega)
    (show 0 ≤ 2*M0-u-u0+6-2*p-2*w by omega)
  have hid : areaGap t p w m u-areaGap t p w M0 u0 =
      2*(m-M0)*(u+w+p-8*t+8)+(u-u0)*(2*M0-u-u0+6-2*p-2*w) := by
    unfold areaGap
    ring
  have hnonpos : areaGap t p w m u ≤ 0 := by unfold areaGap; linarith only [harea]
  nlinarith only [hpoint, hnonpos, hid, hp1, hp2]

theorem certificate_table (t p : ℤ) (ht : 3 ≤ t) (htop : t ≤ 5)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    2 ≤ width t ∧ 3 ≤ pivot t p ∧ 4*t ≤ cutoff t p ∧
    8*t-8 ≤ pivot t p+width t+p ∧
    (16*t-19)+pivot t p+2*width t+2*p-6 ≤ 2*cutoff t p ∧
    (pivot t p+2*width t-7+2*p)^2+6*t-7 <
      4*width t*(cutoff t p-3+p)+2*width t*width t-4*width t ∧
    0 < areaGap t p (width t) (cutoff t p) (pivot t p) := by
  interval_cases t <;> interval_cases p <;> norm_num [width,cutoff,pivot,areaGap]

theorem no_large_scalar (t p m u : ℤ) (ht : 3 ≤ t) (htop : t ≤ 5)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hm : cutoff t p ≤ m)
    (hu : 3 ≤ u) (hupper : u ≤ 16*t-19)
    (hdensity : 4*width t*(m-3+p)+2*width t*width t-4*width t ≤
      (u+2*width t-6+2*p)^2+6*t-7)
    (harea : 2*m*(m+p)-6*t-8 ≤
      4*(2*t-2)*(2*m+p-4*t+2)+(m-3+p)^2+(m-u+3-p-width t)^2+2*width t) :
    False := by
  obtain ⟨hw,hpivot,_,hmonom,hmonou,hsplit,hpoint⟩ := certificate_table t p ht htop hp0 hp1
  exact split_certificate t p (width t) (cutoff t p) (pivot t p) (16*t-19) m u
    hw hp0 hpivot hu hupper hm hmonom hmonou hsplit hpoint hdensity harea

theorem final_size (t m n p : ℤ) (ht : 3 ≤ t) (htop : t ≤ 5)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : n=2*m+p) (hm : m < cutoff t p)
    (hcubic : t^3-3*t*t+4*t+1 ≤ m) :
    t ≤ 4 ∧ n ≤ 89 ∧ (t=3 → n ≤ 57) ∧ (t=3 ∧ p=0 → n ≤ 52) ∧
      (t=4 ∧ p=0 → n ≤ 84) := by
  interval_cases t <;> interval_cases p <;> norm_num [cutoff] at hm hcubic <;> omega

#print axioms lower_mass_square
#print axioms exact_cap_envelope
#print axioms finite_profile_envelope
#print axioms cap_volume
#print axioms strong_density
#print axioms parity_preserving_area
#print axioms split_certificate
#print axioms certificate_table
#print axioms no_large_scalar
#print axioms final_size

end CayleyPy.StrongIntervalCapCutoff
