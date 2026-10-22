import Mathlib

/-! M3/M4, necessary conditions for the unpaid many-component peak (P >= 1).
The constants are those of the corrected zero-additive manuscript, not the
stronger U/epsilon hypotheses of older research modules. This is an arithmetic
reduction, not a proof that an original permutation satisfies its premises.
-/
namespace CoupledPeakCutoff

def width (t : ℤ) : ℤ := if t = 2 then 1 else 2 * (t - 2)

def areaGap (t w m u : ℤ) : ℤ :=
  2*m^2-6*t-12-4*(3*t+1)*(2*m-5*t-1) -
    (m-1)^2-(m+1-u-w)^2-w^2

/-- The elementary J3/J4 consequences are derived from the two C8 peak
bounds and C11. The choose(a,2) term was only dropped in the weaker C8
bound below, never assumed to vanish. -/
theorem unpaid_prebounds (m p t f a v B U eps : ℤ)
    (ht : 2 ≤ t) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hf : 0 ≤ f) (ha : 0 ≤ a) (haf : a ≤ f) (hv : 2*t ≤ v) (hU : 1 ≤ U)
    (hBzero : a=0 → B ≤ t) (hBpos : 1 ≤ a → B ≤ a+t-1)
    (hactivity : f^2 ≤ 4*eps+p) (hcredit : 0 ≤ 2*eps+p-f)
    (hpeak : 1 ≤ 2*B+t-U-(2*eps+p-f))
    (hreserve : 1 ≤ 2*B+m-U-2-2*(t-1)*(v-t)-a*v-eps)
    (htail : 2*f+t^2-2*(v-t) ≤ eps) :
    eps ≤ 3*t+6 ∧ U ≤ 3*t+1 ∧
    (3 ≤ t → t^3-3*t^2+3*t+1 ≤ m) ∧
    2*eps+p-f ≤ 2*a+3*t-2 := by
  have hB : B ≤ a+t := by
    by_cases hz : a=0
    · have := hBzero hz; omega
    · have := hBpos (by omega); omega
  have heps : 0 ≤ eps := by nlinarith [sq_nonneg f]
  have hpre : 2*eps+p ≤ 3*f+3*t-2 := by omega
  have hsq : (f-3)^2 ≤ 6*t+5-p := by nlinarith
  have hfbound : f ≤ t+5 := by
    by_contra h
    have hprod := mul_nonneg (show 0 ≤ f-t-6 by omega) (show 0 ≤ f+t by omega)
    nlinarith [sq_nonneg t]
  refine ⟨by omega, ?_, ?_, by omega⟩
  · by_cases hz : a=0
    · have := hBzero hz
      omega
    · have hb := hBpos (by omega)
      have hu : 2*U ≤ 6*t+3 := by nlinarith [sq_nonneg (f-3)]
      omega
  · intro ht3
    have hv2 : t^2+3 ≤ 2*v := by nlinarith
    have hav := mul_nonneg ha (show 0 ≤ v-2 by omega)
    have hm : 2*(t-1)*v-2*t^2+4 ≤ m := by nlinarith
    have hprod := mul_nonneg (show 0 ≤ t-1 by omega) (show 0 ≤ 2*v-t^2-3 by omega)
    nlinarith

/-- The density allowance follows from C9 and the unpaid first C8 bound.
The slightly weaker 6t-3 form is retained for the shared certificates. -/
theorem unpaid_density_allowance (V S2 a p A t : ℤ)
    (hV : 3 ≤ V) (ha : 0 ≤ a) (hp : 0 ≤ p)
    (hC9 : V^2-2*S2+2*(V-1)*a+a^2+p ≤ 2*A)
    (hA : A ≤ 2*a+3*t-2) : V^2-2*S2 ≤ 6*t-3 := by
  have hprod := mul_nonneg (show 0 ≤ V-3 by omega) ha
  nlinarith [sq_nonneg a]

/-- Unlike the old large-m estimate, this uses the actual -2t-U terms in C10
and is valid for every m >= 2t+1. It needs only U >= 1, not U >= 2. -/
theorem support_cap_all_sizes (m p t U eps a r S2 : ℤ)
    (ht : 2 ≤ t) (hm : 2*t+1 ≤ m) (hp : p=0 ∨ p=1)
    (hU : 1 ≤ U) (he : eps ≤ 3*t+6) (ha : 0 ≤ a)
    (harea : 2*(m*(m+p)-eps) ≤ 4*U*(2*m+p-2*t-a-U)+S2)
    (hcap : S2 ≤ (m-1)*(2*m+p-r)) : r ≤ 8*U+1-p := by
  by_contra h
  have hr : 8*U+2-p ≤ r := by omega
  have hprod := mul_nonneg (show 0 ≤ m-1 by omega)
    (show 0 ≤ r-(8*U+2-p) by omega)
  have hua := mul_nonneg (show 0 ≤ U by omega) ha
  have hut := mul_nonneg (show 0 ≤ U-1 by omega) (show 0 ≤ t by omega)
  rcases hp with hp | hp <;> subst p <;> nlinarith [sq_nonneg (U-1)]

/-- Replace U by its upper bound, while retaining the negative square term. -/
theorem coarse_area (m p t U eps a S2 u w : ℤ)
    (hp : 0 ≤ p) (hU0 : 0 ≤ U) (hU : U ≤ 3*t+1)
    (hm : 6*t+2 ≤ m) (ha : 0 ≤ a) (he : eps ≤ 3*t+6)
    (harea : 2*(m*(m+p)-eps) ≤ 4*U*(2*m+p-2*t-a-U)+S2)
    (henv : S2 ≤ (m-1)^2+(m+1-u-w)^2+w^2) :
    areaGap t w m u ≤ 0 := by
  have hmono := mul_nonneg (show 0 ≤ 3*t+1-U by omega)
    (show 0 ≤ 2*m+p-5*t-1-U by omega)
  have hua := mul_nonneg hU0 ha
  have hpar := mul_nonneg hp (show 0 ≤ m-6*t-2 by omega)
  unfold areaGap
  nlinarith

/-- C9 and the same square envelope used for C10. -/
theorem coupled_density (m u w S2 H : ℤ)
    (hH : H=(2*m-u)^2-2*S2)
    (henv : S2 ≤ (m-1)^2+(m+1-u-w)^2+w^2) :
    4*w*(m-1)-(u+2*w-2)^2 ≤ H := by
  nlinarith

/-- A split at u0 certifies all m >= M at once. No square root or floating
point computation occurs in the certificate or its proof. -/
theorem split_certificate (t w M u0 umax m u : ℤ)
    (hw : 1 ≤ w) (hu0 : 3 ≤ u0) (hu : 3 ≤ u) (hupper : u ≤ umax)
    (hm : M ≤ m) (hmonom : 12*t+4 ≤ u0+w)
    (hmonou : umax+u0+2*w-2 ≤ 2*M)
    (hsplit : (u0+2*w-3)^2+6*t-3 < 4*w*(M-1))
    (hpoint : 0 < areaGap t w M u0)
    (hdensity : 4*w*(m-1) ≤ (u+2*w-2)^2+6*t-3)
    (harea : areaGap t w m u ≤ 0) : False := by
  have hthreshold : u0 ≤ u := by
    by_contra h
    have hsmall : u ≤ u0-1 := by omega
    have hs := mul_nonneg
      (show 0 ≤ (u0+2*w-3)-(u+2*w-2) by omega)
      (show 0 ≤ (u0+2*w-3)+(u+2*w-2) by omega)
    have hwm := mul_nonneg (show 0 ≤ w by omega) (show 0 ≤ m-M by omega)
    nlinarith
  have h1 := mul_nonneg (show 0 ≤ m-M by omega) (show 0 ≤ u+w-12*t-4 by omega)
  have h2 := mul_nonneg (show 0 ≤ u-u0 by omega)
    (show 0 ≤ 2*M-u-u0-2*w+2 by omega)
  have hid : areaGap t w m u-areaGap t w M u0 =
      2*(m-M)*(u+w-12*t-4)+(u-u0)*(2*M-u-u0-2*w+2) := by
    unfold areaGap
    ring
  nlinarith

/-- Uniform linear cutoff: replaces the manuscript's small/large-m split
and its subsequent quartic t >= 13 exclusion. -/
theorem linear_cutoff (t m u : ℤ) (ht : 3 ≤ t)
    (hu : 3 ≤ u) (hupper : u ≤ 24*t+9)
    (hdensity : 4*width t*(m-1) ≤ (u+2*width t-2)^2+6*t-3)
    (harea : areaGap t (width t) m u ≤ 0) : m < 60*t+60 := by
  by_contra hm
  have hw : width t = 2*(t-2) := by simp [width]; omega
  apply split_certificate t (width t) (60*t+60) (12*t+6) (24*t+9) m u
      (by rw [hw]; omega) (by omega) hu hupper (by omega)
      (by rw [hw]; omega) (by rw [hw]; omega)
  · rw [hw]
    nlinarith [sq_nonneg (t-3)]
  · unfold areaGap
    rw [hw]
    nlinarith [sq_nonneg (t-3)]
  · exact hdensity
  · exact harea

theorem component_count_le_nine (t m : ℤ) (_ht : 3 ≤ t)
    (hcubic : t^3-3*t^2+3*t+1 ≤ m) (hlinear : m < 60*t+60) : t ≤ 9 := by
  by_contra h
  have ht10 : 10 ≤ t := by omega
  have hcube := mul_nonneg (show 0 ≤ t-10 by omega) (sq_nonneg (t-10))
  nlinarith [sq_nonneg (t-10)]

def cutoff (t : ℤ) : ℤ :=
  if t=2 then 200 else if t=3 then 224 else if t=4 then 213 else
  if t=5 then 237 else if t=6 then 261 else if t=7 then 289 else
  if t=8 then 318 else 352

def pivot (t : ℤ) : ℤ :=
  if t=2 then 29 else if t=3 then 41 else if t=4 then 53 else
  if t=5 then 65 else if t=6 then 78 else if t=7 then 90 else
  if t=8 then 102 else 114

theorem certificate_table (t : ℤ) (ht : 2 ≤ t) (htop : t ≤ 9) :
    1 ≤ width t ∧ 3 ≤ pivot t ∧ 6*t+2 ≤ cutoff t ∧
    12*t+4 ≤ pivot t+width t ∧
    (24*t+9)+pivot t+2*width t-2 ≤ 2*cutoff t ∧
    (pivot t+2*width t-3)^2+6*t-3 < 4*width t*(cutoff t-1) ∧
    0 < areaGap t (width t) (cutoff t) (pivot t) := by
  interval_cases t <;> norm_num [width, cutoff, pivot, areaGap]

theorem no_large_scalar (t m u : ℤ) (ht : 2 ≤ t) (htop : t ≤ 9)
    (hm : cutoff t ≤ m) (hu : 3 ≤ u) (hupper : u ≤ 24*t+9)
    (hdensity : 4*width t*(m-1) ≤ (u+2*width t-2)^2+6*t-3)
    (harea : areaGap t (width t) m u ≤ 0) : False := by
  obtain ⟨hw,hp,_,hmm,hmu,hs,hpoint⟩ := certificate_table t ht htop
  exact split_certificate t (width t) (cutoff t) (pivot t) (24*t+9) m u
    hw hp hu hupper hm hmm hmu hs hpoint hdensity harea

/-- Final small table. All inequalities are for P >= 1. -/
theorem final_size_bound (t m n p : ℤ) (ht : 2 ≤ t) (htop : t ≤ 9)
    (hp : p ≤ 1) (hn : n=2*m+p) (hcut : m < cutoff t)
    (hcubic : 3 ≤ t → t^3-3*t^2+3*t+1 ≤ m) :
    t ≤ 7 ∧ m ≤ 288 ∧ n ≤ 577 := by
  interval_cases t <;> norm_num [cutoff] at hcut <;>
    (try have h := hcubic (by omega)) <;> norm_num at * <;> omega

/-- Combined reduction with one common S2 in C9, C10 and both envelopes.
For t=2 the refined envelope is only needed at m>=200, where geometry
must provide a third nonempty interval. Small sizes need no such premise. -/
theorem coupled_residual_cutoff (m p t U eps a r S2 : ℤ)
    (ht : 2 ≤ t) (hm : 2*t+1 ≤ m) (hp : p=0 ∨ p=1)
    (hU0 : 1 ≤ U) (hU : U ≤ 3*t+1) (he : eps ≤ 3*t+6) (ha : 0 ≤ a)
    (hr : 4 ≤ r)
    (harea : 2*(m*(m+p)-eps) ≤ 4*U*(2*m+p-2*t-a-U)+S2)
    (hcap : S2 ≤ (m-1)*(2*m+p-r))
    (henv : 3 ≤ t ∨ 200 ≤ m →
      S2 ≤ (m-1)^2+(m+1-(r-p)-width t)^2+(width t)^2)
    (hH : (2*m+p-r)^2-2*S2 ≤ 6*t-3)
    (hcubic : 3 ≤ t → t^3-3*t^2+3*t+1 ≤ m) :
    t ≤ 7 ∧ m ≤ 288 ∧ 2*m+p ≤ 577 := by
  have hp0 : 0 ≤ p := by omega
  have hp1 : p ≤ 1 := by omega
  have hrbound := support_cap_all_sizes m p t U eps a r S2 ht hm hp hU0 he ha harea hcap
  have hu : 3 ≤ r-p := by omega
  have huupper : r-p ≤ 24*t+9 := by omega
  have hdensity (hg : 3 ≤ t ∨ 200 ≤ m) :
      4*width t*(m-1) ≤ (r-p+2*width t-2)^2+6*t-3 := by
    have h := coupled_density m (r-p) (width t) S2 ((2*m+p-r)^2-2*S2)
      (by ring) (henv hg)
    linarith
  have hcoarse (hg : 3 ≤ t ∨ 200 ≤ m) (hmb : 6*t+2 ≤ m) :
      areaGap t (width t) m (r-p) ≤ 0 :=
    coarse_area m p t U eps a S2 (r-p) (width t)
      hp0 (by omega) hU hmb ha he harea (henv hg)
  have ht9 : t ≤ 9 := by
    by_cases h2 : t=2
    · omega
    have ht3 : 3 ≤ t := by omega
    apply component_count_le_nine t m ht3 (hcubic ht3)
    by_cases hmb : 6*t+2 ≤ m
    · exact linear_cutoff t m (r-p) ht3 hu huupper
        (hdensity (Or.inl ht3)) (hcoarse (Or.inl ht3) hmb)
    · omega
  have hcut : m < cutoff t := by
    by_contra h
    have hmb : 6*t+2 ≤ m := le_trans (certificate_table t ht ht9).2.2.1 (by omega)
    have hg : 3 ≤ t ∨ 200 ≤ m := by
      by_cases h2 : t=2
      · subst t
        norm_num [cutoff] at h
        exact Or.inr h
      · exact Or.inl (by omega)
    exact no_large_scalar t m (r-p) ht ht9 (by omega) hu huupper
      (hdensity hg) (hcoarse hg hmb)
  exact final_size_bound t m (2*m+p) p ht ht9 hp1 rfl hcut hcubic

/-- One interface from the manuscript's necessary unpaid-peak conditions.
The first C8 bound contains component-credit information; it is an explicit
premise, not a consequence of the already constructed word alone. -/
theorem cutoff_of_unpaid_peak (m p t f a v B U eps r S2 : ℤ)
    (ht : 2 ≤ t) (hm : 2*t+1 ≤ m) (hp : p=0 ∨ p=1)
    (hf : 0 ≤ f) (ha : 0 ≤ a) (haf : a ≤ f) (hv : 2*t ≤ v) (hU : 1 ≤ U)
    (hBzero : a=0 → B ≤ t) (hBpos : 1 ≤ a → B ≤ a+t-1)
    (hactivity : f^2 ≤ 4*eps+p) (hcredit : 0 ≤ 2*eps+p-f)
    (hpeak : 1 ≤ 2*B+t-U-(2*eps+p-f))
    (hreserve : 1 ≤ 2*B+m-U-2-2*(t-1)*(v-t)-a*v-eps)
    (htail : 2*f+t^2-2*(v-t) ≤ eps)
    (hr : 4 ≤ r) (hV : 3 ≤ 2*m+p-r)
    (hC9 : (2*m+p-r)^2-2*S2+2*(2*m+p-r-1)*a+a^2+p ≤
      2*(2*eps+p-f))
    (hC10 : 2*(m*(m+p)-eps) ≤ 4*U*(2*m+p-v-a-U)+S2)
    (hcap : S2 ≤ (m-1)*(2*m+p-r))
    (henv : 3 ≤ t ∨ 200 ≤ m →
      S2 ≤ (m-1)^2+(m+1-(r-p)-width t)^2+(width t)^2) :
    t ≤ 7 ∧ m ≤ 288 ∧ 2*m+p ≤ 577 := by
  obtain ⟨he,hu,hcubic,hA⟩ := unpaid_prebounds m p t f a v B U eps
    ht (by omega) (by omega) hf ha haf hv hU hBzero hBpos
    hactivity hcredit hpeak hreserve htail
  have hH := unpaid_density_allowance (2*m+p-r) S2 a p (2*eps+p-f) t
    hV ha (by omega) hC9 hA
  have hprod := mul_nonneg (show 0 ≤ U by omega) (show 0 ≤ v-2*t by omega)
  have harea : 2*(m*(m+p)-eps) ≤ 4*U*(2*m+p-2*t-a-U)+S2 := by nlinarith
  exact coupled_residual_cutoff m p t U eps a r S2 ht hm hp hU hu he ha hr
    harea hcap henv hH hcubic

#print axioms unpaid_prebounds
#print axioms unpaid_density_allowance
#print axioms support_cap_all_sizes
#print axioms linear_cutoff
#print axioms certificate_table
#print axioms final_size_bound
#print axioms coupled_residual_cutoff
#print axioms cutoff_of_unpaid_peak
end CoupledPeakCutoff
