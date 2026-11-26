import BourgadeHuang.RationalEdge.ChargedNormalization
import BourgadeHuang.RationalEdge.EdgeExponential

/-! Actual edge-loop concentration gives normalized charged-path estimates.
Both half-planes are allowed; all root and path assumptions are deterministic
geometric conditions, and all probabilistic estimates are proved internally. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge
open RationalBulk

theorem norm_centered_reflect (epsilon : Bool) (s : AnchoredCountingState) (w r : ℂ) :
    ‖anchoredNevanlinna s (reflectComplex epsilon w)-reflectComplex epsilon r‖ =
      ‖anchoredNevanlinna s w-r‖ := by
  cases epsilon
  · simp only [reflectComplex, Bool.false_eq_true, if_false, anchoredNevanlinna_conj,
      ← map_sub, Complex.norm_conj]
  · simp [reflectComplex]

/-- Centered edge resolvents, including lower-half-plane parameters, retain
quadratic concentration after any complex scalar weight. -/
theorem weighted_centered_second_moment
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (epsilon : Bool) (w r b : ℂ) {K δ : ℝ}
    (hw : 0<(reflectComplex epsilon w).im)
    (hr2 : (reflectComplex epsilon r)^2=reflectComplex epsilon w)
    (hr : 0<(reflectComplex epsilon r).im) (hK : 0≤K)
    (hsector : ‖reflectComplex epsilon r‖≤K*(reflectComplex epsilon r).im)
    (hb : ‖b‖≤δ*(reflectComplex epsilon w).im) :
    Integrable (fun s => ‖b*(anchoredNevanlinna s w-r)‖^2) ν ∧
      (∫ s, ‖b*(anchoredNevanlinna s w-r)‖^2 ∂ν) ≤
        (32*localLawConstant β*edgeStabilityConstant K)*δ^2 := by
  have hi0 := (edge_localLaw_even_moment ν β hh ha he hw hr2 hr hK hsector 0).1
  have hb0 := (edge_localLaw_even_moment ν β hh ha he hw hr2 hr hK hsector 0).2
  simp only [norm_centered_reflect] at hi0 hb0
  norm_num only [Nat.cast_zero, zero_add, Nat.reduceAdd, Nat.reduceMul, pow_one, mul_one] at hi0 hb0
  have hd : 0≤δ := by nlinarith [norm_nonneg b]
  have ht := pow_le_pow_left₀ (norm_nonneg b) hb 2
  rw [mul_pow] at ht
  simp only [norm_mul,mul_pow]
  refine ⟨hi0.const_mul (‖b‖^2), ?_⟩
  rw [integral_const_mul]
  apply (mul_le_mul_of_nonneg_left hb0 (sq_nonneg ‖b‖)).trans
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (sq_pos_of_pos hw)).mpr
  have hC : 0≤32*localLawConstant β*edgeStabilityConstant K :=
    mul_nonneg (mul_nonneg (by norm_num) (localLawConstant_pos β).le)
      (edgeStabilityConstant_pos hK).le
  nlinarith [mul_le_mul_of_nonneg_left ht hC]

/-- Uniform linear exponential concentration for weighted resolvents. -/
theorem weighted_centered_exp_bound
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (epsilon : Bool) (w r b : ℂ) {K δ L : ℝ}
    (hw : 0<(reflectComplex epsilon w).im)
    (hr2 : (reflectComplex epsilon r)^2=reflectComplex epsilon w)
    (hr : 0<(reflectComplex epsilon r).im) (hK : 0≤K)
    (hsector : ‖reflectComplex epsilon r‖≤K*(reflectComplex epsilon r).im)
    (hδ : 0≤δ) (hL : 0≤L) (hb : ‖b‖≤δ*(reflectComplex epsilon w).im) :
    Integrable (fun s => Real.exp (L*‖b*(anchoredNevanlinna s w-r)‖)) ν ∧
      (∫ s, Real.exp (L*‖b*(anchoredNevanlinna s w-r)‖) ∂ν) ≤
        2*Real.exp ((L*δ)^2/(4*edgeExponentialScale β K)) := by
  let l := L*‖b‖/(reflectComplex epsilon w).im
  have hln : 0≤l := div_nonneg (mul_nonneg hL (norm_nonneg _)) hw.le
  have hld : l≤L*δ := by
    apply (div_le_iff₀ hw).mpr
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hL
  have heq (s : AnchoredCountingState) : L*‖b*(anchoredNevanlinna s w-r)‖ =
      l*((reflectComplex epsilon w).im*
        ‖anchoredNevanlinna s (reflectComplex epsilon w)-reflectComplex epsilon r‖) := by
    rw [norm_centered_reflect,norm_mul]
    dsimp [l]
    field_simp [hw.ne']
    ring
  obtain ⟨hi,hb'⟩ := edge_centered_exp_linear ν β hh ha he hw hr2 hr hK hsector l
  refine ⟨by simpa only [heq] using hi, ?_⟩
  simp only [heq]
  apply hb'.trans
  gcongr
  exact mul_nonneg (by norm_num) (edgeExponentialScale_pos β hK).le

/-- Edge loop equations imply the small-relative-path normalization for actual
charged observables, with no probabilistic estimates left as hypotheses. -/
theorem expectedChargedObservable_edge_normalized_bound
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {d : ℕ} (hd : 0<d) (c u v : Fin d → ℂ)
    (epsilon : Fin d → Bool) (m : Fin d → RatioInterval → ℂ)
    (huv : ∀ j, SameOpenHalfPlane (u j) (v j)) (hm : ∀ j, Continuous (m j))
    {K δ : ℝ} (hK : 0≤K) (hδ : 0<δ)
    (hw : ∀ j (t : RatioInterval), 0<(reflectComplex (epsilon j) (ratioPath (u j) (v j) t)).im)
    (hr2 : ∀ j t, (reflectComplex (epsilon j) (m j t))^2=
      reflectComplex (epsilon j) (ratioPath (u j) (v j) t))
    (hr : ∀ j t, 0<(reflectComplex (epsilon j) (m j t)).im)
    (hsector : ∀ j t, ‖reflectComplex (epsilon j) (m j t)‖≤
      K*(reflectComplex (epsilon j) (m j t)).im)
    (hcost : ∀ j (t : RatioInterval), ‖c j*(u j-v j)‖≤
      δ*(reflectComplex (epsilon j) (ratioPath (u j) (v j) t)).im) :
    ‖Complex.exp (-(∑ j, c j*centeredPathPhase (u j) (v j) (m j)))*
      expectedChargedObservable ν c v u-1‖ ≤
      δ*(16*localLawConstant β*edgeStabilityConstant K*(d:ℝ)^2+
        (d:ℝ)*Real.exp (((d:ℝ)*δ)^2/edgeExponentialScale β K)) := by
  have h2 j (t : RatioInterval) := weighted_centered_second_moment ν β hh ha he (epsilon j)
    (ratioPath (u j) (v j) t) (m j t) (c j*(u j-v j))
    (hw j t) (hr2 j t) (hr j t) hK (hsector j t) (hcost j t)
  have hE j (t : RatioInterval) := weighted_centered_exp_bound ν β hh ha he (epsilon j)
    (ratioPath (u j) (v j) t) (m j t) (c j*(u j-v j))
    (hw j t) (hr2 j t) (hr j t) hK (hsector j t) hδ.le
    (by positivity : 0≤2*(d:ℝ)) (hcost j t)
  have h := expectedChargedObservable_normalized_source_bound ν hd c u v m huv hm hδ
    (fun j t => (h2 j t).1) (fun j t => (h2 j t).2)
    (fun j t => (hE j t).1) (fun j t => (hE j t).2)
  convert h using 1
  have heq : (2*(d:ℝ)*δ)^2/(4*edgeExponentialScale β K)=
      ((d:ℝ)*δ)^2/edgeExponentialScale β K := by ring
  rw [heq]
  ring

end BourgadeHuang.RationalEdge
