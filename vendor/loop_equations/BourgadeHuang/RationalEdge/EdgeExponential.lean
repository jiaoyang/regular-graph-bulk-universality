import BourgadeHuang.RationalEdge.EdgeLocalLaw
import BourgadeHuang.BulkExponentialControl

/-! Centered sub-Gaussian control on fixed root sectors, derived from the
exact general-beta edge hierarchy. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace BourgadeHuang.RationalEdge

theorem edge_centered_factorial_moments
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {w r : ℂ} {K : ℝ} (hw : 0<w.im) (hr2 : r^2=w)
    (hr : 0<r.im) (hK : 0≤K) (hsector : ‖r‖≤K*r.im) (q : ℕ) :
    Integrable (fun s => (w.im*‖anchoredNevanlinna s w-r‖)^(2*q)) ν ∧
      (∫ s, (w.im*‖anchoredNevanlinna s w-r‖)^(2*q) ∂ν) ≤
        ((32*localLawConstant β*edgeStabilityConstant K)*Real.exp 1)^q*(q.factorial:ℝ) := by
  have hconstant := (localLawConstant_pos β).le
  have hsectorConstant := (edgeStabilityConstant_pos hK).le
  cases q with
  | zero => simp
  | succ n =>
    obtain ⟨hi,hb⟩ := edge_localLaw_even_moment ν β hh ha he hw hr2 hr hK hsector n
    constructor
    · simpa only [mul_pow] using hi.const_mul (w.im^(2*(n+1)))
    · simp only [mul_pow,integral_const_mul]
      have hc : w.im^(2*(n+1))≠0 := pow_ne_zero _ hw.ne'
      calc
        _ ≤ w.im^(2*(n+1))*(((32*localLawConstant β*edgeStabilityConstant K)*((n:ℝ)+1))^(n+1)/w.im^(2*(n+1))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
        _ = ((32*localLawConstant β*edgeStabilityConstant K)*((n:ℝ)+1))^(n+1) := by field_simp
        _ ≤ (32*localLawConstant β*edgeStabilityConstant K)^(n+1)*((Real.exp 1)^(n+1)*((n+1).factorial:ℝ)) := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add,Nat.cast_one] using nat_pow_le_exp_factorial (n+1)) (by positivity)
        _ = _ := by ring

def edgeExponentialScale (β K : ℝ) : ℝ :=
  (2*((32*localLawConstant β*edgeStabilityConstant K)*Real.exp 1))⁻¹

theorem edgeExponentialScale_pos (β : ℝ) {K : ℝ} (hK : 0≤K) :
    0<edgeExponentialScale β K := by
  unfold edgeExponentialScale
  have := localLawConstant_pos β
  have := edgeStabilityConstant_pos hK
  positivity

/-- A uniform sub-Gaussian expectation bound on the specified root sector. -/
theorem edge_centered_exp_square
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {w r : ℂ} {K : ℝ} (hw : 0<w.im) (hr2 : r^2=w)
    (hr : 0<r.im) (hK : 0≤K) (hsector : ‖r‖≤K*r.im) :
    Integrable (fun s => Real.exp (edgeExponentialScale β K*(w.im*‖anchoredNevanlinna s w-r‖)^2)) ν ∧
      (∫ s, Real.exp (edgeExponentialScale β K*(w.im*‖anchoredNevanlinna s w-r‖)^2) ∂ν) ≤ 2 := by
  have hconstant := (localLawConstant_pos β).le
  have hsectorConstant := (edgeStabilityConstant_pos hK).le
  have hconstant_ne := (localLawConstant_pos β).ne'
  have hsector_ne := (edgeStabilityConstant_pos hK).ne'
  have hc : edgeExponentialScale β K*((32*localLawConstant β*edgeStabilityConstant K)*Real.exp 1)=1/2 := by
    dsimp [edgeExponentialScale]
    field_simp
    <;> ring
  have h := integral_exp_sq_le_of_factorial_moments ν
    (fun s => w.im*‖anchoredNevanlinna s w-r‖)
    (continuous_const.mul ((continuous_anchoredNevanlinna hw.ne').sub continuous_const).norm).aestronglyMeasurable
    (by positivity : 0≤(32*localLawConstant β*edgeStabilityConstant K)*Real.exp 1) (edgeExponentialScale_pos β hK).le (by rw [hc]; norm_num)
    (fun q => (edge_centered_factorial_moments ν β hh ha he hw hr2 hr hK hsector q).1)
    (fun q => (edge_centered_factorial_moments ν β hh ha he hw hr2 hr hK hsector q).2)
  simpa only [hc,show (1-(1:ℝ)/2)⁻¹=2 by norm_num] using h

/-- Linear exponential moments are uniformly bounded by the same estimate,
whose constants depend only on beta and the root-sector ratio. -/
theorem edge_centered_exp_linear
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {w r : ℂ} {K : ℝ} (hw : 0<w.im) (hr2 : r^2=w)
    (hr : 0<r.im) (hK : 0≤K) (hsector : ‖r‖≤K*r.im) (L : ℝ) :
    Integrable (fun s => Real.exp (L*(w.im*‖anchoredNevanlinna s w-r‖))) ν ∧
      (∫ s, Real.exp (L*(w.im*‖anchoredNevanlinna s w-r‖)) ∂ν) ≤
        2*Real.exp (L^2/(4*edgeExponentialScale β K)) := by
  have hscale := edgeExponentialScale_pos β hK
  let X := fun s : AnchoredCountingState => w.im*‖anchoredNevanlinna s w-r‖
  have hX : Continuous X := continuous_const.mul
    ((continuous_anchoredNevanlinna hw.ne').sub continuous_const).norm
  have hXn (s) : 0≤X s := mul_nonneg hw.le (norm_nonneg _)
  obtain ⟨hi,hb⟩ := edge_centered_exp_square ν β hh ha he hw hr2 hr hK hsector
  have hlin : Integrable (fun s => Real.exp (L*X s)) ν := by
    simpa only [abs_of_nonneg (hXn _)] using
      integrable_exp_mul_abs_of_exp_sq hX.aestronglyMeasurable (edgeExponentialScale_pos β hK) hi L
  refine ⟨hlin, ?_⟩
  have hp (s) : Real.exp (L*X s) ≤
      Real.exp (L^2/(4*edgeExponentialScale β K))*Real.exp (edgeExponentialScale β K*X s^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hc := edgeExponentialScale_pos β hK
    have hs := sq_nonneg (2*edgeExponentialScale β K*X s-L)
    apply (mul_le_mul_left (by positivity : 0<4*edgeExponentialScale β K)).mp
    field_simp
    nlinarith only [hs]
  calc
    _ ≤ ∫ s, Real.exp (L^2/(4*edgeExponentialScale β K))*Real.exp (edgeExponentialScale β K*X s^2) ∂ν :=
      integral_mono hlin (hi.const_mul _) hp
    _ = Real.exp (L^2/(4*edgeExponentialScale β K))*(∫ s, Real.exp (edgeExponentialScale β K*X s^2) ∂ν) := integral_const_mul _ _
    _ ≤ _ := by nlinarith [Real.exp_pos (L^2/(4*edgeExponentialScale β K))]


end BourgadeHuang.RationalEdge
