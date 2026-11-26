import BourgadeHuang.CMS.AnalyticCoupledVolterra

/-! Explicit contraction bounds after finite triangular elimination. -/
noncomputable section
open scoped BigOperators
namespace BourgadeHuang.CMS
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E]

theorem norm_coupledVolterraRemainder_le
    (P : E →L[ℂ] E) (K : F →L[ℂ] F) (C01 : E →L[ℂ] F)
    (C10 : F →L[ℂ] E) (C11 : E →L[ℂ] E) :
    ‖coupledVolterraRemainder P K C01 C10 C11‖≤
      ‖P‖*(‖C10‖*‖K‖*‖C01‖+‖C11‖) := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg P)
  apply (norm_add_le _ _).trans
  apply add_le_add_right
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg C01))

/-- A uniform finite geometric constant for the principal triangular inverse. -/
def triangularInverseBound (a M : ℝ) (H : ℕ) : ℝ :=
  ∑k∈Finset.range H,(a⁻¹*M)^k

theorem triangularInverseBound_nonneg {a M : ℝ} (ha : 0≤a) (hM : 0≤M) (H : ℕ) :
    0≤triangularInverseBound a M H :=
  Finset.sum_nonneg (fun k _ => pow_nonneg (mul_nonneg (inv_nonneg.mpr ha) hM) k)

theorem norm_triangularInverse_comp_le {a M : ℝ} (ha : 0<a) (_hM : 0≤M)
    (Q N : E →L[ℂ] E) (hQ : ‖Q‖≤a⁻¹) (hN : ‖N‖≤M) (H : ℕ) :
    ‖triangularInverse (Q.comp N) H‖≤triangularInverseBound a M H := by
  apply (norm_triangularInverse_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  apply pow_le_pow_left₀ (norm_nonneg _) _ k
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul hQ hN (norm_nonneg N) (inv_nonneg.mpr ha.le))

/-- The actual effective contraction constant decays as the reciprocal
starting radius, with every coefficient norm accounted for. -/
theorem norm_eliminated_coupledVolterra_le {R a M : ℝ}
    (hR : 0<R) (ha : 0<a) (hM : 0≤M)
    (Q P : E →L[ℂ] E) (K : F →L[ℂ] F)
    (N : E →L[ℂ] E) (C01 : E →L[ℂ] F) (C10 : F →L[ℂ] E) (C11 : E →L[ℂ] E)
    (hQ : ‖Q‖≤a⁻¹) (hP : ‖P‖≤R⁻¹*a⁻¹) (hK : ‖K‖≤1)
    (hN : ‖N‖≤M) (h01 : ‖C01‖≤M) (h10 : ‖C10‖≤M) (h11 : ‖C11‖≤M)
    (H : ℕ) :
    ‖triangularInverse (Q.comp N) H*coupledVolterraRemainder P K C01 C10 C11‖≤
      triangularInverseBound a M H*R⁻¹*a⁻¹*(M*M+M) := by
  have hn := norm_triangularInverse_comp_le ha hM Q N hQ hN H
  have hrem : ‖coupledVolterraRemainder P K C01 C10 C11‖≤(R⁻¹*a⁻¹)*(M*M+M) := by
    apply (norm_coupledVolterraRemainder_le P K C01 C10 C11).trans
    apply mul_le_mul hP _ (by positivity) (by positivity)
    apply add_le_add _ h11
    apply mul_le_mul _ h01 (norm_nonneg C01) hM
    simpa only [mul_one] using mul_le_mul h10 hK (norm_nonneg K) hM
  calc
    _≤‖triangularInverse (Q.comp N) H‖*‖coupledVolterraRemainder P K C01 C10 C11‖ := norm_mul_le _ _
    _≤triangularInverseBound a M H*((R⁻¹*a⁻¹)*(M*M+M)) :=
      mul_le_mul hn hrem (norm_nonneg _) (triangularInverseBound_nonneg ha.le hM H)
    _=_ := by ring

theorem eliminated_coupledVolterra_lt_one_of_radius {R a M : ℝ}
    (hR : 0<R) (ha : 0<a) (hM : 0≤M)
    (Q P : E →L[ℂ] E) (K : F →L[ℂ] F)
    (N : E →L[ℂ] E) (C01 : E →L[ℂ] F) (C10 : F →L[ℂ] E) (C11 : E →L[ℂ] E)
    (hQ : ‖Q‖≤a⁻¹) (hP : ‖P‖≤R⁻¹*a⁻¹) (hK : ‖K‖≤1)
    (hN : ‖N‖≤M) (h01 : ‖C01‖≤M) (h10 : ‖C10‖≤M) (h11 : ‖C11‖≤M)
    (H : ℕ) (hlarge : triangularInverseBound a M H*a⁻¹*(M*M+M)<R) :
    ‖triangularInverse (Q.comp N) H*coupledVolterraRemainder P K C01 C10 C11‖<1 := by
  apply (norm_eliminated_coupledVolterra_le hR ha hM Q P K N C01 C10 C11
    hQ hP hK hN h01 h10 h11 H).trans_lt
  calc
    _=(triangularInverseBound a M H*a⁻¹*(M*M+M))/R := by ring
    _<1 := (div_lt_one hR).mpr hlarge

end BourgadeHuang.CMS
