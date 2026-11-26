import BourgadeHuang.CMS.ImproperVariation

/-! Improper variation of constants for the constructed exponentially decaying
triangular fundamental solution, with integrability derived from its bounds. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace BourgadeHuang.CMS
variable {J : Type*} [Fintype J] [DecidableEq J]
set_option maxHeartbeats 600000

lemma continuous_principalOperator {R : ℝ} (lam : J → ℂ)
    (N : Tail R →ᵇ (J → J → ℂ)) (H : ℕ) :
    Continuous (Function.uncurry (principalOperator lam N H)) := by
  apply continuous_finiteMatrixOperator.comp
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_triangularEvolution lam (extendTailMatrix N) (continuous_extendTailMatrix N) H i j

lemma norm_principalOperator_le {R a : ℝ} (ha : 0<a) (lam : J → ℂ)
    (N : Tail R →ᵇ (J → J → ℂ)) (H : ℕ) (hlam : ∀ i, 2*a≤(lam i).re)
    {t s : ℝ} (ht : R≤t) (hts : t≤s) :
    ‖principalOperator lam N H t s‖ ≤
      triangularDecayConstant (J:=J) a ‖N‖ H*Real.exp (-a*(s-t)) := by
  have hb : 0≤(∑ n ∈ Finset.range (H+1), ((Fintype.card J:ℝ)*‖N‖*a⁻¹)^n)*Real.exp (-a*(s-t)) := by
    apply mul_nonneg _ (Real.exp_nonneg _)
    apply Finset.sum_nonneg
    intro n hn
    exact pow_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg N))
      (inv_nonneg.mpr ha.le)) n
  have hm := norm_finiteMatrixOperator_le
    (A:=triangularEvolution lam (extendTailMatrix N) H t s) hb (fun i j =>
      norm_triangularEvolution_le lam (extendTailMatrix N) (continuous_extendTailMatrix N)
        ha (norm_nonneg N) hlam (fun x _ i j=>norm_extendTailMatrix_le N x i j) H ht hts i j)
  simpa only [principalOperator,triangularDecayConstant,mul_assoc] using hm

lemma integrable_principalOperator_tail {R a : ℝ} (ha : 0<a) (lam : J → ℂ)
    (N : Tail R →ᵇ (J → J → ℂ)) (H : ℕ) (hlam : ∀ i, 2*a≤(lam i).re)
    (f : ℝ →ᵇ (J → ℂ)) :
    IntegrableOn (fun s => principalOperator lam N H R s (f s)) (Ioi R) := by
  let C := triangularDecayConstant (J:=J) a ‖N‖ H
  have hC : 0≤C := triangularDecayConstant_nonneg ha (norm_nonneg N) H
  apply ((integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) R).const_mul
    (C*‖f‖*Real.exp (a*R))).mono'
  · exact (((continuous_principalOperator lam N H).comp
      (continuous_const.prodMk continuous_id)).clm_apply f.continuous).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change R<s at hs
    calc
      _ ≤ ‖principalOperator lam N H R s‖*‖f s‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (C*Real.exp (-a*(s-R)))*‖f‖ := mul_le_mul
        (norm_principalOperator_le ha lam N H hlam le_rfl hs.le) (f.norm_coe_le_norm s)
        (norm_nonneg (f s)) (mul_nonneg hC (Real.exp_nonneg _))
      _ = (C*‖f‖*Real.exp (a*R))*Real.exp (-a*s) := by
        rw [show -a*(s-R)=a*R+ -a*s by ring,Real.exp_add]
        ring

/-- The improper integral solves the actual triangular inhomogeneous ODE.
Its existence and integrability are consequences of the spectral gap. -/
theorem hasDerivAt_triangularBackwardTail {R a : ℝ} (ha : 0<a) (lam : J → ℂ)
    (N : Tail R →ᵇ (J → J → ℂ)) (degree : J → ℕ)
    (hN : ∀ x i j, ¬ degree j<degree i → N x i j=0)
    (H : ℕ) (hH : ∀ i, degree i<H) (hlam : ∀ i, 2*a≤(lam i).re)
    (f : ℝ →ᵇ (J → ℂ)) {t : ℝ} (ht : R<t) :
    HasDerivAt (backwardTail (principalOperator lam N H) R f)
      (triangularGenerator lam N t (backwardTail (principalOperator lam N H) R f t)+f t) t := by
  apply hasDerivAt_backwardTail _ _ _ _
    (principalOperator_comp lam N degree hN H hH) (principalOperator_self lam N H)
    (hasDerivAt_principalOperator lam N degree hN H hH)
  · exact ((continuous_principalOperator lam N H).comp
      (continuous_const.prodMk continuous_id)).clm_apply f.continuous
  · exact integrable_principalOperator_tail ha lam N H hlam f
  · exact ht

end BourgadeHuang.CMS
