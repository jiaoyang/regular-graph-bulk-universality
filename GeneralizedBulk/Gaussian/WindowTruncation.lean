import GeneralizedBulk.Gaussian.WindowLaw
import GeneralizedBulk.Gaussian.SeriesRotation
import GeneralizedBulk.Gaussian.SeriesPresentedBounds

/-! Actual retained-window fields converge to the constructed Gaussian series in L². -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology BigOperators
namespace GeneralizedBulk.Gaussian
open Counting
variable {I : Type*} [Countable I] {s : AnchoredCountingState}

def presentationWindowFinset (p : ParticlePresentation s I) (R : ℝ) : Finset I := by
  classical
  have hfinite : ({i : I | p.location i ∈ Set.Icc (-R) R} : Set I).Finite :=
    Set.finite_coe_iff.mp (p.finite_windowLabels (-R) R)
  exact hfinite.toFinset

@[simp] theorem mem_presentationWindowFinset (p : ParticlePresentation s I) (R : ℝ) (i : I) :
    i ∈ presentationWindowFinset p R ↔ p.location i ∈ Set.Icc (-R) R := by
  classical
  simp [presentationWindowFinset]

theorem sum_presentationWindowFinset {V : Type*} [AddCommMonoid V]
    (p : ParticlePresentation s I) (R : ℝ) (f : I → V) :
    (∑ i ∈ presentationWindowFinset p R, f i) =
      letI : Finite (p.WindowLabels (-R) R) := p.finite_windowLabels (-R) R
      letI := Fintype.ofFinite (p.WindowLabels (-R) R)
      ∑ i : p.WindowLabels (-R) R, f i.val := by
  classical
  letI : Finite (p.WindowLabels (-R) R) := p.finite_windowLabels (-R) R
  letI := Fintype.ofFinite (p.WindowLabels (-R) R)
  exact Finset.sum_subtype (p := fun i => p.location i ∈ Set.Icc (-R) R) (F := inferInstance)
    (presentationWindowFinset p R) (fun i => mem_presentationWindowFinset p R i) f

theorem presentationWindowFinset_tendsto (p : ParticlePresentation s I)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n => presentationWindowFinset p (R n)) atTop atTop := by
  classical
  simp only [Filter.atTop_finset_eq_iInf,Filter.tendsto_iInf,Filter.tendsto_principal]
  intro i
  filter_upwards [hR.eventually (eventually_ge_atTop |p.location i|)] with n hn
  exact Finset.singleton_subset_iff.mpr ((mem_presentationWindowFinset p (R n) i).mpr (abs_le.mp hn))

def windowL2 (parameters : Parameters) (p : ParticlePresentation s I) (R : ℝ)
    (v : ℂ × Bool) (i j : Fin 4) : Lp ℂ 2 (iidLaw (markLaw parameters.p) I) :=
  ∑ k ∈ presentationWindowFinset p R,
    ((parameters.scale : ℂ) * particleCoefficient (p.location k) v) • markQuadraticLp parameters.p k i j

theorem windowL2_coe_ae (parameters : Parameters) (p : ParticlePresentation s I) (R : ℝ)
    (v : ℂ × Bool) (i j : Fin 4) :
    (fun γ => windowL2 parameters p R v i j γ) =ᵐ[iidLaw (markLaw parameters.p) I]
      (fun γ => windowField parameters p (-R) R v γ i j) := by
  classical
  let μ := iidLaw (markLaw parameters.p) I
  let a := fun k => (parameters.scale : ℂ) * particleCoefficient (p.location k) v
  have ht : ∀ᵐ γ ∂μ, ∀ k : I, (a k • markQuadraticLp parameters.p k i j) γ =
      a k * (rawQuadratic parameters.p i j (γ k) : ℂ) := by
    apply ae_all_iff.mpr
    intro k
    filter_upwards [Lp.coeFn_smul (a k) (markQuadraticLp parameters.p k i j),
      markQuadraticLp_ae parameters.p k i j] with γ hs hq
    simp only [Pi.smul_apply,smul_eq_mul,hq] at hs
    exact hs
  filter_upwards [coeFn_finset_sum_L2 μ (presentationWindowFinset p R)
    (fun k => a k • markQuadraticLp parameters.p k i j),ht] with γ hsum hterms
  change (∑ k ∈ presentationWindowFinset p R, a k • markQuadraticLp parameters.p k i j) γ = _
  rw [hsum]
  simp_rw [hterms]
  exact sum_presentationWindowFinset p R _

theorem windowL2_tendsto (parameters : Parameters) (p : ParticlePresentation s I)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (v : ℂ × Bool) (i j : Fin 4) :
    Tendsto (fun n => windowL2 parameters p (R n) v i j) atTop
      (𝓝 (l2Series (iidLaw (markLaw parameters.p) I) (fun k => markQuadraticLp parameters.p k i j)
        (fun k => (parameters.scale : ℂ) * particleCoefficient (p.location k) v))) := by
  have hs := hasSum_l2Series (iidLaw (markLaw parameters.p) I)
    (fun k => markQuadraticLp parameters.p k i j)
    (fun k => (parameters.scale : ℂ) * particleCoefficient (p.location k) v) 2
    (fun k l hkl => markQuadraticLp_inner_off _ parameters.abs_p_lt_one hkl i j)
    (by norm_num) (fun k => markQuadraticLp_norm_sq_le_two _ parameters.abs_p_lt_one k i j)
    (by simpa only [norm_mul,mul_pow] using
      (p.summable_coefficient_sq v).mul_left (‖(parameters.scale : ℂ)‖ ^ 2))
  exact hs.comp (presentationWindowFinset_tendsto p R hR)

/-- The actual pointwise finite-window field and the actual L² series
representative converge in their ordinary second-moment distance. -/
theorem windowField_second_moment_error_tendsto_zero
    (parameters : Parameters) (p : ParticlePresentation s I)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (v : ℂ × Bool) (i j : Fin 4) :
    Tendsto (fun n => ∫ γ, ‖presentedGaussianL2 parameters p v γ i j -
      windowField parameters p (-R n) (R n) v γ i j‖ ^ 2 ∂iidLaw (markLaw parameters.p) I)
      atTop (𝓝 0) := by
  let μ := iidLaw (markLaw parameters.p) I
  let L := l2Series μ (fun k => markQuadraticLp parameters.p k i j)
    (fun k => (parameters.scale : ℂ) * particleCoefficient (p.location k) v)
  have heq (n : ℕ) : (∫ γ, ‖presentedGaussianL2 parameters p v γ i j -
      windowField parameters p (-R n) (R n) v γ i j‖ ^ 2 ∂μ) =
      ‖L - windowL2 parameters p (R n) v i j‖ ^ 2 := by
    rw [← integral_norm_sq_L2 μ]
    apply integral_congr_ae
    filter_upwards [windowL2_coe_ae parameters p (R n) v i j,
      Lp.coeFn_sub L (windowL2 parameters p (R n) v i j)] with γ hw hs
    change ‖L γ - windowField parameters p (-R n) (R n) v γ i j‖ ^ 2 = _
    rw [hs]
    simp only [Pi.sub_apply,hw]
  have h := ((tendsto_const_nhds (x := L)).sub (windowL2_tendsto parameters p R hR v i j)).norm.pow 2
  change Tendsto (fun n => ‖L - windowL2 parameters p (R n) v i j‖ ^ 2) atTop
    (𝓝 (‖L - L‖ ^ 2)) at h
  have hz : Tendsto (fun n => ‖L - windowL2 parameters p (R n) v i j‖ ^ 2) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)] using h
  convert hz using 1
  funext n
  exact heq n

end GeneralizedBulk.Gaussian
