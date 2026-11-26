import GaussianWave.BS.GaussianLabelRestriction
import GaussianWave.BS.IndependentChannelLaw

/-! Joint channels are sampled from literal independent labels on the
channel-times-vertex index set. Their product law is proved from the actual
coefficient Gram matrix, rather than assumed from scalar marginals. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

/-- Put a coefficient row in one actual channel of the label space. -/
def channelFinsupp {κ V : Type*} (c : κ) (a : V →₀ ℝ) : (κ × V) →₀ ℝ :=
  Finsupp.mapDomain (fun v => (c,v)) a

@[simp] theorem channelFinsupp_apply {κ V : Type*} (c b : κ) (a : V →₀ ℝ) (v : V) :
    channelFinsupp c a (b,v) = if c=b then a v else 0 := by
  by_cases h : c=b
  · subst b
    rw [channelFinsupp,Finsupp.mapDomain_apply (fun _ _ he => (Prod.mk.inj he).2)]
    simp
  · rw [channelFinsupp,Finsupp.mapDomain_notin_range]
    · simp [h]
    · rintro ⟨w,hw⟩
      exact h (congrArg Prod.fst hw)

theorem finsuppPairing_channelFinsupp {κ V : Type*} (c b : κ) (a a' : V →₀ ℝ) :
    finsuppPairing (channelFinsupp c a) (channelFinsupp b a') =
      if c=b then finsuppPairing a a' else 0 := by
  rw [finsuppPairing_apply,channelFinsupp,Finsupp.sum_mapDomain_index (by simp) (by intros; ring)]
  by_cases h : c=b
  · simp only [channelFinsupp_apply,h,if_pos rfl]
    exact (finsuppPairing_apply a a').symm
  · simp only [channelFinsupp_apply,if_neg (Ne.symm h),mul_zero,Finsupp.sum_zero_index,if_neg h]
    simp

/-- The joint sampled law is exactly the independent product of the whole
scalar sampled laws, including their correlations across observation sites. -/
theorem finiteSupportGaussianLaw_channels {κ V J : Type*}
    [Fintype κ] [Fintype J] (a : J → V →₀ ℝ) :
    finiteSupportGaussianLaw (fun cj : κ × J => channelFinsupp cj.1 (a cj.2)) =
      independentChannelLaw (fun _ : κ => finiteSupportGaussianLaw a) := by
  let C := finiteSupportGaussianMatrix a*(finiteSupportGaussianMatrix a).transpose
  have hscalar : HasGaussianCovariance (finiteSupportGaussianLaw a) C :=
    finiteSupportGaussianLaw_gaussian a
  have hjoint := finiteSupportGaussianLaw_gaussian
    (fun cj : κ × J => channelFinsupp cj.1 (a cj.2))
  have he : finiteSupportGaussianMatrix (fun cj : κ × J => channelFinsupp cj.1 (a cj.2))*
      (finiteSupportGaussianMatrix (fun cj : κ × J => channelFinsupp cj.1 (a cj.2))).transpose =
      channelBlockCovariance (fun _ : κ => C) := by
    ext cj bj
    rw [finiteSupportGaussianMatrix_gram,finsuppPairing_channelFinsupp]
    change (if cj.1=bj.1 then finsuppPairing (a cj.2) (a bj.2) else 0) = _
    simp only [channelBlockCovariance,C,finiteSupportGaussianMatrix_gram]
  rw [he] at hjoint
  apply measure_eq_of_linear_characteristic
  intro t
  exact (hjoint t).trans ((independentChannelLaw_gaussian
    (fun _ : κ => finiteSupportGaussianLaw a) (fun _ => C) (fun _ => hscalar)) t).symm

/-- The literal channel-label sampler equals evaluation of the scalar rule
at the corresponding channel field. -/
theorem finiteSupportGaussianSample_channels {κ V J : Type*}
    (a : J → V →₀ ℝ) (ξ : (κ × V) → ℝ) (c : κ) (j : J) :
    finiteSupportGaussianSample (fun cj : κ × J => channelFinsupp cj.1 (a cj.2)) ξ (c,j) =
      finiteSupportGaussianSample a (fun v => ξ (c,v)) j := by
  exact finiteSupportGaussianSample_mapDomain (fun v => (c,v)) (a j) ξ

end GaussianWave.BS
