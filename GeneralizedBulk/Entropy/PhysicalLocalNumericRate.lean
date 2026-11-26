import GeneralizedBulk.Graph.PhysicalSampleBounds
import GeneralizedBulk.Entropy.UniformLocalEntropyRate

/-! Uniform polynomial envelopes for the actual resolvent-scale raw factors.
These use their genuine eta floor, rather than the weaker construction floor. -/
noncomputable section
open Filter
open scoped Topology
namespace GeneralizedBulk.Entropy.ChannelRates
open GeneralizedBulk.External.RegularSpectralData

def physicalFloorConstant (d : ℕ) : ℝ := 1/(2*((2*(d : ℝ))^2+1))

theorem physicalFloorConstant_pos (d : ℕ) : 0 < physicalFloorConstant d := by
  unfold physicalFloorConstant
  positivity

theorem physicalResolventFloor_eq (d : ℕ) (eta : ℝ) :
    physicalResolventFloor d eta = physicalFloorConstant d*eta := by
  unfold physicalResolventFloor physicalFloorConstant
  ring

theorem physicalResolventVariance_eq (m s c : ℝ) (N : ℕ) :
    m*(1/(s*(N : ℝ)^(-c))) = (m/s)*(N : ℝ)^c := by
  rw [Real.rpow_neg (Nat.cast_nonneg N)]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,one_mul]
  ring

def physicalLocalEntropyError (I : Type*) [Fintype I] (d : ℕ)
    (m s κref Uref B c C localExponent : ℝ) (q N : ℕ) (p : ℝ) : ℝ :=
  2*p*(uniformMixtureAbsoluteEntropyBound I (physicalResolventFloor d ((N : ℝ)^(-c)))
      (m*(1/(s*(N : ℝ)^(-c)))) (B*Real.log (N : ℝ)^q)+
    uniformMixtureAbsoluteEntropyBound I κref Uref (B*Real.log (N : ℝ)^q))+
    2*Real.binEntropy p+localCovarianceEntropyError C B q localExponent c N

theorem eventually_uniform_physical_entropy_error (I : Type*) [Fintype I] (d : ℕ)
    (m s κref Uref B c C localExponent : ℝ) (hm : 0 < m) (hs : 0 < s)
    (hκref : 0 < κref) (hUref : 0 < Uref) (hc : 0 < c) (hcsmall : c ≤ 1/16)
    (hl : 0 < localExponent) (q : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℝ,0 ≤ p → p ≤ 1 → p ≤ (N : ℝ)^(-(1/2 : ℝ)) →
      physicalLocalEntropyError I d m s κref Uref B c C localExponent q N p ≤
        (N : ℝ)^(-localComparisonExponent localExponent c) := by
  have hh := eventually_uniform_local_entropy_comparison I (physicalFloorConstant d) (m/s) κref Uref B c C localExponent
    (physicalFloorConstant_pos d) (div_pos hm hs) hκref hUref hc hcsmall hl q
  filter_upwards [hh] with N hn p hp hp1 hpsmall
  simpa only [physicalLocalEntropyError,physicalResolventFloor_eq,physicalResolventVariance_eq] using hn p hp hp1 hpsmall

theorem localCovarianceScale_tendsto (C localExponent c : ℝ) (hl : 0 < localExponent) (hc : 0 < c) :
    Tendsto (fun N : ℕ => C*((N : ℝ)^(-localExponent)+Real.sqrt ((N : ℝ)^(-c)))) atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hp := (tendsto_rpow_neg_atTop hl).comp hn
  have hq := (tendsto_rpow_neg_atTop hc).comp hn
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hq
  simpa only [Real.sqrt_zero,add_zero,mul_zero] using (hp.add hs).const_mul C

theorem eventually_localCovarianceScale_small (C κ m localExponent c : ℝ)
    (hl : 0 < localExponent) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      C*((N : ℝ)^(-localExponent)+Real.sqrt ((N : ℝ)^(-c))) ≤ 1 ∧
      (m^2/κ)*(C*((N : ℝ)^(-localExponent)+Real.sqrt ((N : ℝ)^(-c)))) ≤ 1/2 := by
  have he := localCovarianceScale_tendsto C localExponent c hl hc
  have hscaled := he.const_mul (m^2/κ)
  have h1 := (tendsto_order.mp he).2 1 (by norm_num)
  have h2 := (tendsto_order.mp hscaled).2 (1/2) (by norm_num)
  filter_upwards [h1,h2] with N hN hN'
  exact ⟨hN.le,hN'.le⟩

end GeneralizedBulk.Entropy.ChannelRates
