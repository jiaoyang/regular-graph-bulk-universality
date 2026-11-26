import GeneralizedBulk.Entropy.MehlerAbsoluteEntropy
import GeneralizedBulk.Entropy.GaussianMixtureLinearEntropy
import GeneralizedBulk.Entropy.ConstructedEntropyDeficit

/-! Exact conversion of a Mehler scale to a signal plus standard Gaussian,
and cancellation of dimensions in the balanced observation deficit. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Gaussian Hermite
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

theorem smoothingFactor_logabsdet (a : ℝ) (ha : 0 < 1-a^2) :
    Real.log (|(smoothingFactor I a).det|)=(Fintype.card I : ℝ)/2*Real.log (1-a^2) := by
  rw [smoothingFactor,Matrix.det_diagonal,Finset.abs_prod,
    Real.log_prod _ _ (fun i hi => abs_ne_zero.mpr (Real.sqrt_pos.mpr ha).ne')]
  simp only [abs_of_pos (Real.sqrt_pos.mpr ha),Real.log_sqrt ha.le,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]
  ring

def physicalSignalScale (a : ℝ) : ℝ := a/Real.sqrt (1-a^2)

theorem physicalSignalScale_range (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1/2) :
    physicalSignalScale a ∈ Set.Icc (0 : ℝ) 1 := by
  have hv : 0 < 1-a^2 := by nlinarith
  have hs : 0 < Real.sqrt (1-a^2) := Real.sqrt_pos.mpr hv
  refine ⟨div_nonneg ha hs.le,(div_le_one hs).mpr ?_⟩
  have hsq := Real.sq_sqrt hv.le
  nlinarith

namespace NormalizedFiniteSignal
variable (D : NormalizedFiniteSignal I S)

def signalNoiseDensity (r : ℝ) : (I → ℝ) → ℝ :=
  gaussianMixturePDF D.weight (fun s => r • D.signal s) (fun _ => (1 : Matrix I I ℝ))

theorem smoothing_entropy_scale (a : ℝ) (ha : 0 < 1-a^2) :
    differentialEntropy (D.lebesgueDensity a)=differentialEntropy (D.signalNoiseDensity (physicalSignalScale a))+
      (Fintype.card I : ℝ)/2*Real.log (1-a^2) := by
  have hs : Real.sqrt (1-a^2) ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hm (s : S) : (smoothingFactor I a).mulVec (physicalSignalScale a • D.signal s)=fun i => a*D.signal s i := by
    rw [smoothingFactor_mulVec]
    funext i
    simp only [Pi.smul_apply,smul_eq_mul,physicalSignalScale]
    field_simp
  have hh := gaussianMixture_linear_entropy_change D.weight (fun s => physicalSignalScale a • D.signal s)
    (fun _ => (1 : Matrix I I ℝ)) (smoothingFactor I a) D.nonneg D.total
    (fun _ => by simp) (smoothingFactor_det_ne_zero a ha)
  simp only [hm,Matrix.mul_one,smoothingFactor_logabsdet a ha] at hh
  exact hh

theorem relativeEntropy_eq_signalNoise (a : ℝ) (ha : 0 < 1-a^2) :
    relativeEntropy (standardGaussian I) (D.density a)=
      (Fintype.card I : ℝ)/2*(1+Real.log (2*Real.pi)-Real.log (1-a^2))-
        differentialEntropy (D.signalNoiseDensity (physicalSignalScale a)) := by
  rw [D.relativeEntropy_eq_standard_sub_differential a ha,D.smoothing_entropy_scale a ha]
  ring

theorem observationEntropyDeficit_eq_signalNoise
    {C : Type*} [Fintype C] (O : C → Matrix I I ℝ)
    (hO : ∀ c,O c*(O c).transpose=1) (observed : C → Finset I)
    (hbalanced : (∑ c,(Fintype.card (observed c) : ℝ))=2*(Fintype.card I : ℝ))
    (a : ℝ) (ha : 0 < 1-a^2) :
    D.observationEntropyDeficit O hO observed a=
      -differentialEntropy (D.signalNoiseDensity (physicalSignalScale a))+
        (1/2 : ℝ)*∑ c,differentialEntropy ((D.observedSignal (O c) (hO c) (observed c)).signalNoiseDensity (physicalSignalScale a)) := by
  unfold observationEntropyDeficit
  rw [D.relativeEntropy_eq_signalNoise a ha]
  simp_rw [relativeEntropy_eq_signalNoise _ a ha]
  rw [Finset.sum_sub_distrib]
  have he (t : ℝ) : (∑ c,(Fintype.card (observed c) : ℝ)/2*t)=(Fintype.card I : ℝ)*t := by
    simp only [← Finset.sum_mul,← Finset.sum_div,hbalanced]
    ring
  rw [he]
  ring

end NormalizedFiniteSignal
end GeneralizedBulk.Entropy.Mehler
