import GeneralizedBulk.Graph.ConfigurationRepairCount
import GeneralizedBulk.Graph.ConfigurationDefectExpectation
import GeneralizedBulk.Graph.ConfigurationUniform

/-! An internal polynomial lower bound on the probability that a uniform
configuration is simple. No asymptotic simplicity theorem is assumed. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph.Configuration

variable {N d : ℕ} [Nonempty (Pairing (Stub N d))]

theorem pairingLaw_real_subtype (R : Pairing (Stub N d) → Prop) [DecidablePred R] :
    (pairingLaw (Stub N d)).real {p | R p} =
      (Fintype.card {p : Pairing (Stub N d) // R p} : ℝ) / Fintype.card (Pairing (Stub N d)) := by
  have hs : ({p : Pairing (Stub N d) | R p} : Set _) =
      (Finset.univ.filter R : Finset (Pairing (Stub N d))) := by ext p; simp
  rw [measureReal_def,pairingLaw,hs,Graph.finiteUniform_finset_toReal,Fintype.card_subtype]

theorem boundedDefect_probability_half (M : ℕ) (hL : 6 ≤ N*d) (hM : 8*d*(d+1) ≤ M) :
    (1/2 : ℝ) ≤ (pairingLaw (Stub N d)).real {p | defect p ≤ M} := by
  letI : IsProbabilityMeasure (pairingLaw (Stub N d)) := pairingLaw_isProbability _
  have hE := integral_defect_le_degree_bound (N := N) (d := d) hL
  have hMr : (8 : ℝ)*d*((d : ℝ)+1) ≤ M := by exact_mod_cast hM
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun p : Pairing (Stub N d) => (by positivity : (0 : ℝ) ≤ defect p)))
    (integrable_pairingLaw_real (fun p => (defect p : ℝ))) ((M : ℝ)+1)
  have hs : {p : Pairing (Stub N d) | (M : ℝ)+1 ≤ (defect p : ℝ)} =
      {p | M+1 ≤ defect p} := by ext p; norm_cast
  rw [hs] at hm
  have hbad : (pairingLaw (Stub N d)).real {p | M+1 ≤ defect p} ≤ (1/2 : ℝ) := by
    have hnonneg := measureReal_nonneg (μ := pairingLaw (Stub N d)) (s := {p | M+1 ≤ defect p})
    nlinarith [show (0 : ℝ) ≤ M by positivity]
  have hcomp : {p : Pairing (Stub N d) | defect p ≤ M} = {p | M+1 ≤ defect p}ᶜ := by
    ext p; simp only [Set.mem_setOf_eq,Set.mem_compl_iff]; omega
  rw [hcomp,measureReal_compl (show MeasurableSet {p : Pairing (Stub N d) | M+1 ≤ defect p} from trivial)]
  simp only [measureReal_univ_eq_one]
  linarith

set_option maxHeartbeats 1000000 in
theorem polynomial_simplicity_probability_lower_bound (M : ℕ)
    (hL : 6 ≤ N*d) (hM : 8*d*(d+1) ≤ M)
    (hsize : 4*d*(d+1)+M < N*d) :
    (1 : ℝ) / (2 * (1+(N*d)^2)^M) ≤
      (pairingLaw (Stub N d)).real {p | SimpleConfiguration p} := by
  have hgood := boundedDefect_probability_half M hL hM
  have hcount := boundedDefect_card_le (N := N) (d := d) M hsize
  have htotal : (0 : ℝ) < Fintype.card (Pairing (Stub N d)) := by exact_mod_cast Fintype.card_pos
  have hzero : {p : Pairing (Stub N d) | defect p = 0} = {p | SimpleConfiguration p} := by
    ext p
    exact defect_zero_iff p
  have hprob : (pairingLaw (Stub N d)).real {p | defect p ≤ M} ≤
      (pairingLaw (Stub N d)).real {p | SimpleConfiguration p} * (1+(N*d)^2)^M := by
    rw [← hzero,pairingLaw_real_subtype,pairingLaw_real_subtype,div_mul_eq_mul_div]
    apply (div_le_div_iff_of_pos_right htotal).mpr
    exact_mod_cast hcount
  have hK : (0 : ℝ) < (1+(N*d)^2)^M := by positivity
  apply (div_le_iff₀ (mul_pos (by norm_num) hK)).mpr
  nlinarith [hgood.trans hprob]

theorem simplicity_probability_exp_lower_bound (M : ℕ)
    (hL : 6 ≤ N*d) (hM : 8*d*(d+1) ≤ M)
    (hsize : 4*d*(d+1)+M < N*d) :
    Real.exp (-(((2*M+1 : ℕ) : ℝ) * Real.log ((N*d : ℕ)+1))) ≤
      (pairingLaw (Stub N d)).real {p | SimpleConfiguration p} := by
  let L : ℝ := N*d
  have hLr : (1 : ℝ) ≤ L := by dsimp [L]; exact_mod_cast (show 1 ≤ N*d by omega)
  have hbase : Real.log (1+L^2) ≤ 2*Real.log (L+1) := by
    have hp : (0 : ℝ) < 1+L^2 := by positivity
    have hh : 1+L^2 ≤ (L+1)^2 := by nlinarith
    have h := Real.log_le_log hp hh
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have htwo : Real.log 2 ≤ Real.log (L+1) := Real.log_le_log (by norm_num) (by linarith)
  have hcost : Real.log 2 + (M : ℝ)*Real.log (1+L^2) ≤ (2*(M : ℝ)+1)*Real.log (L+1) := by
    nlinarith [mul_le_mul_of_nonneg_left hbase (show (0 : ℝ) ≤ M by positivity)]
  have hex : Real.exp (-(Real.log 2 + (M : ℝ)*Real.log (1+L^2))) =
      (1 : ℝ)/(2*(1+(N*d)^2)^M) := by
    rw [Real.exp_neg,Real.exp_add,Real.exp_nat_mul,Real.exp_log (by norm_num),Real.exp_log (by positivity)]
    dsimp [L]
    push_cast
    ring
  apply le_trans _ (polynomial_simplicity_probability_lower_bound M hL hM hsize)
  rw [← hex]
  apply Real.exp_le_exp.mpr
  dsimp [L] at hcost
  push_cast at hcost ⊢
  linarith

end GeneralizedBulk.Graph.Configuration
