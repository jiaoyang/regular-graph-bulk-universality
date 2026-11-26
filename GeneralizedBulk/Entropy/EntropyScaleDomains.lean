import GeneralizedBulk.Entropy.LocalEntropyRates
import GeneralizedBulk.Entropy.ConstructedQuarticEstimate

/-! The actual covariance-comparison and ninth-root Taylor domains hold at
every sufficiently large graph size. No domain restriction is a new input. -/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace GeneralizedBulk.Entropy.ChannelRates
open GeneralizedBulk.Entropy.Channel GeneralizedBulk.Entropy.Mehler

theorem eventually_local_covariance_small (C m κ localExponent height : ℝ)
    (hl : 0 < localExponent) (hh : 0 < height) (hκ : 0 < κ) :
    ∀ᶠ N : ℕ in atTop,
      C*((N : ℝ)^(-localExponent)+Real.sqrt ((N : ℝ)^(-height))) ≤ 1 ∧
      (m^2/κ)*(C*((N : ℝ)^(-localExponent)+Real.sqrt ((N : ℝ)^(-height)))) ≤ 1/2 := by
  have hl0 : Tendsto (fun N : ℕ => (N : ℝ)^(-localExponent)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hl).comp tendsto_natCast_atTop_atTop
  have hh0 : Tendsto (fun N : ℕ => (N : ℝ)^(-height)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hh).comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun N : ℕ => C*((N : ℝ)^(-localExponent)+Real.sqrt ((N : ℝ)^(-height)))) atTop (nhds 0) := by
    simpa using (hl0.add hh0.sqrt).const_mul C
  have ht2 : Tendsto (fun N : ℕ => (m^2/κ)*(C*((N : ℝ)^(-localExponent)+Real.sqrt ((N : ℝ)^(-height))))) atTop (nhds 0) := by
    simpa using ht.const_mul (m^2/κ)
  exact (ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).and
    (ht2.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2))) |>.mono (fun N h => ⟨h.1.le,h.2.le⟩)

theorem starTaylorCoefficient_lower (d k : ℕ) (hd : 2 ≤ d) (B : ℝ) :
    NormalizedFiniteSignal.observationRemainderConstant (coloredObserved d k hd) ≤
      starTaylorCoefficient d k hd B := by
  have hpow : (1 : ℝ) ≤ (1+(((Fintype.card (ScalarCoordinate d k) : ℝ)+1)*B)^2)^9 := by
    exact one_le_pow₀ (by nlinarith [sq_nonneg (((Fintype.card (ScalarCoordinate d k) : ℝ)+1)*B)])
  unfold starTaylorCoefficient
  exact le_mul_of_one_le_right (NormalizedFiniteSignal.observationRemainderConstant_pos _).le hpow

set_option maxHeartbeats 1500000 in
theorem ninthRootScale_bigO (A : ℕ → ℝ) (A₀ γ : ℝ) (hA₀ : 0 < A₀)
    (hA : ∀ᶠ N in atTop,A₀ ≤ A N) :
    (fun N : ℕ => ((N : ℝ)^(-γ)/A N)^((9 : ℝ)⁻¹)) =O[atTop]
      fun N => (N : ℝ)^(-γ/9) := by
  have hi : (fun N : ℕ => (N : ℝ)^(-γ)/A N) =O[atTop] fun N => (N : ℝ)^(-γ) := by
    apply IsBigO.of_bound (A₀⁻¹)
    filter_upwards [hA] with N hN
    have hpos : 0 < A N := hA₀.trans_le hN
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _),
      abs_of_nonneg (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) hpos.le)]
    rw [div_eq_mul_inv]
    exact (mul_le_mul_of_nonneg_left (inv_anti₀ hA₀ hN) (Real.rpow_nonneg (Nat.cast_nonneg N) _)).trans_eq (mul_comm _ _)
  have hr := IsBigO.rpow (show (0 : ℝ) ≤ (9 : ℝ)⁻¹ by norm_num)
    (Eventually.of_forall (fun N : ℕ => Real.rpow_nonneg (Nat.cast_nonneg N) (-γ))) hi
  apply hr.congr_right
  intro N
  rw [← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 1

set_option maxHeartbeats 2000000 in
theorem eventually_ninthRootScale_domains (d k : ℕ) (hd : 2 ≤ d)
    (B : ℕ → ℝ) (C γ : ℝ) (q : ℕ) (hγ : 0 < γ)
    (hB : B =O[atTop] fun N => C*Real.log (N : ℝ)^q) :
    ∀ᶠ N : ℕ in atTop,
      let a := ((N : ℝ)^(-γ)/starTaylorCoefficient d k hd (B N))^((9 : ℝ)⁻¹)
      a ≤ 1/2 ∧ a*(((Fintype.card (ScalarCoordinate d k) : ℝ)+1)*B N) ≤ 1/2 := by
  have hscale := ninthRootScale_bigO (fun N => starTaylorCoefficient d k hd (B N))
    (NormalizedFiniteSignal.observationRemainderConstant (coloredObserved d k hd)) γ
    (NormalizedFiniteSignal.observationRemainderConstant_pos _)
    (Eventually.of_forall (fun N => starTaylorCoefficient_lower d k hd (B N)))
  have hB' := hB.trans (polylog_bigO_nat_rpow C q (γ/18) (by linarith))
  have hprod := nat_rpow_mul_bigO hscale (hB'.const_mul_left ((Fintype.card (ScalarCoordinate d k) : ℝ)+1))
    (show -γ/9+γ/18 ≤ -γ/18 by linarith)
  have hs := nat_rpow_bigO_eventually_le hscale (show -γ/9 < -γ/18 by linarith)
  have hp := nat_rpow_bigO_eventually_le hprod (show -γ/18 < -γ/36 by linarith)
  have hz : Tendsto (fun N : ℕ => (N : ℝ)^(-γ/36)) atTop (nhds 0) := by
    convert (tendsto_rpow_neg_atTop (show 0 < γ/36 by linarith)).comp tendsto_natCast_atTop_atTop using 1 <;> ext N <;> congr 1 <;> ring
  have hz' : ∀ᶠ N : ℕ in atTop,(N : ℝ)^(-γ/36) ≤ 1/2 :=
    (hz.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2))).mono (fun _ h => h.le)
  filter_upwards [hs,hp,hz',eventually_ge_atTop 1] with N hs hp hz hN
  have hmono : (N : ℝ)^(-γ/18) ≤ (N : ℝ)^(-γ/36) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)
  exact ⟨hs.trans (hmono.trans hz),hp.trans hz⟩

end GeneralizedBulk.Entropy.ChannelRates
