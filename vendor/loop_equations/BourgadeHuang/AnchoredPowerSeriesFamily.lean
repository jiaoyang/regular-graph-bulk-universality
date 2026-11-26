import BourgadeHuang.PowerSeriesProduct
import BourgadeHuang.PowerSeriesPullback
import BourgadeHuang.ExponentialLoop

/-! Uniform analytic families of anchored observables. Their coefficients have
an exponential anchor bound, so a positive exponential-square moment permits
termwise integration on an actual common multivariate ball. -/
noncomputable section
open scoped Topology BigOperators NNReal ENNReal
open MeasureTheory
namespace BourgadeHuang
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

def HasAnchoredPowerSeries (f : AnchoredCountingState → E → ℂ) (x : E) : Prop :=
  ∃ r : ℝ≥0, 0 < r ∧ ∃ p : AnchoredCountingState → FormalMultilinearSeries ℂ E ℂ,
    ∃ L : ℝ, 0 ≤ L ∧
      (∀ n, StronglyMeasurable (fun s => p s n)) ∧
      (∀ s, HasFPowerSeriesOnBall (f s) (p s) x r) ∧
      ∀ s n, ‖p s n‖ ≤ Real.exp (L*‖s.val.2‖)/(r:ℝ)^n

theorem HasAnchoredPowerSeries.one (x : E) :
    HasAnchoredPowerSeries (fun _ _ => 1) x := by
  refine ⟨1, by norm_num, fun _ => constFormalMultilinearSeries ℂ E (1:ℂ),
    0, le_rfl, fun _ => stronglyMeasurable_const, fun _ => ?_, ?_⟩
  · exact hasFPowerSeriesOnBall_const.mono (by norm_num) le_top
  · intro s n
    cases n with
    | zero => simp [constFormalMultilinearSeries]
    | succ n => simp

theorem HasAnchoredPowerSeries.mul {f g : AnchoredCountingState → E → ℂ} {x : E}
    (hf : HasAnchoredPowerSeries f x) (hg : HasAnchoredPowerSeries g x) :
    HasAnchoredPowerSeries (fun s z => f s z*g s z) x := by
  obtain ⟨r,hr,p,L,hL,hpm,hp,hpb⟩ := hf
  obtain ⟨t,ht,q,M,hM,hqm,hq,hqb⟩ := hg
  let u : ℝ≥0 := min r t
  have hu : 0 < u := lt_min hr ht
  have hu' : (0:ℝ) < u := hu
  have hur : (u:ℝ) ≤ r := min_le_left _ _
  have hut : (u:ℝ) ≤ t := min_le_right _ _
  have hpb' (s : AnchoredCountingState) (n : ℕ) :
      ‖p s n‖ ≤ Real.exp (L*‖s.val.2‖)/(u:ℝ)^n :=
    (hpb s n).trans (div_le_div_of_nonneg_left (Real.exp_nonneg _)
      (pow_pos hu' _) (pow_le_pow_left₀ hu'.le hur _))
  have hqb' (s : AnchoredCountingState) (n : ℕ) :
      ‖q s n‖ ≤ Real.exp (M*‖s.val.2‖)/(u:ℝ)^n :=
    (hqb s n).trans (div_le_div_of_nonneg_left (Real.exp_nonneg _)
      (pow_pos hu' _) (pow_le_pow_left₀ hu'.le hut _))
  refine ⟨u/2, by positivity, fun s => powerSeriesProduct (p s) (q s),
    L+M, add_nonneg hL hM, stronglyMeasurable_powerSeriesProduct p q hpm hqm,
    fun s => ?_, fun s n => ?_⟩
  · exact hasFPowerSeriesOnBall_product hu
      ((hp s).mono (by exact_mod_cast hu) (by exact_mod_cast min_le_left r t))
      ((hq s).mono (by exact_mod_cast hu) (by exact_mod_cast min_le_right r t))
      (Real.exp_nonneg _) (Real.exp_nonneg _) (hpb' s) (hqb' s)
  · simpa only [NNReal.coe_div, NNReal.coe_ofNat, add_mul, Real.exp_add] using
      norm_powerSeriesProduct_le (p s) (q s) hu' (Real.exp_nonneg _)
        (Real.exp_nonneg _) (hpb' s) (hqb' s) n

theorem HasAnchoredPowerSeries.finset_prod {ι : Type*} (I : Finset ι)
    (f : ι → AnchoredCountingState → E → ℂ) (x : E)
    (hf : ∀ i ∈ I, HasAnchoredPowerSeries (f i) x) :
    HasAnchoredPowerSeries (fun s z => ∏ i ∈ I, f i s z) x := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using HasAnchoredPowerSeries.one x
  | @insert i I hi ih =>
    simpa only [Finset.prod_insert hi] using
      (hf i (Finset.mem_insert_self _ _)).mul
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem HasAnchoredPowerSeries.pullback {f : AnchoredCountingState → F → ℂ}
    (L : E →L[ℂ] F) (hL : ‖L‖ ≤ 1) (x : E)
    (hf : HasAnchoredPowerSeries f (L x)) :
    HasAnchoredPowerSeries (fun s z => f s (L z)) x := by
  obtain ⟨r,hr,p,M,hM,hpm,hp,hpb⟩ := hf
  exact ⟨r,hr,fun s => (p s).compContinuousLinearMap L,M,hM,
    fun n => stronglyMeasurable_powerSeries_pullback p L n (hpm n),
    fun s => hasFPowerSeriesOnBall_pullback L hL x r (hp s),
    fun s n => norm_powerSeries_pullback_le_div_pow (p s) L hL _ _ (hpb s) n⟩

theorem HasAnchoredPowerSeries.analyticAt_integral
    {f : AnchoredCountingState → E → ℂ} {x : E}
    (hf : HasAnchoredPowerSeries f x) (ν : Measure AnchoredCountingState)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν) :
    AnalyticAt ℂ (fun z => ∫ s, f s z ∂ν) x := by
  obtain ⟨r,hr,p,L,_,hpm,hp,hpb⟩ := hf
  have hi : Integrable (fun s : AnchoredCountingState => Real.exp (L*‖s.val.2‖)) ν := by
    simpa using integrable_anchor_polynomial_exp ν ha he (by norm_num : (0:ℝ)≤1) 0 L
  have hic (n : ℕ) : Integrable (fun s => p s n) ν :=
    (hi.div_const _).mono' (hpm n).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun s => hpb s n))
  exact analyticAt_integral_of_powerSeries f p x r hr hp hic _ hi
    (fun _ => Real.exp_nonneg _) hpb

end BourgadeHuang
