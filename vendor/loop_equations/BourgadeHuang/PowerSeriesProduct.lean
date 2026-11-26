import BourgadeHuang.IntegralPowerSeries
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! A concrete Cauchy product of multivariate multilinear power series, with
uniform geometric coefficient bounds. -/
noncomputable section
open scoped Topology BigOperators NNReal ENNReal
open MeasureTheory
namespace BourgadeHuang
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def multilinearTensorProduct {m n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin m => E) ℂ)
    (q : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) ℂ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (m+n) => E) ℂ :=
  (((ContinuousLinearMap.toSpanSingleton ℂ q).compContinuousMultilinearMap p).uncurrySum).domDomCongr
    finSumFinEquiv

theorem multilinearTensorProduct_apply_const {m n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin m => E) ℂ)
    (q : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) ℂ) (y : E) :
    multilinearTensorProduct p q (fun _ => y) = p (fun _ => y)*q (fun _ => y) := rfl

theorem multilinearTensorProduct_apply {m n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin m => E) ℂ)
    (q : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) ℂ) (v : Fin (m+n) → E) :
    multilinearTensorProduct p q v =
      p (fun i => v (Fin.castAdd n i))*q (fun j => v (Fin.natAdd m j)) := rfl

theorem norm_multilinearTensorProduct_le {m n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin m => E) ℂ)
    (q : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) ℂ) :
    ‖multilinearTensorProduct p q‖ ≤ ‖p‖*‖q‖ := by
  rw [multilinearTensorProduct, ContinuousMultilinearMap.norm_domDomCongr]
  change ‖(ContinuousMultilinearMap.currySumEquiv ℂ (Fin m) (Fin n) E ℂ).symm
    ((ContinuousLinearMap.toSpanSingleton ℂ q).compContinuousMultilinearMap p)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  simpa [ContinuousLinearMap.norm_toSpanSingleton, mul_comm] using
    (ContinuousLinearMap.toSpanSingleton ℂ q).norm_compContinuousMultilinearMap_le p

theorem continuous_multilinearTensorProduct (m n : ℕ) :
    Continuous (fun t : (ContinuousMultilinearMap ℂ (fun _ : Fin m => E) ℂ) ×
      (ContinuousMultilinearMap ℂ (fun _ : Fin n => E) ℂ) => multilinearTensorProduct t.1 t.2) := by
  apply IsBoundedBilinearMap.continuous (𝕜 := ℂ)
  refine ⟨?_,?_,?_,?_,1,by norm_num,?_⟩
  · intro p p' q
    ext v
    simp [multilinearTensorProduct_apply, add_mul]
  · intro c p q
    ext v
    simp [multilinearTensorProduct_apply, smul_eq_mul, mul_assoc]
  · intro p q q'
    ext v
    simp [multilinearTensorProduct_apply, mul_add]
  · intro c p q
    ext v
    simp [multilinearTensorProduct_apply, smul_eq_mul, mul_left_comm]
  · intro p q
    simpa using norm_multilinearTensorProduct_le p q

def powerSeriesProductTerm (p q : FormalMultilinearSeries ℂ E ℂ)
    (n : ℕ) (i : Fin (n+1)) : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) ℂ :=
  (multilinearTensorProduct (p i) (q (n-i))).domDomCongr
    (finCongr (Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)))

def powerSeriesProduct (p q : FormalMultilinearSeries ℂ E ℂ) :
    FormalMultilinearSeries ℂ E ℂ := fun n => ∑ i : Fin (n+1), powerSeriesProductTerm p q n i

theorem continuous_powerSeriesProductTerm (n : ℕ) (i : Fin (n+1)) :
    Continuous (fun t : (ContinuousMultilinearMap ℂ (fun _ : Fin i => E) ℂ) ×
      (ContinuousMultilinearMap ℂ (fun _ : Fin (n-i) => E) ℂ) =>
      (multilinearTensorProduct t.1 t.2).domDomCongr
        (finCongr (Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)))) :=
  (ContinuousMultilinearMap.domDomCongrₗᵢ ℂ E ℂ
    (finCongr (Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)))).continuous.comp
      (continuous_multilinearTensorProduct i (n-i))

theorem stronglyMeasurable_powerSeriesProduct {Ω : Type*} [MeasurableSpace Ω]
    (p q : Ω → FormalMultilinearSeries ℂ E ℂ)
    (hp : ∀ n, StronglyMeasurable (fun ω => p ω n))
    (hq : ∀ n, StronglyMeasurable (fun ω => q ω n)) (n : ℕ) :
    StronglyMeasurable (fun ω => powerSeriesProduct (p ω) (q ω) n) := by
  have ht (i : Fin (n+1)) :
      StronglyMeasurable (fun ω => powerSeriesProductTerm (p ω) (q ω) n i) := by
    let T : (ContinuousMultilinearMap ℂ (fun _ : Fin i => E) ℂ) ×
        (ContinuousMultilinearMap ℂ (fun _ : Fin (n-i) => E) ℂ) →
        ContinuousMultilinearMap ℂ (fun _ : Fin n => E) ℂ :=
      fun t => (multilinearTensorProduct t.1 t.2).domDomCongr
        (finCongr (Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)))
    have hT : Continuous T := continuous_powerSeriesProductTerm (E := E) n i
    have hpq : StronglyMeasurable (fun ω => (p ω i,q ω (n-i))) :=
      (hp i).prodMk (hq (n-i))
    change StronglyMeasurable (T ∘ (fun ω => (p ω i,q ω (n-i))))
    exact hT.comp_stronglyMeasurable hpq
  exact Finset.stronglyMeasurable_sum Finset.univ (fun i _ => ht i)

theorem powerSeriesProduct_apply_const (p q : FormalMultilinearSeries ℂ E ℂ)
    (n : ℕ) (y : E) :
    powerSeriesProduct p q n (fun _ => y) =
      ∑ i ∈ Finset.range (n+1), p i (fun _ => y)*q (n-i) (fun _ => y) := by
  simp only [powerSeriesProduct, ContinuousMultilinearMap.sum_apply, powerSeriesProductTerm,
    ContinuousMultilinearMap.domDomCongr_apply, Function.comp_def,
    multilinearTensorProduct_apply_const]
  exact Fin.sum_univ_eq_sum_range (fun i => p i (fun _ => y)*q (n-i) (fun _ => y)) (n+1)

theorem norm_powerSeriesProduct_le (p q : FormalMultilinearSeries ℂ E ℂ)
    {r C D : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hp : ∀ n, ‖p n‖ ≤ C/r^n) (hq : ∀ n, ‖q n‖ ≤ D/r^n) (n : ℕ) :
    ‖powerSeriesProduct p q n‖ ≤ C*D/(r/2)^n := by
  have htwo : (n+1 : ℝ) ≤ (2 : ℝ)^n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      push_cast
      linarith
  have ht (i : Fin (n+1)) : ‖powerSeriesProductTerm p q n i‖ ≤ C*D/r^n := by
    rw [powerSeriesProductTerm, ContinuousMultilinearMap.norm_domDomCongr]
    apply (norm_multilinearTensorProduct_le _ _).trans
    apply (mul_le_mul (hp i) (hq (n-i)) (norm_nonneg _) (by positivity)).trans_eq
    rw [div_mul_div_comm, ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]
  calc
    _ ≤ ∑ i : Fin (n+1), ‖powerSeriesProductTerm p q n i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (n+1), C*D/r^n := Finset.sum_le_sum (fun i _ => ht i)
    _ = (n+1 : ℝ)*(C*D/r^n) := by simp
    _ ≤ 2^n*(C*D/r^n) := mul_le_mul_of_nonneg_right htwo (by positivity)
    _ = _ := by rw [div_pow]; field_simp; ring

/-- The concrete coefficient convolution represents the actual product on
a common ball; its radius is independent of the coefficient constants. -/
theorem hasFPowerSeriesOnBall_product
    {f g : E → ℂ} {p q : FormalMultilinearSeries ℂ E ℂ} {x : E}
    {r : ℝ≥0} (hr : 0 < r)
    (hf : HasFPowerSeriesOnBall f p x r) (hg : HasFPowerSeriesOnBall g q x r)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hp : ∀ n, ‖p n‖ ≤ C/(r : ℝ)^n) (hq : ∀ n, ‖q n‖ ≤ D/(r : ℝ)^n) :
    HasFPowerSeriesOnBall (fun z => f z*g z) (powerSeriesProduct p q) x (r/2 : ℝ≥0) := by
  have hr' : (0 : ℝ) < r := hr
  have hr2 : (0 : ℝ) < (r : ℝ)/2 := by positivity
  refine ⟨?_, by positivity, ?_⟩
  · apply FormalMultilinearSeries.le_radius_of_bound _ (C*D)
    intro n
    have hb := norm_powerSeriesProduct_le p q hr' hC hD hp hq n
    have hh := mul_le_mul_of_nonneg_right hb (pow_nonneg hr2.le n)
    simpa only [NNReal.coe_div, NNReal.coe_ofNat,
      div_mul_cancel₀ _ (pow_ne_zero n hr2.ne')] using hh
  · intro y hy
    have hy' : y ∈ EMetric.ball (0 : E) (r : ℝ≥0∞) := by
      apply EMetric.ball_subset_ball _ hy
      exact_mod_cast (div_le_self (zero_le r) (by norm_num : (1 : ℝ≥0) ≤ 2))
    have hpy := p.summable_norm_apply (EMetric.ball_subset_ball hf.r_le hy')
    have hqy := q.summable_norm_apply (EMetric.ball_subset_ball hg.r_le hy')
    have hs := hasSum_sum_range_mul_of_summable_norm hpy hqy
    simp only [(hf.hasSum hy').tsum_eq, (hg.hasSum hy').tsum_eq] at hs
    simpa only [powerSeriesProduct_apply_const] using hs

end BourgadeHuang
