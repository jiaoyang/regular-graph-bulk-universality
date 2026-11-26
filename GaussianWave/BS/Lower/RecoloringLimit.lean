import GaussianWave.BS.Lower.EdgeRecoloringConcentration
import GaussianWave.BS.Lower.MarkedStarRecoloring

/-! Vanishing counting/concentration errors and the k=0 randomized entropy
lower bound obtained from actual weak limits of marked finite graph stars. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
set_option maxHeartbeats 1000000

namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite
open GaussianWave.BS.Reused.Graph GaussianWave.BS.Reused.Graph.Configuration
open GaussianWave.BS.Reused.Graph.ColorProfiles

/-- The divided finite-graph error for the common event with slack `sqrt N`.
All terms tend to zero for a fixed palette and degree. -/
def recoloringError (d q M : ℕ) (C n : ℝ) : ℝ :=
  ((d : ℝ)/2)*(3+Real.log (q*q : ℕ))*
    Real.sqrt (((q*q : ℕ) : ℝ)/2*Real.sqrt ((4+2*(d : ℝ))/n))+
  ((q : ℝ)^2/2+2)*(C/n+Real.log ((d : ℝ)*n+1)/n)+
  3*(q^(d+1) : ℕ)*(Real.log (n+1)/n)+
  Real.sqrt (1/n)+((2*M+1 : ℕ) : ℝ)*(Real.log ((d : ℝ)*n+1)/n)

theorem log_affine_div_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℝ => Real.log (a*n+1)/n) atTop (𝓝 0) := by
  have hlarge : Tendsto (fun n : ℝ => a*n+1) atTop atTop := by
    apply tendsto_atTop_mono (fun n : ℝ => by linarith : ∀ n : ℝ,a*n ≤ a*n+1)
    exact tendsto_id.const_mul_atTop ha
  have h := (Real.tendsto_pow_log_div_mul_add_atTop (1/a) (-(1/a)) 1
    (one_div_ne_zero (ne_of_gt ha))).comp hlarge
  have he (n : ℝ) : (1/a)*(a*n+1)+(-(1/a)) = n := by
    field_simp
  change Tendsto (fun n : ℝ => Real.log (a*n+1)^1 / ((1/a)*(a*n+1)+(-(1/a)))) atTop (𝓝 0) at h
  simpa only [pow_one,he] using h

theorem recoloringError_tendsto (d q M : ℕ) (hd : 0 < d) (C : ℝ) :
    Tendsto (recoloringError d q M C) atTop (𝓝 0) := by
  have hV : Tendsto (fun n : ℝ => (4+2*(d : ℝ))/n) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop _
  have hA := ((hV.sqrt.const_mul (((q*q : ℕ) : ℝ)/2)).sqrt).const_mul
    (((d : ℝ)/2)*(3+Real.log (q*q : ℕ)))
  have hlogd := log_affine_div_tendsto (d : ℝ) (by exact_mod_cast hd)
  have hlog1 := log_affine_div_tendsto 1 (by norm_num)
  have hC : Tendsto (fun n : ℝ => C/n) atTop (𝓝 0) := tendsto_id.const_div_atTop C
  have hB := (hC.add hlogd).const_mul ((q : ℝ)^2/2+2)
  have hD := hlog1.const_mul (3*((q^(d+1) : ℕ) : ℝ))
  have hE := (tendsto_id.const_div_atTop (1 : ℝ)).sqrt
  have hF := hlogd.const_mul ((2*M+1 : ℕ) : ℝ)
  simpa only [recoloringError,one_mul,add_zero,mul_zero,Real.sqrt_zero] using
    (((hA.add hB).add hD).add hE).add hF

/-- The finite common-event estimate divided by the number of vertices. -/
theorem normalized_recoloring_entropy_bound {N d q m : ℕ} (G : RegularGraph N d)
    (hN : 0 < N) (hd : 0 < d) (hNd : N*d = 2*m) (hq : 0 < q) (C : ℝ) (M : ℕ)
    (hG : GraphProfileGood (q := q) (m := m) C (Real.sqrt (N : ℝ)) M G)
    (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b = 1) :
    (N : ℝ)⁻¹*(∑ v,entropy (p v)) ≤
      entropy (meanProfile (independentColoringLaw p hp hs) (graphStarProfile G))-
        ((d : ℝ)/2)*entropy (meanProfile (independentColoringLaw p hp hs) (graphEdgeProfile G))+
        recoloringError d q M C (N : ℝ) := by
  have h := independent_recoloring_entropy_bound G hN hd hNd hq C (Real.sqrt (N : ℝ)) M hG p hp hs
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hNdR : (N : ℝ)*d = 2*(m : ℝ) := by exact_mod_cast hNd
  have hm : (m : ℝ) = (N : ℝ)*d/2 := by linarith
  have hlog : 2*(m : ℝ)+1 = (d : ℝ)*(N : ℝ)+1 := by nlinarith
  have hscale := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Nat.cast_nonneg N))
  apply hscale.trans_eq
  have hsqrtrat : Real.sqrt (1/(N : ℝ)) = Real.sqrt (N : ℝ)/(N : ℝ) := by
    rw [one_div,Real.sqrt_inv,Real.sqrt_div_self]
  have hlog2 : Real.log ((N : ℝ)*d+1) = Real.log ((d : ℝ)*N+1) := by congr 1; ring
  unfold recoloringError paletteLog simplicityCost
  push_cast
  rw [hlog,hm,hsqrtrat,hlog2]
  field_simp only [hn]
  ring

/-- Expected edge profiles are the explicit linear directed-edge marginal
of the expected symmetrized star profile. -/
theorem mean_edgeProfile_eq_star_marginal {N d q : ℕ} (G : RegularGraph N d)
    (P : Measure (VertexColoring N q)) [IsProbabilityMeasure P] :
    meanProfile P (graphEdgeProfile G) = edgeMassOfStar (meanProfile P (graphStarProfile G)) := by
  funext ab
  unfold meanProfile graphEdgeProfile edgeMassOfStar
  rw [integral_const_mul,integral_finset_sum _ (fun s _ => Integrable.of_finite)]
  simp_rw [integral_mul_const]

/-- Finite-alphabet Shannon entropy is continuous, including boundary masses
that equal zero. -/
theorem continuous_finite_entropy {A : Type*} [Fintype A] :
    Continuous (fun P : A → ℝ => entropy P) := by
  unfold entropy
  exact continuous_finset_sum _ (fun a _ => Real.continuous_negMulLog.comp (continuous_apply a))

theorem edgeMassOfStar_tendsto {d q : ℕ} (S : ℕ → StarWord d q → ℝ) (s : StarWord d q → ℝ)
    (hS : ∀ w,Tendsto (fun n => S n w) atTop (𝓝 (s w))) (ab : Fin q × Fin q) :
    Tendsto (fun n => edgeMassOfStar (S n) ab) atTop (𝓝 (edgeMassOfStar s ab)) := by
  unfold edgeMassOfStar
  exact (tendsto_finset_sum _ (fun w _ => (hS w).mul_const ((wordPortCount w ab.1 ab.2 : ℕ) : ℝ))).const_mul _

/-- The actual common graph-counting estimate passes to every continuous
randomized finite recoloring of a weak marked-star limit. This is randomized
L1 at radius zero, with its conditional-entropy term retained. -/
theorem randomized_star_entropy_lower_of_graph_limit {d q r : ℕ}
    (hd : 0 < d) (hq : 0 < q) (N m : ℕ → ℕ) (hN : ∀ n,0 < N n)
    (hNinf : Tendsto N atTop atTop) (hNd : ∀ n,N n*d = 2*m n)
    (G : ∀ n,RegularGraph (N n) d) (x : ∀ n,Fin (N n) → Fin r → ℝ)
    (C : ℝ) (M : ℕ)
    (hG : ∀ᶠ n in atTop,GraphProfileGood (q := q) (m := m n) C (Real.sqrt (N n : ℝ)) M (G n))
    (μ : Measure ((Fin r × Fin (d+1)) → ℝ))
    (hweak : WeakLawConverges (fun n => markedStarLaw (G n) (x n)) μ)
    (φ : (Fin r → ℝ) → Fin q → ℝ)
    (hφ0 : ∀ y b,0 ≤ φ y b) (hφ1 : ∀ y,∑ b,φ y b = 1)
    (hφc : ∀ b,Continuous (fun y => φ y b)) :
    (∫ y,rootEntropyTest φ y ∂μ) ≤
      entropy (starRecolorMass μ φ)-((d : ℝ)/2)*entropy (edgeMassOfStar (starRecolorMass μ φ)) := by
  let P (n : ℕ) := independentColoringLaw (fun v => φ (x n v))
    (fun v => hφ0 (x n v)) (fun v => hφ1 (x n v))
  let S (n : ℕ) := meanProfile (P n) (graphStarProfile (G n))
  let E (n : ℕ) := meanProfile (P n) (graphEdgeProfile (G n))
  have hS : ∀ w,Tendsto (fun n => S n w) atTop (𝓝 (starRecolorMass μ φ w)) :=
    fun w => weak_markedStar_recolorMass G x μ hweak φ hφ0 hφ1 hφc w
  have hE : ∀ ab,Tendsto (fun n => E n ab) atTop (𝓝 (edgeMassOfStar (starRecolorMass μ φ) ab)) := by
    intro ab
    have h := edgeMassOfStar_tendsto S (starRecolorMass μ φ) hS ab
    simpa only [E,mean_edgeProfile_eq_star_marginal] using h
  have hHS := continuous_finite_entropy.tendsto (starRecolorMass μ φ) |>.comp (tendsto_pi_nhds.mpr hS)
  have hHE := continuous_finite_entropy.tendsto (edgeMassOfStar (starRecolorMass μ φ)) |>.comp
    (tendsto_pi_nhds.mpr hE)
  have herr := (recoloringError_tendsto d q M hd C).comp (tendsto_natCast_atTop_atTop.comp hNinf)
  have hright := (hHS.sub (hHE.const_mul ((d : ℝ)/2))).add herr
  have hleft := weak_markedStar_rootEntropy G hN x μ hweak φ hφ0 hφ1 hφc
  have hle : ∀ᶠ n in atTop,(N n : ℝ)⁻¹*(∑ v,entropy (φ (x n v))) ≤
      entropy (S n)-((d : ℝ)/2)*entropy (E n)+recoloringError d q M C (N n : ℝ) := by
    filter_upwards [hG] with n hn
    exact normalized_recoloring_entropy_bound (G n) (hN n) hd (hNd n) hq C M hn
      (fun v => φ (x n v)) (fun v => hφ0 (x n v)) (fun v => hφ1 (x n v))
  have h := le_of_tendsto_of_tendsto hleft hright hle
  simpa only [add_zero] using h

end GaussianWave.BS.Lower
