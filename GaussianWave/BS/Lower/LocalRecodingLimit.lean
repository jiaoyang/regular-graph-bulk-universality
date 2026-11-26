import GaussianWave.BS.Lower.LocalRecodingEntropy
import GaussianWave.BS.Lower.RecoloringLimit

/-! Vanishing finite-radius recoding errors and the entropy lower bound for
actual limiting finite recoded profiles. The graph-to-tree code comparison
is a separate combinatorial sampling statement. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
set_option maxHeartbeats 1000000
namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite
open GaussianWave.BS.Reused.Graph GaussianWave.BS.Reused.Graph.Configuration
open GaussianWave.BS.Reused.Graph.ColorProfiles

def localRecodingError (d Q R M : ℕ) (C n : ℝ) : ℝ :=
  ((d : ℝ)/2)*(3+Real.log (Q*Q : ℕ))*
    Real.sqrt (((Q*Q : ℕ) : ℝ)/2*Real.sqrt ((regularBallBound d (2*(R+1)) : ℝ)/n))+
  ((Q : ℝ)^2/2+2)*(C/n+Real.log ((d : ℝ)*n+1)/n)+
  3*(Q^(d+1) : ℕ)*(Real.log (n+1)/n)+
  Real.sqrt (1/n)+((2*M+1 : ℕ) : ℝ)*(Real.log ((d : ℝ)*n+1)/n)

theorem localRecodingError_tendsto (d Q R M : ℕ) (hd : 0 < d) (C : ℝ) :
    Tendsto (localRecodingError d Q R M C) atTop (𝓝 0) := by
  have hV : Tendsto (fun n : ℝ => (regularBallBound d (2*(R+1)) : ℝ)/n) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop _
  have hA := ((hV.sqrt.const_mul (((Q*Q : ℕ) : ℝ)/2)).sqrt).const_mul
    (((d : ℝ)/2)*(3+Real.log (Q*Q : ℕ)))
  have hlogd := log_affine_div_tendsto (d : ℝ) (by exact_mod_cast hd)
  have hlog1 := log_affine_div_tendsto 1 (by norm_num)
  have hC : Tendsto (fun n : ℝ => C/n) atTop (𝓝 0) := tendsto_id.const_div_atTop C
  have hB := (hC.add hlogd).const_mul ((Q : ℝ)^2/2+2)
  have hD := hlog1.const_mul (3*((Q^(d+1) : ℕ) : ℝ))
  have hE := (tendsto_id.const_div_atTop (1 : ℝ)).sqrt
  have hF := hlogd.const_mul ((2*M+1 : ℕ) : ℝ)
  simpa only [localRecodingError,one_mul,add_zero,mul_zero,Real.sqrt_zero] using
    (((hA.add hB).add hD).add hE).add hF

theorem normalized_local_recoding_entropy_bound {N d q Q m : ℕ} (G : RegularGraph N d)
    (hN : 0 < N) (hd : 0 < d) (hq : 0 < q) (hQ : 0 < Q) (hNd : N*d=2*m)
    (R : ℕ) (recode : (Fin N → Fin q) → (Fin N → Fin Q)) (hlocal : IsGraphLocal G R recode)
    (decode : Fin Q → Fin q) (hdecode : ∀ c v,decode (recode c v)=c v)
    (C : ℝ) (M : ℕ) (hG : GraphProfileGood (q := Q) (m := m) C (Real.sqrt (N : ℝ)) M G)
    (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b=1) :
    (N : ℝ)⁻¹*(∑ v,entropy (p v)) ≤
      entropy (meanProfile (independentColoringLaw p hp hs) (fun c => graphStarProfile G (recode c)))-
      ((d : ℝ)/2)*entropy (meanProfile (independentColoringLaw p hp hs) (fun c => graphEdgeProfile G (recode c)))+
      localRecodingError d Q R M C (N : ℝ) := by
  have h := local_recoding_entropy_bound G hN hd hq hQ hNd R recode hlocal decode hdecode
    C (Real.sqrt (N : ℝ)) M hG p hp hs
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hNdR : (N : ℝ)*d=2*(m : ℝ) := by exact_mod_cast hNd
  have hm : (m : ℝ)=(N : ℝ)*d/2 := by linarith
  have hlog : 2*(m : ℝ)+1=(d : ℝ)*(N : ℝ)+1 := by nlinarith
  have hscale := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Nat.cast_nonneg N))
  apply hscale.trans_eq
  have hsqrtrat : Real.sqrt (1/(N : ℝ))=Real.sqrt (N : ℝ)/(N : ℝ) := by
    rw [one_div,Real.sqrt_inv,Real.sqrt_div_self]
  have hlog2 : Real.log ((N : ℝ)*d+1)=Real.log ((d : ℝ)*N+1) := by congr 1; ring
  unfold localRecodingError paletteLog simplicityCost
  push_cast
  rw [hlog,hm,hsqrtrat,hlog2]
  field_simp only [hn]
  ring

theorem mean_recoded_edgeProfile_eq_star_marginal {N d q Q : ℕ} (G : RegularGraph N d)
    (P : Measure (Fin N → Fin q)) [IsProbabilityMeasure P]
    (recode : (Fin N → Fin q) → (Fin N → Fin Q)) :
    meanProfile P (fun c => graphEdgeProfile G (recode c))=
      edgeMassOfStar (meanProfile P (fun c => graphStarProfile G (recode c))) := by
  funext ab
  unfold meanProfile graphEdgeProfile edgeMassOfStar
  rw [integral_const_mul,integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_mul_const]

/-- Actual finite-radius recoding laws inherit the common-event entropy
bound at every coordinatewise finite-profile limit. -/
theorem local_recoding_entropy_lower_of_profile_limits {d q Q : ℕ}
    (hd : 0 < d) (hq : 0 < q) (hQ : 0 < Q) (N m : ℕ → ℕ)
    (hN : ∀ n,0 < N n) (hNinf : Tendsto N atTop atTop) (hNd : ∀ n,N n*d=2*m n)
    (G : ∀ n,RegularGraph (N n) d) (R : ℕ)
    (recode : ∀ n,(Fin (N n) → Fin q) → (Fin (N n) → Fin Q))
    (hlocal : ∀ n,IsGraphLocal (G n) R (recode n))
    (decode : Fin Q → Fin q) (hdecode : ∀ n c v,decode (recode n c v)=c v)
    (p : ∀ n,Fin (N n) → Fin q → ℝ)
    (hp : ∀ n v b,0 ≤ p n v b) (hs : ∀ n v,∑ b,p n v b=1)
    (C : ℝ) (M : ℕ)
    (hG : ∀ᶠ n in atTop,GraphProfileGood (q := Q) (m := m n) C (Real.sqrt (N n : ℝ)) M (G n))
    (s : StarWord d Q → ℝ) (h : ℝ)
    (hS : ∀ w,Tendsto (fun n => meanProfile (independentColoringLaw (p n) (hp n) (hs n))
      (fun c => graphStarProfile (G n) (recode n c)) w) atTop (𝓝 (s w)))
    (hH : Tendsto (fun n => (N n : ℝ)⁻¹*(∑ v,entropy (p n v))) atTop (𝓝 h)) :
    h ≤ entropy s-((d : ℝ)/2)*entropy (edgeMassOfStar s) := by
  let P n := independentColoringLaw (p n) (hp n) (hs n)
  let S n := meanProfile (P n) (fun c => graphStarProfile (G n) (recode n c))
  let E n := meanProfile (P n) (fun c => graphEdgeProfile (G n) (recode n c))
  have hE : ∀ ab,Tendsto (fun n => E n ab) atTop (𝓝 (edgeMassOfStar s ab)) := by
    intro ab
    have hh := edgeMassOfStar_tendsto S s hS ab
    simpa only [E,mean_recoded_edgeProfile_eq_star_marginal] using hh
  have hHS := continuous_finite_entropy.tendsto s |>.comp (tendsto_pi_nhds.mpr hS)
  have hHE := continuous_finite_entropy.tendsto (edgeMassOfStar s) |>.comp (tendsto_pi_nhds.mpr hE)
  have herr := (localRecodingError_tendsto d Q R M hd C).comp (tendsto_natCast_atTop_atTop.comp hNinf)
  have hright := (hHS.sub (hHE.const_mul ((d : ℝ)/2))).add herr
  have hle : ∀ᶠ n in atTop,(N n : ℝ)⁻¹*(∑ v,entropy (p n v)) ≤
      entropy (S n)-((d : ℝ)/2)*entropy (E n)+localRecodingError d Q R M C (N n : ℝ) := by
    filter_upwards [hG] with n hn
    exact normalized_local_recoding_entropy_bound (G n) (hN n) hd hq hQ (hNd n) R (recode n)
      (hlocal n) decode (hdecode n) C M hn (p n) (hp n) (hs n)
  simpa only [add_zero] using le_of_tendsto_of_tendsto hH hright hle

end GaussianWave.BS.Lower
