import GaussianWave.BS.Lower.LocalRecoloringConcentration
import GaussianWave.BS.Lower.ApproximateCodingEntropy

/-! The common graph-counting inequality applied to actual finite-radius
recodings of independent vertex colors. Retaining the root color preserves
the entropy lower bound, while graph-local dependence gives concentration. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
set_option maxHeartbeats 1000000

namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite
open GaussianWave.BS.Reused.Graph GaussianWave.BS.Reused.Graph.Configuration

variable {N d q Q : ℕ}

def IsGraphLocal (G : RegularGraph N d) (R : ℕ)
    (recode : (Fin N → Fin q) → (Fin N → Fin Q)) : Prop :=
  ∀ v c c',(∀ w,G.val.edist v w ≤ (R : ℕ∞) → c w=c' w) → recode c v=recode c' v

def recodedEdgeObservation (G : RegularGraph N d)
    (recode : (Fin N → Fin q) → (Fin N → Fin Q))
    (ab : Fin Q × Fin Q) (v : Fin N) (c : Fin N → Fin q) : ℝ :=
  (d : ℝ)⁻¹*∑ j : Fin d,
    if recode c v=ab.1 ∧ recode c (graphNeighbor G v j)=ab.2 then 1 else 0

theorem recodedEdgeObservation_nonneg (G : RegularGraph N d)
    (recode : (Fin N → Fin q) → (Fin N → Fin Q)) (ab : Fin Q × Fin Q)
    (v : Fin N) (c : Fin N → Fin q) : 0 ≤ recodedEdgeObservation G recode ab v c := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

theorem recodedEdgeObservation_le_one (G : RegularGraph N d) (hd : 0 < d)
    (recode : (Fin N → Fin q) → (Fin N → Fin Q)) (ab : Fin Q × Fin Q)
    (v : Fin N) (c : Fin N → Fin q) : recodedEdgeObservation G recode ab v c ≤ 1 := by
  calc
    _ ≤ (d : ℝ)⁻¹*∑ _j : Fin d,(1 : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun _ _ => by split_ifs <;> norm_num)) (by positivity)
    _ = _ := by simp [inv_mul_cancel₀ (show (d : ℝ) ≠ 0 by positivity)]

theorem recodedEdgeObservation_local (G : RegularGraph N d) (R : ℕ)
    (recode : (Fin N → Fin q) → (Fin N → Fin Q)) (hlocal : IsGraphLocal G R recode)
    (ab : Fin Q × Fin Q) :
    ∀ v c c',(∀ w,G.val.edist v w ≤ (R+1 : ℕ∞) → c w=c' w) →
      recodedEdgeObservation G recode ab v c=recodedEdgeObservation G recode ab v c' := by
  intro v c c' hc
  have hr : recode c v=recode c' v := hlocal v c c' (fun w hw => hc w (hw.trans (by norm_num)))
  have hn (j : Fin d) : recode c (graphNeighbor G v j)=recode c' (graphNeighbor G v j) := by
    apply hlocal
    intro w hw
    apply hc
    calc
      _ ≤ G.val.edist v (graphNeighbor G v j)+G.val.edist (graphNeighbor G v j) w := SimpleGraph.edist_triangle
      _ ≤ (1 : ℕ∞)+(R : ℕ∞) := add_le_add
        ((SimpleGraph.edist_eq_one_iff_adj.mpr (canonicalPortLabeling G v j).property).le) hw
      _ = _ := by norm_num [Nat.cast_add,add_comm]
  simp only [recodedEdgeObservation,hr,hn]

theorem recodedEdgeProfile_average {m : ℕ} (G : RegularGraph N d)
    (hN : 0 < N) (hd : 0 < d) (hNd : N*d=2*m)
    (recode : (Fin N → Fin q) → (Fin N → Fin Q))
    (ab : Fin Q × Fin Q) (c : Fin N → Fin q) :
    graphEdgeProfile G (recode c) ab=(N : ℝ)⁻¹*∑ v,recodedEdgeObservation G recode ab v c := by
  rw [graphEdgeProfile_vertex_sum G hN hd hNd]
  simp only [recodedEdgeObservation,Nat.cast_mul,mul_inv_rev,← Finset.mul_sum]
  ring

theorem recodedEdgeProfile_variance {m : ℕ} (G : RegularGraph N d)
    (hN : 0 < N) (hd : 0 < d) (hq : 0 < q) (hNd : N*d=2*m) (R : ℕ)
    (recode : (Fin N → Fin q) → (Fin N → Fin Q)) (hlocal : IsGraphLocal G R recode)
    (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b=1)
    (ab : Fin Q × Fin Q) :
    (∫ c,(graphEdgeProfile G (recode c) ab-
      meanProfile (independentColoringLaw p hp hs) (fun z => graphEdgeProfile G (recode z)) ab)^2
      ∂independentColoringLaw p hp hs) ≤ (regularBallBound d (2*(R+1)) : ℝ)/(N : ℝ) := by
  unfold meanProfile
  simp_rw [recodedEdgeProfile_average G hN hd hNd recode ab]
  exact graphAverage_variance_of_local G hN hq (R+1) (recodedEdgeObservation G recode ab)
    (recodedEdgeObservation_nonneg G recode ab) (recodedEdgeObservation_le_one G hd recode ab)
    (recodedEdgeObservation_local G R recode hlocal ab) p hp hs

theorem recodedEdgeProfile_totalVariation {m : ℕ} (G : RegularGraph N d)
    (hN : 0 < N) (hd : 0 < d) (hq : 0 < q) (hNd : N*d=2*m) (R : ℕ)
    (recode : (Fin N → Fin q) → (Fin N → Fin Q)) (hlocal : IsGraphLocal G R recode)
    (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b=1) :
    (∫ c,totalVariation (graphEdgeProfile G (recode c))
      (meanProfile (independentColoringLaw p hp hs) (fun z => graphEdgeProfile G (recode z)))
      ∂independentColoringLaw p hp hs) ≤
      ((Q*Q : ℕ) : ℝ)/2*Real.sqrt ((regularBallBound d (2*(R+1)) : ℝ)/(N : ℝ)) := by
  let P := independentColoringLaw p hp hs
  let E := fun c => graphEdgeProfile G (recode c)
  have hmem (ab : Fin Q × Fin Q) : MemLp (fun c => E c ab) 2 P :=
    profile_coordinate_memLp P E (fun ab => measurable_of_finite _)
      (fun c ab => graphEdgeProfile_nonneg G (recode c) ab)
      (fun c => graphEdgeProfile_sum G hN hd (recode c)) ab 2
  have h := integral_profileL1_mean_le_variance P E hmem
    ((regularBallBound d (2*(R+1)) : ℝ)/(N : ℝ))
    (fun ab => recodedEdgeProfile_variance G hN hd hq hNd R recode hlocal p hp hs ab)
  have he : (∫ c,totalVariation (E c) (meanProfile P E) ∂P) =
      (1/2 : ℝ)*(∫ c,profileL1 (E c) (meanProfile P E) ∂P) := integral_const_mul _ _
  change (∫ c,totalVariation (E c) (meanProfile P E) ∂P) ≤ _
  rw [he]
  have hhalf := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1/2)
  convert hhalf using 1 <;> simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] <;> ring

/-- Recovering every input root color from its recoded root label gives an
actual entropy lower bound for the entire recoded coloring. -/
theorem recoding_entropy_ge_independent
    (recode : (Fin N → Fin q) → (Fin N → Fin Q)) (decode : Fin Q → Fin q)
    (hdecode : ∀ c v,decode (recode c v)=c v)
    (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b=1) :
    (∑ v,entropy (p v)) ≤ entropy (lawMass (independentColoringLaw p hp hs) recode) := by
  let P := independentColoringLaw p hp hs
  let D (z : Fin N → Fin Q) (v : Fin N) := decode (z v)
  have hleft : D ∘ recode=id := by funext c v; exact hdecode c v
  have he : pushMass D (lawMass P recode)=lawMass P id := by
    funext c
    rw [finite_pushMass_lawMass P recode (measurable_of_finite _) D,hleft]
    rfl
  have hb := entropy_pushMass_le D (lawMass P recode) (lawMass_nonneg P recode)
  rw [he] at hb
  simpa only [P,independentColoringLaw_entropy] using hb

/-- The finite graph-counting event controls all deterministic finite-radius
recodings of all independent recolorings. The only coding requirements are
ordinary locality and recovery of each input root color. -/
theorem local_recoding_entropy_bound {m : ℕ} (G : RegularGraph N d)
    (hN : 0 < N) (hd : 0 < d) (hq : 0 < q) (hQ : 0 < Q) (hNd : N*d=2*m)
    (R : ℕ) (recode : (Fin N → Fin q) → (Fin N → Fin Q)) (hlocal : IsGraphLocal G R recode)
    (decode : Fin Q → Fin q) (hdecode : ∀ c v,decode (recode c v)=c v)
    (C t : ℝ) (M : ℕ) (hG : GraphProfileGood (q := Q) (m := m) C t M G)
    (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b=1) :
    (∑ v,entropy (p v)) ≤
      (N : ℝ)*entropy (meanProfile (independentColoringLaw p hp hs) (fun c => graphStarProfile G (recode c)))-
      (m : ℝ)*entropy (meanProfile (independentColoringLaw p hp hs) (fun c => graphEdgeProfile G (recode c)))+
      (m : ℝ)*(3+Real.log (Q*Q : ℕ))*
        Real.sqrt (((Q*Q : ℕ) : ℝ)/2*Real.sqrt ((regularBallBound d (2*(R+1)) : ℝ)/(N : ℝ)))+
      ((Q : ℝ)^2/2+2)*(C+Real.log (2*m+1))+
      3*paletteLog N d Q+t+simplicityCost N d M := by
  have h := random_coloring_entropy_mean_bound G hN hd C t M hG
    (independentColoringLaw p hp hs) recode (measurable_of_finite _)
  have hlower := recoding_entropy_ge_independent recode decode hdecode p hp hs
  have htv := recodedEdgeProfile_totalVariation G hN hd hq hNd R recode hlocal p hp hs
  have hlog : 0 ≤ Real.log (Q*Q : ℕ) := Real.log_nonneg (by exact_mod_cast (Nat.mul_pos hQ hQ))
  have hcoef : 0 ≤ (m : ℝ)*(3+Real.log (Q*Q : ℕ)) := mul_nonneg (by positivity) (by linarith)
  have herr := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htv) hcoef
  linarith

end GaussianWave.BS.Lower
