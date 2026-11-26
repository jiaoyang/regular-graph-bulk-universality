import GaussianWave.BS.Lower.FiniteRecoloring
import GaussianWave.BS.Lower.DependencyVariance

/-! Uniform edge-profile concentration for the actual independent finite
recoloring measure on every finite simple regular graph. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
set_option maxHeartbeats 800000

namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite
open GaussianWave.BS.Reused.Graph GaussianWave.BS.Reused.Graph.Configuration

variable {q N d : ℕ}

def edgeColorIndicator (G : RegularGraph N d) (ab : Fin q × Fin q) (e : G.val.Dart)
    (c : VertexColoring N q) : ℝ := if (c e.fst,c e.snd) = ab then 1 else 0

/-- Disjoint edges see independent colors under the actual vertex-product
measure. We use the existing larger switching-rejection set to count all
possible dependent partners uniformly. -/
theorem edgeColorIndicator_indep (G : RegularGraph N d) (ab : Fin q × Fin q)
    (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b = 1)
    (e f : G.val.Dart) (hf : f ∉ badSecond G.val e) :
    IndepFun (edgeColorIndicator G ab e) (edgeColorIndicator G ab f)
      (independentColoringLaw p hp hs) := by
  have hgood : Function.Injective (dartEndpoints G.val e f) := by
    have h := hf
    simp only [badSecond,Finset.mem_filter,Finset.mem_univ,true_and,not_or] at h
    exact not_not.mp h.1
  have hne := (dartEndpoints_injective_iff G.val e f).mp hgood
  have hpair := (independentColoringLaw_iIndepFun p hp hs).indepFun_prodMk_prodMk
    (fun v => measurable_pi_apply v) e.fst e.snd f.fst f.snd hne.1 hne.2.1 hne.2.2.1 hne.2.2.2
  exact hpair.comp (measurable_of_finite (fun z : Fin q × Fin q => if z = ab then (1 : ℝ) else 0))
    (measurable_of_finite (fun z : Fin q × Fin q => if z = ab then (1 : ℝ) else 0))

/-- Centered sum of all oriented-edge indicators has variance `O(N)`, with
a constant depending only on the degree. -/
theorem edgeColorIndicator_centered_sum_sq (G : RegularGraph N d) (ab : Fin q × Fin q)
    (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b = 1) :
    (∫ c,(∑ e : G.val.Dart,(edgeColorIndicator G ab e c-
        ∫ z,edgeColorIndicator G ab e z ∂independentColoringLaw p hp hs))^2
        ∂independentColoringLaw p hp hs) ≤
      (Fintype.card G.val.Dart : ℝ)*(4*d+2*d^2 : ℕ) := by
  apply integral_centered_sum_sq_le (independentColoringLaw p hp hs)
    (edgeColorIndicator G ab)
    (fun e c => by unfold edgeColorIndicator; split_ifs <;> norm_num)
    (fun e c => by unfold edgeColorIndicator; split_ifs <;> norm_num)
    (badSecond G.val) (4*d+2*d^2) (fun e => badSecond_card_le G.val G.property e)
  exact fun e f hf => edgeColorIndicator_indep G ab p hp hs e f hf

/-- The actual symmetrized profile's directed-edge marginal is the literal
uniform average over oriented graph edges. -/
theorem graphEdgeProfile_dart_average {m : ℕ} (G : RegularGraph N d)
    (hN : 0 < N) (hd : 0 < d) (hNd : N*d = 2*m) (ab : Fin q × Fin q) (c : VertexColoring N q) :
    graphEdgeProfile G c ab = (Fintype.card G.val.Dart : ℝ)⁻¹*
      ∑ e : G.val.Dart,edgeColorIndicator G ab e c := by
  rw [graphEdgeProfile_vertex_sum G hN hd hNd,regular_dart_card G.val G.property,Fintype.card_fin]
  congr 1
  have h := Equiv.sum_comp (labelingDartEquiv G (canonicalPortLabeling G))
    (fun e : G.val.Dart => edgeColorIndicator G ab e c)
  rw [Fintype.sum_prod_type] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro j hj
  change (if c v = ab.1 ∧ c (graphNeighbor G v j) = ab.2 then (1 : ℝ) else 0) =
    (if (c v,c (graphNeighbor G v j)) = ab then (1 : ℝ) else 0)
  simp only [Prod.ext_iff]

/-- Every coordinate of the empirical edge profile concentrates under
independent vertex recoloring, uniformly in the input vertex marks and graph. -/
theorem graphEdgeProfile_recoloring_variance {m : ℕ} (G : RegularGraph N d)
    (hN : 0 < N) (hd : 0 < d) (hNd : N*d = 2*m) (ab : Fin q × Fin q)
    (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b = 1) :
    (∫ c,(graphEdgeProfile G c ab-
      meanProfile (independentColoringLaw p hp hs) (graphEdgeProfile G) ab)^2
        ∂independentColoringLaw p hp hs) ≤ (4+2*(d : ℝ))/(N : ℝ) := by
  let P := independentColoringLaw p hp hs
  let L : ℝ := Fintype.card G.val.Dart
  have hL : 0 < L := by
    dsimp [L]
    rw [regular_dart_card G.val G.property,Fintype.card_fin]
    positivity
  have hmean : meanProfile P (graphEdgeProfile G) ab =
      L⁻¹*∑ e : G.val.Dart,∫ c,edgeColorIndicator G ab e c ∂P := by
    unfold meanProfile
    simp_rw [graphEdgeProfile_dart_average G hN hd hNd ab]
    rw [integral_const_mul,integral_finset_sum _ (fun e _ => Integrable.of_finite)]
  have hpoint (c : VertexColoring N q) :
      (graphEdgeProfile G c ab-meanProfile P (graphEdgeProfile G) ab)^2 =
        (L⁻¹)^2*(∑ e : G.val.Dart,(edgeColorIndicator G ab e c-∫ z,edgeColorIndicator G ab e z ∂P))^2 := by
    rw [graphEdgeProfile_dart_average G hN hd hNd ab,hmean,Finset.sum_sub_distrib]
    dsimp only [L]
    ring
  change (∫ c,(graphEdgeProfile G c ab-meanProfile P (graphEdgeProfile G) ab)^2 ∂P) ≤ _
  simp_rw [hpoint]
  rw [integral_const_mul]
  have hbound := mul_le_mul_of_nonneg_left (edgeColorIndicator_centered_sum_sq G ab p hp hs)
    (sq_nonneg L⁻¹)
  apply hbound.trans_eq
  dsimp [L]
  rw [regular_dart_card G.val G.property,Fintype.card_fin]
  push_cast
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  field_simp
  ring

/-- Total-variation fluctuation tends to zero uniformly over all vertex
color probabilities; the displayed finite bound is already enough for L1. -/
theorem graphEdgeProfile_recoloring_totalVariation {m : ℕ} (G : RegularGraph N d)
    (hN : 0 < N) (hd : 0 < d) (hNd : N*d = 2*m)
    (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b = 1) :
    (∫ c,totalVariation (graphEdgeProfile G c)
      (meanProfile (independentColoringLaw p hp hs) (graphEdgeProfile G))
        ∂independentColoringLaw p hp hs) ≤
          ((q*q : ℕ) : ℝ)/2*Real.sqrt ((4+2*(d : ℝ))/(N : ℝ)) := by
  let P := independentColoringLaw p hp hs
  have hmem (ab : Fin q × Fin q) : MemLp (fun c => graphEdgeProfile G c ab) 2 P :=
    profile_coordinate_memLp P (graphEdgeProfile G)
      (fun ab => measurable_of_finite _) (fun c ab => graphEdgeProfile_nonneg G c ab)
      (fun c => graphEdgeProfile_sum G hN hd c) ab 2
  have h := integral_profileL1_mean_le_variance P (graphEdgeProfile G) hmem
    ((4+2*(d : ℝ))/(N : ℝ))
      (fun ab => graphEdgeProfile_recoloring_variance G hN hd hNd ab p hp hs)
  have he : (∫ c,totalVariation (graphEdgeProfile G c) (meanProfile P (graphEdgeProfile G)) ∂P) =
      (1/2 : ℝ)*(∫ c,profileL1 (graphEdgeProfile G c) (meanProfile P (graphEdgeProfile G)) ∂P) := by
    exact integral_const_mul _ _
  change (∫ c,totalVariation (graphEdgeProfile G c) (meanProfile P (graphEdgeProfile G)) ∂P) ≤ _
  rw [he]
  have hhalf := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1/2)
  convert hhalf using 1 <;> simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] <;> ring

/-- The common counting event yields the full randomized k=0 lower estimate
with a deterministic error that vanishes for fixed palette and degree. -/
theorem independent_recoloring_entropy_bound {m : ℕ} (G : RegularGraph N d)
    (hN : 0 < N) (hd : 0 < d) (hNd : N*d = 2*m) (hq : 0 < q) (C t : ℝ) (M : ℕ)
    (hG : GraphProfileGood (q := q) (m := m) C t M G)
    (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b = 1) :
    (∑ v,entropy (p v)) ≤
      (N : ℝ)*entropy (meanProfile (independentColoringLaw p hp hs) (graphStarProfile G))-
        (m : ℝ)*entropy (meanProfile (independentColoringLaw p hp hs) (graphEdgeProfile G))+
        (m : ℝ)*(3+Real.log (q*q : ℕ))*
          Real.sqrt (((q*q : ℕ) : ℝ)/2*Real.sqrt ((4+2*(d : ℝ))/(N : ℝ)))+
        ((q : ℝ)^2/2+2)*(C+Real.log (2*m+1))+
        3*paletteLog N d q+t+simplicityCost N d M := by
  have h := independent_recoloring_entropy_mean_bound G hN hd C t M hG p hp hs
  have htv := graphEdgeProfile_recoloring_totalVariation G hN hd hNd p hp hs
  have hlog : 0 ≤ Real.log (q*q : ℕ) := Real.log_nonneg (by exact_mod_cast (Nat.mul_pos hq hq))
  have hcoef : 0 ≤ (m : ℝ)*(3+Real.log (q*q : ℕ)) := mul_nonneg (by positivity) (by linarith)
  have herr := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htv) hcoef
  linarith

end GaussianWave.BS.Lower
