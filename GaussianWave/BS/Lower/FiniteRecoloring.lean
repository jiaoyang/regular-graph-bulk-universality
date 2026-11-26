import GaussianWave.BS.Reused.Graph.RandomColoringEntropy
import GaussianWave.BS.Reused.Graph.ColorSampling
import GaussianWave.BS.Reused.Entropy.FiniteProduct

/-! Actual independent finite recoloring laws. Their atoms, independence and
whole-coloring entropy are derived from the finite product measure. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
set_option maxHeartbeats 400000

namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite
open GaussianWave.BS.Reused.Graph GaussianWave.BS.Reused.Graph.Configuration

variable {q N d : ℕ}

/-- A literal finite probability law with the prescribed nonnegative masses. -/
def finiteColorPMF (p : Fin q → ℝ) (hp : ∀ b,0 ≤ p b) (hs : ∑ b,p b = 1) : PMF (Fin q) :=
  PMF.ofFintype (fun b => ENNReal.ofReal (p b)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => hp b),hs,ENNReal.ofReal_one])

def finiteColorLaw (p : Fin q → ℝ) (hp : ∀ b,0 ≤ p b) (hs : ∑ b,p b = 1) : Measure (Fin q) :=
  (finiteColorPMF p hp hs).toMeasure

instance finiteColorLaw_isProbability (p : Fin q → ℝ) (hp : ∀ b,0 ≤ p b) (hs : ∑ b,p b = 1) :
    IsProbabilityMeasure (finiteColorLaw p hp hs) := by
  unfold finiteColorLaw
  infer_instance

theorem finiteColorLaw_singleton (p : Fin q → ℝ) (hp : ∀ b,0 ≤ p b) (hs : ∑ b,p b = 1) (b : Fin q) :
    finiteColorLaw p hp hs {b} = ENNReal.ofReal (p b) := by
  rw [finiteColorLaw,PMF.toMeasure_apply_singleton _ b (measurableSet_singleton b)]
  rfl

/-- Each vertex receives an independent draw from its own finite color law. -/
def independentColoringLaw (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b)
    (hs : ∀ v,∑ b,p v b = 1) : Measure (VertexColoring N q) :=
  Measure.pi (fun v => finiteColorLaw (p v) (hp v) (hs v))

instance independentColoringLaw_isProbability (p : Fin N → Fin q → ℝ)
    (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b = 1) :
    IsProbabilityMeasure (independentColoringLaw p hp hs) := by
  unfold independentColoringLaw
  infer_instance

/-- The actual measure has exactly the independently multiplied atoms. -/
theorem independentColoringLaw_lawMass (p : Fin N → Fin q → ℝ)
    (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b = 1) :
    lawMass (independentColoringLaw p hp hs) id = productMass p := by
  funext c
  have hc : ({c} : Set (Fin N → Fin q)) = Set.univ.pi (fun v => {c v}) := by ext w; simp [funext_iff]
  change (independentColoringLaw p hp hs {c}).toReal = _
  rw [independentColoringLaw,hc,Measure.pi_pi]
  simp only [finiteColorLaw_singleton,ENNReal.toReal_prod,ENNReal.toReal_ofReal (hp _ _),productMass]

/-- Entropy of the whole independent recoloring is the sum of the conditional
one-vertex entropies. This is an equality of actual finite laws. -/
theorem independentColoringLaw_entropy (p : Fin N → Fin q → ℝ)
    (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b = 1) :
    entropy (lawMass (independentColoringLaw p hp hs) id) = ∑ v,entropy (p v) := by
  rw [independentColoringLaw_lawMass,entropy_productMass N p hs]

/-- Each coordinate of the literal product recoloring has its prescribed law. -/
theorem independentColoringLaw_eval (p : Fin N → Fin q → ℝ)
    (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b = 1) (v : Fin N) :
    Measure.map (fun c : VertexColoring N q => c v) (independentColoringLaw p hp hs) =
      finiteColorLaw (p v) (hp v) (hs v) := by
  ext s hsmeas
  rw [Measure.map_apply (measurable_pi_apply v) hsmeas,independentColoringLaw]
  change (Measure.pi (fun w => finiteColorLaw (p w) (hp w) (hs w))) (Function.eval v ⁻¹' s) = _
  have he : Set.univ.pi (Function.update (fun _ : Fin N => (Set.univ : Set (Fin q))) v s) =
      (Function.eval v : (Fin N → Fin q) → Fin q) ⁻¹' s :=
    Set.univ_pi_update_univ (α := fun _ : Fin N => Fin q) v s
  rw [← he,Measure.pi_pi]
  rw [Finset.prod_eq_single v]
  · simp only [Function.update_same]
  · intro w hw hwv
    simp only [Function.update_of_ne hwv,measure_univ]
  · simp

/-- Independence is proved for the actual product law, not supplied as an
independence certificate in the eventual entropy theorem. -/
theorem independentColoringLaw_iIndepFun (p : Fin N → Fin q → ℝ)
    (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b = 1) :
    iIndepFun (fun v (c : VertexColoring N q) => c v) (independentColoringLaw p hp hs) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun v => (measurable_pi_apply v).aemeasurable)).mpr
  change Measure.map id (independentColoringLaw p hp hs) = _
  rw [Measure.map_id]
  simp_rw [independentColoringLaw_eval]
  rfl

/-- Every injectively sampled finite set of vertices has the literal product
of its one-site color masses. -/
theorem independentColoringLaw_restrict_mass {k : ℕ} (p : Fin N → Fin q → ℝ)
    (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b = 1)
    (site : Fin k ↪ Fin N) (w : Fin k → Fin q) :
    lawMass (independentColoringLaw p hp hs) (fun c i => c (site i)) w =
      ∏ i,p (site i) (w i) := by
  let P := independentColoringLaw p hp hs
  have hInd := (independentColoringLaw_iIndepFun p hp hs).precomp site.injective
  have hevent : (fun c : VertexColoring N q => fun i => c (site i)) ⁻¹' {w} =
      ⋂ i : Fin k,(fun c : VertexColoring N q => c (site i)) ⁻¹' {w i} := by
    ext c
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_iInter]
    exact funext_iff
  have hmarg (i : Fin k) : P ((fun c : VertexColoring N q => c (site i)) ⁻¹' {w i}) =
      ENNReal.ofReal (p (site i) (w i)) := by
    rw [← Measure.map_apply (measurable_pi_apply (site i)) (measurableSet_singleton (w i))]
    change Measure.map _ (independentColoringLaw p hp hs) _ = _
    rw [independentColoringLaw_eval,finiteColorLaw_singleton]
  have heq : P ((fun c : VertexColoring N q => fun i => c (site i)) ⁻¹' {w}) =
      ∏ i : Fin k,P ((fun c : VertexColoring N q => c (site i)) ⁻¹' {w i}) := by
    rw [hevent]
    simpa only [Finset.mem_univ,Set.iInter_true] using
      (hInd.measure_inter_preimage_eq_mul Finset.univ
        (sets := fun i : Fin k => {w i}) (fun i _ => measurableSet_singleton (w i)))
  change (P ((fun c : VertexColoring N q => fun i => c (site i)) ⁻¹' {w})).toReal = _
  rw [heq]
  simp_rw [hmarg]
  simp only [ENNReal.toReal_prod,ENNReal.toReal_ofReal (hp _ _)]

/-- The one common graph-counting event controls every independent randomized
recoloring, retaining the required conditional-entropy term. -/
theorem independent_recoloring_entropy_mean_bound {m : ℕ} (G : RegularGraph N d)
    (hN : 0 < N) (hd : 0 < d) (C t : ℝ) (M : ℕ)
    (hG : GraphProfileGood (q := q) (m := m) C t M G)
    (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b = 1) :
    (∑ v,entropy (p v)) ≤
      (N : ℝ)*entropy (meanProfile (independentColoringLaw p hp hs) (graphStarProfile G))-
        (m : ℝ)*entropy (meanProfile (independentColoringLaw p hp hs) (graphEdgeProfile G))+
        (m : ℝ)*(3+Real.log (q*q : ℕ))*
          Real.sqrt (∫ c,totalVariation (graphEdgeProfile G c)
            (meanProfile (independentColoringLaw p hp hs) (graphEdgeProfile G))
            ∂independentColoringLaw p hp hs)+
        ((q : ℝ)^2/2+2)*(C+Real.log (2*m+1))+
        3*paletteLog N d q+t+simplicityCost N d M := by
  have h := random_coloring_entropy_mean_bound G hN hd C t M hG
    (independentColoringLaw p hp hs) id measurable_id
  rw [independentColoringLaw_entropy] at h
  exact h

end GaussianWave.BS.Lower
