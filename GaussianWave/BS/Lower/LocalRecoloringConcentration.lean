import GaussianWave.BS.Lower.FiniteRecoloring
import GaussianWave.BS.Lower.DependencyVariance
import GaussianWave.BS.Reused.Graph.BallCounting

/-! Actual independent recoloring concentration for arbitrary bounded
finite-radius graph observations. The dependence constant is the size of a
radius-`2R` graph ball and is uniform in all vertex color probabilities. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
set_option maxHeartbeats 800000

namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Graph

variable {N d q : ℕ}

theorem graphBall_disjoint_of_far (G : RegularGraph N d) (R : ℕ) (v w : Fin N)
    (hfar : w ∉ graphBallVertices G.val v (2*R)) :
    Disjoint (graphBallVertices G.val v R) (graphBallVertices G.val w R) := by
  apply Finset.disjoint_left.mpr
  intro z hzv hzw
  apply hfar
  simp only [graphBallVertices,Finset.mem_filter,Finset.mem_univ,true_and] at hzv hzw ⊢
  calc
    _ ≤ G.val.edist v z+G.val.edist z w := SimpleGraph.edist_triangle
    _ ≤ (R : ℕ∞)+(R : ℕ∞) := by
      have hzw' : G.val.edist z w ≤ (R : ℕ∞) := by rw [SimpleGraph.edist_comm]; exact hzw
      exact add_le_add hzv hzw'
    _ = _ := by norm_num [two_mul,Nat.cast_add]

/-- A local observation takes as input only the actual colors on its graph
ball; no independence premise is imposed on these observations. -/
def graphLocalObservation (G : RegularGraph N d) (R : ℕ)
    (f : ∀ v : Fin N,((graphBallVertices G.val v R) → Fin q) → ℝ)
    (v : Fin N) (c : Fin N → Fin q) : ℝ := f v (fun w => c w)

theorem graphLocalObservation_indep (G : RegularGraph N d) (R : ℕ)
    (f : ∀ v : Fin N,((graphBallVertices G.val v R) → Fin q) → ℝ)
    (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b = 1)
    (v w : Fin N) (hfar : w ∉ graphBallVertices G.val v (2*R)) :
    IndepFun (graphLocalObservation G R f v) (graphLocalObservation G R f w)
      (independentColoringLaw p hp hs) := by
  have hi := (independentColoringLaw_iIndepFun p hp hs).indepFun_finset
    (graphBallVertices G.val v R) (graphBallVertices G.val w R)
    (graphBall_disjoint_of_far G R v w hfar) (fun i => measurable_pi_apply i)
  exact hi.comp (measurable_of_finite (f v)) (measurable_of_finite (f w))

/-- The unnormalized sum has variance at most `N B_d(2R)`. In particular
the local rules and their palette sizes do not affect the dependence bound. -/
theorem graphLocalObservation_centered_sum_sq (G : RegularGraph N d) (R : ℕ)
    (f : ∀ v : Fin N,((graphBallVertices G.val v R) → Fin q) → ℝ)
    (hf0 : ∀ v z,0 ≤ f v z) (hf1 : ∀ v z,f v z ≤ 1)
    (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b = 1) :
    (∫ c,(∑ v : Fin N,(graphLocalObservation G R f v c-
        ∫ z,graphLocalObservation G R f v z ∂independentColoringLaw p hp hs))^2
      ∂independentColoringLaw p hp hs) ≤ (N : ℝ)*regularBallBound d (2*R) := by
  simpa only [Fintype.card_fin] using integral_centered_sum_sq_le
    (independentColoringLaw p hp hs) (graphLocalObservation G R f)
    (fun v c => hf0 v _) (fun v c => hf1 v _)
    (fun v => graphBallVertices G.val v (2*R)) (regularBallBound d (2*R))
    (fun v => regular_graphBall_card_le G.val G.property v (2*R))
    (fun v w hw => graphLocalObservation_indep G R f p hp hs v w hw)

def graphLocalAverage (G : RegularGraph N d) (R : ℕ)
    (f : ∀ v : Fin N,((graphBallVertices G.val v R) → Fin q) → ℝ)
    (c : Fin N → Fin q) : ℝ := (N : ℝ)⁻¹*∑ v,graphLocalObservation G R f v c

/-- Every empirical bounded finite-radius observation has variance
`B_d(2R)/N` under the literal product recoloring law. -/
theorem graphLocalAverage_variance (G : RegularGraph N d) (hN : 0 < N) (R : ℕ)
    (f : ∀ v : Fin N,((graphBallVertices G.val v R) → Fin q) → ℝ)
    (hf0 : ∀ v z,0 ≤ f v z) (hf1 : ∀ v z,f v z ≤ 1)
    (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b = 1) :
    (∫ c,(graphLocalAverage G R f c-
        ∫ z,graphLocalAverage G R f z ∂independentColoringLaw p hp hs)^2
      ∂independentColoringLaw p hp hs) ≤ (regularBallBound d (2*R) : ℝ)/(N : ℝ) := by
  let P := independentColoringLaw p hp hs
  have hmean : (∫ z,graphLocalAverage G R f z ∂P) =
      (N : ℝ)⁻¹*∑ v : Fin N,∫ z,graphLocalObservation G R f v z ∂P := by
    simp only [graphLocalAverage]
    rw [integral_const_mul,integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  have hpoint (c : Fin N → Fin q) :
      (graphLocalAverage G R f c-∫ z,graphLocalAverage G R f z ∂P)^2 =
        ((N : ℝ)⁻¹)^2*(∑ v : Fin N,(graphLocalObservation G R f v c-
          ∫ z,graphLocalObservation G R f v z ∂P))^2 := by
    rw [graphLocalAverage,hmean,Finset.sum_sub_distrib]
    ring
  change (∫ c,(graphLocalAverage G R f c-∫ z,graphLocalAverage G R f z ∂P)^2 ∂P) ≤ _
  simp_rw [hpoint]
  rw [integral_const_mul]
  have hb := mul_le_mul_of_nonneg_left
    (graphLocalObservation_centered_sum_sq G R f hf0 hf1 p hp hs) (sq_nonneg ((N : ℝ)⁻¹))
  apply hb.trans_eq
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp
  ring

/-- The preceding bound in the usual local-dependence formulation. Equality
of colors throughout the ball suffices; a particular coding of its vertices
does not have to be chosen by the caller. -/
theorem graphAverage_variance_of_local (G : RegularGraph N d) (hN : 0 < N) (hq : 0 < q)
    (R : ℕ) (X : Fin N → (Fin N → Fin q) → ℝ)
    (hX0 : ∀ v c,0 ≤ X v c) (hX1 : ∀ v c,X v c ≤ 1)
    (hlocal : ∀ v c c',
      (∀ w,G.val.edist v w ≤ (R : ℕ∞) → c w=c' w) → X v c=X v c')
    (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b = 1) :
    (∫ c,((N : ℝ)⁻¹*(∑ v,X v c)-
        ∫ z,(N : ℝ)⁻¹*(∑ v,X v z) ∂independentColoringLaw p hp hs)^2
      ∂independentColoringLaw p hp hs) ≤ (regularBallBound d (2*R) : ℝ)/(N : ℝ) := by
  let extend (v : Fin N) (z : (graphBallVertices G.val v R) → Fin q) (w : Fin N) : Fin q :=
    if hw : w ∈ graphBallVertices G.val v R then z ⟨w,hw⟩ else ⟨0,hq⟩
  let f (v : Fin N) (z : (graphBallVertices G.val v R) → Fin q) := X v (extend v z)
  have heq (v : Fin N) (c : Fin N → Fin q) : graphLocalObservation G R f v c=X v c := by
    apply hlocal
    intro w hw
    have hmem : w ∈ graphBallVertices G.val v R := by simp only [graphBallVertices,Finset.mem_filter,Finset.mem_univ,true_and]; exact hw
    simp only [extend,dif_pos hmem]
  have havg (c : Fin N → Fin q) : graphLocalAverage G R f c=(N : ℝ)⁻¹*∑ v,X v c := by
    simp only [graphLocalAverage,heq]
  have hb := graphLocalAverage_variance G hN R f (fun v z => hX0 v _) (fun v z => hX1 v _) p hp hs
  simpa only [havg] using hb

end GaussianWave.BS.Lower
