import GeneralizedBulk.Entropy.ScalarCoordinates
import GeneralizedBulk.Entropy.ObservationBasis
import GeneralizedBulk.Entropy.GaussianFrameSystem

/-! Actual edge observation subspaces, Parseval, and reversal in fixed star
coordinates. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Channel

def coloredEdgeSpace (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) : Submodule ℝ (ColoredStar d k) :=
  LinearMap.range (coloredEdgeProjection d k hd i)

theorem mem_coloredEdgeSpace_iff (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) (x : ColoredStar d k) :
    x ∈ coloredEdgeSpace d k hd i ↔ coloredEdgeProjection d k hd i x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact coloredEdgeProjection_idempotent d k hd i y
  · intro hx
    exact ⟨x, hx⟩

/-- The two adapted directions in each color reconstruct the genuine edge
projection. This gives the span needed by the mixed-derivative argument. -/
theorem edgeProjection_reconstruction (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (i : Fin d) (y : WhiteStar d) :
    edgeProjection d hd i y =
      (@inner ℝ (WhiteStar d) _ (directionA d hd c i) y) • directionA d hd c i +
      (@inner ℝ (WhiteStar d) _ (directionB d hd c i) y) • directionB d hd c i := by
  rw [directionA_inner, directionB_inner]
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · change y.fst = (alpha c * y.fst - beta c * @inner ℝ (Transverse d) _ (simplex d hd i) y.snd) * alpha c +
      (beta c * y.fst + alpha c * @inner ℝ (Transverse d) _ (simplex d hd i) y.snd) * beta c
    calc
      _ = (alpha c ^ 2 + beta c ^ 2) * y.fst := by rw [alpha_sq_add_beta_sq c hc, one_mul]
      _ = _ := by ring
  · change (@inner ℝ (Transverse d) _ (simplex d hd i) y.snd) • simplex d hd i =
      (alpha c * y.fst - beta c * @inner ℝ (Transverse d) _ (simplex d hd i) y.snd) • (-(beta c) • simplex d hd i) +
      (beta c * y.fst + alpha c * @inner ℝ (Transverse d) _ (simplex d hd i) y.snd) • (alpha c • simplex d hd i)
    rw [smul_smul, smul_smul, ← add_smul]
    congr 1
    calc
      _ = (alpha c ^ 2 + beta c ^ 2) * @inner ℝ (Transverse d) _ (simplex d hd i) y.snd := by
        rw [alpha_sq_add_beta_sq c hc, one_mul]
      _ = _ := by ring

theorem edgeProjection_directionA (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (i : Fin d) :
    edgeProjection d hd i (directionA d hd c i) = directionA d hd c i := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · rfl
  · change (@inner ℝ (Transverse d) _ (simplex d hd i) (-(beta c) • simplex d hd i)) • simplex d hd i = _
    simp only [inner_smul_right, simplex_inner, ↓reduceIte, mul_one]
    rfl

theorem edgeProjection_directionB (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (i : Fin d) :
    edgeProjection d hd i (directionB d hd c i) = directionB d hd c i := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · rfl
  · change (@inner ℝ (Transverse d) _ (simplex d hd i) (alpha c • simplex d hd i)) • simplex d hd i = _
    simp only [inner_smul_right, simplex_inner, ↓reduceIte, mul_one]
    rfl

/-- Ordinary ON-frame Parseval on a single actual edge observation. -/
theorem edge_frame_energy (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (i : Fin d) (y : WhiteStar d) :
    (@inner ℝ (WhiteStar d) _ (directionA d hd c i) y) ^ 2 +
      (@inner ℝ (WhiteStar d) _ (directionB d hd c i) y) ^ 2 = ‖edgeProjection d hd i y‖ ^ 2 := by
  rw [edgeProjection_reconstruction d hd c hc i y, norm_add_sq_real, norm_smul, norm_smul,
    inner_smul_left, inner_smul_right, directionA_inner_directionB]
  have ha := directionA_norm_sq d hd c hc i
  have hb := directionB_norm_sq d hd c hc i
  simp only [starRingEnd_apply, star_trivial, mul_zero, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [ha, hb]
  ring

theorem colored_edge_frame_energy (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ)
    (hc : ∀ a, |c a| < 1) (i : Fin d) (y : ColoredStar d k) :
    (∑ a : Fin k, ((@inner ℝ (ColoredStar d k) _ (coloredDirectionA d k hd c i a) y) ^ 2 +
      (@inner ℝ (ColoredStar d k) _ (coloredDirectionB d k hd c i a) y) ^ 2)) =
      ‖coloredEdgeProjection d k hd i y‖ ^ 2 := by
  rw [colored_norm_sq]
  simp only [coloredDirectionA, coloredDirectionB, blockVector_inner, coloredEdgeProjection_apply]
  apply Finset.sum_congr rfl
  intro a ha
  exact edge_frame_energy d hd (c a) (hc a) i (y a)

/-- Actual simultaneous endpoint reversal on all color blocks. -/
def coloredReversal (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ) (i : Fin d) :
    ColoredStar d k ≃ₗᵢ[ℝ] ColoredStar d k :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun a => endpointReversal d hd (c a) i)

@[simp] theorem coloredReversal_directionA (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ)
    (hc : ∀ a, |c a| < 1) (i : Fin d) (a : Fin k) :
    coloredReversal d k hd c i (coloredDirectionA d k hd c i a) = coloredDirectionB d k hd c i a := by
  change LinearIsometryEquiv.piLpCongrRight 2 (fun a => endpointReversal d hd (c a) i)
    ((WithLp.equiv 2 _).symm (Pi.single a (directionA d hd (c a) i))) = _
  rw [LinearIsometryEquiv.piLpCongrRight_single]
  simp only [endpointReversal_directionA d hd (c a) (hc a) i]
  rfl


theorem coloredEdgeProjection_blockVector (d k : ℕ) (hd : 2 ≤ d) (i : Fin d)
    (a : Fin k) (v : WhiteStar d) :
    coloredEdgeProjection d k hd i (blockVector d k a v) = blockVector d k a (edgeProjection d hd i v) := by
  classical
  ext b
  by_cases hb : b = a
  · simp only [coloredEdgeProjection_apply, blockVector_apply, hb, ↓reduceIte]
  · simp only [coloredEdgeProjection_apply, blockVector_apply, hb, ↓reduceIte, map_zero]

theorem coloredDirectionA_mem_edgeSpace (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ)
    (i : Fin d) (a : Fin k) : coloredDirectionA d k hd c i a ∈ coloredEdgeSpace d k hd i := by
  rw [mem_coloredEdgeSpace_iff]
  exact (coloredEdgeProjection_blockVector d k hd i a _).trans
    (congrArg (blockVector d k a) (edgeProjection_directionA d hd (c a) i))

theorem coloredDirectionB_mem_edgeSpace (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ)
    (i : Fin d) (a : Fin k) : coloredDirectionB d k hd c i a ∈ coloredEdgeSpace d k hd i := by
  rw [mem_coloredEdgeSpace_iff]
  exact (coloredEdgeProjection_blockVector d k hd i a _).trans
    (congrArg (blockVector d k a) (edgeProjection_directionB d hd (c a) i))

/-- Pointwise reconstruction of the actual overlapping edge projector from
all adapted directions and colors. -/
theorem coloredEdgeProjection_reconstruction (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ)
    (hc : ∀ a, |c a| < 1) (i : Fin d) (y : ColoredStar d k) :
    coloredEdgeProjection d k hd i y = ∑ a : Fin k,
      ((@inner ℝ (ColoredStar d k) _ (coloredDirectionA d k hd c i a) y) • coloredDirectionA d k hd c i a +
        (@inner ℝ (ColoredStar d k) _ (coloredDirectionB d k hd c i a) y) • coloredDirectionB d k hd c i a) := by
  classical
  ext b
  rw [colored_sum_apply]
  simp only [PiLp.add_apply, PiLp.smul_apply, coloredDirectionA, coloredDirectionB,
    blockVector_inner, blockVector_apply]
  rw [Finset.sum_eq_single b]
  · simpa only [↓reduceIte] using edgeProjection_reconstruction d hd (c b) (hc b) i (y b)
  · intro a ha hab
    have hba : b ≠ a := Ne.symm hab
    simp [hba]
  · simp

end GeneralizedBulk.Entropy.Channel
