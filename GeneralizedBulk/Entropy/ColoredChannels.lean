import GeneralizedBulk.Entropy.ChannelReversal

/-! Simultaneous correlated star channels on a single fixed Euclidean space. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Channel

abbrev ColoredStar (d k : ℕ) := PiLp 2 (fun _ : Fin k => WhiteStar d)

def blockVector (d k : ℕ) (a : Fin k) (v : WhiteStar d) : ColoredStar d k :=
  (WithLp.equiv 2 _).symm (Pi.single a v)

@[simp] theorem blockVector_apply (d k : ℕ) (a b : Fin k) (v : WhiteStar d) :
    blockVector d k a v b = if b = a then v else 0 := by
  simp [blockVector, Pi.single_apply]

/-- Orthogonal color blocks have independent standard-Gaussian coordinates;
the deterministic inner-product identity is proved here without assuming a law. -/
theorem blockVector_inner (d k : ℕ) (a : Fin k) (v : WhiteStar d) (y : ColoredStar d k) :
    @inner ℝ (ColoredStar d k) _ (blockVector d k a v) y =
      @inner ℝ (WhiteStar d) _ v (y a) := by
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_single a]
  · simp only [blockVector_apply, ↓reduceIte]
  · intro b hb hba
    simp only [blockVector_apply, hba, ↓reduceIte, inner_zero_left]
  · intro h
    simp at h

def coloredDirectionA (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ)
    (i : Fin d) (a : Fin k) : ColoredStar d k := blockVector d k a (directionA d hd (c a) i)

def coloredDirectionB (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ)
    (i : Fin d) (a : Fin k) : ColoredStar d k := blockVector d k a (directionB d hd (c a) i)

theorem colored_norm_sq (d k : ℕ) (y : ColoredStar d k) :
    ‖y‖ ^ 2 = ∑ a : Fin k, ‖y a‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp only [real_inner_self_eq_norm_sq]

/-- The weighted frame works simultaneously at different spectral parameters
in every color, with exactly the source coefficients and no independence
assumption on a signal observed through these overlapping edge projections. -/
theorem colored_weighted_frame_energy (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ)
    (hc : ∀ a, |c a| < 1) (y : ColoredStar d k) :
    (∑ i : Fin d, ∑ a : Fin k,
      (weightA d (c a) * (@inner ℝ (ColoredStar d k) _ (coloredDirectionA d k hd c i a) y) ^ 2 +
       weightB d (c a) * (@inner ℝ (ColoredStar d k) _ (coloredDirectionB d k hd c i a) y) ^ 2)) = ‖y‖ ^ 2 := by
  simp only [coloredDirectionA, coloredDirectionB, blockVector_inner]
  rw [Finset.sum_comm, colored_norm_sq]
  apply Finset.sum_congr rfl
  intro a ha
  exact weighted_frame_energy d hd (c a) (hc a) (y a)

/-- All weights in the actual multiple-channel bulk construction are positive. -/
theorem colored_bulk_weights_pos (d k : ℕ) (hd : 3 ≤ d) (c : Fin k → ℝ)
    (hbulk : ∀ a, (c a) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2) :
    ∀ a, 0 < weightA d (c a) ∧ 0 < weightB d (c a) :=
  fun a => bulk_weights_pos d hd (c a) (hbulk a)

/-- The actual overlapping edge projections retain the scalar and the same
simplex transverse direction in every color. -/
def coloredEdgeProjection (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    ColoredStar d k →ₗ[ℝ] ColoredStar d k where
  toFun y := (WithLp.equiv 2 _).symm (fun a => edgeProjection d hd i (y a))
  map_add' x y := by ext a; simp
  map_smul' r y := by ext a; simp

@[simp] theorem coloredEdgeProjection_apply (d k : ℕ) (hd : 2 ≤ d) (i : Fin d)
    (y : ColoredStar d k) (a : Fin k) :
    coloredEdgeProjection d k hd i y a = edgeProjection d hd i (y a) := rfl

@[simp] theorem coloredEdgeProjection_idempotent (d k : ℕ) (hd : 2 ≤ d) (i : Fin d)
    (y : ColoredStar d k) :
    coloredEdgeProjection d k hd i (coloredEdgeProjection d k hd i y) =
      coloredEdgeProjection d k hd i y := by
  ext a
  exact edgeProjection_idempotent d hd i (y a)

theorem coloredEdgeProjection_selfAdjoint (d k : ℕ) (hd : 2 ≤ d) (i : Fin d)
    (x y : ColoredStar d k) :
    @inner ℝ (ColoredStar d k) _ (coloredEdgeProjection d k hd i x) y =
      @inner ℝ (ColoredStar d k) _ x (coloredEdgeProjection d k hd i y) := by
  simp only [PiLp.inner_apply, coloredEdgeProjection_apply]
  apply Finset.sum_congr rfl
  intro a ha
  exact edgeProjection_selfAdjoint d hd i (x a) (y a)

end GeneralizedBulk.Entropy.Channel
