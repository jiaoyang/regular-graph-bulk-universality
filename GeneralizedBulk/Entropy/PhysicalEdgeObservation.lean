import GeneralizedBulk.Entropy.ColoredObservationSymmetry

/-! The whitened edge projection is determined exactly by its two physical endpoints. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Channel

def edgeRootValue (d : ℕ) (y : WhiteStar d) : ℝ := @inner ℝ (WhiteStar d) _ (rootVector d) y

def edgeLeafValue (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (i : Fin d) (y : WhiteStar d) : ℝ :=
  @inner ℝ (WhiteStar d) _ (leafVector d hd c (rho c) i) y

@[simp] theorem edgeRootValue_eq (d : ℕ) (y : WhiteStar d) : edgeRootValue d y = y.fst := by
  simp [edgeRootValue, rootVector, WithLp.prod_inner_apply]

theorem edgeLeafValue_eq (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (i : Fin d) (y : WhiteStar d) :
    edgeLeafValue d hd c i y = c * y.fst + rho c * @inner ℝ (Transverse d) _ (simplex d hd i) y.snd := by
  unfold edgeLeafValue leafVector
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  simp [rootVector, transverseVector, WithLp.prod_inner_apply]

def decodeEdge (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (i : Fin d) (r l : ℝ) : WhiteStar d :=
  (WithLp.equiv 2 _).symm (r, ((l - c * r) / rho c) • simplex d hd i)

theorem edgeProjection_decode (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (i : Fin d) (y : WhiteStar d) :
    edgeProjection d hd i y = decodeEdge d hd c i (edgeRootValue d y) (edgeLeafValue d hd c i y) := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · exact (edgeRootValue_eq d y).symm
  · change (@inner ℝ (Transverse d) _ (simplex d hd i) y.snd) • simplex d hd i =
      ((edgeLeafValue d hd c i y - c * edgeRootValue d y) / rho c) • simplex d hd i
    rw [edgeLeafValue_eq, edgeRootValue_eq]
    congr 1
    field_simp [ne_of_gt (rho_pos c hc)]

theorem edgeRootValue_reversal (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (i : Fin d) (y : WhiteStar d) :
    edgeRootValue d (endpointReversal d hd c i y) = edgeLeafValue d hd c i y := by
  have h := (endpointReversal d hd c i).inner_map_map (rootVector d) (endpointReversal d hd c i y)
  rw [endpointReversal_involutive d hd c i y, endpointReversal_root d hd c hc i] at h
  exact h.symm

theorem edgeLeafValue_reversal (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (i : Fin d) (y : WhiteStar d) :
    edgeLeafValue d hd c i (endpointReversal d hd c i y) = edgeRootValue d y := by
  have h := (endpointReversal d hd c i).inner_map_map (leafVector d hd c (rho c) i) (endpointReversal d hd c i y)
  rw [endpointReversal_involutive d hd c i y, endpointReversal_leaf d hd c hc i] at h
  exact h.symm

theorem reversed_edgeProjection_decode (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (i : Fin d) (y : WhiteStar d) :
    endpointReversal d hd c i (edgeProjection d hd i y) =
      decodeEdge d hd c i (edgeLeafValue d hd c i y) (edgeRootValue d y) := by
  rw [endpointReversal_projection_commute d hd c hc i y, edgeProjection_decode d hd c hc i,
    edgeRootValue_reversal d hd c hc i, edgeLeafValue_reversal d hd c hc i]

def coloredEdgeValues (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ) (i : Fin d)
    (y : ColoredStar d k) (aj : Fin k × Fin 2) : ℝ :=
  ![edgeRootValue d (y aj.1), edgeLeafValue d hd (c aj.1) i (y aj.1)] aj.2

def swapEdgeValues {k : ℕ} (x : (Fin k × Fin 2) → ℝ) (aj : Fin k × Fin 2) : ℝ :=
  ![x (aj.1, 1), x (aj.1, 0)] aj.2

def decodeColoredEdge (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ) (i : Fin d)
    (x : (Fin k × Fin 2) → ℝ) : ColoredStar d k :=
  (WithLp.equiv 2 _).symm (fun a => decodeEdge d hd (c a) i (x (a, 0)) (x (a, 1)))

theorem coloredEdgeProjection_decode (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ)
    (hc : ∀ a, |c a| < 1) (i : Fin d) (y : ColoredStar d k) :
    coloredEdgeProjection d k hd i y = decodeColoredEdge d k hd c i (coloredEdgeValues d k hd c i y) := by
  apply (WithLp.equiv 2 _).injective
  funext a
  exact edgeProjection_decode d hd (c a) (hc a) i (y a)

theorem coloredReversedProjection_decode (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ)
    (hc : ∀ a, |c a| < 1) (i : Fin d) (y : ColoredStar d k) :
    coloredReversal d k hd c i (coloredEdgeProjection d k hd i y) =
      decodeColoredEdge d k hd c i (swapEdgeValues (coloredEdgeValues d k hd c i y)) := by
  apply (WithLp.equiv 2 _).injective
  funext a
  exact reversed_edgeProjection_decode d hd (c a) (hc a) i (y a)

end GeneralizedBulk.Entropy.Channel
