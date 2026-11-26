import GeneralizedBulk.Entropy.SpanningMoments
import GeneralizedBulk.Entropy.ScalarCoordinates
import GeneralizedBulk.Entropy.ChannelWhitening
import GeneralizedBulk.Gaussian.StarLaw

/-! The actual colored physical star rows span the whitened signal space. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Channel
open GeneralizedBulk.Gaussian

@[simp] theorem starRow_inner_root (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (x : WhiteStar d) :
    @inner ℝ (WhiteStar d) _ (starRow d hd E 0) x = x.fst := by
  simp [starRow, rootVector, WithLp.prod_inner_apply]

@[simp] theorem starRow_inner_leaf (d : ℕ) (hd : 2 ≤ d) (E : ℝ)
    (i : Fin d) (x : WhiteStar d) :
    @inner ℝ (WhiteStar d) _ (starRow d hd E i.succ) x =
      (E / d) * x.fst + starRho d E * @inner ℝ (Transverse d) _ (simplex d hd i) x.snd := by
  change @inner ℝ (WhiteStar d) _
    ((E / d) • rootVector d + starRho d E • transverseVector d hd i) x = _
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  simp [rootVector, transverseVector, WithLp.prod_inner_apply]

theorem starRho_pos (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d) : 0 < starRho d E := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  apply rho_pos (E / d)
  rw [abs_div, abs_of_pos hdpos, div_lt_one hdpos]
  exact hE

theorem eq_zero_of_starRow_inner_zero (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d)
    (x : WhiteStar d) (hx : ∀ j, @inner ℝ (WhiteStar d) _ (starRow d hd E j) x = 0) : x = 0 := by
  have hp : physicalLinearMap d hd (E / d) (starRho d E) x = 0 := by
    ext j
    cases j with
    | none => simpa only [physicalLinearMap_root, PiLp.zero_apply, starRow_inner_root] using hx 0
    | some i => simpa only [physicalLinearMap_leaf, PiLp.zero_apply, starRow_inner_leaf] using hx i.succ
  apply (whiteningEquiv d hd (E / d) (starRho d E) (ne_of_gt (starRho_pos d hd E hE))).injective
  apply Subtype.ext
  change physicalLinearMap d hd (E / d) (starRho d E) x = physicalLinearMap d hd (E / d) (starRho d E) 0
  rw [hp, map_zero]

theorem starRow_inner_inverseWhitening (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d)
    (x : physicalStar d (E / d)) (j : Fin (d + 1)) :
    @inner ℝ (WhiteStar d) _ (starRow d hd E j) (inverseWhitening d (E / d) (starRho d E) x) =
      Fin.cases ((x : Physical d) none) (fun i => (x : Physical d) (some i)) j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [starRow_inner_root]
    rfl
  · rw [starRow_inner_leaf]
    have h := congrArg (fun y : physicalStar d (E / d) => (y : Physical d) (some i))
      (inverseWhitening_right d hd (E / d) (starRho d E) (ne_of_gt (starRho_pos d hd E hE)) x)
    exact h

def coloredPhysicalRow (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (j : Fin k × Fin (d + 1)) : ColoredStar d k :=
  blockVector d k j.1 (starRow d hd (energy j.1) j.2)

theorem coloredPhysicalRow_gram (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (hE : ∀ a, |energy a| < d) (j l : Fin k × Fin (d + 1)) :
    @inner ℝ (ColoredStar d k) _ (coloredPhysicalRow d k hd energy j) (coloredPhysicalRow d k hd energy l) =
      (if j.1 = l.1 then 1 else 0) *
        External.RegularSpectralData.starWaveCovariance d (energy j.1) j.2 l.2 := by
  unfold coloredPhysicalRow
  rw [blockVector_inner, blockVector_apply]
  by_cases h : j.1 = l.1
  · simp only [h, ↓reduceIte, one_mul]
    exact starRow_gram d hd _ (hE l.1) _ _
  · simp only [h, ↓reduceIte, inner_zero_right, zero_mul]

/-- Spanning is proved against the actual whitening map, uniformly over all
strictly nondegenerate spectral parameters in different colors. -/
theorem coloredPhysicalRow_span (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (hE : ∀ a, |energy a| < d) :
    Submodule.span ℝ (Set.range (coloredPhysicalRow d k hd energy)) = ⊤ := by
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hzero (a : Fin k) : x a = 0 := by
    apply eq_zero_of_starRow_inner_zero d hd (energy a) (hE a)
    intro j
    have h := Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self (a, j))) hx
    simpa only [coloredPhysicalRow, blockVector_inner] using h
  apply (WithLp.equiv 2 _).injective
  funext a
  exact hzero a

end GeneralizedBulk.Entropy.Channel
