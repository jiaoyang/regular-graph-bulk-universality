import GeneralizedBulk.Entropy.ColoredEdgeBasis
import GeneralizedBulk.Entropy.PhysicalStarFrame
import GeneralizedBulk.Gaussian.EdgeReferenceBounds

/-! The literal physical root-neighbor edge is an invertible linear image of
the actual retained observation coordinates. -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Matrix
namespace GeneralizedBulk.Gaussian
open GeneralizedBulk.Entropy.Channel GeneralizedBulk.External.RegularSpectralData GeneralizedBulk.Covariance

def physicalEdgeIndex {d : ℕ} (i : Fin d) : Fin 2 → Fin (d+1) :=
  Fin.cases 0 (fun _ => i.succ)

theorem edgeProjection_rootVector (d : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    edgeProjection d hd i (rootVector d) = rootVector d := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext <;> simp [rootVector, edgeProjection_fst, edgeProjection_snd]

theorem edgeProjection_transverseVector (d : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    edgeProjection d hd i (transverseVector d hd i) = transverseVector d hd i := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · rfl
  · change (@inner ℝ (Transverse d) _ (simplex d hd i) (simplex d hd i)) • simplex d hd i = simplex d hd i
    rw [simplex_inner]
    simp

theorem edgeProjection_starRow (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (i : Fin d) (j : Fin 2) :
    edgeProjection d hd i (starRow d hd E (physicalEdgeIndex i j)) =
      starRow d hd E (physicalEdgeIndex i j) := by
  refine Fin.cases ?_ (fun j => ?_) j
  · exact edgeProjection_rootVector d hd i
  · change edgeProjection d hd i ((E/d) • rootVector d + starRho d E • transverseVector d hd i) = _
    rw [map_add, map_smul, map_smul, edgeProjection_rootVector, edgeProjection_transverseVector]
    rfl

def physicalEdgeRow (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ) (i : Fin d)
    (j : Fin k × Fin 2) : ColoredStar d k :=
  coloredPhysicalRow d k hd energy (j.1, physicalEdgeIndex i j.2)

theorem physicalEdgeRow_mem (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ) (i : Fin d)
    (j : Fin k × Fin 2) : physicalEdgeRow d k hd energy i j ∈ coloredEdgeSpace d k hd i := by
  rw [mem_coloredEdgeSpace_iff]
  change coloredEdgeProjection d k hd i (blockVector d k j.1 (starRow d hd (energy j.1) (physicalEdgeIndex i j.2))) = _
  rw [coloredEdgeProjection_blockVector, edgeProjection_starRow]
  rfl

def physicalEdgeRowInSpace (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ) (i : Fin d)
    (j : Fin k × Fin 2) : coloredEdgeSpace d k hd i :=
  ⟨physicalEdgeRow d k hd energy i j, physicalEdgeRow_mem d k hd energy i j⟩

theorem starWaveCovariance_edge (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (i : Fin d) (j l : Fin 2) :
    starWaveCovariance d E (physicalEdgeIndex i j) (physicalEdgeIndex i l) = edgeWaveCovariance d E j l := by
  refine Fin.cases ?_ (fun j => ?_) j
  · refine Fin.cases ?_ (fun l => ?_) l
    · rfl
    · have hl : l = 0 := Fin.eq_zero l
      subst l
      rfl
  · refine Fin.cases ?_ (fun l => ?_) l
    · have hj : j = 0 := Fin.eq_zero j
      subst j
      rfl
    · have hj : j = 0 := Fin.eq_zero j
      have hl : l = 0 := Fin.eq_zero l
      subst j
      subst l
      change (if i = i then (1 : ℝ) else (E^2-d)/((d : ℝ)*(d-1))) = 1
      exact if_pos rfl

theorem physicalEdgeRow_gram (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (hE : ∀ a, |energy a| < d) (i : Fin d) (j l : Fin k × Fin 2) :
    @inner ℝ (ColoredStar d k) _ (physicalEdgeRow d k hd energy i j) (physicalEdgeRow d k hd energy i l) =
      colorBlock (fun a => edgeWaveCovariance d (energy a)) j l := by
  rw [physicalEdgeRow, physicalEdgeRow, coloredPhysicalRow_gram d k hd energy hE,
    starWaveCovariance_edge d hd]
  by_cases h : j.1 = l.1 <;> simp [colorBlock, h]

def edgeObservationBasis (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    OrthonormalBasis (coloredObserved d k hd i) ℝ (coloredEdgeSpace d k hd i) :=
  retainedObservationBasis (scalarAdaptedBasis d k) (coloredEdgeSpace d k hd i)

def edgeObservationCoefficients (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ) (i : Fin d) :
    Matrix (Fin k × Fin 2) (coloredObserved d k hd i) ℝ :=
  fun j a => (edgeObservationBasis d k hd i).repr (physicalEdgeRowInSpace d k hd energy i j) a

theorem edgeObservationCoefficients_gram (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (hE : ∀ a, |energy a| < d) (i : Fin d) :
    edgeObservationCoefficients d k hd energy i * (edgeObservationCoefficients d k hd energy i).transpose =
      colorBlock (fun a => edgeWaveCovariance d (energy a)) := by
  ext j l
  change (∑ a, (edgeObservationBasis d k hd i).repr (physicalEdgeRowInSpace d k hd energy i j) a *
    (edgeObservationBasis d k hd i).repr (physicalEdgeRowInSpace d k hd energy i l) a) = _
  rw [orthonormalCoordinates_dot]
  exact physicalEdgeRow_gram d k hd energy hE i j l

def edgeInputEquiv (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    (Fin k × Fin 2) ≃ coloredObserved d k hd i :=
  Fintype.equivOfCardEq (by rw [card_coloredObserved]; simp; omega)

def edgePhysicalFactor (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ) (i : Fin d) :
    Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℝ :=
  (edgeObservationCoefficients d k hd energy i).submatrix id (edgeInputEquiv d k hd i)

theorem edgePhysicalFactor_covariance (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (hE : ∀ a, |energy a| < d) (i : Fin d) :
    edgePhysicalFactor d k hd energy i * (edgePhysicalFactor d k hd energy i).transpose =
      colorBlock (fun a => edgeWaveCovariance d (energy a)) := by
  unfold edgePhysicalFactor
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id,
    edgeObservationCoefficients_gram d k hd energy hE]

theorem edgeWaveCovariance_posDef (d : ℕ) (hd : 0 < d) (E : ℝ) (hE : |E| < d) :
    (edgeWaveCovariance d E).PosDef := by
  have hp : 0 < 1 - |E / (d : ℝ)| := by
    have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
    have h : |E / (d : ℝ)| < 1 := by
      rw [abs_div, abs_of_pos hdR, div_lt_one hdR]
      exact hE
    linarith
  apply posDef_of_quadratic_lower _ _ _ hp (edgeWaveCovariance_quadratic_floor d E)
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  ext j l
  fin_cases j <;> fin_cases l <;> rfl

theorem edgePhysicalFactor_det_ne_zero (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (hE : ∀ a, |energy a| < d) (i : Fin d) : (edgePhysicalFactor d k hd energy i).det ≠ 0 := by
  have hh := (colorBlock_posDef (fun a => edgeWaveCovariance d (energy a))
    (fun a => edgeWaveCovariance_posDef d (by omega) _ (hE a))).det_pos
  rw [← edgePhysicalFactor_covariance d k hd energy hE i, Matrix.det_mul, Matrix.det_transpose] at hh
  intro hz
  simp only [hz, zero_mul, lt_self_iff_false] at hh

theorem edgePhysicalFactor_logabsdet (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (hE : ∀ a, |energy a| < d) (i : Fin d) :
    Real.log (|(edgePhysicalFactor d k hd energy i).det|) =
      ∑ a, Real.log ((edgeWaveCovariance d (energy a)).det) / 2 := by
  have hh := congrArg (fun A : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℝ => Real.log A.det)
    (edgePhysicalFactor_covariance d k hd energy hE i)
  change Real.log ((edgePhysicalFactor d k hd energy i * (edgePhysicalFactor d k hd energy i).transpose).det) =
    Real.log ((colorBlock (fun a => edgeWaveCovariance d (energy a))).det) at hh
  rw [Matrix.det_mul, Matrix.det_transpose, ← sq, Real.log_pow,
    colorBlock_eq_blockDiagonal, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal,
    Real.log_prod _ _ (fun a _ => (edgeWaveCovariance_posDef d (by omega) _ (hE a)).det_pos.ne')] at hh
  rw [Real.log_abs, ← Finset.sum_div]
  norm_num at hh
  linarith

theorem edgeObservationCoefficients_action (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (i : Fin d) (x : ColoredStar d k) :
    (edgeObservationCoefficients d k hd energy i).mulVec
      (fun a : coloredObserved d k hd i =>
        ((coloredObservationMatrix d k hd i).transpose.mulVec (scalarCoordinates d k x)) a) =
      fun j => @inner ℝ (ColoredStar d k) _ (physicalEdgeRow d k hd energy i j) x := by
  ext j
  have hc (a : coloredObserved d k hd i) :
      ((coloredObservationMatrix d k hd i).transpose.mulVec (scalarCoordinates d k x)) a =
        (observationBasis (scalarAdaptedBasis d k) (coloredEdgeSpace d k hd i)).repr x a := by
    exact congrFun (observationMatrix_transpose_repr (scalarAdaptedBasis d k)
      (coloredEdgeSpace d k hd i) x) a
  change (∑ a, (edgeObservationBasis d k hd i).repr (physicalEdgeRowInSpace d k hd energy i j) a *
    ((coloredObservationMatrix d k hd i).transpose.mulVec (scalarCoordinates d k x)) a) = _
  simp_rw [hc]
  have hh := congrArg (fun y : coloredEdgeSpace d k hd i =>
      @inner ℝ (ColoredStar d k) _ (y : ColoredStar d k) x)
    ((edgeObservationBasis d k hd i).sum_repr (physicalEdgeRowInSpace d k hd energy i j))
  simp only [Submodule.coe_sum, Submodule.coe_smul, sum_inner, real_inner_smul_left] at hh
  have hb (a : coloredObserved d k hd i) :
      @inner ℝ (ColoredStar d k) _ ((edgeObservationBasis d k hd i a : coloredEdgeSpace d k hd i) : ColoredStar d k) x =
        (observationBasis (scalarAdaptedBasis d k) (coloredEdgeSpace d k hd i)).repr x a := by
    have he := retainedObservationBasis_apply (scalarAdaptedBasis d k) (coloredEdgeSpace d k hd i) a
    change ((edgeObservationBasis d k hd i a : coloredEdgeSpace d k hd i) : ColoredStar d k) = _ at he
    rw [he, OrthonormalBasis.repr_apply_apply]
  simp_rw [hb] at hh
  exact hh

end GeneralizedBulk.Gaussian
