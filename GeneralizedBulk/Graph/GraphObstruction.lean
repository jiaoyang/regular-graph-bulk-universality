import GeneralizedBulk.Graph.FiniteObstruction
import GeneralizedBulk.Graph.SwitchTraceBound

/-!
# The large-scalar obstruction for the actual accepted graph switch

Boundary invertibility follows from the genuine finite Schur complement.
The compression shift and rank-sensitive scalar bound are then discharged
for the concrete accepted/rejected switching involution.
-/
noncomputable section
open scoped BigOperators Classical
namespace GeneralizedBulk.Graph
open GeneralizedSwitching Exterior External.RegularSpectralData
attribute [local instance] outsideFintype

/-- Every injectively selected compression of a nonreal Hermitian resolvent
is invertible. This follows from its actual Schur representation. -/
theorem boundary_resolvent_isUnit
    {V m : Type*} [Fintype V] [Fintype m] [DecidableEq V] [DecidableEq m]
    (H : Matrix V V ℂ) (hH : H.IsHermitian) (e : m → V) (he : Function.Injective e)
    (z : ℂ) (hz : z.im ≠ 0) :
    IsUnit (((H - z • (1 : Matrix V V ℂ))⁻¹).submatrix e e) := by
  let q := boundaryEquiv e he
  let A := H.submatrix e e
  let B := H.submatrix e (fun v : Outside e => (v : V))
  let C := H.submatrix (fun v : Outside e => (v : V)) e
  let D := H.submatrix (fun v : Outside e => (v : V)) (fun v : Outside e => (v : V))
  have hblocks : (Matrix.fromBlocks A B C D).IsHermitian := by
    rw [show Matrix.fromBlocks A B C D = H.submatrix q q from (boundary_reindex H e he).symm]
    exact hH.submatrix q
  have hD : D.IsHermitian := hH.submatrix (fun v : Outside e => (v : V))
  have hminor := hermitian_shift_isUnit D hD z hz
  have hschur := shifted_schurComplement_isUnit A B C D hblocks z hz
  have hb : ((Matrix.fromBlocks (A - z • 1) B C (D - z • 1))⁻¹).submatrix Sum.inl Sum.inl =
      ((H - z • (1 : Matrix V V ℂ))⁻¹).submatrix e e := by
    rw [← boundary_reindex_shift_inverse H e he z]
    ext a b
    rfl
  rw [← hb, inverse_boundary_eq_schurInverse _ _ _ _ hminor hschur]
  exact Matrix.isUnit_nonsing_inv_iff.mpr hschur

/-- The inverse-free compression identity is a theorem about the literal
resolvents of the switched and original finite graph. -/
theorem graphBoundary_compression_shift
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (e : Fin 4 → V) (he : Function.Injective e) (h : Alternating G e)
    (z : ℂ) (hz : z.im ≠ 0) :
    (1 + graphBoundary G e z * switchIncrement) *
      (endpointPermutation * graphBoundary (switchGraph G e) (e ∘ swapPartners) z * endpointPermutation) =
        graphBoundary G e z := by
  let M := graphBoundary G e z
  let Mnew := graphBoundary (switchGraph G e) e z
  have hM : IsUnit M := boundary_resolvent_isUnit (G.adjMatrix ℂ) (graphAdjacency_isHermitian G) e he z hz
  have hMnew : IsUnit Mnew := boundary_resolvent_isUnit ((switchGraph G e).adjMatrix ℂ)
    (graphAdjacency_isHermitian (switchGraph G e)) e he z hz
  have hk := graphExteriorMatrix_switch G e he h z hz
  change edgeMatrix - Mnew⁻¹ = (edgeMatrix - M⁻¹) - switchIncrement at hk
  have hi : Mnew⁻¹ = M⁻¹ + switchIncrement := by
    apply sub_eq_zero.mp
    calc
      _ = -((edgeMatrix - Mnew⁻¹) - ((edgeMatrix - M⁻¹) - switchIncrement)) := by abel
      _ = 0 := by rw [hk, sub_self, neg_zero]
  have hperm : endpointPermutation * graphBoundary (switchGraph G e) (e ∘ swapPartners) z *
      (endpointPermutation : Mat) = Mnew := by
    rw [graphBoundary_swap, endpointPermutation_transpose]
    calc
      _ = (endpointPermutation * endpointPermutation) * Mnew * (endpointPermutation * endpointPermutation) := by
        simp only [Matrix.mul_assoc, Mnew]
      _ = Mnew := by rw [endpointPermutation_sq]; simp
  rw [hperm]
  change (1 + M * switchIncrement) * Mnew = M
  have hcancelM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det _).mp hM)
  have hcancelNew : Mnew⁻¹ * Mnew = 1 :=
    Matrix.nonsing_inv_mul Mnew ((Matrix.isUnit_iff_isUnit_det _).mp hMnew)
  calc
    _ = (M * (M⁻¹ + switchIncrement)) * Mnew := by rw [Matrix.mul_add, hcancelM]
    _ = (M * Mnew⁻¹) * Mnew := by rw [hi]
    _ = M := by rw [Matrix.mul_assoc, hcancelNew, mul_one]

/-- The exact identity on the actual accepted finite proposal involution. -/
theorem proposalSwitch_compression_shift {N d : ℕ} (s : EdgePairState N d) (hs : Accepted s)
    (z : ℂ) (hz : z.im ≠ 0) :
    (1 + graphBoundary s.val.1 s.val.2 z * switchIncrement) *
      (endpointPermutation * graphBoundary (proposalSwitch s).val.1 (proposalSwitch s).val.2 z *
        endpointPermutation) = graphBoundary s.val.1 s.val.2 z := by
  rw [proposalSwitch, dif_pos hs]
  exact graphBoundary_compression_shift s.val.1 s.val.2 hs.1 (accepted_alternating s hs) z hz

def graphNormalizedScalar {N : ℕ} (G : SimpleGraph (Fin N)) (z : ℂ) : ℂ :=
  (N : ℂ)⁻¹ * Matrix.trace (graphResolvent G z)

/-- A lower bound on `N eta` yields the scalar shift used by the recursion.
The constant four comes from the internally proved rank-two trace estimate. -/
theorem graphNormalizedScalar_proposalSwitch_bound {N d : ℕ} (hN : 0 < N)
    (s : EdgePairState N d) (E eta cstar : ℝ) (heta : 0 < eta) (hcstar : 0 < cstar)
    (hheight : cstar ≤ (N : ℝ) * eta) :
    ‖graphNormalizedScalar (proposalSwitch s).val.1 (spectralParameter E eta) -
      graphNormalizedScalar s.val.1 (spectralParameter E eta)‖ ≤ 4 / cstar := by
  have htrace := proposalSwitch_trace_bound s (spectralParameter E eta) (by simpa using heta.ne')
  simp only [spectralParameter_im, abs_of_pos heta] at htrace
  rw [graphNormalizedScalar, graphNormalizedScalar, ← mul_sub, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (N : ℝ)⁻¹ * (4 / eta) := mul_le_mul_of_nonneg_left htrace (by positivity)
    _ = 4 / ((N : ℝ) * eta) := by ring
    _ ≤ 4 / cstar := div_le_div_of_nonneg_left (by norm_num) hcstar hheight

/-- There are uniform constants forcing a forward or reverse entry failure
on every large-scalar accepted proposal. No inverse or matrix relation is an
assumption here: they are proved from the actual finite graph switch. -/
theorem exists_graph_large_scalar_obstruction (d : ℕ) (hd : 0 < d)
    (E : ℝ) (hE : |E| < d) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∃ T0 : ℝ, 1 ≤ T0 ∧
      ∀ N : ℕ, 0 < N → ∀ eta : ℝ, 0 < eta → eta ≤ 1 → cstar ≤ (N : ℝ) * eta →
        ∀ s : EdgePairState N d, Accepted s →
          T0 ≤ ‖graphNormalizedScalar s.val.1 (spectralParameter E eta)‖ →
          ¬ (EntryBound (graphBoundary s.val.1 s.val.2 (spectralParameter E eta) -
              finiteMean N d (spectralParameter E eta) (graphNormalizedScalar s.val.1 (spectralParameter E eta)))
                (delta * ‖graphNormalizedScalar s.val.1 (spectralParameter E eta)‖) ∧
            EntryBound (graphBoundary (proposalSwitch s).val.1 (proposalSwitch s).val.2 (spectralParameter E eta) -
              finiteMean N d (spectralParameter E eta)
                (graphNormalizedScalar (proposalSwitch s).val.1 (spectralParameter E eta)))
                  (delta * ‖graphNormalizedScalar (proposalSwitch s).val.1 (spectralParameter E eta)‖)) := by
  obtain ⟨delta, hdelta, hdeltaup, T0, hT0, hobstruct⟩ :=
    exists_finiteMean_large_scalar_obstruction d hd E hE (4 / cstar) (by positivity)
  refine ⟨delta, hdelta, hdeltaup, T0, hT0, ?_⟩
  intro N hN eta heta hetaup hheight s hs hlarge
  apply hobstruct N hN eta (by simpa only [abs_of_pos heta] using hetaup) _ _ hlarge
    (graphNormalizedScalar_proposalSwitch_bound hN s E eta cstar heta hcstar hheight)
  exact proposalSwitch_compression_shift s hs _ (by simpa using heta.ne')

end GeneralizedBulk.Graph
