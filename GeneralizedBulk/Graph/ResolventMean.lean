import GeneralizedBulk.Graph.Resolvent
import GeneralizedBulk.Graph.StarCovariance
import GeneralizedBulk.Graph.UniformSwitching
import GeneralizedBulk.MatrixGeometry

/-!
# Exact conditional mean of the two-edge compressed finite resolvent

The two oriented edges are sampled independently before any acceptance test.
Their uniform root and neighbor enumerations give the exact finite proposal
mean, including the deterministic `J/d` background and constant-mode term.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Graph

def complexAverage {A : Type*} [Fintype A] (f : A → ℂ) : ℂ :=
  (Fintype.card A : ℂ)⁻¹ * ∑ a, f a

theorem complexAverage_const {A : Type*} [Fintype A] [Nonempty A] (c : ℂ) :
    complexAverage (fun _ : A => c) = c := by
  have h : (Fintype.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [complexAverage, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]

theorem complexAverage_const_mul {A : Type*} [Fintype A] (c : ℂ) (f : A → ℂ) :
    complexAverage (fun a => c * f a) = c * complexAverage f := by
  simp only [complexAverage, ← Finset.mul_sum]
  ring

theorem complexAverage_prod {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℂ) :
    complexAverage f = complexAverage (fun a => complexAverage (fun b => f (a, b))) := by
  simp only [complexAverage, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    ← Finset.mul_sum, mul_inv_rev]
  ring

theorem complexAverage_prod_left {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (f : A → ℂ) : complexAverage (fun p : A × B => f p.1) = complexAverage f := by
  rw [complexAverage_prod]
  simp only [complexAverage_const]

theorem complexAverage_prod_right {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (f : B → ℂ) : complexAverage (fun p : A × B => f p.2) = complexAverage f := by
  rw [complexAverage_prod]
  change complexAverage (fun _ : A => complexAverage f) = complexAverage f
  exact complexAverage_const (A := A) _

/-- The finite average is the literal expectation under the finite uniform law. -/
theorem integral_finiteUniform_complex {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (f : A → ℂ) :
    (∫ a, f a ∂finiteUniform A) = complexAverage f := by
  rw [finiteUniform, integral_smul_measure,
    integral_finset_sum_measure (fun _ _ => integrable_dirac)]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Complex.real_smul, complexAverage, Complex.ofReal_inv, Complex.ofReal_natCast]

def uniformOrientedProposals (N d : ℕ) : Measure ((Fin N × Fin d) × (Fin N × Fin d)) :=
  finiteUniform _

theorem uniformOrientedProposals_isProbability (N d : ℕ) (hN : 0 < N) (hd : 0 < d) :
    IsProbabilityMeasure (uniformOrientedProposals N d) := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact finiteUniform_isProbability _

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem sum_neighbor_complex (v : Fin (N n)) (f : Fin (N n) → ℂ) :
    (∑ j : Fin d, f (D.neighbor n ω v j)) =
      ∑ w, (D.adjacency n ω v w : ℂ) * f w := by
  apply Complex.ext
  · simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero] using D.sum_neighbor n ω v (fun w => (f w).re)
  · simpa only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
      zero_mul, add_zero] using D.sum_neighbor n ω v (fun w => (f w).im)

theorem sum_neighbor_global_complex (f : Fin (N n) → ℂ) :
    (∑ v, ∑ j : Fin d, f (D.neighbor n ω v j)) = (d : ℂ) * ∑ w, f w := by
  apply Complex.ext
  · simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero] using D.sum_neighbor_global n ω (fun w => (f w).re)
  · simpa only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
      zero_mul, add_zero] using D.sum_neighbor_global n ω (fun w => (f w).im)

/-- The regular constant mode makes every row sum of the genuine resolvent
exactly `(d-z)⁻¹`, with no asymptotic approximation. -/
theorem resolvent_row_sum (z : ℂ) (hz : z.im ≠ 0) (v : Fin (N n)) :
    (∑ w, D.resolvent n ω z v w) = ((d : ℂ) - z)⁻¹ := by
  let A := (D.adjacency n ω).map Complex.ofReal - z • (1 : Matrix (Fin (N n)) _ ℂ)
  let u : Fin (N n) → ℂ := fun _ => 1
  have hAu : A.mulVec u = ((d : ℂ) - z) • u := by
    ext i
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
    change (∑ w, (D.adjacency n ω i w : ℂ) * 1) - z * 1 = ((d : ℂ) - z) * 1
    simp only [mul_one, ← Complex.ofReal_sum, D.regular n ω, Complex.ofReal_natCast]
  have hu : D.resolvent n ω z * A = 1 :=
    Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det _).mp (D.shifted_adjacency_isUnit n ω z hz))
  have h := congrArg (fun M => M.mulVec u) hu
  change (D.resolvent n ω z * A).mulVec u = (1 : Matrix (Fin (N n)) _ ℂ).mulVec u at h
  rw [← Matrix.mulVec_mulVec, hAu, Matrix.mulVec_smul, Matrix.one_mulVec] at h
  have hv := congrFun h v
  change (((d : ℂ) - z) * ∑ w, D.resolvent n ω z v w * 1) = 1 at hv
  simp only [mul_one] at hv
  have hdz : (d : ℂ) - z ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.natCast_im, Complex.zero_im, zero_sub, neg_eq_zero] at hi
    exact hz hi
  apply mul_left_cancel₀ hdz
  rw [mul_inv_cancel₀ hdz]
  exact hv

/-- The trace relation retains the exact finite deterministic background. -/
theorem adjacency_mul_resolvent (z : ℂ) (hz : z.im ≠ 0) :
    (D.adjacency n ω).map Complex.ofReal * D.resolvent n ω z =
      1 + z • D.resolvent n ω z := by
  have h := Matrix.mul_nonsing_inv
    ((D.adjacency n ω).map Complex.ofReal - z • (1 : Matrix (Fin (N n)) _ ℂ))
    ((Matrix.isUnit_iff_isUnit_det _).mp (D.shifted_adjacency_isUnit n ω z hz))
  change ((D.adjacency n ω).map Complex.ofReal - z • (1 : Matrix (Fin (N n)) _ ℂ)) *
    D.resolvent n ω z = 1 at h
  rw [Matrix.sub_mul, Matrix.smul_mul, one_mul] at h
  exact sub_eq_iff_eq_add.mp h

/-- Uniform oriented-edge summation of a resolvent entry. -/
theorem sum_resolvent_oriented_edges (z : ℂ) (hz : z.im ≠ 0) :
    (∑ v, ∑ j : Fin d, D.resolvent n ω z v (D.neighbor n ω v j)) =
      (N n : ℂ) + z * Matrix.trace (D.resolvent n ω z) := by
  have hs : (∑ v, ∑ j : Fin d, D.resolvent n ω z v (D.neighbor n ω v j)) =
      Matrix.trace ((D.adjacency n ω).map Complex.ofReal * D.resolvent n ω z) := by
    simp only [Matrix.trace, Matrix.mul_apply, Matrix.map_apply]
    apply Finset.sum_congr rfl
    intro v hv
    rw [D.sum_neighbor_complex n ω v]
    apply Finset.sum_congr rfl
    intro w hw
    have hsym : D.resolvent n ω z v w = D.resolvent n ω z w v :=
      congrFun (congrFun (D.resolvent_transpose n ω z hz) w) v
    rw [hsym]
    rfl
  rw [hs, D.adjacency_mul_resolvent n ω z hz, Matrix.trace_add,
    Matrix.trace_one, Fintype.card_fin, Matrix.trace_smul, smul_eq_mul]

/-- One uniform oriented edge, sampled by its uniform root and neighbor index. -/
def proposalEndpoint (a : Fin (N n) × Fin d) : Fin 2 → Fin (N n) :=
  ![a.1, D.neighbor n ω a.1 a.2]

/-- Two independent edge proposals, before acceptance or rejection. -/
def proposalEndpoints (s : (Fin (N n) × Fin d) × (Fin (N n) × Fin d)) : Fin 4 → Fin (N n) :=
  ![s.1.1, D.neighbor n ω s.1.1 s.1.2, s.2.1, D.neighbor n ω s.2.1 s.2.2]

def proposalMean (z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := fun i j =>
  complexAverage (fun s : (Fin (N n) × Fin d) × (Fin (N n) × Fin d) =>
    D.resolvent n ω z (D.proposalEndpoints n ω s i) (D.proposalEndpoints n ω s j))

/-- Either endpoint of the uniform oriented edge is exactly uniform on vertices. -/
theorem proposalEndpoint_average (hd : 0 < d) (f : Fin (N n) → ℂ) (i : Fin 2) :
    complexAverage (fun a : Fin (N n) × Fin d => f (D.proposalEndpoint n ω a i)) =
      (N n : ℂ)⁻¹ * ∑ v, f v := by
  have hN : (N n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n))
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  fin_cases i
  · simp only [complexAverage, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
      Fintype.sum_prod_type]
    change ((N n : ℂ) * (d : ℂ))⁻¹ * (∑ v, ∑ _ : Fin d, f v) = _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    field_simp
    ring
  · simp only [complexAverage, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
      Fintype.sum_prod_type]
    change ((N n : ℂ) * (d : ℂ))⁻¹ *
      (∑ v, ∑ j, f (D.neighbor n ω v j)) = _
    rw [D.sum_neighbor_global_complex n ω f]
    field_simp
    ring

theorem proposalEndpoint_diagonal_resolvent (hd : 0 < d) (z : ℂ) (i : Fin 2) :
    complexAverage (fun a : Fin (N n) × Fin d =>
      D.resolvent n ω z (D.proposalEndpoint n ω a i) (D.proposalEndpoint n ω a i)) =
        D.scalarResolvent n ω z := by
  simpa only [scalarResolvent, Matrix.trace] using
    D.proposalEndpoint_average n ω hd (fun v => D.resolvent n ω z v v) i

/-- The within-edge resolvent mean includes the exact background `1/d`. -/
theorem proposalEndpoint_edge_resolvent (hd : 0 < d) (z : ℂ) (hz : z.im ≠ 0) :
    complexAverage (fun a : Fin (N n) × Fin d =>
      D.resolvent n ω z (D.proposalEndpoint n ω a 0) (D.proposalEndpoint n ω a 1)) =
        (z * D.scalarResolvent n ω z + 1) / (d : ℂ) := by
  have hN : (N n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n))
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  simp only [complexAverage, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
    Fintype.sum_prod_type, proposalEndpoint, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [D.sum_resolvent_oriented_edges n ω z hz]
  simp only [scalarResolvent]
  field_simp
  ring

theorem proposalEndpoint_edge_resolvent_reverse (hd : 0 < d) (z : ℂ) (hz : z.im ≠ 0) :
    complexAverage (fun a : Fin (N n) × Fin d =>
      D.resolvent n ω z (D.proposalEndpoint n ω a 1) (D.proposalEndpoint n ω a 0)) =
        (z * D.scalarResolvent n ω z + 1) / (d : ℂ) := by
  have he : (fun a : Fin (N n) × Fin d =>
      D.resolvent n ω z (D.proposalEndpoint n ω a 1) (D.proposalEndpoint n ω a 0)) =
    (fun a : Fin (N n) × Fin d =>
      D.resolvent n ω z (D.proposalEndpoint n ω a 0) (D.proposalEndpoint n ω a 1)) := by
    funext a
    exact congrFun (congrFun (D.resolvent_transpose n ω z hz) _ ) _
  rw [he]
  exact D.proposalEndpoint_edge_resolvent n ω hd z hz

/-- Independent edge proposals retain the exact finite constant-mode term. -/
theorem proposalEndpoint_cross_resolvent (hd : 0 < d) (z : ℂ) (hz : z.im ≠ 0) (i j : Fin 2) :
    complexAverage (fun s : (Fin (N n) × Fin d) × (Fin (N n) × Fin d) =>
      D.resolvent n ω z (D.proposalEndpoint n ω s.1 i) (D.proposalEndpoint n ω s.2 j)) =
        ((N n : ℂ) * ((d : ℂ) - z))⁻¹ := by
  letI : Nonempty (Fin (N n) × Fin d) := ⟨⟨⟨0, D.size_pos n⟩, ⟨0, hd⟩⟩⟩
  rw [complexAverage_prod]
  simp_rw [D.proposalEndpoint_average n ω hd]
  simp_rw [D.resolvent_row_sum n ω z hz]
  rw [complexAverage_const]
  simp only [mul_inv_rev]
  ring

theorem proposalEndpoint_cross_resolvent_reverse (hd : 0 < d) (z : ℂ) (hz : z.im ≠ 0) (i j : Fin 2) :
    complexAverage (fun s : (Fin (N n) × Fin d) × (Fin (N n) × Fin d) =>
      D.resolvent n ω z (D.proposalEndpoint n ω s.2 j) (D.proposalEndpoint n ω s.1 i)) =
        ((N n : ℂ) * ((d : ℂ) - z))⁻¹ := by
  have he : (fun s : (Fin (N n) × Fin d) × (Fin (N n) × Fin d) =>
      D.resolvent n ω z (D.proposalEndpoint n ω s.2 j) (D.proposalEndpoint n ω s.1 i)) =
    (fun s : (Fin (N n) × Fin d) × (Fin (N n) × Fin d) =>
      D.resolvent n ω z (D.proposalEndpoint n ω s.1 i) (D.proposalEndpoint n ω s.2 j)) := by
    funext s
    exact congrFun (congrFun (D.resolvent_transpose n ω z hz) _ ) _
  rw [he]
  exact D.proposalEndpoint_cross_resolvent n ω hd z hz i j

/-- Every entry of `proposalMean` is the actual conditional expectation under
uniform independent oriented-edge proposals, before acceptance. -/
theorem proposalMean_integral_entry (hd : 0 < d) (z : ℂ) (i j : Fin 4) :
    (∫ s, D.resolvent n ω z (D.proposalEndpoints n ω s i) (D.proposalEndpoints n ω s j)
      ∂uniformOrientedProposals (N n) d) = D.proposalMean n ω z i j := by
  letI : Nonempty (Fin (N n) × Fin d) := ⟨⟨⟨0, D.size_pos n⟩, ⟨0, hd⟩⟩⟩
  exact integral_finiteUniform_complex _

/-- Measurability of the genuine finite resolvent follows directly from its
proved spectral expansion and the measurable input eigenpairs. -/
theorem measurable_resolvent_entry (z : ℂ) (hz : z.im ≠ 0) (v w : Fin (N n)) :
    Measurable (fun η => D.resolvent n η z v w) := by
  have he : (fun η => D.resolvent n η z v w) =
      (fun η => ∑ a, ((D.eigenvalue n η a : ℂ) - z)⁻¹ *
        (D.eigenvector n η a v : ℂ) * (D.eigenvector n η a w : ℂ)) := by
    funext η
    exact D.resolvent_entry n η z hz v w
  rw [he]
  exact Finset.measurable_sum _ (fun a _ =>
    ((((D.measurable_eigenvalue n a).complex_ofReal.sub_const z).inv.mul
      (D.measurable_eigenvector n a v).complex_ofReal).mul
        (D.measurable_eigenvector n a w).complex_ofReal))

/-- The exact mean in the common finite switching-polynomial coordinates.
The rank-one correction is retained; proposals are not conditioned on acceptance. -/
theorem proposalMean_eq_meanMatrix (hd : 0 < d) (z : ℂ) (hz : z.im ≠ 0) :
    D.proposalMean n ω z = GeneralizedSwitching.meanMatrix
      (D.scalarResolvent n ω z - ((N n : ℂ) * ((d : ℂ) - z))⁻¹)
      ((z * D.scalarResolvent n ω z + 1) / (d : ℂ) - ((N n : ℂ) * ((d : ℂ) - z))⁻¹)
      (((N n : ℂ) * ((d : ℂ) - z))⁻¹) := by
  letI : Nonempty (Fin (N n) × Fin d) := ⟨⟨⟨0, D.size_pos n⟩, ⟨0, hd⟩⟩⟩
  let m := D.scalarResolvent n ω z
  let b := (z * m + 1) / (d : ℂ)
  let q := ((N n : ℂ) * ((d : ℂ) - z))⁻¹
  have hdiagA (i : Fin 2) :
      complexAverage (fun s : (Fin (N n) × Fin d) × (Fin (N n) × Fin d) =>
        D.resolvent n ω z (D.proposalEndpoint n ω s.1 i) (D.proposalEndpoint n ω s.1 i)) = m := by
    rw [complexAverage_prod_left (fun a : Fin (N n) × Fin d =>
      D.resolvent n ω z (D.proposalEndpoint n ω a i) (D.proposalEndpoint n ω a i))]
    exact D.proposalEndpoint_diagonal_resolvent n ω hd z i
  have hdiagB (i : Fin 2) :
      complexAverage (fun s : (Fin (N n) × Fin d) × (Fin (N n) × Fin d) =>
        D.resolvent n ω z (D.proposalEndpoint n ω s.2 i) (D.proposalEndpoint n ω s.2 i)) = m := by
    rw [complexAverage_prod_right (fun a : Fin (N n) × Fin d =>
      D.resolvent n ω z (D.proposalEndpoint n ω a i) (D.proposalEndpoint n ω a i))]
    exact D.proposalEndpoint_diagonal_resolvent n ω hd z i
  have hedgeA :
      complexAverage (fun s : (Fin (N n) × Fin d) × (Fin (N n) × Fin d) =>
        D.resolvent n ω z (D.proposalEndpoint n ω s.1 0) (D.proposalEndpoint n ω s.1 1)) = b := by
    rw [complexAverage_prod_left (fun a : Fin (N n) × Fin d =>
      D.resolvent n ω z (D.proposalEndpoint n ω a 0) (D.proposalEndpoint n ω a 1))]
    exact D.proposalEndpoint_edge_resolvent n ω hd z hz
  have hedgeB :
      complexAverage (fun s : (Fin (N n) × Fin d) × (Fin (N n) × Fin d) =>
        D.resolvent n ω z (D.proposalEndpoint n ω s.2 0) (D.proposalEndpoint n ω s.2 1)) = b := by
    rw [complexAverage_prod_right (fun a : Fin (N n) × Fin d =>
      D.resolvent n ω z (D.proposalEndpoint n ω a 0) (D.proposalEndpoint n ω a 1))]
    exact D.proposalEndpoint_edge_resolvent n ω hd z hz
  have hedgeAr :
      complexAverage (fun s : (Fin (N n) × Fin d) × (Fin (N n) × Fin d) =>
        D.resolvent n ω z (D.proposalEndpoint n ω s.1 1) (D.proposalEndpoint n ω s.1 0)) = b := by
    rw [complexAverage_prod_left (fun a : Fin (N n) × Fin d =>
      D.resolvent n ω z (D.proposalEndpoint n ω a 1) (D.proposalEndpoint n ω a 0))]
    exact D.proposalEndpoint_edge_resolvent_reverse n ω hd z hz
  have hedgeBr :
      complexAverage (fun s : (Fin (N n) × Fin d) × (Fin (N n) × Fin d) =>
        D.resolvent n ω z (D.proposalEndpoint n ω s.2 1) (D.proposalEndpoint n ω s.2 0)) = b := by
    rw [complexAverage_prod_right (fun a : Fin (N n) × Fin d =>
      D.resolvent n ω z (D.proposalEndpoint n ω a 1) (D.proposalEndpoint n ω a 0))]
    exact D.proposalEndpoint_edge_resolvent_reverse n ω hd z hz
  change D.proposalMean n ω z = GeneralizedSwitching.meanMatrix (m - q) (b - q) q
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [GeneralizedSwitching.meanMatrix]
  · exact hdiagA 0
  · exact hedgeA
  · exact D.proposalEndpoint_cross_resolvent n ω hd z hz 0 0
  · exact D.proposalEndpoint_cross_resolvent n ω hd z hz 0 1
  · exact hedgeAr
  · exact hdiagA 1
  · exact D.proposalEndpoint_cross_resolvent n ω hd z hz 1 0
  · exact D.proposalEndpoint_cross_resolvent n ω hd z hz 1 1
  · exact D.proposalEndpoint_cross_resolvent_reverse n ω hd z hz 0 0
  · exact D.proposalEndpoint_cross_resolvent_reverse n ω hd z hz 1 0
  · exact hdiagB 0
  · exact hedgeB
  · exact D.proposalEndpoint_cross_resolvent_reverse n ω hd z hz 0 1
  · exact D.proposalEndpoint_cross_resolvent_reverse n ω hd z hz 1 1
  · exact hedgeBr
  · exact hdiagB 1

set_option maxHeartbeats 2000000 in
/-- The manuscript's exact finite conditional mean formula, including its
constant-mode correction. No BS, HY, Gaussian, or accepted-switch input occurs. -/
theorem proposalMean_eq (hd : 0 < d) (z : ℂ) (hz : z.im ≠ 0) :
    D.proposalMean n ω z =
      D.scalarResolvent n ω z • covarianceMatrix (z / (d : ℂ)) +
        (d : ℂ)⁻¹ • GeneralizedSwitching.edgeMatrix +
        (((N n : ℂ) * ((d : ℂ) - z))⁻¹) •
          ((Matrix.of (fun _ _ : Fin 4 => (1 : ℂ))) -
            (1 : Matrix (Fin 4) (Fin 4) ℂ) -
              (GeneralizedSwitching.edgeMatrix : Matrix (Fin 4) (Fin 4) ℂ)) := by
  rw [D.proposalMean_eq_meanMatrix n ω hd z hz]
  ext i j
  rw [covarianceMatrix_eq]
  fin_cases i <;> fin_cases j <;>
    simp [GeneralizedSwitching.meanMatrix, GeneralizedSwitching.edgeMatrix,
      Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, div_eq_mul_inv] <;> ring

end GeneralizedBulk.External.RegularSpectralData
