import GeneralizedBulk.Graph.ResolventNormalIdentities
import GeneralizedBulk.Graph.StarCovariance

/-! Literal local star normal covariance identities for the actual finite
resolvent noise. -/
noncomputable section
open scoped BigOperators Matrix
namespace GeneralizedBulk.External.RegularSpectralData
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def entropyStarVertex (o : Fin (N n)) : Fin (d + 1) → Fin (N n) :=
  Fin.cases o (D.neighbor n ω o)

def entropyStarNormal (E : ℝ) : Fin (d + 1) → ℝ :=
  Fin.cases (-E) (fun _ => 1)

theorem entropyStarNormal_pairing (o : Fin (N n)) (E : ℝ) (f : Fin (N n) → ℝ) :
    (∑ i : Fin (d + 1), entropyStarNormal (d := d) E i * f (D.entropyStarVertex n ω o i)) =
      (D.centeredAdjacency n ω E *ᵥ f) o := by
  rw [Fin.sum_univ_succ]
  simp only [entropyStarNormal, entropyStarVertex, Fin.cases_zero, Fin.cases_succ, one_mul]
  rw [D.sum_neighbor n ω]
  simp only [centeredAdjacency, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  change -E * f o + ∑ w, D.adjacency n ω o w * f w =
    (∑ w, D.adjacency n ω o w * f w) - E * f o
  ring

/-- Cross covariance of the literal normal vector with any vertex. -/
theorem entropyStarNormal_cross_covariance (o v : Fin (N n)) (E eta sigma : ℝ) (heta : 0 < eta) :
    (∑ i : Fin (d + 1), entropyStarNormal (d := d) E i *
      D.resolventCovariance n ω E eta sigma (D.entropyStarVertex n ω o i) v) =
      (eta / sigma) * (D.resolvent n ω (⟨E, eta⟩ : ℂ) o v).re := by
  rw [D.entropyStarNormal_pairing n ω o E (fun a => D.resolventCovariance n ω E eta sigma a v)]
  have hh := congrFun (congrFun (D.centeredAdjacency_mul_covariance n ω E eta sigma) o) v
  simpa only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    D.realResolventPart_entry n ω E eta heta] using hh

/-- The local normal has exactly the deterministic Euclidean length used in
the manuscript's normal rescaling. -/
theorem entropyStarNormal_sq_sum (E : ℝ) :
    (∑ i : Fin (d + 1), entropyStarNormal (d := d) E i ^ 2) = d + E ^ 2 := by
  rw [Fin.sum_univ_succ]
  simp only [entropyStarNormal, Fin.cases_zero, Fin.cases_succ, neg_sq, one_pow,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

theorem centeredAdjacency_transpose (E : ℝ) :
    (D.centeredAdjacency n ω E).transpose = D.centeredAdjacency n ω E := by
  rw [centeredAdjacency, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
  congr 1
  ext v w
  exact D.symmetric n ω w v

/-- The actual quadratic normal variance of the restricted star covariance. -/
theorem entropyStarNormal_quadratic_covariance (o : Fin (N n)) (E eta sigma : ℝ) (heta : 0 < eta) :
    dotProduct (entropyStarNormal (d := d) E)
      ((D.resolventCovariance n ω E eta sigma).submatrix (D.entropyStarVertex n ω o) (D.entropyStarVertex n ω o) *ᵥ
        entropyStarNormal (d := d) E) =
      eta / sigma - eta ^ 2 * D.resolventCovariance n ω E eta sigma o o := by
  let v := D.entropyStarVertex n ω o
  let nn := entropyStarNormal (d := d) E
  let Q := D.resolventCovariance n ω E eta sigma
  let T := D.centeredAdjacency n ω E
  have hin (j : Fin (d + 1)) : (∑ i, nn i * Q (v i) (v j)) = (T * Q) o (v j) :=
    D.entropyStarNormal_pairing n ω o E (fun a => Q a (v j))
  have hsym (a b : Fin (N n)) : T a b = T b a := by
    have hh := congrFun (congrFun (D.centeredAdjacency_transpose n ω E) b) a
    exact hh
  calc
    _ = ∑ j, nn j * (∑ i, nn i * Q (v i) (v j)) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ j, nn j * (T * Q) o (v j) := by simp_rw [hin]
    _ = (T * Q * T) o o := by
      rw [D.entropyStarNormal_pairing n ω o E (fun a => (T * Q) o a)]
      change (∑ a, T o a * (T * Q) o a) = ∑ a, (T * Q) o a * T a o
      apply Finset.sum_congr rfl
      intro a ha
      rw [hsym o a, mul_comm]
    _ = _ := by
      have hh := congrFun (congrFun (D.centeredAdjacency_covariance_centeredAdjacency n ω E eta sigma heta) o) o
      simpa only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] using hh

end GeneralizedBulk.External.RegularSpectralData
