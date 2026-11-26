import GeneralizedBulk.Exterior.Positivity

/-!
# Entrywise matrix calculus for the exterior resolvent

This uses the usual finite-product topology on matrices. Differentiability of
inverse is obtained from the determinant/adjugate formula; its derivative is
then solved from the differentiated inverse identity.
-/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace GeneralizedBulk.Exterior

/-- Constant matrices have zero derivative entry by entry. -/
theorem hasDerivAt_matrix_const (K : Mat) (z : ℂ) :
    HasDerivAt (fun _ : ℂ => K) (0 : Mat) z := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact hasDerivAt_const z (K i j)

/-- Matrix multiplication differentiates by the usual ordered product rule. -/
theorem hasDerivAt_matrix_mul {f g : ℂ → Mat} {f' g' : Mat} {z : ℂ}
    (hf : HasDerivAt f f' z) (hg : HasDerivAt g g' z) :
    HasDerivAt (fun u => f u * g u) (f' * g z + f z * g') z := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h := HasDerivAt.sum (u := Finset.univ) (fun k _ =>
    ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i)) k).mul
      ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hg k)) j))
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib] using h

theorem hasDerivAt_matrix_transpose {f : ℂ → Mat} {f' : Mat} {z : ℂ}
    (hf : HasDerivAt f f' z) :
    HasDerivAt (fun u => (f u).transpose) f'.transpose z := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hf j)) i

theorem hasDerivAt_matrix_sub {f g : ℂ → Mat} {f' g' : Mat} {z : ℂ}
    (hf : HasDerivAt f f' z) (hg : HasDerivAt g g' z) :
    HasDerivAt (fun u => f u - g u) (f' - g') z := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i)) j).sub
    ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hg i)) j)

/-- Determinant is a finite polynomial in the matrix entries. -/
theorem differentiableAt_matrix_det {f : ℂ → Mat} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) : DifferentiableAt ℂ (fun u => (f u).det) z := by
  simp_rw [Matrix.det_apply']
  apply DifferentiableAt.sum
  intro σ _
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.finset_prod
  intro i _
  exact differentiableAt_pi.mp (differentiableAt_pi.mp hf (σ i)) i

/-- Adjugate is likewise a finite polynomial in entries, including replaced rows. -/
theorem differentiableAt_matrix_adjugate {f : ℂ → Mat} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) : DifferentiableAt ℂ (fun u => (f u).adjugate) z := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  simp_rw [Matrix.adjugate_apply]
  apply differentiableAt_matrix_det
  apply differentiableAt_pi.mpr
  intro a
  apply differentiableAt_pi.mpr
  intro b
  by_cases ha : a = j
  · simp only [Matrix.updateRow_apply, ha, ↓reduceIte]
    exact differentiableAt_const _
  · simp only [Matrix.updateRow_apply, ha, ↓reduceIte]
    exact differentiableAt_pi.mp (differentiableAt_pi.mp hf a) b

/-- At a genuine unit, the determinant/adjugate inverse is differentiable. -/
theorem differentiableAt_matrix_inverse {f : ℂ → Mat} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hu : IsUnit (f z)) :
    DifferentiableAt ℂ (fun u => (f u)⁻¹) z := by
  have hd : (f z).det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have hdet := (differentiableAt_matrix_det hf).inv hd
  have hadj := differentiableAt_matrix_adjugate hf
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  exact hdet.mul (differentiableAt_pi.mp (differentiableAt_pi.mp hadj i) j)

/-- The inverse derivative is proved by differentiating the inverse identity,
with the order of the three matrix factors retained. -/
theorem hasDerivAt_matrix_inverse {f : ℂ → Mat} {f' : Mat} {z : ℂ}
    (hf : HasDerivAt f f' z) (hu : IsUnit (f z)) :
    HasDerivAt (fun u => (f u)⁻¹) (-((f z)⁻¹ * f' * (f z)⁻¹)) z := by
  let inverseDerivative : Mat := fun i j => deriv (fun u : ℂ => (f u)⁻¹ i j) z
  have hfDiff : DifferentiableAt ℂ f z := by
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i)) j).differentiableAt
  have hdiff := differentiableAt_matrix_inverse hfDiff hu
  have hi : HasDerivAt (fun u : ℂ => (f u)⁻¹) inverseDerivative z := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    exact (differentiableAt_pi.mp (differentiableAt_pi.mp hdiff i) j).hasDerivAt
  have hdet : IsUnit (f z).det := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have hd0 : (f z).det ≠ 0 := isUnit_iff_ne_zero.mp hdet
  have hevent : ∀ᶠ u in 𝓝 z, (f u).det ≠ 0 :=
    (differentiableAt_matrix_det hfDiff).continuousAt.tendsto.eventually
      (eventually_ne_nhds hd0)
  have hconst : HasDerivAt (fun u => (f u)⁻¹ * f u) (0 : Mat) z := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    apply (hasDerivAt_const z ((1 : Mat) i j)).congr_of_eventuallyEq
    filter_upwards [hevent] with u hu
    exact congrArg (fun A : Mat => A i j)
      (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hu))
  have heq : inverseDerivative * f z + (f z)⁻¹ * f' = 0 := by
    ext i j
    exact ((hasDerivAt_pi.mp (hasDerivAt_pi.mp
      (hasDerivAt_matrix_mul hi hf) i)) j).unique
        ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hconst i)) j)
  have heq' := congrArg (fun A : Mat => A * (f z)⁻¹) heq
  simp only [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet,
    mul_one, zero_mul] at heq'
  have hderiv : inverseDerivative = -((f z)⁻¹ * f' * (f z)⁻¹) := by
    simpa only [Matrix.mul_assoc] using eq_neg_of_add_eq_zero_left heq'
  rwa [hderiv] at hi

end GeneralizedBulk.Exterior
