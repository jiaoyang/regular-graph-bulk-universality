import GeneralizedBulk.Entropy.SignalChaosPairing

/-! Actual Gaussian fourth Wick tests along arbitrary unit linear directions. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite
variable {I : Type*} [Fintype I] [DecidableEq I]

@[simp] theorem multiHermite_single (i : I) (n : ℕ) (x : I → ℝ) :
    multiHermite I (Pi.single i n) x = (hermite n).eval (x i) := by
  classical
  unfold multiHermite
  rw [Finset.prod_eq_single i]
  · simp only [Pi.single_eq_same]
  · intro j hj hji
    simp only [Pi.single_eq_of_ne hji, hermite_zero, Polynomial.eval_one]
  · simp

@[simp] theorem multiFactorial_single (i : I) (n : ℕ) :
    multiFactorial I (Pi.single i n) = (n.factorial : ℝ) := by
  classical
  unfold multiFactorial
  rw [Finset.prod_eq_single i]
  · simp only [Pi.single_eq_same]
  · intro j hj hji
    simp only [Pi.single_eq_of_ne hji, Nat.factorial_zero, Nat.cast_one]
  · simp

theorem hermite_four_eval (x : ℝ) : (hermite 4).eval x = x ^ 4 - 6 * x ^ 2 + 3 := by
  norm_num [hermite, Polynomial.derivative_mul, Polynomial.derivative_sub]
  ring

/-- A unit Euclidean row is an actual coordinate after an actual orthogonal
reflection. This is a concrete finite Gaussian construction. -/
theorem exists_orthogonal_row (u : I → ℝ) (hu : ∑ j, u j ^ 2 = 1) :
    ∃ (i : I) (O : Matrix I I ℝ), O * O.transpose = 1 ∧ ∀ x : I → ℝ, O.mulVec x i = linearForm u x := by
  classical
  have hI : Nonempty I := by
    by_contra h
    haveI : IsEmpty I := not_nonempty_iff.mp h
    simp at hu
  let i : I := Classical.choice hI
  let v : EuclideanSpace ℝ I := (WithLp.equiv 2 (I → ℝ)).symm u
  let b := EuclideanSpace.basisFun I ℝ
  have hv : ‖v‖ = 1 := by
    have hs : ‖v‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
      simpa only [v, RCLike.inner_apply, conj_trivial, ← pow_two] using hu
    nlinarith [norm_nonneg v]
  let R : EuclideanSpace ℝ I ≃ₗᵢ[ℝ] EuclideanSpace ℝ I :=
    Submodule.reflection (ℝ ∙ (b i - v))ᗮ
  have hswap : R (b i) = v := Submodule.reflection_sub (by rw [b.norm_eq_one, hv])
  have hinv (x : EuclideanSpace ℝ I) : R (R x) = x := Submodule.reflection_involutive _ x
  let O := GeneralizedBulk.Entropy.Channel.isometryMatrix b R
  refine ⟨i, O, GeneralizedBulk.Entropy.Channel.isometryMatrix_orthogonal b R, ?_⟩
  intro x
  let y : EuclideanSpace ℝ I := (WithLp.equiv 2 (I → ℝ)).symm x
  have hm := GeneralizedBulk.Entropy.Channel.isometryMatrix_repr b R y
  have hip := R.inner_map_map (b i) (R y)
  rw [hswap, hinv] at hip
  calc
    O.mulVec x i = b.repr (R y) i := by
      simpa only [b, EuclideanSpace.basisFun_repr] using congrFun hm i
    _ = @inner ℝ (EuclideanSpace ℝ I) _ (b i) (R y) := b.repr_apply_apply _ _
    _ = @inner ℝ (EuclideanSpace ℝ I) _ v y := hip.symm
    _ = linearForm u x := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, v, y, linearForm, mul_comm]
      rfl

/-- Exact Gaussian L² norm of the actual unit-direction fourth Wick test. -/
theorem exists_unit_wickFourth (u : I → ℝ) (hu : ∑ j, u j ^ 2 = 1) :
    ∃ g : fullChaosSpace I 4,
      (∀ x, fullChaosEval I 4 x g = linearForm u x ^ 4 - 6 * linearForm u x ^ 2 + 3) ∧
      ‖g‖ = Real.sqrt 24 := by
  obtain ⟨i, O, hO, hrow⟩ := exists_orthogonal_row u hu
  have hdegree : (∑ j, (Pi.single i 4 : I → ℕ) j) = 4 := by simp
  let g0 := gaussianPullback O hO (multiLp I (Pi.single i 4))
  have hg0 : g0 ∈ fullChaosSpace I 4 := gaussianPullback_mem_fullChaos O hO 4
    (multiLp_mem_fullChaosSpace I 4 _ hdegree)
  let g : fullChaosSpace I 4 := ⟨g0, hg0⟩
  refine ⟨g, ?_, ?_⟩
  · have hraw : (g0 : (I → ℝ) → ℝ) =ᵐ[standardGaussian I]
        fun x => linearForm u x ^ 4 - 6 * linearForm u x ^ 2 + 3 := by
      have hae := (standardGaussian_matrixAction_measurePreserving O hO).quasiMeasurePreserving.ae_eq_comp
        (multiLp_ae I (Pi.single i 4))
      filter_upwards [gaussianPullback_ae O hO (multiLp I (Pi.single i 4)), hae] with x hp hx
      simp only [Function.comp_apply] at hx
      rw [hp, hx, multiHermite_single, hrow, hermite_four_eval]
    have hcanon : (g0 : (I → ℝ) → ℝ) =ᵐ[standardGaussian I]
        chaosFunction (degreeIndexNat I) (fullChaosCoordinates I 4 g) := by
      have hh := chaosLp_ae (degreeIndexNat I) (fullChaosCoordinates I 4 g)
      have heq := fullChaosCoordinates_spec I 4 g
      change chaosLp (degreeIndexNat I) (fullChaosCoordinates I 4 g) = g0 at heq
      rw [heq] at hh
      exact hh
    have hfil : (fun x => linearForm u x ^ 4 - 6 * linearForm u x ^ 2 + 3) ∈ functionFiltration 4 := by
      have hh := polynomial_linearForm_mul_mem (I := I) (one_mem_functionFiltration (I := I)) u (hermite 4)
      simp only [hermite_natDegree, Nat.zero_add, mul_one] at hh
      simpa only [hermite_four_eval] using hh
    have hEq := functionFiltration_eq_of_ae_eq I
      (chaosFunction_mem_functionFiltration I (degreeIndexNat I) (fullChaosCoordinates I 4 g) 4
        (fun a => (degreeIndexNat_sum I a).le)) hfil (hcanon.symm.trans hraw)
    intro x
    rw [fullChaosEval_apply, hEq]
  · change ‖gaussianPullback O hO (multiLp I (Pi.single i 4))‖ = _
    rw [(gaussianPullback O hO).norm_map]
    rw [← Real.sqrt_sq (norm_nonneg (multiLp I (Pi.single i 4))), multiLp_norm_sq, multiFactorial_single]
    norm_num

end GeneralizedBulk.Entropy.Hermite
