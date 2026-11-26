import GeneralizedBulk.Entropy.MehlerRotation

/-! Finite signal symmetry propagates through the actual Gaussian observation kernel. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Entropy.Hermite
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

def coordinateProjection (observed : Finset I) (y : I → ℝ) : I → ℝ :=
  fun i => if i ∈ observed then y i else 0

theorem retained_projection (observed : Finset I) (y : I → ℝ) :
    retainedCoordinates observed (coordinateProjection observed y) = retainedCoordinates observed y := by
  funext i
  exact if_pos i.property

theorem retained_dot (observed : Finset I) (y z : I → ℝ) :
    (∑ i : observed, y i * z i) = ∑ i : I, coordinateProjection observed y i * coordinateProjection observed z i := by
  rw [Finset.sum_coe_sort observed (fun i : I => y i * z i)]
  symm
  calc
    _ = ∑ i : I, if i ∈ observed then y i * z i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : i ∈ observed <;> simp [coordinateProjection, h]
    _ = _ := by simp

def retainedKernel (observed : Finset I) (a : ℝ) (y x : I → ℝ) : ℝ :=
  vectorKernel a (retainedCoordinates observed y) (retainedCoordinates observed x)

theorem retainedKernel_projection (observed : Finset I) (a : ℝ) (y x : I → ℝ) :
    retainedKernel observed a (coordinateProjection observed y) x = retainedKernel observed a y x := by
  unfold retainedKernel
  rw [retained_projection]

theorem retainedKernel_orthogonal (observed : Finset I) (Q : Matrix I I ℝ)
    (hQ : Q * Q.transpose = 1)
    (hcomm : ∀ y, coordinateProjection observed (Q.mulVec y) = Q.mulVec (coordinateProjection observed y))
    (a : ℝ) (y x : I → ℝ) :
    retainedKernel observed a (Q.mulVec y) (Q.mulVec x) = retainedKernel observed a y x := by
  have hdot (u v : I → ℝ) : (∑ i : observed, Q.mulVec u i * Q.mulVec v i) = ∑ i : observed, u i * v i := by
    rw [retained_dot, hcomm u, hcomm v, orthogonal_dotProduct Q hQ, ← retained_dot]
  unfold retainedKernel vectorKernel
  change kernel _ (∑ i : observed, Q.mulVec x i * Q.mulVec y i)
    (∑ i : observed, ((Q.mulVec y i) ^ 2 + (Q.mulVec x i) ^ 2)) a =
    kernel _ (∑ i : observed, x i * y i) (∑ i : observed, (y i ^ 2 + x i ^ 2)) a
  rw [hdot, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [pow_two, hdot]

/-- The symmetry premise below is entirely finite: it is equality of all
weighted functions of the projected signal. Gaussian density symmetry is a
proved consequence of it. -/
theorem retained_mixture_symmetry (observed : Finset I) (Q : Matrix I I ℝ)
    (hQ : Q * Q.transpose = 1) (hinv : ∀ y, Q.mulVec (Q.mulVec y) = y)
    (hcomm : ∀ y, coordinateProjection observed (Q.mulVec y) = Q.mulVec (coordinateProjection observed y))
    (weight : S → ℝ) (signal : S → I → ℝ)
    (hsym : ∀ F : (I → ℝ) → ℝ,
      (∑ s, weight s * F (Q.mulVec (coordinateProjection observed (signal s)))) =
        ∑ s, weight s * F (coordinateProjection observed (signal s)))
    (a : ℝ) (x : I → ℝ) :
    finiteMixtureKernel weight (fun s => retainedCoordinates observed (signal s)) a
        (retainedCoordinates observed (Q.mulVec x)) =
      finiteMixtureKernel weight (fun s => retainedCoordinates observed (signal s)) a
        (retainedCoordinates observed x) := by
  have hkernel (y : I → ℝ) : retainedKernel observed a y (Q.mulVec x) =
      retainedKernel observed a (Q.mulVec y) x := by
    have h := retainedKernel_orthogonal observed Q hQ hcomm a (Q.mulVec y) x
    rw [hinv] at h
    exact h
  change (∑ s, weight s * retainedKernel observed a (signal s) (Q.mulVec x)) =
    ∑ s, weight s * retainedKernel observed a (signal s) x
  calc
    _ = ∑ s, weight s * retainedKernel observed a
        (Q.mulVec (coordinateProjection observed (signal s))) x := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [← retainedKernel_projection observed a (signal s) (Q.mulVec x), hkernel]
    _ = ∑ s, weight s * retainedKernel observed a (coordinateProjection observed (signal s)) x :=
      hsym (fun y => retainedKernel observed a y x)
    _ = _ := by simp_rw [retainedKernel_projection]

end GeneralizedBulk.Entropy.Mehler
