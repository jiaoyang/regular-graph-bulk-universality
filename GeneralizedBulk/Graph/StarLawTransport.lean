import GaussianWave.BS.SpectralBSClassification
import GeneralizedBulk.BS.SpectralAdapter

/-! Random neighbor ordering makes the actual star law independent of a
chosen neighbor enumeration. All physical coordinates, including repeats,
are retained in this equality of probability measures. -/
noncomputable section
open MeasureTheory
open scoped Classical

namespace GaussianWave.RegularEigenData

theorem starLaw_eq_of_adjacency {d M c e r : ℕ} (hd : 3 ≤ d)
    (A : RegularEigenData d M c) (B : RegularEigenData d M e)
    (hAB : A.adjacency=B.adjacency) (q : Fin r → Fin M → ℝ) :
    A.starLaw q=B.starLaw q := by
  have hg : A.regularGraph=B.regularGraph := by
    apply Subtype.ext
    apply SimpleGraph.ext
    funext v w
    apply propext
    change A.adjacency v w=1 ↔ B.adjacency v w=1
    rw [hAB]
  cases d with
  | zero => omega
  | succ d =>
    cases d with
    | zero => omega
    | succ m =>
      rw [A.starLaw_eq_lifted_star_window q,B.starLaw_eq_lifted_star_window q,hg]

end GaussianWave.RegularEigenData
