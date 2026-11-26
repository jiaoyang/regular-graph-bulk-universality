import GaussianWave.BS.Lower.PathRecoloringSampling
import GaussianWave.BS.Lower.PathMarkerCancellation

/-! Finite palette encoding does not change the entropy of the literal
path-neighborhood tuple codes used in marker cancellation. -/
noncomputable section
open scoped BigOperators Classical
namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite
open GaussianWave.BS.Reused.Graph.ColorProfiles

theorem entropy_pushMass_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : A → ℝ) : entropy (pushMass e p)=entropy p := by
  unfold entropy
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  simp only [pushMass,e.injective.eq_iff]
  have hfilter : (Finset.univ.filter (fun x : A => x=a))={a} := by ext x; simp
  rw [hfilter]
  simp

theorem entropy_pushMass_equiv_comp {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (e : B ≃ C) (f : A → B) (p : A → ℝ) : entropy (pushMass (e ∘ f) p)=entropy (pushMass f p) := by
  rw [← pushMass_comp]
  exact entropy_pushMass_equiv e _

def pathCodeStarEquiv (d q k : ℕ) :
    (Fin (d+1) → PathNeighborhoodCode (Fin q) k) ≃ StarWord d (pathNeighborhoodPalette q k) where
  toFun := fun x j => Fintype.equivFin (PathNeighborhoodCode (Fin q) k) (x j)
  invFun := fun x j => (Fintype.equivFin (PathNeighborhoodCode (Fin q) k)).symm (x j)
  left_inv := by intro x; funext j; simp
  right_inv := by intro x; funext j; simp

theorem entropy_vertexPathStarCode (d q k : ℕ) (p : (GaussianWave.BS.VertexBallVertex d k → Fin q) → ℝ) :
    entropy (pushMass (vertexPathStarCode d q k) p)=
      entropy (pushMass (centerPathCodes (vertexBallGraph d k) k (vertexBallStarCenter d k)) p) := by
  exact entropy_pushMass_equiv_comp (pathCodeStarEquiv d q k) _ p

end GaussianWave.BS.Lower
