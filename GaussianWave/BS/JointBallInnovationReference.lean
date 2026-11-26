import GaussianWave.BS.ColoredGaussianInnovationDensity
import GaussianWave.BS.IndependentLocalChart

/-! Canonical actual joint Gaussian ball innovation reference densities,
and their identification with every overlap reference chart. -/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

theorem PositiveEntropyDensity.entropy_eq_of_law_eq {I : Type*} [Fintype I]
    (p q : PositiveEntropyDensity (volume : Measure (I → ℝ))) (h : p.law = q.law) :
    p.entropy = q.entropy := p.toFiniteEntropy.entropy_eq_of_measure_eq q.toFiniteEntropy h

theorem siblingScale_ne_zero (m : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    Real.sqrt (siblingVariance (m + 2) energy) ≠ 0 :=
  (Real.sqrt_pos.mpr (siblingVariance_pos (m + 2) (by omega) energy
    (by simpa only [Nat.cast_add, Nat.cast_ofNat] using he))).ne'

def jointVertexInnovationReference (κ : Type*) [Fintype κ]
    (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :=
  jointForestGaussianPositiveDensity κ m k (Real.sqrt (siblingVariance (m + 2) energy))
    (siblingScale_ne_zero m energy he) (vertexRootInnovationFactor m energy)
    (vertexRootInnovationFactor_surjective m energy he)

def jointEdgeInnovationReference (κ : Type*) [Fintype κ]
    (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :=
  jointForestGaussianPositiveDensity κ m k (Real.sqrt (siblingVariance (m + 2) energy))
    (siblingScale_ne_zero m energy he) (physicalEdgeMatrix (energy / (m + 2)))
    (physicalEdgeMatrix_surjective m energy he)

def jointNewInnovationReference (κ : Type*) [Fintype κ]
    (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :=
  jointNewBranchGaussianPositiveDensity κ m k (Real.sqrt (siblingVariance (m + 2) energy))
    (siblingScale_ne_zero m energy he)

@[simp] theorem jointVertexInnovationReference_law (κ : Type*) [Fintype κ]
    (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    (jointVertexInnovationReference κ m k energy he).law =
      independentChannelLaw (fun _ : κ => forestGaussianInnovationLaw m k
        (Real.sqrt (siblingVariance (m + 2) energy)) (vertexRootInnovationFactor m energy)) :=
  jointForestGaussianPositiveDensity_law _ _ _ _ _ _ _

@[simp] theorem jointEdgeInnovationReference_law (κ : Type*) [Fintype κ]
    (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    (jointEdgeInnovationReference κ m k energy he).law =
      independentChannelLaw (fun _ : κ => forestGaussianInnovationLaw m k
        (Real.sqrt (siblingVariance (m + 2) energy)) (physicalEdgeMatrix (energy / (m + 2)))) :=
  jointForestGaussianPositiveDensity_law _ _ _ _ _ _ _

@[simp] theorem jointNewInnovationReference_law (κ : Type*) [Fintype κ]
    (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    (jointNewInnovationReference κ m k energy he).law =
      independentChannelLaw (fun _ : κ => newBranchGaussianLaw m k
        (Real.sqrt (siblingVariance (m + 2) energy))) :=
  jointNewBranchGaussianPositiveDensity_law _ _ _ _ _

theorem vertexReferenceFull_law (κ : Type*) [Fintype κ] [DecidableEq κ]
    (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    (innovationReferenceFull (coloredForestSplit κ (Fin (m + 2)) m k)
      (jointVertexInnovationReference κ m k energy he)
      (jointNewInnovationReference κ m k energy he)).law =
      (jointVertexInnovationReference κ m (k + 1) energy he).law := by
  rw [jointVertexInnovationReference_law]
  exact innovationReferenceFull_jointGaussian_law _ _ _ _ _ _

theorem edgeReferenceFull_law (κ : Type*) [Fintype κ] [DecidableEq κ]
    (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    (innovationReferenceFull (coloredForestSplit κ Bool m k)
      (jointEdgeInnovationReference κ m k energy he)
      (jointNewInnovationReference κ m k energy he)).law =
      (jointEdgeInnovationReference κ m (k + 1) energy he).law := by
  rw [jointEdgeInnovationReference_law]
  exact innovationReferenceFull_jointGaussian_law _ _ _ _ _ _

theorem vertexReferenceLocal_law (κ : Type*) [Fintype κ] [DecidableEq κ]
    (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) (a : Fin (m + 2)) :
    (innovationReferenceLocal (coloredLocalEdgeInnovationEquiv κ m k energy
        (ne_of_lt ((le_abs_self energy).trans_lt he)) a)
      (jointVertexInnovationReference κ m k energy he)
      (jointNewInnovationReference κ m k energy he)).law =
      (jointEdgeInnovationReference κ m (k + 1) energy he).law := by
  rw [innovationReferenceLocal, PositiveEntropyDensity.linearEquiv_law,
    innovationReferenceLocalVector, PositiveEntropyDensity.transport_law, PositiveEntropyDensity.prod_law,
    jointVertexInnovationReference_law, jointNewInnovationReference_law, jointEdgeInnovationReference_law]
  exact coloredLocalEdgeInnovationEquiv_reference κ m k energy he a

theorem edgeReferenceLocal_law (κ : Type*) [Fintype κ] [DecidableEq κ]
    (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) (b : Bool) :
    (innovationReferenceLocal (coloredLocalVertexInnovationEquiv κ m k energy
        (ne_of_lt ((le_abs_self energy).trans_lt he)) b)
      (jointEdgeInnovationReference κ m k energy he)
      (jointNewInnovationReference κ m k energy he)).law =
      (jointVertexInnovationReference κ m k energy he).law := by
  rw [innovationReferenceLocal, PositiveEntropyDensity.linearEquiv_law,
    innovationReferenceLocalVector, PositiveEntropyDensity.transport_law, PositiveEntropyDensity.prod_law,
    jointEdgeInnovationReference_law, jointNewInnovationReference_law, jointVertexInnovationReference_law]
  exact coloredLocalVertexInnovationEquiv_reference κ m k energy he b

end GaussianWave.BS
