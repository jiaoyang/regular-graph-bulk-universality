import GeneralizedBulk.Entropy.ObservationBasis

/-! Restricting the constructed observation basis gives an actual
orthonormal basis of the retained subspace. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Channel
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]

def retainedObservationVector (reference : OrthonormalBasis I ℝ E) (S : Submodule ℝ E)
    (j : observationIndices reference S) : S :=
  ⟨observationBasis reference S j, (mem_observationIndices reference S j).mp j.property⟩

theorem retainedObservationVector_orthonormal (reference : OrthonormalBasis I ℝ E) (S : Submodule ℝ E) :
    Orthonormal ℝ (retainedObservationVector reference S) := by
  apply S.subtypeₗᵢ.orthonormal_comp_iff.mp
  exact (observationBasis reference S).orthonormal.comp _ Subtype.val_injective

theorem retainedObservationVector_sum_repr (reference : OrthonormalBasis I ℝ E) (S : Submodule ℝ E) (x : S) :
    (∑ j : observationIndices reference S, (observationBasis reference S).repr (x : E) j •
      retainedObservationVector reference S j) = x := by
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul, retainedObservationVector]
  rw [Finset.sum_coe_sort (observationIndices reference S)
    (fun j : I => (observationBasis reference S).repr (x : E) j • observationBasis reference S j)]
  calc
    _ = ∑ j : I, (observationBasis reference S).repr (x : E) j • observationBasis reference S j := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j hj hnot
      rw [(observationBasis_mem_iff reference S x).mp x.property j hnot, zero_smul]
    _ = (x : E) := (observationBasis reference S).sum_repr x

def retainedObservationBasis (reference : OrthonormalBasis I ℝ E) (S : Submodule ℝ E) :
    OrthonormalBasis (observationIndices reference S) ℝ S :=
  OrthonormalBasis.mk (retainedObservationVector_orthonormal reference S) (by
    intro x hx
    rw [← retainedObservationVector_sum_repr reference S x]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))))

@[simp] theorem retainedObservationBasis_apply (reference : OrthonormalBasis I ℝ E) (S : Submodule ℝ E)
    (j : observationIndices reference S) :
    (retainedObservationBasis reference S j : E) = observationBasis reference S j := by
  simp [retainedObservationBasis, retainedObservationVector]

theorem card_observationIndices (reference : OrthonormalBasis I ℝ E) (S : Submodule ℝ E) :
    Fintype.card (observationIndices reference S) = Module.finrank ℝ S := by
  exact (Module.finrank_eq_card_basis (retainedObservationBasis reference S).toBasis).symm

end GeneralizedBulk.Entropy.Channel
