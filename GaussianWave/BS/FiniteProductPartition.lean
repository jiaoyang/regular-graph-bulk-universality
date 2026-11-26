import GaussianWave.BS.ForestGaussianReference

/-!
# Actual finite-product partition and regrouping identities
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

theorem measurable_uncurryBlocks {A B X : Type*} [MeasurableSpace X] :
    Measurable (fun f : A → B → X => fun ab : A × B => f ab.1 ab.2) := by
  apply measurable_pi_lambda
  intro ab
  exact (measurable_pi_apply ab.2).comp (measurable_pi_apply ab.1)

theorem pi_uncurryBlocks {A B X : Type*} [Fintype A] [Fintype B] [MeasurableSpace X]
    (μ : A → B → Measure X) [∀ a b, SigmaFinite (μ a b)] :
    Measure.map (fun f : A → B → X => fun ab : A × B => f ab.1 ab.2)
      (Measure.pi (fun a => Measure.pi (μ a))) = Measure.pi (fun ab : A × B => μ ab.1 ab.2) := by
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply measurable_uncurryBlocks (MeasurableSet.univ_pi hs)]
  have hpre : (fun f : A → B → X => fun ab : A × B => f ab.1 ab.2) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun a => Set.pi Set.univ (fun b => s (a, b))) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · intro h a b; exact h (a, b)
    · intro h ab; exact h ab.1 ab.2
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun ab : A × B => μ ab.1 ab.2 (s ab))).symm

def partitionProductCoordinates {N O L X : Type*} (e : N ≃ O ⊕ L) (f : N → X) :
    (O → X) × (L → X) :=
  (fun o => f (e.symm (Sum.inl o)), fun l => f (e.symm (Sum.inr l)))

theorem measurePreserving_partitionProductCoordinates {N O L X : Type*}
    [Fintype N] [Fintype O] [Fintype L] [MeasurableSpace X]
    (e : N ≃ O ⊕ L) (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (partitionProductCoordinates (X := X) e) (Measure.pi (fun _ : N => μ))
      ((Measure.pi (fun _ : O => μ)).prod (Measure.pi (fun _ : L => μ))) := by
  have he := measurePreserving_piCongrLeft (α := fun _ : O ⊕ L => X) (μ := fun _ => μ) e
  have hs := measurePreserving_sumPiEquivProdPi (X := fun _ : O ⊕ L => X) (fun _ => μ)
  convert hs.comp he using 1
  funext f
  apply Prod.ext <;> funext j <;>
    simp [partitionProductCoordinates, Function.comp_def, MeasurableEquiv.coe_piCongrLeft,
      MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.piCongrLeft_apply]

theorem root_product_partition {R N O L X : Type*} [MeasurableSpace R] [MeasurableSpace X]
    [Fintype N] [Fintype O] [Fintype L]
    (e : N ≃ O ⊕ L) (ν : Measure R) (μ : Measure X) [SigmaFinite ν] [SigmaFinite μ] :
    Measure.map (fun p : R × (N → X) =>
      ((p.1, fun o => p.2 (e.symm (Sum.inl o))), fun l => p.2 (e.symm (Sum.inr l))))
      (ν.prod (Measure.pi (fun _ : N => μ))) =
      (ν.prod (Measure.pi (fun _ : O => μ))).prod (Measure.pi (fun _ : L => μ)) := by
  have hid : MeasurePreserving (id : R → R) ν ν := ⟨measurable_id, Measure.map_id⟩
  have hp := hid.prod (measurePreserving_partitionProductCoordinates e μ)
  have ha := (measurePreserving_prodAssoc ν (Measure.pi (fun _ : O => μ))
    (Measure.pi (fun _ : L => μ))).symm
  exact (ha.comp hp).map_eq

end GaussianWave.BS
