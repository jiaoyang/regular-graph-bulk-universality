import GaussianWave.BS.InnovationEntropyCoordinates
import GaussianWave.BS.IndependentChannelLaw

/-! An actual independent-channel reference split, retaining all channels
in each spatial extension block. -/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

def transposeBlocks (κ A X : Type*) (x : κ → A → X) : A → κ → X := fun a c => x c a

theorem measurable_transposeBlocks (κ A X : Type*) [MeasurableSpace X] :
    Measurable (transposeBlocks κ A X) := by
  exact measurable_pi_lambda _ (fun _ => measurable_pi_lambda _ (fun _ =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)))

theorem measurePreserving_transposeBlocks (κ A X : Type*) [Fintype κ] [Fintype A]
    [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν] :
    MeasurePreserving (transposeBlocks κ A X)
      (Measure.pi (fun _ : κ => Measure.pi (fun _ : A => ν)))
      (Measure.pi (fun _ : A => Measure.pi (fun _ : κ => ν))) := by
  have h1 : MeasurePreserving (curryBlocksEquiv κ A X).symm
      (Measure.pi (fun _ : κ => Measure.pi (fun _ : A => ν)))
      (Measure.pi (fun _ : κ × A => ν)) := (measurePreserving_curryBlocks ν).symm
  have h2 := measurePreserving_piCongrLeft (α := fun _ : A × κ => X)
    (μ := fun _ => ν) (Equiv.prodComm κ A)
  have h3 := measurePreserving_curryBlocks (A := A) (B := κ) ν
  convert h3.comp (h2.comp h1) using 1

def coloredFiniteSplit (κ : Type*) {V Z A Y : Type*} (e : V ≃ Z ⊕ (A × Y)) :
    (κ × V) ≃ (κ × Z) ⊕ (A × (κ × Y)) where
  toFun cv := Sum.elim (fun z => Sum.inl (cv.1, z))
    (fun ay => Sum.inr (ay.1, (cv.1, ay.2))) (e cv.2)
  invFun := Sum.elim (fun cz => (cz.1, e.symm (Sum.inl cz.2)))
    (fun acy => (acy.2.1, e.symm (Sum.inr (acy.1, acy.2.2))))
  left_inv cv := by
    cases h : e cv.2 with
    | inl z => simp only [h, Sum.elim_inl]; rw [← h, e.symm_apply_apply]
    | inr ay => simp only [h, Sum.elim_inr]; rw [← h, e.symm_apply_apply]
  right_inv j := by
    cases j with
    | inl cz => simp only [e.apply_symm_apply, Sum.elim_inl]
    | inr acy => simp only [e.apply_symm_apply, Sum.elim_inr]

theorem independentChannelLaw_split {κ V Z A Y : Type*}
    [Fintype κ] [Fintype V] [Fintype Z] [Fintype A] [Fintype Y]
    (e : V ≃ Z ⊕ (A × Y)) (μ : Measure (V → ℝ)) [IsProbabilityMeasure μ]
    (μZ : Measure (Z → ℝ)) [IsProbabilityMeasure μZ]
    (ν : Measure (Y → ℝ)) [IsProbabilityMeasure ν]
    (hsplit : Measure.map (finiteInnovationSplitEquiv e) μ =
      μZ.prod (Measure.pi (fun _ : A => ν))) :
    Measure.map (finiteInnovationSplitEquiv (coloredFiniteSplit κ e))
      (independentChannelLaw (fun _ : κ => μ)) =
      (independentChannelLaw (fun _ : κ => μZ)).prod
        (Measure.pi (fun _ : A => independentChannelLaw (fun _ : κ => ν))) := by
  letI : IsProbabilityMeasure (Measure.pi (fun _ : A => ν)) := Measure.pi.instIsProbabilityMeasure _
  letI : IsProbabilityMeasure (Measure.pi (fun _ : κ => ν)) := Measure.pi.instIsProbabilityMeasure _
  letI : IsProbabilityMeasure (Measure.pi (fun _ : κ => Measure.pi (fun _ : A => ν))) :=
    Measure.pi.instIsProbabilityMeasure _
  letI : IsProbabilityMeasure (Measure.pi (fun _ : A => Measure.pi (fun _ : κ => ν))) :=
    Measure.pi.instIsProbabilityMeasure _
  have h1 := measurePreserving_pi (fun _ : κ => μ)
    (fun _ : κ => μZ.prod (Measure.pi (fun _ : A => ν)))
    (f := fun _ => finiteInnovationSplitEquiv e)
    (fun _ => ⟨(finiteInnovationSplitEquiv e).measurable, hsplit⟩)
  have h2 := measurePreserving_arrowProdEquivProdArrow (Z → ℝ) (A → Y → ℝ) κ
    (fun _ => μZ) (fun _ => Measure.pi (fun _ : A => ν))
  have hid : MeasurePreserving (id : (κ → Z → ℝ) → (κ → Z → ℝ))
      (Measure.pi (fun _ : κ => μZ)) (Measure.pi (fun _ : κ => μZ)) :=
    ⟨measurable_id, Measure.map_id⟩
  have h3 := hid.prod (measurePreserving_transposeBlocks κ A (Y → ℝ) ν)
  have h4core : MeasurePreserving (flattenChannels (κ := κ) (ι := Z))
      (Measure.pi (fun _ : κ => μZ)) (independentChannelLaw (fun _ : κ => μZ)) :=
    ⟨measurable_flattenChannels, rfl⟩
  have h4new := measurePreserving_pi (fun _ : A => Measure.pi (fun _ : κ => ν))
    (fun _ : A => independentChannelLaw (fun _ : κ => ν))
    (f := fun _ => flattenChannels)
    (fun _ => (show MeasurePreserving (flattenChannels (κ := κ) (ι := Y))
      (Measure.pi (fun _ : κ => ν)) (independentChannelLaw (fun _ : κ => ν)) from
      ⟨measurable_flattenChannels, rfl⟩))
  have hfinal := ((h4core.prod h4new).comp (h3.comp (h2.comp h1))).map_eq
  rw [independentChannelLaw, Measure.map_map
    (finiteInnovationSplitEquiv (coloredFiniteSplit κ e)).measurable measurable_flattenChannels]
  convert hfinal using 1

theorem independentChannelLaw_mapVector {κ I J : Type*} [Fintype κ]
    (Q : κ → Measure (I → ℝ)) [∀ a, IsProbabilityMeasure (Q a)]
    (F : (I → ℝ) → (J → ℝ)) (hF : Measurable F) :
    Measure.map (fun x : (κ × I) → ℝ => fun cj => F (fun i => x (cj.1, i)) cj.2)
      (independentChannelLaw Q) =
      independentChannelLaw (fun a => Measure.map F (Q a)) := by
  letI (a : κ) : IsProbabilityMeasure (Measure.map F (Q a)) := isProbabilityMeasure_map hF.aemeasurable
  have hp := measurePreserving_pi Q (fun a => Measure.map F (Q a))
    (f := fun _ => F) (fun _ => ⟨hF, rfl⟩)
  rw [independentChannelLaw, Measure.map_map (by
    exact measurable_pi_lambda _ (fun cj => (measurable_pi_apply cj.2).comp
      (hF.comp (measurable_pi_lambda _ (fun _ => measurable_pi_apply _))))) measurable_flattenChannels]
  change Measure.map (flattenChannels ∘ (fun z : κ → I → ℝ => fun a => F (z a))) _ = _
  rw [← Measure.map_map measurable_flattenChannels hp.measurable, hp.map_eq]
  rfl

theorem independent_forestGaussianInnovationLaw_split {κ A : Type*}
    [Fintype κ] [Fintype A] [DecidableEq A]
    (m k : ℕ) (scale : ℝ) (R : Matrix A A ℝ) :
    Measure.map (coloredForestSplitCoordinates κ A m k)
      (independentChannelLaw (fun _ : κ => forestGaussianInnovationLaw m (k + 1) scale R)) =
      (independentChannelLaw (fun _ : κ => forestGaussianInnovationLaw m k scale R)).prod
        (Measure.pi (fun _ : A => independentChannelLaw (fun _ : κ => newBranchGaussianLaw m k scale))) :=
  independentChannelLaw_split (forestInnovationSplit A m k) _ _ _
    (forestGaussianInnovationLaw_split m k scale R)

end GaussianWave.BS
