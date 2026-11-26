import GaussianWave.BS.FiniteProductDensities
import GaussianWave.BS.LocalGaussianReference

/-! Finite-family relative strong subadditivity against the actual
independent innovation reference. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

section
variable {A Y Z : Type*} [Fintype A] [MeasurableSpace Y] [MeasurableSpace Z]
    (my : Measure Y) (mz : Measure Z) [SigmaFinite my] [SigmaFinite mz]

theorem finiteStrongSubadditivity_productReference_zero
    (s : PositiveEntropyDensity mz) (q : PositiveEntropyDensity my)
    (fG : PositiveEntropyDensity (mz.prod (Measure.pi (fun _ : A => my))))
    (hG : fG.law = s.law.prod (Measure.pi (fun _ : A => q.law))) :
    (∑ _ : A, (s.prod q).entropy) - (Fintype.card A - 1 : ℝ) * s.entropy - fG.entropy = 0 := by
  have hp (a : A) : Measure.map (fun zy : Z × (A → Y) => (zy.1, zy.2 a)) fG.law =
      (s.prod q).law := by
    rw [hG, core_new_projection_product, PositiveEntropyDensity.prod_law]
  have hs : Measure.map Prod.fst fG.law = s.law := by
    rw [hG, Measure.map_fst_prod]
    simp
  apply (finiteStrongSubadditivity_equality_iff_of_marginals my mz fG (fun _ : A => s.prod q) s hp hs).mpr
  exact hG.trans (finiteConditionalGluingLaw_product my mz s (fun _ : A => q)).symm

theorem relativeFiniteStrongSubadditivity_of_product_reference
    (f : PositiveEntropyDensity (mz.prod (Measure.pi (fun _ : A => my))))
    (p : A → PositiveEntropyDensity (mz.prod my)) (s : PositiveEntropyDensity mz)
    (hp : ∀ a, Measure.map (fun zy : Z × (A → Y) => (zy.1, zy.2 a)) f.law = (p a).law)
    (hs : Measure.map Prod.fst f.law = s.law)
    (gZ : PositiveEntropyDensity mz) (gY : PositiveEntropyDensity my)
    (gF : PositiveEntropyDensity (mz.prod (Measure.pi (fun _ : A => my))))
    (hG : gF.law = gZ.law.prod (Measure.pi (fun _ : A => gY.law))) :
    0 ≤ (∑ a, ((p a).entropy - (gZ.prod gY).entropy)) -
      (Fintype.card A - 1 : ℝ) * (s.entropy - gZ.entropy) - (f.entropy - gF.entropy) := by
  have h := finiteStrongSubadditivity_of_marginals my mz f p s hp hs
  have hzero := finiteStrongSubadditivity_productReference_zero my mz gZ gY gF hG
  simp only [Finset.sum_sub_distrib] at *
  linarith

theorem relativeFiniteStrongSubadditivity_equality_iff_of_product_reference
    (f : PositiveEntropyDensity (mz.prod (Measure.pi (fun _ : A => my))))
    (p : A → PositiveEntropyDensity (mz.prod my)) (s : PositiveEntropyDensity mz)
    (hp : ∀ a, Measure.map (fun zy : Z × (A → Y) => (zy.1, zy.2 a)) f.law = (p a).law)
    (hs : Measure.map Prod.fst f.law = s.law)
    (gZ : PositiveEntropyDensity mz) (gY : PositiveEntropyDensity my)
    (gF : PositiveEntropyDensity (mz.prod (Measure.pi (fun _ : A => my))))
    (hG : gF.law = gZ.law.prod (Measure.pi (fun _ : A => gY.law))) :
    ((∑ a, ((p a).entropy - (gZ.prod gY).entropy)) -
      (Fintype.card A - 1 : ℝ) * (s.entropy - gZ.entropy) - (f.entropy - gF.entropy) = 0) ↔
      f.law = finiteConditionalGluingLaw my mz p s := by
  have hzero := finiteStrongSubadditivity_productReference_zero my mz gZ gY gF hG
  have he := finiteStrongSubadditivity_equality_iff_of_marginals my mz f p s hp hs
  simp only [Finset.sum_sub_distrib]
  rw [← he]
  constructor <;> intro h <;> linarith

end
end GaussianWave.BS
