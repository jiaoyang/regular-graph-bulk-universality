import GaussianWave.BS.DensityMarginals
import GaussianWave.BS.Reused.Analysis.ProductDensityEntropy

/-! Relative SSA against literal independent extension blocks. The
reference entropy cancellation is proved from actual product densities. -/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

namespace PositiveEntropyDensity
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {mx : Measure X} {my : Measure Y} [SigmaFinite mx] [SigmaFinite my]

def prod (p : PositiveEntropyDensity mx) (q : PositiveEntropyDensity my) :
    PositiveEntropyDensity (mx.prod my) where
  density := fun z => p.density z.1*q.density z.2
  measurable := (p.measurable.comp measurable_fst).mul (q.measurable.comp measurable_snd)
  positive := fun _ => mul_pos (p.positive _) (q.positive _)
  integrable := p.integrable.mul_prod q.integrable
  integral_one := by rw [integral_prod_mul,p.integral_one,q.integral_one,one_mul]
  integrable_log := (Reused.Analysis.product_density_entropy mx my p.density q.density
    p.integrable q.integrable p.positive q.positive p.integrable_log q.integrable_log
    p.integral_one q.integral_one).1

theorem prod_entropy (p : PositiveEntropyDensity mx) (q : PositiveEntropyDensity my) :
    (p.prod q).entropy = p.entropy+q.entropy := by
  exact (Reused.Analysis.product_density_entropy mx my p.density q.density
    p.integrable q.integrable p.positive q.positive p.integrable_log q.integrable_log
    p.integral_one q.integral_one).2

theorem prod_law (p : PositiveEntropyDensity mx) (q : PositiveEntropyDensity my) :
    (p.prod q).law = p.law.prod q.law := by
  rw [law,law,law,prod_withDensity p.measurable.ennreal_ofReal q.measurable.ennreal_ofReal]
  congr 1
  funext z
  exact ENNReal.ofReal_mul (p.positive z.1).le

end PositiveEntropyDensity

section RelativeSSA
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  (mx : Measure X) (my : Measure Y) (mz : Measure Z)
  [SigmaFinite mx] [SigmaFinite my] [SigmaFinite mz]
  (f : PositiveEntropyDensity (mz.prod (mx.prod my)))
  (p : PositiveEntropyDensity (mz.prod mx)) (q : PositiveEntropyDensity (mz.prod my))
  (s : PositiveEntropyDensity mz)
  (hpx : Measure.map (fun zxy : Z × (X × Y) => (zxy.1,zxy.2.1)) f.law = p.law)
  (hqy : Measure.map (fun zxy : Z × (X × Y) => (zxy.1,zxy.2.2)) f.law = q.law)
  (hsz : Measure.map Prod.fst f.law = s.law)
  (gZ : PositiveEntropyDensity mz) (gX : PositiveEntropyDensity mx) (gY : PositiveEntropyDensity my)

include hpx hqy hsz

theorem relativeStrongSubadditivity_of_product_reference :
    0 ≤ (p.entropy-(gZ.prod gX).entropy) + (q.entropy-(gZ.prod gY).entropy) -
      (s.entropy-gZ.entropy) - (f.entropy-(gZ.prod (gX.prod gY)).entropy) := by
  have h := strongSubadditivity_of_marginals mx my mz f p q s hpx hqy hsz
  simp only [PositiveEntropyDensity.prod_entropy]
  linarith

theorem relativeStrongSubadditivity_equality_iff_of_product_reference :
    ((p.entropy-(gZ.prod gX).entropy) + (q.entropy-(gZ.prod gY).entropy) -
      (s.entropy-gZ.entropy) - (f.entropy-(gZ.prod (gX.prod gY)).entropy) = 0) ↔
      f.law = conditionalGluingLaw mx my mz p q s := by
  have h := strongSubadditivity_equality_iff_of_marginals mx my mz f p q s hpx hqy hsz
  simp only [PositiveEntropyDensity.prod_entropy]
  convert h using 2 <;> ring

end RelativeSSA
end GaussianWave.BS
