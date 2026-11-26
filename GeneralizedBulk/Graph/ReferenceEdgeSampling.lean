import GeneralizedBulk.Graph.IdealEmpiricalEntropy
import GeneralizedBulk.Entropy.FiniteSampleMap

/-! Every ordered leaf reference mixture is exactly the actual uniformly
sampled oriented-edge reference mixture, including all colors jointly. -/
noncomputable section
open scoped BigOperators Classical
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Entropy GeneralizedBulk.Gaussian
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem uniform_star_port_average (leaf : Fin d) (f : Fin (N n) × Fin d → ℝ) :
    (∑ s : Fin (N n) × Equiv.Perm (Fin d),(D.empiricalStarWeight n s)*f (s.1,s.2 leaf))=
      ∑ s : Fin (N n) × Fin d,uniformSampleWeight (Fin (N n) × Fin d) s*f s := by
  letI : Nonempty (Fin d) := ⟨leaf⟩
  have hN : (N n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (D.size_pos n).ne'
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt leaf.isLt)
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [empiricalStarWeight,uniformSampleWeight,Fintype.sum_prod_type,← Finset.mul_sum,
    Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
  have he (v : Fin (N n)) := GeneralizedBulk.Graph.sum_perm_eval (fun j => f (v,j)) leaf
  simp_rw [he]
  rw [← Finset.mul_sum]
  field_simp
  <;> ring

theorem referenceEdgeGaussianMixturePDF_eq_oriented {k : ℕ} (q : Fin k → Fin (N n) → ℝ)
    (leaf : Fin d) (r : ℝ) (M : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℝ) :
    gaussianMixturePDF (D.empiricalStarWeight n)
      (fun s => fun a : Fin k × Fin 2 => r*D.starSample n ω q s (a.1,physicalEdgeIndex leaf a.2)) (fun _ => M)=
      gaussianMixturePDF (uniformSampleWeight (Fin (N n) × Fin d))
        (fun s => r • D.orientedEdgeMark n ω q s) (fun _ => M) := by
  funext x
  have he (s : Fin (N n) × Equiv.Perm (Fin d)) :
      (fun a : Fin k × Fin 2 => r*D.starSample n ω q s (a.1,physicalEdgeIndex leaf a.2))=
        r • D.orientedEdgeMark n ω q (s.1,s.2 leaf) := by
    funext a
    rcases a with ⟨a,j⟩
    fin_cases j <;> rfl
  change (∑ s,D.empiricalStarWeight n s*affineGaussianPDF _ M x)=_
  simp only [he]
  exact D.uniform_star_port_average n leaf
    (fun s => affineGaussianPDF (r • D.orientedEdgeMark n ω q s) M x)

end GeneralizedBulk.External.RegularSpectralData
