import BourgadeHuang.EdgeCMS.PhysicalChamberBounds
import BourgadeHuang.EdgeCMS.AiryPullback
import BourgadeHuang.RationalBulk.ChargedSectorial

/-! The concrete edge comparison cone instantiated with the numerator and
denominator charges of rational characteristic observables. Its inverse Airy
coordinates belong to the actual analytic domain of these observables. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.RationalEdge
open RationalBulk EdgeCMS CMS

def numeratorColors (n m : ℕ) : Fin (n+m) → Bool :=
  Fin.append (fun _ : Fin n => true) (fun _ : Fin m => false)

theorem charges_eq_physicalCharge (β : ℝ) (n m : ℕ) :
    charges β n m = fun i => physicalCharge β (numeratorColors n m i) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [charges,realCharges,physicalCharge,numeratorColors]

theorem charges_sum_zero {β : ℝ} {n m : ℕ}
    (hn : (n:ℝ)=(m:ℝ)*β/2) : ∑i,charges β n m i=0 := by
  unfold charges
  rw [←Complex.ofReal_sum,sum_realCharges,hn]
  simp

theorem charges_signed_sum_zero {β : ℝ} {n m : ℕ}
    (theta : Fin n→Bool) (eta : Fin m→Bool)
    (hn : (n:ℝ)=(m:ℝ)*β/2)
    (hbal : β*(signCount eta true:ℝ)=2*(signCount theta true:ℝ)) :
    ∑i,charges β n m i*signValue (Fin.append theta eta i)=0 := by
  unfold charges
  simp only [←ofReal_realSign,←Complex.ofReal_mul,←Complex.ofReal_sum]
  rw [signedCharge_neutral β hn,hbal]
  simp

theorem chargedPhysicalAiryBasePoint_mem {β : ℝ} (hβ : 0<β) {n m : ℕ}
    (theta : Fin n→Bool) (eta : Fin m→Bool) :
    physicalAiryBasePoint (numeratorColors n m) (Fin.append theta eta) ∈
      physicalChamberSet (charges β n m) (Fin.append theta eta) := by
  rw [charges_eq_physicalCharge]
  exact physicalAiryBasePoint_mem hβ _ _

theorem chargedPhysicalOpenCone_nonempty {β : ℝ} (hβ : 0<β) {n m : ℕ}
    (theta : Fin n→Bool) (eta : Fin m→Bool) :
    (physicalOpenCone (charges β n m) (Fin.append theta eta)).carrier.Nonempty :=
  ⟨physicalAiryBasePoint (numeratorColors n m) (Fin.append theta eta),
    chargedPhysicalAiryBasePoint_mem hβ theta eta⟩

theorem physicalChamber_inverse_reflected_im_pos {d : ℕ}
    {c : Fin d→ℂ} {upper : Fin d→Bool} {y : Point d}
    (hy : y∈physicalChamberSet c upper) (i : Fin d) :
    0<(reflectComplex (upper i) (airyInverse (y i))).im :=
  (hy.1 i).1.2.1.trans (hy.1 i).1.2.2

theorem chargedPhysicalChamber_inverse_denominatorDomain {β : ℝ} {n m : ℕ}
    {theta : Fin n→Bool} {eta : Fin m→Bool} {y : Point (n+m)}
    (hy : y∈physicalChamberSet (charges β n m) (Fin.append theta eta)) :
    airyInverseCoordinates y∈denominatorDomain n eta := by
  intro j
  have hj := physicalChamber_inverse_reflected_im_pos hy (Fin.natAdd n j)
  simp only [Fin.append_right] at hj
  change if eta j then 0<(airyInverse (y (Fin.natAdd n j))).im
    else (airyInverse (y (Fin.natAdd n j))).im<0
  cases he : eta j <;> simp only [reflectComplex,he,Bool.false_eq_true,if_false,if_true,
    Complex.conj_im] at hj ⊢ <;> linarith

theorem chargedPhysicalChamber_inverse_chargedDomain {β : ℝ} {n m : ℕ}
    {theta : Fin n→Bool} {eta : Fin m→Bool} {y : Point (n+m)}
    (hy : y∈physicalChamberSet (charges β n m) (Fin.append theta eta)) :
    ChargedDomain (charges β n m) (blockAnchors theta eta) (airyInverseCoordinates y) :=
  chargedDomain_of_denominatorDomain β theta eta _
    (chargedPhysicalChamber_inverse_denominatorDomain hy)

theorem chargedPhysicalChamber_inverse_collisionFree {β : ℝ} {n m : ℕ}
    {theta : Fin n→Bool} {eta : Fin m→Bool} {y : Point (n+m)}
    (hy : y∈physicalChamberSet (charges β n m) (Fin.append theta eta)) :
    CollisionFree (airyInverseCoordinates y) := physicalChamber_inverse_collisionFree hy

theorem chargedPhysicalChamber_uniform_gap {β : ℝ} {n m : ℕ}
    (hd : 0<n+m) {theta : Fin n→Bool} {eta : Fin m→Bool} {y : Point (n+m)}
    (hy : y∈physicalChamberSet (charges β n m) (Fin.append theta eta)) :
    ∃γ : ℝ,0<γ ∧ ∀S : Finset (Fin (n+m)),S.Nonempty →
      γ≤(∑i∈S,-2*charges β n m i*y i).re :=
  physicalChamber_uniform_gap hd hy

end BourgadeHuang.RationalEdge
