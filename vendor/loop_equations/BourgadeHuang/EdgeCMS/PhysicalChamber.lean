import BourgadeHuang.EdgeCMS.RootGeometry
import BourgadeHuang.EdgeCMS.AiryInverse
import BourgadeHuang.EdgeCMS.HomogeneousCoefficients
import BourgadeHuang.FiniteObservableBounds

/-! A concrete nonempty physical chamber for the edge CMS system. Its
numerator directions are 3±4i and denominator directions are 5±12i. These
lie in the same right-hand local-law sector, but their Airy phases have
opposite real signs, giving strictly positive nonconstant jet gaps. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.EdgeCMS
open CMS

private theorem root_three_four : root (3+4*Complex.I) = 2+Complex.I := by
  have hz : (3+4*Complex.I:ℂ)≠0 := by norm_num [Complex.ext_iff]
  have hs : root (3+4*Complex.I)^2=(2+Complex.I)^2 := by
    rw [root_sq hz]
    ring_nf
    simp
    ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h|h
  · exact h
  · have hr := root_re_pos (show 0<(3+4*Complex.I:ℂ).im by norm_num)
    rw [h] at hr
    norm_num at hr

private theorem root_five_twelve : root (5+12*Complex.I) = 3+2*Complex.I := by
  have hz : (5+12*Complex.I:ℂ)≠0 := by norm_num [Complex.ext_iff]
  have hs : root (5+12*Complex.I)^2=(3+2*Complex.I)^2 := by
    rw [root_sq hz]
    ring_nf
    simp
    ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h|h
  · exact h
  · have hr := root_re_pos (show 0<(5+12*Complex.I:ℂ).im by norm_num)
    rw [h] at hr
    norm_num at hr

def physicalBase (numerator upper : Bool) : ℂ :=
  reflectComplex upper (if numerator then 3+4*Complex.I else 5+12*Complex.I)

def physicalCharge (β : ℝ) (numerator : Bool) : ℂ :=
  if numerator then -1 else (β:ℂ)/2

theorem physicalBase_offReal (numerator upper : Bool) :
    (physicalBase numerator upper).im≠0 := by
  cases numerator <;> cases upper <;> norm_num [physicalBase,reflectComplex]

theorem physicalBase_sector (numerator upper : Bool) :
    0<(reflectComplex upper (physicalBase numerator upper)).re ∧
      (reflectComplex upper (physicalBase numerator upper)).re <
        (reflectComplex upper (physicalBase numerator upper)).im := by
  cases numerator <;> cases upper <;> norm_num [physicalBase,reflectComplex]

theorem root_physicalBase (numerator upper : Bool) :
    root (physicalBase numerator upper) =
      reflectComplex upper (if numerator then 2+Complex.I else 3+2*Complex.I) := by
  cases numerator <;> cases upper
  · simp only [physicalBase,reflectComplex,Bool.false_eq_true,if_false]
    rw [root_conj (by norm_num),root_five_twelve]
  · simpa [physicalBase,reflectComplex] using root_five_twelve
  · simp only [physicalBase,reflectComplex,Bool.false_eq_true,if_false,if_true]
    rw [root_conj (by norm_num),root_three_four]
  · simpa [physicalBase,reflectComplex] using root_three_four

theorem airyCoordinate_physicalBase_re (numerator upper : Bool) :
    (airyCoordinate (physicalBase numerator upper)).re = if numerator then 4/3 else -6 := by
  unfold airyCoordinate
  rw [root_physicalBase]
  cases numerator <;> cases upper <;> norm_num [physicalBase,reflectComplex,Complex.mul_re,Complex.mul_im,map_ofNat]

theorem airyCoordinate_physicalBase_im (numerator upper : Bool) :
    0<(reflectComplex upper (airyCoordinate (physicalBase numerator upper))).im := by
  unfold airyCoordinate
  rw [root_physicalBase]
  cases numerator <;> cases upper <;> norm_num [physicalBase,reflectComplex,Complex.mul_re,Complex.mul_im,map_ofNat]

theorem physicalBase_gap {β : ℝ} (hβ : 0<β) (numerator upper : Bool) :
    0<(-2*physicalCharge β numerator*airyCoordinate (physicalBase numerator upper)).re := by
  have hr := airyCoordinate_physicalBase_re numerator upper
  cases numerator <;> norm_num [physicalCharge,Complex.mul_re,Complex.mul_im,hr] at *
  linarith

/-- Distinct integer square scales retain both physical phase signs. -/
def physicalBasePoint {d : ℕ} (numerator upper : Fin d→Bool) (i : Fin d) : ℂ :=
  ((i.val+1:ℝ):ℂ)^2*physicalBase (numerator i) (upper i)

theorem physicalBasePoint_offReal {d : ℕ} (numerator upper : Fin d→Bool) (i : Fin d) :
    (physicalBasePoint numerator upper i).im≠0 := by
  have hb := physicalBase_offReal (numerator i) (upper i)
  have hi : (i.val+1:ℝ)^2≠0 := by positivity
  rw [physicalBasePoint,←Complex.ofReal_pow]
  simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using mul_ne_zero hi hb

theorem airyCoordinate_physicalBasePoint {d : ℕ} (numerator upper : Fin d→Bool) (i : Fin d) :
    airyCoordinate (physicalBasePoint numerator upper i) =
      ((i.val+1:ℝ):ℂ)^3*airyCoordinate (physicalBase (numerator i) (upper i)) :=
  airyCoordinate_ofReal_sq_mul (by positivity)
    (by intro h; exact physicalBase_offReal (numerator i) (upper i) (by simp [h]))

theorem physicalBasePoint_gap {d : ℕ} {β : ℝ} (hβ : 0<β)
    (numerator upper : Fin d→Bool) (i : Fin d) :
    0<(-2*physicalCharge β (numerator i)*airyCoordinate (physicalBasePoint numerator upper i)).re := by
  rw [airyCoordinate_physicalBasePoint]
  have heq : -2*physicalCharge β (numerator i)*
      (((i.val+1:ℝ):ℂ)^3*airyCoordinate (physicalBase (numerator i) (upper i))) =
    (((i.val+1:ℝ)^3:ℝ):ℂ)*
      (-2*physicalCharge β (numerator i)*airyCoordinate (physicalBase (numerator i) (upper i))) := by
    push_cast
    ring
  rw [heq]
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using
    mul_pos (by positivity : 0<(i.val+1:ℝ)^3) (physicalBase_gap hβ (numerator i) (upper i))

theorem reflectComplex_ofReal_mul (upper : Bool) (t : ℝ) (z : ℂ) :
    reflectComplex upper ((t:ℂ)*z) = (t:ℂ)*reflectComplex upper z := by
  cases upper <;> simp [reflectComplex]

theorem physicalBasePoint_re {d : ℕ} (numerator upper : Fin d→Bool) (i : Fin d) :
    (physicalBasePoint numerator upper i).re =
      (i.val+1:ℝ)^2*(if numerator i then 3 else 5) := by
  rw [physicalBasePoint,←Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  cases h: numerator i <;> cases h': upper i <;>
    norm_num [physicalBase,reflectComplex,h,h']

theorem physicalBasePoint_im {d : ℕ} (numerator upper : Fin d→Bool) (i : Fin d) :
    (physicalBasePoint numerator upper i).im =
      (i.val+1:ℝ)^2*(if upper i then 1 else -1)*(if numerator i then 4 else 12) := by
  rw [physicalBasePoint,←Complex.ofReal_pow]
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  cases h: numerator i <;> cases h': upper i <;>
    norm_num [physicalBase,reflectComplex,h,h'] <;> ring

theorem physicalBasePoint_re_pos {d : ℕ} (numerator upper : Fin d→Bool) (i : Fin d) :
    0<(physicalBasePoint numerator upper i).re := by
  rw [physicalBasePoint_re]
  split <;> positivity

theorem physicalBasePoint_sector {d : ℕ} (numerator upper : Fin d→Bool) (i : Fin d) :
    (physicalBasePoint numerator upper i).re <
      (reflectComplex (upper i) (physicalBasePoint numerator upper i)).im := by
  rw [physicalBasePoint,←Complex.ofReal_pow,reflectComplex_ofReal_mul]
  have h := (physicalBase_sector (numerator i) (upper i)).2
  have hr : (reflectComplex (upper i) (physicalBase (numerator i) (upper i))).re =
      (physicalBase (numerator i) (upper i)).re := by
    cases h: upper i <;> simp [reflectComplex,h]
  rw [hr] at h
  simpa only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,add_zero] using mul_lt_mul_of_pos_left h (by positivity : 0<(i.val+1:ℝ)^2)

theorem physicalBasePoint_collisionFree {d : ℕ} (numerator upper : Fin d→Bool) :
    CollisionFree (physicalBasePoint numerator upper) := by
  intro i j hij
  have hre := congrArg Complex.re hij
  have him := congrArg Complex.im hij
  simp only [physicalBasePoint_re,physicalBasePoint_im] at hre him
  have hi : 0<(i.val+1:ℝ) := by positivity
  have hj : 0<(j.val+1:ℝ) := by positivity
  have hs : (i.val+1:ℝ)^2=(j.val+1:ℝ)^2 := by
    cases h: numerator i <;> cases h': numerator j <;>
      cases u: upper i <;> cases u': upper j <;> simp [h,h',u,u'] at hre him <;> nlinarith
  have hq := (sq_eq_sq₀ hi.le hj.le).mp hs
  apply Fin.ext
  exact_mod_cast (show (i.val:ℝ)=(j.val:ℝ) by linarith)

theorem airyCoordinate_physicalBasePoint_im {d : ℕ} (numerator upper : Fin d→Bool) (i : Fin d) :
    0<(reflectComplex (upper i) (airyCoordinate (physicalBasePoint numerator upper i))).im := by
  rw [airyCoordinate_physicalBasePoint,←Complex.ofReal_pow,reflectComplex_ofReal_mul]
  simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using
    mul_pos (by positivity : 0<(i.val+1:ℝ)^3)
      (airyCoordinate_physicalBase_im (numerator i) (upper i))

/-- A scalar physical comparison region in the Airy coordinate. -/
def physicalScalarDomain (c : ℂ) (upper : Bool) : Set ℂ :=
  (Complex.slitPlane ∩ airyInverse ⁻¹' {z | 0<z.re ∧ z.re<(reflectComplex upper z).im}) ∩
    {y | 0<(reflectComplex upper y).im ∧ 0<(-2*c*y).re}

theorem continuous_reflectComplex (upper : Bool) : Continuous (reflectComplex upper) := by
  cases upper
  · exact Complex.continuous_conj
  · exact continuous_id

theorem isOpen_physicalScalarDomain (c : ℂ) (upper : Bool) :
    IsOpen (physicalScalarDomain c upper) := by
  have hc : ContinuousOn airyInverse Complex.slitPlane :=
    fun y hy => (analyticAt_airyInverse hy).continuousAt.continuousWithinAt
  apply IsOpen.inter
  · apply hc.isOpen_inter_preimage Complex.isOpen_slitPlane
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re
        (Complex.continuous_im.comp (continuous_reflectComplex upper)))
  · exact (isOpen_lt continuous_const
      (Complex.continuous_im.comp (continuous_reflectComplex upper))).inter
      (isOpen_lt continuous_const (Complex.continuous_re.comp
        (continuous_const.mul continuous_id)))

/-- Ordered coordinates are unnecessary: removing all collision diagonals
still gives an open cone, and the physical phase is positive in every slot. -/
def physicalChamberSet {d : ℕ} (c : Fin d→ℂ) (upper : Fin d→Bool) : Set (Point d) :=
  {y | (∀i, y i∈physicalScalarDomain (c i) (upper i)) ∧ CollisionFree y}

theorem isOpen_collisionFree (d : ℕ) : IsOpen {y : Point d | CollisionFree y} := by
  have hr : {y : Point d | CollisionFree y} = {y | ∀i j, i≠j → y i≠y j} := by
    ext y
    constructor
    · intro h i j hij
      exact h.ne hij
    · intro h i j hij
      by_contra hn
      exact h i j hn hij
  rw [hr]
  simp only [setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro hij
  exact isOpen_ne_fun (continuous_apply i) (continuous_apply j)

theorem isOpen_physicalChamberSet {d : ℕ} (c : Fin d→ℂ) (upper : Fin d→Bool) :
    IsOpen (physicalChamberSet c upper) := by
  change IsOpen ({y : Point d | ∀i, y i∈physicalScalarDomain (c i) (upper i)} ∩
    {y | CollisionFree y})
  apply IsOpen.inter
  · simp only [setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact (isOpen_physicalScalarDomain (c i) (upper i)).preimage (continuous_apply i)
  · exact isOpen_collisionFree d

theorem physicalScalarDomain_scale {c y : ℂ} {upper : Bool}
    (hy : y∈physicalScalarDomain c upper) {t : ℝ} (ht : 0<t) :
    (t:ℂ)*y∈physicalScalarDomain c upper := by
  obtain ⟨u,hu,huc⟩ := exists_positive_cube_root ht
  have hscale : airyInverse ((t:ℂ)*y) = ((u^2:ℝ):ℂ)*airyInverse y := by
    have hc : (u:ℂ)^3=(t:ℂ) := by exact_mod_cast huc
    rw [←hc,airyInverse_ofReal_cube_mul hu (Complex.slitPlane_ne_zero hy.1.1),Complex.ofReal_pow]
  refine ⟨⟨positive_real_mul_mem_slitPlane ht hy.1.1,?_⟩,⟨?_,?_⟩⟩
  · change 0<(airyInverse ((t:ℂ)*y)).re ∧
      (airyInverse ((t:ℂ)*y)).re<(reflectComplex upper (airyInverse ((t:ℂ)*y))).im
    rw [hscale,reflectComplex_ofReal_mul]
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,add_zero]
    exact ⟨mul_pos (sq_pos_of_pos hu) hy.1.2.1,
      mul_lt_mul_of_pos_left hy.1.2.2 (sq_pos_of_pos hu)⟩
  · rw [reflectComplex_ofReal_mul]
    simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using
      mul_pos ht hy.2.1
  · have he : -2*c*((t:ℂ)*y)=(t:ℂ)*(-2*c*y) := by ring
    rw [he]
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using
      mul_pos ht hy.2.2

def physicalOpenCone {d : ℕ} (c : Fin d→ℂ) (upper : Fin d→Bool) : OpenCone d where
  carrier := physicalChamberSet c upper
  isOpen := isOpen_physicalChamberSet c upper
  scale_mem := by
    intro t ht y hy
    refine ⟨fun i=>physicalScalarDomain_scale (hy.1 i) ht,?_⟩
    intro i j hij
    apply hy.2
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr ht.ne') hij

def physicalAiryBasePoint {d : ℕ} (numerator upper : Fin d→Bool) : Point d :=
  fun i=>airyCoordinate (physicalBasePoint numerator upper i)

theorem physicalAiryBasePoint_mem {d : ℕ} {β : ℝ} (hβ : 0<β)
    (numerator upper : Fin d→Bool) :
    physicalAiryBasePoint numerator upper ∈
      physicalChamberSet (fun i=>physicalCharge β (numerator i)) upper := by
  have hleft i : airyInverse (physicalAiryBasePoint numerator upper i)=physicalBasePoint numerator upper i :=
    airyInverse_airyCoordinate (physicalBasePoint_re_pos numerator upper i)
  refine ⟨fun i=>?_,?_⟩
  · have hi := airyCoordinate_physicalBasePoint_im numerator upper i
    have hslit : physicalAiryBasePoint numerator upper i∈Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      right
      cases h: upper i <;> simp only [h,reflectComplex,Bool.false_eq_true,if_false,if_true,
        Complex.conj_im] at hi
      · dsimp [physicalAiryBasePoint]
        linarith
      · exact hi.ne'
    refine ⟨⟨hslit,?_⟩,⟨hi,physicalBasePoint_gap hβ numerator upper i⟩⟩
    change 0<(airyInverse (physicalAiryBasePoint numerator upper i)).re ∧
      (airyInverse (physicalAiryBasePoint numerator upper i)).re <
        (reflectComplex (upper i) (airyInverse (physicalAiryBasePoint numerator upper i))).im
    rw [hleft]
    exact ⟨physicalBasePoint_re_pos numerator upper i,physicalBasePoint_sector numerator upper i⟩
  · intro i j hij
    have he := congrArg airyInverse hij
    rw [hleft,hleft] at he
    exact physicalBasePoint_collisionFree numerator upper he

theorem physicalOpenCone_nonempty {d : ℕ} {β : ℝ} (hβ : 0<β)
    (numerator upper : Fin d→Bool) :
    (physicalOpenCone (fun i=>physicalCharge β (numerator i)) upper).carrier.Nonempty :=
  ⟨physicalAiryBasePoint numerator upper,physicalAiryBasePoint_mem hβ numerator upper⟩

theorem physicalChamber_gap {d : ℕ} {c : Fin d→ℂ} {upper : Fin d→Bool}
    {y : Point d} (hy : y∈physicalChamberSet c upper) (i : Fin d) :
    0<(-2*c i*y i).re := (hy.1 i).2.2

theorem physicalChamber_inverse_collisionFree {d : ℕ} {c : Fin d→ℂ} {upper : Fin d→Bool}
    {y : Point d} (hy : y∈physicalChamberSet c upper) :
    CollisionFree (fun i=>airyInverse (y i)) := by
  intro i j hij
  apply hy.2
  have he := congrArg airyCoordinate hij
  simpa only [airyCoordinate_airyInverse (Complex.slitPlane_ne_zero (hy.1 i).1.1),
    airyCoordinate_airyInverse (Complex.slitPlane_ne_zero (hy.1 j).1.1)] using he

theorem physicalChamber_root_sum_ne_zero {d : ℕ} (y : Point d) (i j : Fin d) :
    root (airyInverse (y i))+root (airyInverse (y j))≠0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re,Complex.zero_re] at hr
  linarith [root_airyInverse_re_pos (y i),root_airyInverse_re_pos (y j)]

end BourgadeHuang.EdgeCMS


