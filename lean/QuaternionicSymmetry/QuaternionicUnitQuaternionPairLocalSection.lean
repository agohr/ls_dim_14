import QuaternionicSymmetry.QuaternionicUnitQuaternionSmoothTransport
import QuaternionicSymmetry.QuaternionicUnitQuaternionPairTransport

/-! A smooth quaternion formula on an open chart of ordered imaginary-axis
pairs. It becomes an `Sp(1)` lift on pairs satisfying the quaternion relations. -/

namespace QuaternionicSymmetry.QuaternionicUnitQuaternionPairLocalSection

open scoped Quaternion ContDiff Topology
open QuaternionicUnitQuaternionTransport
  QuaternionicUnitQuaternionSmoothTransport
  QuaternionicUnitQuaternionLocalSections

noncomputable section

private def starLinear : ℍ →ₗ[ℝ] ℍ where
  toFun := star
  map_add' a b := by simp
  map_smul' r a := by simp [Quaternion.star_smul]

private theorem contDiffAt_star (q : ℍ) :
    ContDiffAt ℝ ∞ (star : ℍ → ℍ) q := by
  change ContDiffAt ℝ ∞ starLinear q
  exact (starLinear.toContinuousLinearMap).contDiff.contDiffAt

def firstRaw (u : ℍ) : ℍ := normalizedRaw basisI u

def correctedSecond (p : ℍ × ℍ) : ℍ :=
  star (firstRaw p.1) * p.2 * firstRaw p.1

def pairRaw (p : ℍ × ℍ) : ℍ :=
  firstRaw p.1 * normalizedRaw basisJ (correctedSecond p)

def goodPair : Set (ℍ × ℍ) :=
  {p | p.1 ≠ -basisI ∧ correctedSecond p ≠ -basisJ}

theorem contDiffAt_pairRaw (p : ℍ × ℍ) (hp : p ∈ goodPair) :
    ContDiffAt ℝ ∞ pairRaw p := by
  have hfirst : ContDiffAt ℝ ∞ (fun z : ℍ × ℍ => firstRaw z.1) p :=
    (contDiffAt_normalizedRaw basisI p.1
      (imaginaryUnit_sq basisI basisI_unit.1 basisI_unit.2) hp.1).comp
        p contDiffAt_fst
  have hstar : ContDiffAt ℝ ∞
      (fun z : ℍ × ℍ => star (firstRaw z.1)) p :=
    (contDiffAt_star (firstRaw p.1)).comp p hfirst
  have hcorrected : ContDiffAt ℝ ∞ correctedSecond p :=
    (hstar.mul contDiffAt_snd).mul hfirst
  have hsecond : ContDiffAt ℝ ∞
      (fun z : ℍ × ℍ => normalizedRaw basisJ (correctedSecond z)) p :=
    (contDiffAt_normalizedRaw basisJ (correctedSecond p)
      (imaginaryUnit_sq basisJ basisJ_unit.1 basisJ_unit.2) hp.2).comp
        p hcorrected
  exact hfirst.mul hsecond

theorem isOpen_goodPair : IsOpen goodPair := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hfirst : ContinuousAt (fun z : ℍ × ℍ => firstRaw z.1) p :=
    ((contDiffAt_normalizedRaw basisI p.1
      (imaginaryUnit_sq basisI basisI_unit.1 basisI_unit.2) hp.1).comp
        p contDiffAt_fst).continuousAt
  have hcorrected : ContinuousAt correctedSecond p :=
    ((continuousAt_star.comp hfirst).mul continuousAt_snd).mul hfirst
  have h₁ : {z : ℍ × ℍ | z.1 ≠ -basisI} ∈ 𝓝 p :=
    (isOpen_ne.preimage continuous_fst).mem_nhds hp.1
  have h₂ : {z : ℍ × ℍ | correctedSecond z ≠ -basisJ} ∈ 𝓝 p :=
    hcorrected.preimage_mem_nhds (isOpen_ne.mem_nhds hp.2)
  exact Filter.inter_mem h₁ h₂

theorem contDiffOn_pairRaw : ContDiffOn ℝ ∞ pairRaw goodPair := by
  intro p hp
  exact (contDiffAt_pairRaw p hp).contDiffWithinAt

private theorem basisI_basisJ_anti :
    basisI * basisJ = -basisJ * basisI := by
  ext <;> norm_num [basisI, basisJ, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

/-- The formula is a unit quaternion carrying the standard imaginary axes
to a valid ordered pair. -/
theorem pairRaw_unit_and_intertwines (u v : ℍ)
    (hu : u.re = 0) (hv : v.re = 0)
    (hnu : Quaternion.normSq u = 1) (hnv : Quaternion.normSq v = 1)
    (huv : u * v = -v * u)
    (hp : (u, v) ∈ goodPair) :
    Quaternion.normSq (pairRaw (u, v)) = 1 ∧
      pairRaw (u, v) * basisI = u * pairRaw (u, v) ∧
      pairRaw (u, v) * basisJ = v * pairRaw (u, v) := by
  let q₁ : unitary ℍ := localTransport basisI
    (imaginaryUnit_sq basisI basisI_unit.1 basisI_unit.2) ⟨u, hp.1⟩
  have hq₁ : (q₁ : ℍ) * basisI = u * q₁ :=
    localTransport_intertwines basisI
      (imaginaryUnit_sq basisI basisI_unit.1 basisI_unit.2)
      ⟨u, hp.1⟩ (imaginaryUnit_sq u hu hnu)
  have hq₁raw : (q₁ : ℍ) = firstRaw u := rfl
  have hs₁ : star (q₁ : ℍ) * (q₁ : ℍ) = 1 :=
    (Unitary.mem_iff.mp q₁.property).1
  have hs₂ : (q₁ : ℍ) * star (q₁ : ℍ) = 1 :=
    (Unitary.mem_iff.mp q₁.property).2
  let w : ℍ := correctedSecond (u, v)
  have hwdef : w = star (q₁ : ℍ) * v * q₁ := by
    simp [w, correctedSecond, ← hq₁raw]
  have hwre : w.re = 0 := by
    rw [hwdef]
    simpa only [star_star] using
      (QuaternionicUnitScalarIsometries.conjugate_imaginary
        (star (q₁ : ℍ)) v hv)
  have hwn : Quaternion.normSq w = 1 := by
    rw [hwdef, map_mul, map_mul, Quaternion.normSq_star,
      QuaternionicUnitScalarIsometries.normSq_one_of_unitary]
    simp [hnv]
  have hqw : (q₁ : ℍ) * w = v * q₁ := by
    calc
      (q₁ : ℍ) * w = ((q₁ : ℍ) * star (q₁ : ℍ)) * v * q₁ := by
        simp only [hwdef, mul_assoc]
      _ = v * q₁ := by rw [hs₂]; simp
  have hi : basisI = star (q₁ : ℍ) * u * q₁ := by
    calc
      basisI = (star (q₁ : ℍ) * (q₁ : ℍ)) * basisI := by rw [hs₁, one_mul]
      _ = star (q₁ : ℍ) * u * q₁ := by rw [mul_assoc, hq₁, ← mul_assoc]
  have hconj (a b : ℍ) :
      (star (q₁ : ℍ) * a * q₁) * (star (q₁ : ℍ) * b * q₁) =
        star (q₁ : ℍ) * (a * b) * q₁ := by
    calc
      _ = star (q₁ : ℍ) * a * ((q₁ : ℍ) * star (q₁ : ℍ)) * b * q₁ := by
        simp only [mul_assoc]
      _ = _ := by rw [hs₂]; simp [mul_assoc]
  have hanti : basisI * w = -w * basisI := by
    calc
      basisI * w =
          (star (q₁ : ℍ) * u * q₁) *
            (star (q₁ : ℍ) * v * q₁) := by rw [← hi, ← hwdef]
      _ = star (q₁ : ℍ) * (u * v) * q₁ := hconj u v
      _ = -(star (q₁ : ℍ) * (v * u) * q₁) := by rw [huv]; simp
      _ = -w * basisI := by
        rw [hi, hwdef]
        rw [← hconj v u]
        simp only [neg_mul]
  let q₂ : unitary ℍ := localTransport basisJ
    (imaginaryUnit_sq basisJ basisJ_unit.1 basisJ_unit.2) ⟨w, hp.2⟩
  have hq₂j : (q₂ : ℍ) * basisJ = w * q₂ :=
    localTransport_intertwines basisJ
      (imaginaryUnit_sq basisJ basisJ_unit.1 basisJ_unit.2)
      ⟨w, hp.2⟩ (imaginaryUnit_sq w hwre hwn)
  have hq₂i : (q₂ : ℍ) * basisI = basisI * q₂ :=
    (normalize_commutes_axis basisI (1 - w * basisJ)
      (rawTransport_ne_zero basisJ w
        (imaginaryUnit_sq basisJ basisJ_unit.1 basisJ_unit.2) hp.2)
      (rawTransport_commutes_axis basisI basisJ w
        basisI_basisJ_anti hanti)).symm
  have hraw : pairRaw (u, v) = (q₁ * q₂ : unitary ℍ) := by
    change firstRaw u * normalizedRaw basisJ w =
      ((q₁ : ℍ) * (q₂ : ℍ))
    rw [← hq₁raw]
    rfl
  rw [hraw]
  refine ⟨QuaternionicUnitScalarIsometries.normSq_one_of_unitary _, ?_, ?_⟩
  · change ((q₁ : ℍ) * (q₂ : ℍ)) * basisI =
      u * ((q₁ : ℍ) * (q₂ : ℍ))
    rw [mul_assoc, hq₂i, ← mul_assoc, hq₁, mul_assoc]
  · change ((q₁ : ℍ) * (q₂ : ℍ)) * basisJ =
      v * ((q₁ : ℍ) * (q₂ : ℍ))
    rw [mul_assoc, hq₂j, ← mul_assoc, hqw, mul_assoc]

theorem standard_mem_goodPair : (basisI, basisJ) ∈ goodPair := by
  have hi : basisI ≠ -basisI := by
    intro h
    have := congrArg (fun z : ℍ => z.imI) h
    norm_num [basisI] at this
  have hfirst : firstRaw basisI = 1 := by
    simp only [firstRaw, normalizedRaw,
      imaginaryUnit_sq basisI basisI_unit.1 basisI_unit.2]
    norm_num only [sub_neg_eq_add, one_add_one_eq_two]
    change ‖((2 : ℝ) : ℍ)‖⁻¹ • ((2 : ℝ) : ℍ) = 1
    rw [Quaternion.norm_coe]
    norm_num [Algebra.smul_def]
    exact inv_mul_cancel₀ (by
      intro h
      have := congrArg (fun z : ℍ => z.re) h
      norm_num at this)
  constructor
  · exact hi
  · simp only [correctedSecond, hfirst, star_one, one_mul, mul_one]
    intro h
    have := congrArg (fun z : ℍ => z.imJ) h
    norm_num [basisJ] at this

end
end QuaternionicSymmetry.QuaternionicUnitQuaternionPairLocalSection
