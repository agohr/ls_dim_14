import QuaternionicSymmetry.QuaternionicUnitQuaternionPairLocalSection

/-! Every oriented pair of imaginary quaternionic axes has an explicit smooth
local section of the unit-quaternion rotation map. The chart depends on one
fixed pointwise quaternion lift, so it makes no global overlap choice. -/

namespace QuaternionicSymmetry.QuaternionicUnitQuaternionLocalRotationLift

open scoped Quaternion ContDiff Topology
open QuaternionicUnitQuaternionTransport
  QuaternionicUnitQuaternionPairTransport
  QuaternionicUnitQuaternionPairLocalSection

noncomputable section

def backPair (q : unitary ℍ) (p : ℍ × ℍ) : ℍ × ℍ :=
  (star (q : ℍ) * p.1 * q, star (q : ℍ) * p.2 * q)

def localDomain (q : unitary ℍ) : Set (ℍ × ℍ) :=
  (backPair q) ⁻¹' goodPair

def localLiftRaw (q : unitary ℍ) (p : ℍ × ℍ) : ℍ :=
  (q : ℍ) * pairRaw (backPair q p)

theorem contDiff_backPair (q : unitary ℍ) :
    ContDiff ℝ ∞ (backPair q) := by
  have hfst : ContDiff ℝ ∞
      (fun p : ℍ × ℍ => star (q : ℍ) * p.1 * q) :=
    (contDiff_const.mul contDiff_fst).mul contDiff_const
  have hsnd : ContDiff ℝ ∞
      (fun p : ℍ × ℍ => star (q : ℍ) * p.2 * q) :=
    (contDiff_const.mul contDiff_snd).mul contDiff_const
  exact hfst.prodMk hsnd

theorem isOpen_localDomain (q : unitary ℍ) : IsOpen (localDomain q) :=
  isOpen_goodPair.preimage (contDiff_backPair q).continuous

theorem contDiffAt_localLiftRaw (q : unitary ℍ) (p : ℍ × ℍ)
    (hp : p ∈ localDomain q) :
    ContDiffAt ℝ ∞ (localLiftRaw q) p := by
  exact contDiffAt_const.mul
    ((contDiffAt_pairRaw (backPair q p) hp).comp p
      (contDiff_backPair q).contDiffAt)

theorem contDiffOn_localLiftRaw (q : unitary ℍ) :
    ContDiffOn ℝ ∞ (localLiftRaw q) (localDomain q) := by
  intro p hp
  exact (contDiffAt_localLiftRaw q p hp).contDiffWithinAt

theorem backPair_at_axes (q : unitary ℍ) (u v : ℍ)
    (hqi : (q : ℍ) * basisI = u * q)
    (hqj : (q : ℍ) * basisJ = v * q) :
    backPair q (u, v) = (basisI, basisJ) := by
  have hs : star (q : ℍ) * (q : ℍ) = 1 :=
    (Unitary.mem_iff.mp q.property).1
  apply Prod.ext
  · change star (q : ℍ) * u * q = basisI
    calc
      _ = star (q : ℍ) * ((q : ℍ) * basisI) := by rw [hqi]; simp [mul_assoc]
      _ = basisI := by rw [← mul_assoc, hs, one_mul]
  · change star (q : ℍ) * v * q = basisJ
    calc
      _ = star (q : ℍ) * ((q : ℍ) * basisJ) := by rw [hqj]; simp [mul_assoc]
      _ = basisJ := by rw [← mul_assoc, hs, one_mul]

theorem axes_mem_localDomain (q : unitary ℍ) (u v : ℍ)
    (hqi : (q : ℍ) * basisI = u * q)
    (hqj : (q : ℍ) * basisJ = v * q) :
    (u, v) ∈ localDomain q := by
  change backPair q (u, v) ∈ goodPair
  rw [backPair_at_axes q u v hqi hqj]
  exact standard_mem_goodPair

theorem backPair_valid (q : unitary ℍ) (u v : ℍ)
    (hu : u.re = 0) (hv : v.re = 0)
    (hnu : Quaternion.normSq u = 1) (hnv : Quaternion.normSq v = 1)
    (huv : u * v = -v * u) :
    (backPair q (u, v)).1.re = 0 ∧
    (backPair q (u, v)).2.re = 0 ∧
    Quaternion.normSq (backPair q (u, v)).1 = 1 ∧
    Quaternion.normSq (backPair q (u, v)).2 = 1 ∧
    (backPair q (u, v)).1 * (backPair q (u, v)).2 =
      -(backPair q (u, v)).2 * (backPair q (u, v)).1 := by
  have hs : (q : ℍ) * star (q : ℍ) = 1 :=
    (Unitary.mem_iff.mp q.property).2
  have hconj (a b : ℍ) :
      (star (q : ℍ) * a * q) * (star (q : ℍ) * b * q) =
        star (q : ℍ) * (a * b) * q := by
    calc
      _ = star (q : ℍ) * a * ((q : ℍ) * star (q : ℍ)) * b * q := by
        simp only [mul_assoc]
      _ = _ := by rw [hs]; simp [mul_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [backPair, star_star] using
      (QuaternionicUnitScalarIsometries.conjugate_imaginary
        (star (q : ℍ)) u hu)
  · simpa only [backPair, star_star] using
      (QuaternionicUnitScalarIsometries.conjugate_imaginary
        (star (q : ℍ)) v hv)
  · change Quaternion.normSq (star (q : ℍ) * u * (q : ℍ)) = 1
    rw [map_mul, map_mul, Quaternion.normSq_star,
      QuaternionicUnitScalarIsometries.normSq_one_of_unitary]
    simp [hnu]
  · change Quaternion.normSq (star (q : ℍ) * v * (q : ℍ)) = 1
    rw [map_mul, map_mul, Quaternion.normSq_star,
      QuaternionicUnitScalarIsometries.normSq_one_of_unitary]
    simp [hnv]
  · change (star (q : ℍ) * u * q) * (star (q : ℍ) * v * q) =
      -(star (q : ℍ) * v * q) * (star (q : ℍ) * u * q)
    rw [hconj u v, huv]
    simp only [neg_mul, mul_neg]
    rw [hconj v u]

/-- On valid quaternionic axis pairs in the local chart, the smooth raw
formula is a genuine unit-quaternion rotation lift. -/
theorem localLiftRaw_unit_and_intertwines (q : unitary ℍ) (u v : ℍ)
    (hu : u.re = 0) (hv : v.re = 0)
    (hnu : Quaternion.normSq u = 1) (hnv : Quaternion.normSq v = 1)
    (huv : u * v = -v * u)
    (hp : (u, v) ∈ localDomain q) :
    Quaternion.normSq (localLiftRaw q (u, v)) = 1 ∧
      localLiftRaw q (u, v) * basisI = u * localLiftRaw q (u, v) ∧
      localLiftRaw q (u, v) * basisJ = v * localLiftRaw q (u, v) := by
  let w := backPair q (u, v)
  obtain ⟨hw₁, hw₂, hwn₁, hwn₂, hwanti⟩ :=
    backPair_valid q u v hu hv hnu hnv huv
  obtain ⟨hrn, hri, hrj⟩ :=
    pairRaw_unit_and_intertwines w.1 w.2
      hw₁ hw₂ hwn₁ hwn₂ hwanti hp
  have hs : (q : ℍ) * star (q : ℍ) = 1 :=
    (Unitary.mem_iff.mp q.property).2
  have hqw₁ : (q : ℍ) * w.1 = u * q := by
    change (q : ℍ) * (star (q : ℍ) * u * q) = u * q
    simp only [← mul_assoc, hs, one_mul]
  have hqw₂ : (q : ℍ) * w.2 = v * q := by
    change (q : ℍ) * (star (q : ℍ) * v * q) = v * q
    simp only [← mul_assoc, hs, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · change Quaternion.normSq ((q : ℍ) * pairRaw w) = 1
    rw [map_mul, QuaternionicUnitScalarIsometries.normSq_one_of_unitary,
      hrn, one_mul]
  · change ((q : ℍ) * pairRaw w) * basisI =
      u * ((q : ℍ) * pairRaw w)
    rw [mul_assoc, hri, ← mul_assoc, hqw₁, mul_assoc]
  · change ((q : ℍ) * pairRaw w) * basisJ =
      v * ((q : ℍ) * pairRaw w)
    rw [mul_assoc, hrj, ← mul_assoc, hqw₂, mul_assoc]

/-- Every valid ordered pair has an open neighborhood with a smooth
unit-quaternion lift of the rotation on valid pairs in that neighborhood. -/
theorem exists_smooth_local_lift (u v : ℍ)
    (hu : u.re = 0) (hv : v.re = 0)
    (hnu : Quaternion.normSq u = 1) (hnv : Quaternion.normSq v = 1)
    (huv : u * v = -v * u) :
    ∃ q : unitary ℍ,
      (u, v) ∈ localDomain q ∧
      IsOpen (localDomain q) ∧
      ContDiffOn ℝ ∞ (localLiftRaw q) (localDomain q) ∧
      ∀ a b : ℍ, a.re = 0 → b.re = 0 →
        Quaternion.normSq a = 1 → Quaternion.normSq b = 1 →
        a * b = -b * a → (a, b) ∈ localDomain q →
        Quaternion.normSq (localLiftRaw q (a, b)) = 1 ∧
          localLiftRaw q (a, b) * basisI = a * localLiftRaw q (a, b) ∧
          localLiftRaw q (a, b) * basisJ = b * localLiftRaw q (a, b) := by
  obtain ⟨q, hqi, hqj⟩ := exists_unitPairTransport u v hu hv hnu hnv huv
  refine ⟨q, axes_mem_localDomain q u v hqi hqj,
    isOpen_localDomain q, contDiffOn_localLiftRaw q, ?_⟩
  intro a b ha hb hna hnb hab hp
  exact localLiftRaw_unit_and_intertwines q a b ha hb hna hnb hab hp

end
end QuaternionicSymmetry.QuaternionicUnitQuaternionLocalRotationLift
