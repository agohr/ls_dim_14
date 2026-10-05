import QuaternionicSymmetry.QuaternionicUnitQuaternionTransport

/-! A single unit quaternion transports an oriented orthonormal pair of
imaginary quaternionic axes. -/

namespace QuaternionicSymmetry.QuaternionicUnitQuaternionPairTransport

open scoped Quaternion
open QuaternionicUnitQuaternionTransport

noncomputable section

private theorem basisI_basisJ_anti :
    basisI * basisJ = -basisJ * basisI := by
  ext <;> norm_num [basisI, basisJ, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

/-- Transport both standard imaginary axes to any pair satisfying the same
quaternionic multiplication relations. -/
theorem exists_unitPairTransport (u v : ℍ)
    (hu : u.re = 0) (hv : v.re = 0)
    (hnu : Quaternion.normSq u = 1) (hnv : Quaternion.normSq v = 1)
    (huv : u * v = -v * u) :
    ∃ q : unitary ℍ,
      (q : ℍ) * basisI = u * q ∧
      (q : ℍ) * basisJ = v * q := by
  obtain ⟨q₁, hq₁⟩ := exists_unitTransport basisI u
    basisI_unit.1 hu basisI_unit.2 hnu
  have hs₁ : star (q₁ : ℍ) * (q₁ : ℍ) = 1 :=
    (Unitary.mem_iff.mp q₁.property).1
  have hs₂ : (q₁ : ℍ) * star (q₁ : ℍ) = 1 :=
    (Unitary.mem_iff.mp q₁.property).2
  let w : ℍ := star (q₁ : ℍ) * v * q₁
  have hwre : w.re = 0 := by
    simpa only [w, star_star] using
      (QuaternionicUnitScalarIsometries.conjugate_imaginary
        (star (q₁ : ℍ)) v hv)
  have hwn : Quaternion.normSq w = 1 := by
    dsimp [w]
    rw [map_mul, map_mul, Quaternion.normSq_star,
      QuaternionicUnitScalarIsometries.normSq_one_of_unitary]
    simp [hnv]
  have hqw : (q₁ : ℍ) * w = v * q₁ := by
    calc
      (q₁ : ℍ) * w = ((q₁ : ℍ) * star (q₁ : ℍ)) * v * q₁ := by
        simp only [w, mul_assoc]
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
            (star (q₁ : ℍ) * v * q₁) := by rw [← hi]
      _ = star (q₁ : ℍ) * (u * v) * q₁ := hconj u v
      _ = -(star (q₁ : ℍ) * (v * u) * q₁) := by rw [huv]; simp
      _ = -w * basisI := by
        rw [hi]
        rw [← hconj v u]
        simp only [w, neg_mul]
  obtain ⟨q₂, hq₂j, hq₂i⟩ := exists_unitTransport_commuting_axis
    basisI basisJ w basisI_unit.2 basisJ_unit.1 hwre
      basisJ_unit.2 hwn basisI_basisJ_anti hanti
  refine ⟨q₁ * q₂, ?_, ?_⟩
  · change ((q₁ : ℍ) * (q₂ : ℍ)) * basisI =
      u * ((q₁ : ℍ) * (q₂ : ℍ))
    rw [mul_assoc, hq₂i, ← mul_assoc, hq₁, mul_assoc]
  · change ((q₁ : ℍ) * (q₂ : ℍ)) * basisJ =
      v * ((q₁ : ℍ) * (q₂ : ℍ))
    rw [mul_assoc, hq₂j, ← mul_assoc, hqw, mul_assoc]

end
end QuaternionicSymmetry.QuaternionicUnitQuaternionPairTransport
