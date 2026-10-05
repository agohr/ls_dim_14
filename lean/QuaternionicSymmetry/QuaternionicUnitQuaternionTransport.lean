import QuaternionicSymmetry.QuaternionicUnitScalarIsometries

/-! Explicit unit-quaternion transport between imaginary unit directions. -/

namespace QuaternionicSymmetry.QuaternionicUnitQuaternionTransport

open scoped Quaternion

noncomputable section

/-- A unit pure imaginary quaternion squares to minus one. -/
theorem imaginaryUnit_sq (u : ℍ) (hu : u.re = 0)
    (hn : Quaternion.normSq u = 1) : u * u = -1 := by
  have h := (Quaternion.sq_eq_neg_normSq).mpr hu
  rw [hn] at h
  simpa only [pow_two] using h

/-- The elementary transporter `1 - v u` intertwines `u` and `v`. -/
theorem rawTransport_intertwines (u v : ℍ)
    (hu : u * u = -1) (hv : v * v = -1) :
    (1 - v * u) * u = v * (1 - v * u) := by
  calc
    (1 - v * u) * u = u + v := by
      rw [sub_mul, one_mul, mul_assoc, hu]
      simp
    _ = v * (1 - v * u) := by
      rw [mul_sub, mul_one, ← mul_assoc, hv]
      simp [add_comm]

/-- The raw transporter is nonzero except at the antipodal direction. -/
theorem rawTransport_ne_zero (u v : ℍ)
    (hu : u * u = -1) (hanti : v ≠ -u) :
    1 - v * u ≠ 0 := by
  intro hzero
  have hmul : v * u = 1 := (sub_eq_zero.mp hzero).symm
  have h := congrArg (fun z : ℍ => z * u) hmul
  change (v * u) * u = (1 : ℍ) * u at h
  rw [mul_assoc, hu, one_mul, mul_neg, mul_one] at h
  exact hanti (by simpa using congrArg Neg.neg h)

/-- Normalize a nonzero quaternion to a unit quaternion. -/
def normalize (q : ℍ) (hq : q ≠ 0) : unitary ℍ := by
  let r : ℍ := (‖q‖⁻¹ : ℝ) • q
  have hn : Quaternion.normSq r = 1 := by
    rw [Quaternion.normSq_smul, Quaternion.normSq_eq_norm_mul_self]
    have hnorm : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
    field_simp [hnorm]
  refine ⟨r, (Unitary.mem_iff).mpr ?_⟩
  constructor
  · rw [Quaternion.star_mul_self, hn]
    rfl
  · rw [Quaternion.self_mul_star, hn]
    rfl

def ofNormSqOne (q : ℍ) (hq : Quaternion.normSq q = 1) : unitary ℍ :=
  ⟨q, (Unitary.mem_iff).mpr ⟨by rw [Quaternion.star_mul_self, hq]; rfl,
    by rw [Quaternion.self_mul_star, hq]; rfl⟩⟩

@[simp] theorem normalize_coe (q : ℍ) (hq : q ≠ 0) :
    ((normalize q hq : unitary ℍ) : ℍ) = (‖q‖⁻¹ : ℝ) • q := rfl

theorem normalize_intertwines (q u v : ℍ) (hq : q ≠ 0)
    (h : q * u = v * q) :
    ((normalize q hq : unitary ℍ) : ℍ) * u =
      v * ((normalize q hq : unitary ℍ) : ℍ) := by
  simp only [normalize_coe, smul_mul_assoc, mul_smul_comm]
  rw [h]

/-- Every non-antipodal pair of imaginary unit directions has an explicitly
constructed unit-quaternion transporter. -/
theorem exists_unitTransport_nonantipodal (u v : ℍ)
    (hu : u.re = 0) (hv : v.re = 0)
    (hnu : Quaternion.normSq u = 1) (hnv : Quaternion.normSq v = 1)
    (hanti : v ≠ -u) :
    ∃ q : unitary ℍ, (q : ℍ) * u = v * q := by
  have hu2 := imaginaryUnit_sq u hu hnu
  have hv2 := imaginaryUnit_sq v hv hnv
  let q := normalize (1 - v * u) (rawTransport_ne_zero u v hu2 hanti)
  exact ⟨q, normalize_intertwines _ u v _
    (rawTransport_intertwines u v hu2 hv2)⟩

def basisI : ℍ := ⟨0, 1, 0, 0⟩
def basisJ : ℍ := ⟨0, 0, 1, 0⟩

theorem basisI_unit :
    basisI.re = 0 ∧ Quaternion.normSq basisI = 1 := by
  simp [basisI, Quaternion.normSq_def']

theorem basisJ_unit :
    basisJ.re = 0 ∧ Quaternion.normSq basisJ = 1 := by
  simp [basisJ, Quaternion.normSq_def']

private theorem basisJ_ne_basisI : basisJ ≠ basisI := by
  intro h
  have := congrArg (fun z : ℍ => z.imI) h
  norm_num [basisI, basisJ] at this

private theorem basisJ_ne_neg_basisI : basisJ ≠ -basisI := by
  intro h
  have := congrArg (fun z : ℍ => z.imI) h
  norm_num [basisI, basisJ] at this

private def intermediate (u : ℍ) : ℍ := by
  classical
  exact if u = basisI ∨ u = -basisI then basisJ else basisI

private theorem intermediate_unit (u : ℍ) :
    (intermediate u).re = 0 ∧
      Quaternion.normSq (intermediate u) = 1 := by
  classical
  unfold intermediate
  split_ifs <;> [exact basisJ_unit; exact basisI_unit]

private theorem intermediate_ne_pos (u : ℍ) : intermediate u ≠ u := by
  classical
  unfold intermediate
  split_ifs with h
  · rcases h with h | h
    · rw [h]
      exact basisJ_ne_basisI
    · rw [h]
      exact basisJ_ne_neg_basisI
  · exact fun hu => h (Or.inl hu.symm)

private theorem intermediate_ne_neg (u : ℍ) : intermediate u ≠ -u := by
  classical
  unfold intermediate
  split_ifs with h
  · rcases h with h | h
    · rw [h]
      exact basisJ_ne_neg_basisI
    · rw [h]
      simpa using basisJ_ne_basisI
  · exact fun hu => h (Or.inr (by simpa using (congrArg Neg.neg hu).symm))

/-- Every pair of unit imaginary quaternion directions has a unit
transporter. The antipodal case factors through a third basis direction. -/
theorem exists_unitTransport (u v : ℍ)
    (hu : u.re = 0) (hv : v.re = 0)
    (hnu : Quaternion.normSq u = 1) (hnv : Quaternion.normSq v = 1) :
    ∃ q : unitary ℍ, (q : ℍ) * u = v * q := by
  by_cases hanti : v = -u
  · let w := intermediate u
    have hw := intermediate_unit u
    obtain ⟨q₁, hq₁⟩ := exists_unitTransport_nonantipodal u w
      hu hw.1 hnu hw.2 (intermediate_ne_neg u)
    obtain ⟨q₂, hq₂⟩ := exists_unitTransport_nonantipodal w v
      hw.1 hv hw.2 hnv (by
        rw [hanti]
        intro h
        exact intermediate_ne_pos u (neg_injective h).symm)
    refine ⟨q₂ * q₁, ?_⟩
    change ((q₂ : ℍ) * (q₁ : ℍ)) * u =
      v * ((q₂ : ℍ) * (q₁ : ℍ))
    rw [mul_assoc, hq₁, ← mul_assoc, hq₂, mul_assoc]
  · exact exists_unitTransport_nonantipodal u v hu hv hnu hnv hanti

theorem rawTransport_commutes_axis (a u v : ℍ)
    (hau : a * u = -u * a) (hav : a * v = -v * a) :
    a * (1 - v * u) = (1 - v * u) * a := by
  have hcomm : a * (v * u) = (v * u) * a := by
    calc
      a * (v * u) = (a * v) * u := by rw [mul_assoc]
      _ = (-v * a) * u := by rw [hav]
      _ = -v * (a * u) := by simp only [neg_mul, mul_assoc]
      _ = -v * (-u * a) := by rw [hau]
      _ = v * (u * a) := by simp
      _ = (v * u) * a := by rw [mul_assoc]
  simp only [mul_sub, sub_mul, mul_one, one_mul, hcomm]

theorem normalize_commutes_axis (a q : ℍ) (hq : q ≠ 0)
    (h : a * q = q * a) :
    a * ((normalize q hq : unitary ℍ) : ℍ) =
      ((normalize q hq : unitary ℍ) : ℍ) * a := by
  simp only [normalize_coe, mul_smul_comm, smul_mul_assoc]
  rw [h]

/-- Transport in the imaginary circle perpendicular to a fixed unit axis.
The chosen quaternion also commutes with that axis. -/
theorem exists_unitTransport_commuting_axis (a u v : ℍ)
    (hna : Quaternion.normSq a = 1)
    (hu : u.re = 0) (hv : v.re = 0)
    (hnu : Quaternion.normSq u = 1) (hnv : Quaternion.normSq v = 1)
    (hau : a * u = -u * a) (hav : a * v = -v * a) :
    ∃ q : unitary ℍ,
      (q : ℍ) * u = v * q ∧ (q : ℍ) * a = a * q := by
  by_cases hanti : v = -u
  · refine ⟨ofNormSqOne a hna, ?_, rfl⟩
    change a * u = v * a
    rw [hanti]
    exact hau
  · let r := 1 - v * u
    have hu2 := imaginaryUnit_sq u hu hnu
    have hv2 := imaginaryUnit_sq v hv hnv
    have hr : r ≠ 0 := rawTransport_ne_zero u v hu2 hanti
    refine ⟨normalize r hr,
      normalize_intertwines r u v hr (rawTransport_intertwines u v hu2 hv2), ?_⟩
    exact (normalize_commutes_axis a r hr
      (rawTransport_commutes_axis a u v hau hav)).symm

end
end QuaternionicSymmetry.QuaternionicUnitQuaternionTransport
