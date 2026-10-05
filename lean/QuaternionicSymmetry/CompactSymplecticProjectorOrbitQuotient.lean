import QuaternionicSymmetry.CompactSymplecticProjectorOrbit
import Mathlib.Topology.Homeomorph.Lemmas

/-! Descent of the genuine matrix projector orbit to the compact coset carrier. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorOrbitQuotient

open Matrix Topology CompactSymplecticProjectiveQuotient CompactSymplecticProjectorOrbit
open scoped Matrix.Norms.Elementwise
noncomputable section

private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev P (n : ℕ) := firstPairProjector n

/-- Conjugation of the coordinate projector respects group multiplication. -/
theorem orbitProjector_mul (n : ℕ) (u v : G n) :
    orbitProjector n (u * v) =
      (u.1 : Matrix _ _ ℂ) * orbitProjector n v *
        ((u⁻¹).1 : Matrix _ _ ℂ) := by
  simp only [orbitProjector_eq_mul_inverse, _root_.mul_inv_rev,
    Subgroup.coe_mul, Submonoid.coe_mul, mul_assoc]

/-- A stabilizer element fixes the projector under conjugation. -/
theorem orbitProjector_of_mem (n : ℕ) (k : G n)
    (hk : k ∈ firstPairStabilizer n) : orbitProjector n k = P n := by
  have hki : (k.1.1 : Matrix _ _ ℂ) * ((k⁻¹).1.1 : Matrix _ _ ℂ) = 1 := by
    change ((k * k⁻¹ : G n).1.1 : Matrix _ _ ℂ) = 1
    simp
  rw [orbitProjector_eq_mul_inverse]
  change (k.1 : Matrix _ _ ℂ) * P n * ((k⁻¹).1 : Matrix _ _ ℂ) = P n
  calc
    _ = P n * ((k.1 : Matrix _ _ ℂ) * ((k⁻¹).1 : Matrix _ _ ℂ)) := by
      rw [← mul_assoc, hk]
    _ = P n := by rw [hki, mul_one]

/-- The orbit is unchanged on right cosets of the projector stabilizer. -/
theorem orbitProjector_mul_stabilizer (n : ℕ) (u : G n)
    (k : firstPairStabilizer n) :
    orbitProjector n (u * (k : G n)) = orbitProjector n u := by
  rw [orbitProjector_mul, orbitProjector_of_mem n k k.2,
    ← orbitProjector_eq_mul_inverse]

/-- The projector orbit as an honest function on the coset quotient. -/
def quotientOrbitProjector (n : ℕ) : ProjectiveCarrier n →
    Matrix (Fin (n + 1) ⊕ Fin (n + 1))
      (Fin (n + 1) ⊕ Fin (n + 1)) ℂ :=
  fun q => Quotient.liftOn' q (orbitProjector n) (by
    intro u v huv
    have hk : u⁻¹ * v ∈ firstPairStabilizer n :=
      QuotientGroup.leftRel_apply.mp huv
    have hv : v = u * (u⁻¹ * v) := by simp
    rw [hv]
    exact (orbitProjector_mul_stabilizer n u ⟨u⁻¹ * v, hk⟩).symm)

@[simp]
theorem quotientOrbitProjector_mk (n : ℕ) (u : G n) :
    quotientOrbitProjector n (u : ProjectiveCarrier n) =
      orbitProjector n u := rfl

/-- The descended orbit map is continuous for the genuine quotient topology. -/
theorem continuous_quotientOrbitProjector (n : ℕ) :
    Continuous (quotientOrbitProjector n) := by
  apply (QuotientGroup.isQuotientMap_mk (firstPairStabilizer n)).continuous_iff.mpr
  simpa only [Function.comp_def, quotientOrbitProjector_mk] using
    continuous_orbitProjector n

/-- A group element fixes the projector exactly when it lies in the
coordinate-pair stabilizer. -/
theorem mem_firstPairStabilizer_iff_orbitProjector_eq (n : ℕ) (k : G n) :
    k ∈ firstPairStabilizer n ↔ orbitProjector n k = P n := by
  constructor
  · exact orbitProjector_of_mem n k
  · intro h
    have hki : ((k⁻¹).1.1 : Matrix _ _ ℂ) * (k.1.1 : Matrix _ _ ℂ) = 1 := by
      change ((k⁻¹ * k : G n).1.1 : Matrix _ _ ℂ) = 1
      simp
    change (k.1 : Matrix _ _ ℂ) * P n = P n * (k.1 : Matrix _ _ ℂ)
    calc
      (k.1 : Matrix _ _ ℂ) * P n = orbitProjector n k * (k.1 : Matrix _ _ ℂ) := by
        rw [orbitProjector_eq_mul_inverse]
        simp [mul_assoc]
      _ = P n * (k.1 : Matrix _ _ ℂ) := by rw [h]

/-- Equal orbit projectors imply equality of the corresponding right cosets. -/
theorem orbitProjector_eq_implies_coset_eq (n : ℕ) (u v : G n)
    (h : orbitProjector n u = orbitProjector n v) :
    (u : ProjectiveCarrier n) = v := by
  apply QuotientGroup.eq.mpr
  apply (mem_firstPairStabilizer_iff_orbitProjector_eq n (u⁻¹ * v)).mpr
  have hu := orbitProjector_mul n u⁻¹ u
  have hv := orbitProjector_mul n u⁻¹ v
  rw [inv_mul_cancel] at hu
  rw [h] at hu
  rw [← hu] at hv
  exact hv.trans (by simp [orbitProjector])

/-- The descended orbit map is injective; the quotient has no extra
identifications beyond equality of concrete Hermitian projectors. -/
theorem quotientOrbitProjector_injective (n : ℕ) :
    Function.Injective (quotientOrbitProjector n) := by
  intro q r h
  induction q using QuotientGroup.induction_on with
  | _ u =>
    induction r using QuotientGroup.induction_on with
    | _ v =>
      exact orbitProjector_eq_implies_coset_eq n u v (by simpa using h)

/-- The compact quotient is homeomorphic to its actual projector orbit
inside the Hausdorff complex matrix space. -/
theorem quotientOrbitProjector_closedEmbedding (n : ℕ) :
    IsClosedEmbedding (quotientOrbitProjector n) :=
  (continuous_quotientOrbitProjector n).isClosedEmbedding
    (quotientOrbitProjector_injective n)

/-- The actual orbit of the paired-coordinate Hermitian projector. -/
def projectorOrbit (n : ℕ) : Set
    (Matrix (Fin (n + 1) ⊕ Fin (n + 1))
      (Fin (n + 1) ⊕ Fin (n + 1)) ℂ) :=
  Set.range (orbitProjector n)

theorem quotientOrbitProjector_range (n : ℕ) :
    Set.range (quotientOrbitProjector n) = projectorOrbit n := by
  ext A
  constructor
  · rintro ⟨q, rfl⟩
    induction q using QuotientGroup.induction_on with
    | _ u => exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(u : ProjectiveCarrier n), rfl⟩

/-- A checked topological identification of the compact coset carrier
with the concrete matrix-projector orbit. -/
def carrierHomeomorphProjectorOrbit (n : ℕ) :
    ProjectiveCarrier n ≃ₜ projectorOrbit n := by
  let f : ProjectiveCarrier n → projectorOrbit n := fun q =>
    ⟨quotientOrbitProjector n q, by
      rw [← quotientOrbitProjector_range]
      exact Set.mem_range_self q⟩
  have hfcont : Continuous f :=
    (continuous_quotientOrbitProjector n).subtype_mk _
  have hfinj : Function.Injective f := by
    intro q r h
    exact quotientOrbitProjector_injective n (congrArg Subtype.val h)
  have hfsurj : Function.Surjective f := by
    rintro ⟨p, hp⟩
    rw [← quotientOrbitProjector_range] at hp
    obtain ⟨q, hq⟩ := hp
    exact ⟨q, Subtype.ext hq⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective f ⟨hfinj, hfsurj⟩) hfcont

end
end QuaternionicSymmetry.CompactSymplecticProjectorOrbitQuotient
