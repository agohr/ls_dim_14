import QuaternionicSymmetry.CompactSymplecticProjectiveCarrierDimension
import QuaternionicSymmetry.CompactSymplecticQuaternionicOrbit

/-! The actual compact symplectic matrix group acts transitively on the
checked orbit of rank-two quaternionic Hermitian projectors by matrix
conjugation. This is a concrete algebraic action, not a homogeneous-space
predicate or a model-identification premise. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorOrbitAction

open Matrix CompactSymplecticHaar CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbit
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticHomogeneousAtlasSource
open scoped Matrix.Norms.Elementwise
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

/-- Actual conjugation on the matrix projector orbit. -/
def conjugate (n : ℕ) (u : G n) (p : projectorOrbit n) : projectorOrbit n := by
  let v := Classical.choose p.2
  have hv : orbitProjector n v = p.1 := Classical.choose_spec p.2
  refine ⟨(u.1 : Matrix (I n) (I n) ℂ) * p.1 *
    (u.1 : Matrix (I n) (I n) ℂ)ᴴ, ⟨u * v, ?_⟩⟩
  rw [← hv]
  exact CompactSymplecticProjectorOrbitQuotient.orbitProjector_mul n u v

theorem conjugate_one (n : ℕ) (p : projectorOrbit n) :
    conjugate n 1 p = p := by
  apply Subtype.ext
  change (1 : Matrix (I n) (I n) ℂ) * p.1 *
    (1 : Matrix (I n) (I n) ℂ)ᴴ = p.1
  simp

theorem conjugate_mul (n : ℕ) (u v : G n) (p : projectorOrbit n) :
    conjugate n (u * v) p = conjugate n u (conjugate n v p) := by
  apply Subtype.ext
  change ((u.1 : Matrix (I n) (I n) ℂ) *
      (v.1 : Matrix (I n) (I n) ℂ)) * p.1 *
      ((u.1 : Matrix (I n) (I n) ℂ) *
        (v.1 : Matrix (I n) (I n) ℂ))ᴴ =
    (u.1 : Matrix (I n) (I n) ℂ) *
      ((v.1 : Matrix (I n) (I n) ℂ) * p.1 *
        (v.1 : Matrix (I n) (I n) ℂ)ᴴ) *
      (u.1 : Matrix (I n) (I n) ℂ)ᴴ
  rw [Matrix.conjTranspose_mul]
  simp only [mul_assoc]

theorem conjugate_transitive (n : ℕ) (p q : projectorOrbit n) :
    ∃ u : G n, conjugate n u p = q := by
  obtain ⟨v, hv⟩ := p.2
  obtain ⟨w, hw⟩ := q.2
  refine ⟨w * v⁻¹, ?_⟩
  apply Subtype.ext
  change ((w * v⁻¹).1 : Matrix (I n) (I n) ℂ) * p.1 *
      ((w * v⁻¹).1 : Matrix (I n) (I n) ℂ)ᴴ = q.1
  rw [← hv, ← hw]
  exact (CompactSymplecticProjectorOrbitQuotient.orbitProjector_mul n (w * v⁻¹) v).symm.trans
    (by simp)

theorem continuous_conjugate (n : ℕ) :
    Continuous (fun p : G n × projectorOrbit n => conjugate n p.1 p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : G n × projectorOrbit n =>
    (p.1.1 : Matrix (I n) (I n) ℂ) * p.2.1 *
      (p.1.1 : Matrix (I n) (I n) ℂ)ᴴ)
  fun_prop

private theorem carrierHomeomorph_coe (n : ℕ) (q : ProjectiveCarrier n) :
    ((carrierHomeomorphProjectorOrbit n q).1 : Matrix (I n) (I n) ℂ) =
      quotientOrbitProjector n q := rfl

private theorem leftCosetAction_coe (n : ℕ) (u v : G n) :
    leftCosetAction n u (v : ProjectiveCarrier n) =
      ((u * v : G n) : ProjectiveCarrier n) := rfl

/-- The concrete matrix conjugation agrees pointwise with the already
constructed left-coset action through the quotient-orbit homeomorphism. -/
theorem orbit_action_agrees_with_coset_action (n : ℕ) (u : G n)
    (q : ProjectiveCarrier n) :
    carrierHomeomorphProjectorOrbit n (leftCosetAction n u q) =
      conjugate n u (carrierHomeomorphProjectorOrbit n q) := by
  induction q using Quotient.inductionOn' with
  | _ v =>
    apply Subtype.ext
    change quotientOrbitProjector n (leftCosetAction n u (v : ProjectiveCarrier n)) =
      (u.1 : Matrix (I n) (I n) ℂ) *
        (carrierHomeomorphProjectorOrbit n (v : ProjectiveCarrier n)).1 *
        (u.1 : Matrix (I n) (I n) ℂ)ᴴ
    rw [carrierHomeomorph_coe, leftCosetAction_coe]
    change orbitProjector n (u * v) =
      (u.1 : Matrix (I n) (I n) ℂ) * orbitProjector n v *
        (u.1 : Matrix (I n) (I n) ℂ)ᴴ
    exact CompactSymplecticProjectorOrbitQuotient.orbitProjector_mul n u v

end
end QuaternionicSymmetry.CompactSymplecticProjectorOrbitAction
