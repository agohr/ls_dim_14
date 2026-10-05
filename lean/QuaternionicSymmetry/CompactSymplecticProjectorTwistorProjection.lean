import QuaternionicSymmetry.CompactSymplecticProjectorTwistorNormalized

/-! An actual well-defined matrix-valued twistor projection from the
complex projective space of the defining symplectic representation to
quaternionic-line projectors. Its comparison to the smooth quotient orbit
and to the Levi-Civita twistor atlas remain separate obligations. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTwistorProjection

open CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnAlgebra
open CompactSymplecticProjectorTwistorAntipodal
open CompactSymplecticProjectorTwistorFiberLaw
open CompactSymplecticProjectorTwistorNormalized
open scoped LinearAlgebra.Projectivization

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

def projectiveProjector (n : ℕ) : ℙ ℂ (V n) → Mat n :=
  Projectivization.lift
    (fun v => normalizedProjector n v.1)
    (by
      intro a b t h
      have ht : t ≠ 0 := by
        intro ht
        apply a.2
        simpa [ht] using h
      change normalizedProjector n a.1 = normalizedProjector n b.1
      rw [h]
      exact normalizedProjector_smul n t b.1 ht)

@[simp] theorem projectiveProjector_mk (n : ℕ) (v : V n) (hv : v ≠ 0) :
    projectiveProjector n (Projectivization.mk ℂ v hv) =
      normalizedProjector n v := by
  simp [projectiveProjector]

theorem projectiveProjector_antipodal (n : ℕ) (p : ℙ ℂ (V n)) :
    projectiveProjector n (antipodal n p) = projectiveProjector n p := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [antipodal_mk, projectiveProjector_mk, projectiveProjector_mk]
    simp only [normalizedProjector]
    rw [columnProjector_pairedColumn]
    congr 1
    exact congrArg (fun z : ℂ => z⁻¹) (pairedColumn_norm_sq n v)

end
end QuaternionicSymmetry.CompactSymplecticProjectorTwistorProjection
