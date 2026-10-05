import QuaternionicSymmetry.CompactSymplecticProjectorColumnPhase
import Mathlib.LinearAlgebra.Projectivization.Basic

/-! The canonical fixed-point-free quaternionic antipodal involution on
complex projective lines of the defining compact symplectic representation.
This is concrete model-side twistor data, not an identification with the
Levi-Civita twistor complex manifold. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTwistorAntipodal

open CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnAlgebra
open CompactSymplecticProjectorColumnPhase
open scoped LinearAlgebra.Projectivization

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ

private theorem paired_ne_zero (n : ℕ) {v : V n} (hv : v ≠ 0) :
    pairedColumn n v ≠ 0 := by
  intro hp
  have := pairedColumn_pair n v
  have hzero : pairedColumn n (0 : V n) = 0 := by
    funext i
    cases i <;> simp [pairedColumn]
  rw [hp] at this
  rw [hzero] at this
  exact hv (neg_eq_zero.mp this.symm)

/-- The quaternionic mate of a complex line, defined on actual projective
space rather than on a chosen representative. -/
def antipodal (n : ℕ) : ℙ ℂ (V n) → ℙ ℂ (V n) :=
  Projectivization.lift
    (fun v => Projectivization.mk ℂ (pairedColumn n v.1)
      (paired_ne_zero n v.2))
    (by
      intro a b t h
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
      refine ⟨star t, ?_⟩
      rw [← pairedColumn_smul]
      exact (congrArg (pairedColumn n) h).symm)

@[simp] theorem antipodal_mk (n : ℕ) (v : V n) (hv : v ≠ 0) :
    antipodal n (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (pairedColumn n v) (paired_ne_zero n hv) := by
  simp [antipodal]

/-- Applying the quaternionic mate twice multiplies a vector by `-1`,
which disappears after projectivization. -/
theorem antipodal_involutive (n : ℕ) : Function.Involutive (antipodal n) := by
  apply Projectivization.ind
  intro v hv
  rw [antipodal_mk, antipodal_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨-1, ?_⟩
  simpa using (pairedColumn_pair n v).symm

/-- No complex line is fixed by the quaternionic mate: `v` is orthogonal
to `J\bar v`, and a nonzero vector cannot be orthogonal to itself. -/
theorem antipodal_ne_self (n : ℕ) (p : ℙ ℂ (V n)) : antipodal n p ≠ p := by
  induction p using Projectivization.ind with
  | h v hv =>
    intro heq
    rw [antipodal_mk] at heq
    obtain ⟨t, ht⟩ :=
      (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).1 heq.symm
    have hdot := congrArg (fun w : V n => (star v) ⬝ᵥ w) ht
    change (star v) ⬝ᵥ (t • pairedColumn n v) = (star v) ⬝ᵥ v at hdot
    have hscale : (star v) ⬝ᵥ (t • pairedColumn n v) =
        t * ((star v) ⬝ᵥ pairedColumn n v) := by
      simp [dotProduct, Finset.mul_sum, mul_add, mul_left_comm, mul_assoc]
    rw [hscale] at hdot
    have horth : (star v) ⬝ᵥ pairedColumn n v = 0 :=
      pairedColumn_orthogonal n v
    rw [horth] at hdot
    have hzero : (star v) ⬝ᵥ v = 0 := by simpa using hdot.symm
    let w : EuclideanSpace ℂ (I n) :=
      (EuclideanSpace.equiv (I n) ℂ).symm v
    have hw : inner ℂ w w = 0 := by
      change v ⬝ᵥ star v = 0
      simpa [dotProduct, mul_comm] using hzero
    have hw0 : w = 0 := inner_self_eq_zero.mp hw
    exact hv (by simpa [w] using congrArg (EuclideanSpace.equiv (I n) ℂ) hw0)

end
end QuaternionicSymmetry.CompactSymplecticProjectorTwistorAntipodal
