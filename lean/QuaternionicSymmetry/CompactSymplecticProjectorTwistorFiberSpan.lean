import QuaternionicSymmetry.CompactSymplecticProjectorTwistorContinuous
import QuaternionicSymmetry.CompactSymplecticProjectorColumnUnit

/-! An exact algebraic description of the image of the paired-column
projector: it is the complex span of `v` and its quaternionic mate. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberSpan

open Matrix
open CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnAlgebra
open CompactSymplecticProjectorColumnUnit
open CompactSymplecticProjectorColumnSphereMap

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ
private abbrev EV (n : ℕ) := EuclideanSpace ℂ (I n)

theorem columnProjector_mulVec (n : ℕ) (v w : V n) :
    columnProjector n v *ᵥ w =
      ((star v) ⬝ᵥ w) • v + ((star (pairedColumn n v)) ⬝ᵥ w) • pairedColumn n v := by
  classical
  funext i
  simp [Matrix.mulVec, columnProjector, dotProduct, Finset.sum_add_distrib,
    Finset.mul_sum, mul_add, mul_comm, mul_left_comm, mul_assoc]

theorem unit_columnProjector_mulVec_self (n : ℕ)
    (w : Metric.sphere (0 : EV n) 1) :
    columnProjector n ((EuclideanSpace.equiv (I n) ℂ) w.1) *ᵥ
      ((EuclideanSpace.equiv (I n) ℂ) w.1) =
        ((EuclideanSpace.equiv (I n) ℂ) w.1) := by
  let v : V n := (EuclideanSpace.equiv (I n) ℂ) w.1
  have hn : (star v) ⬝ᵥ v = 1 := by
    simpa [v] using unit_column_dot_self n w
  have ho : (star (pairedColumn n v)) ⬝ᵥ v = 0 :=
    pairedColumn_orthogonal_rev n v
  rw [columnProjector_mulVec]
  simp [v, hn, ho]

theorem same_unitProjector_implies_span (n : ℕ)
    (v w : Metric.sphere (0 : EV n) 1)
    (h : sphereColumnProjector n v = sphereColumnProjector n w) :
    ∃ a b : ℂ,
      ((EuclideanSpace.equiv (I n) ℂ) w.1) =
        a • ((EuclideanSpace.equiv (I n) ℂ) v.1) +
          b • pairedColumn n ((EuclideanSpace.equiv (I n) ℂ) v.1) := by
  let x : V n := (EuclideanSpace.equiv (I n) ℂ) v.1
  let y : V n := (EuclideanSpace.equiv (I n) ℂ) w.1
  have hy : (columnProjector n y) *ᵥ y = y :=
    unit_columnProjector_mulVec_self n w
  have hxy : columnProjector n x = columnProjector n y := h
  rw [← hxy, columnProjector_mulVec] at hy
  exact ⟨(star x) ⬝ᵥ y, (star (pairedColumn n x)) ⬝ᵥ y, hy.symm⟩

end
end QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberSpan
