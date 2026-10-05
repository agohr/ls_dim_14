import QuaternionicSymmetry.CompactSymplecticProjectiveQuotient
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Analysis.Matrix.Normed

/-! A concrete closed embedding of the compact symplectic group in the unit
group of finite complex matrices. The latter has Mathlib's genuine Lie-group
atlas. A Lie subgroup atlas for the source requires the separate closed
subgroup theorem; it is not installed by this file. -/

namespace QuaternionicSymmetry.CompactSymplecticMatrixUnits

open Matrix Topology
open scoped Matrix.Norms.Elementwise
open scoped Manifold ContDiff
noncomputable section

private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)
private abbrev Mat (n : ℕ) :=
  Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℂ

/-- The actual matrix-unit homomorphism underlying the standard compact
symplectic representation. -/
def toMatrixUnits (n : ℕ) : G n →* (Mat n)ˣ :=
  (Unitary.toUnits : Matrix.unitaryGroup _ ℂ →* (Mat n)ˣ).comp
    (CompactSymplecticHaar.Group (n + 1)).subtype

/-- The topology selected for the finite matrix type is definitionally
unchanged by choosing the entrywise or operator norm structures: both select
the canonical topology of the finite matrix function type. -/
theorem elementwise_operator_topology_eq (n : ℕ) :
    (by
      letI : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
      exact (inferInstance : TopologicalSpace (Mat n))) =
    (by
      letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
      exact (inferInstance : TopologicalSpace (Mat n))) := rfl

/- The target admits Mathlib's actual smooth complex Lie-group atlas under
the operator matrix norm and the same canonical matrix topology. -/
open scoped Matrix.Norms.Operator in
example (n : ℕ) : LieGroup 𝓘(ℂ, Mat n) ∞ (Mat n)ˣ := inferInstance

open scoped Matrix.Norms.Operator in
example (n : ℕ) : LieGroup 𝓘(ℝ, Mat n) ∞ (Mat n)ˣ := inferInstance

theorem toMatrixUnits_injective (n : ℕ) :
    Function.Injective (toMatrixUnits n) := by
  intro u v h
  apply Subtype.ext
  exact Unitary.toUnits_injective h

theorem continuous_toMatrixUnits (n : ℕ) :
    Continuous (toMatrixUnits n) := by
  rw [Units.continuous_iff]
  constructor
  · exact continuous_subtype_val.comp continuous_subtype_val
  · simpa only [← map_inv] using
      (continuous_subtype_val.comp continuous_subtype_val).comp continuous_inv

/-- The compact symplectic group embeds as a closed topological subgroup
of the actual matrix-units Lie group. -/
theorem toMatrixUnits_closedEmbedding (n : ℕ) :
    IsClosedEmbedding (toMatrixUnits n) :=
  (continuous_toMatrixUnits n).isClosedEmbedding (toMatrixUnits_injective n)

end
end QuaternionicSymmetry.CompactSymplecticMatrixUnits
