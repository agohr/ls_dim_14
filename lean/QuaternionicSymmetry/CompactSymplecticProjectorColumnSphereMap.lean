import QuaternionicSymmetry.CompactSymplecticProjectorColumnSphereConnected
import QuaternionicSymmetry.CompactSymplecticProjectorOrbitQuotient

/-! The concrete unit-sphere projector map. Its image contains the actual
symplectic orbit; the reverse inclusion is exactly the outstanding completion
of arbitrary unit quaternionic columns to a compact-symplectic matrix. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorColumnSphereMap

open CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorFirstColumnUnit
open CompactSymplecticProjectorColumnContinuity
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorOrbit
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := EuclideanSpace ℂ (I n)

def sphereColumnProjector (n : ℕ) :
    Metric.sphere (0 : V n) 1 → Matrix (I n) (I n) ℂ :=
  fun v => columnProjector n ((EuclideanSpace.equiv (I n) ℂ) v.1)

theorem continuous_sphereColumnProjector (n : ℕ) :
    Continuous (sphereColumnProjector n) :=
  (continuous_columnProjector n).comp
    ((EuclideanSpace.equiv (I n) ℂ).continuous.comp continuous_subtype_val)

theorem orbitProjector_eq_sphereColumnProjector (n : ℕ)
    (u : CompactSymplecticHaar.Group (n + 1)) :
    orbitProjector n u = sphereColumnProjector n (firstColumnSphere n u) := by
  simpa [sphereColumnProjector, firstColumnSphere, firstColumnEuclidean] using
    orbitProjector_eq_columnProjector n u

theorem projectorOrbit_subset_sphereColumnProjector_range (n : ℕ) :
    projectorOrbit n ⊆ Set.range (sphereColumnProjector n) := by
  rintro p ⟨u, rfl⟩
  exact ⟨firstColumnSphere n u, (orbitProjector_eq_sphereColumnProjector n u).symm⟩

end
end QuaternionicSymmetry.CompactSymplecticProjectorColumnSphereMap
