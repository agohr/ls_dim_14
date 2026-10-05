import QuaternionicSymmetry.CompactSymplecticProjectorTwistorFiberConstant
import QuaternionicSymmetry.CompactSymplecticProjectorTwistorGroupFiberLinear

/-! Every concrete projective line obtained by moving the standard first
pair with a genuine compact-symplectic matrix lies over exactly its right
coset in the actual HP quotient. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorTwistorGroupFiberBase

open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorFirstColumnUnit
open CompactSymplecticProjectorColumnSphereMap
open CompactSymplecticProjectorTwistorCarrierMap
open CompactSymplecticProjectorTwistorFiberLine
open CompactSymplecticProjectorTwistorFiberConstant
open CompactSymplecticProjectorTwistorProjection
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorTwistorNormalized
open CompactSymplecticProjectorOrbit
open CompactSymplecticProjectorColumnUnit
open scoped LinearAlgebra.Projectivization

noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := I n → ℂ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

theorem twistorToCarrier_fiberLine_at_group (n : ℕ)
    (u : G n) (z : ℙ ℂ (Fin 2 → ℂ)) :
    twistorToCarrier n (fiberProjectiveLine n (firstColumnSphere n u) z) =
      (u : ProjectiveCarrier n) := by
  rw [fiberProjectiveLine_constant]
  apply (carrierHomeomorphProjectorOrbit n).injective
  apply Subtype.ext
  change quotientOrbitProjector n (twistorToCarrier n
    (Projectivization.mk ℂ
      ((EuclideanSpace.equiv (I n) ℂ) (firstColumnSphere n u).1) (by
        intro hz
        have hu : (firstColumnSphere n u).1 = 0 :=
          (EuclideanSpace.equiv (I n) ℂ).injective hz
        have hn := mem_sphere_zero_iff_norm.mp (firstColumnSphere n u).2
        simp [hu] at hn))) = quotientOrbitProjector n (u : ProjectiveCarrier n)
  rw [carrier_projector_twistorToCarrier]
  change projectiveProjector n
    (Projectivization.mk ℂ
      ((EuclideanSpace.equiv (I n) ℂ) (firstColumnSphere n u).1) (by
        intro hz
        have hu : (firstColumnSphere n u).1 = 0 :=
          (EuclideanSpace.equiv (I n) ℂ).injective hz
        have hn := mem_sphere_zero_iff_norm.mp (firstColumnSphere n u).2
        simp [hu] at hn)) =
      orbitProjector n u
  rw [projectiveProjector_mk]
  rw [orbitProjector_eq_sphereColumnProjector]
  have hunit : columnNormSq n
      ((EuclideanSpace.equiv (I n) ℂ) (firstColumnSphere n u).1) = 1 := by
    simpa [columnNormSq] using unit_column_dot_self n (firstColumnSphere n u)
  simp [normalizedProjector, hunit, sphereColumnProjector]

end
end QuaternionicSymmetry.CompactSymplecticProjectorTwistorGroupFiberBase
