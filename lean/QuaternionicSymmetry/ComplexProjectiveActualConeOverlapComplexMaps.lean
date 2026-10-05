import QuaternionicSymmetry.ComplexProjectiveActualConeOverlapLocalization
import QuaternionicSymmetry.ComplexProjectiveActualConeOverlapScalars

/-! The two actual standard-open restriction maps to a pairwise overlap
preserve the single global complex-scalar structure. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeOverlapComplexMaps

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeDegreeZeroScalars
noncomputable section

variable {d : ℕ}

def overlapRestrictionLeft (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
      awayComplexAlgebra A hA hNonempty
        (coordinateClass A i * coordinateClass A j)
    HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) →ₐ[ℂ]
      HomogeneousLocalization.Away (quotientPiece A)
        (coordinateClass A i * coordinateClass A j) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
    awayComplexAlgebra A hA hNonempty
      (coordinateClass A i * coordinateClass A j)
  exact { HomogeneousLocalization.awayMap (quotientPiece A)
      (coordinateClass_mem_degreeOne A j) rfl with
    commutes' := by
      intro c
      change HomogeneousLocalization.awayMap (quotientPiece A)
          (coordinateClass_mem_degreeOne A j) rfl
          (HomogeneousLocalization.fromZeroRingHom (quotientPiece A)
            (Submonoid.powers (coordinateClass A i))
            (scalarToDegreeZero A hA hNonempty c)) =
        HomogeneousLocalization.fromZeroRingHom (quotientPiece A)
          (Submonoid.powers (coordinateClass A i * coordinateClass A j))
          (scalarToDegreeZero A hA hNonempty c)
      exact HomogeneousLocalization.awayMap_fromZeroRingHom
        (quotientPiece A) (coordinateClass_mem_degreeOne A j) rfl
        (scalarToDegreeZero A hA hNonempty c)
  }

def overlapRestrictionRight (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i j : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A j)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A j)
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
      awayComplexAlgebra A hA hNonempty
        (coordinateClass A i * coordinateClass A j)
    HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A j) →ₐ[ℂ]
      HomogeneousLocalization.Away (quotientPiece A)
        (coordinateClass A i * coordinateClass A j) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A j)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A j)
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i * coordinateClass A j)) :=
    awayComplexAlgebra A hA hNonempty
      (coordinateClass A i * coordinateClass A j)
  exact { HomogeneousLocalization.awayMap (quotientPiece A)
      (coordinateClass_mem_degreeOne A i) (by ring) with
    commutes' := by
      intro c
      change HomogeneousLocalization.awayMap (quotientPiece A)
          (coordinateClass_mem_degreeOne A i) (by ring)
          (HomogeneousLocalization.fromZeroRingHom (quotientPiece A)
            (Submonoid.powers (coordinateClass A j))
            (scalarToDegreeZero A hA hNonempty c)) =
        HomogeneousLocalization.fromZeroRingHom (quotientPiece A)
          (Submonoid.powers (coordinateClass A i * coordinateClass A j))
          (scalarToDegreeZero A hA hNonempty c)
      exact HomogeneousLocalization.awayMap_fromZeroRingHom
        (quotientPiece A) (coordinateClass_mem_degreeOne A i) (by ring)
        (scalarToDegreeZero A hA hNonempty c)
  }

end
end QuaternionicSymmetry.ComplexProjectiveActualConeOverlapComplexMaps
