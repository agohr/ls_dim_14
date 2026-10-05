import QuaternionicSymmetry.ComplexProjectiveActualConeClassicalChartCarrier

/-! The canonical Proj-to-Spec carrier at a classical quotient-Proj point
detects the value of every translated homogeneous coordinate fraction. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeClassicalTranslatedCarrier

open AlgebraicGeometry ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeClassicalPoint
open ComplexProjectiveActualConeClassicalPointInjective
open ComplexProjectiveActualConeClassicalPointChart
open ComplexProjectiveLineProjPoint
noncomputable section

variable {d : ℕ}

def coordinateDifferenceFraction (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i j : Fin (d + 1)) (c : ℂ) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  exact HomogeneousLocalization.Away.mk (quotientPiece A)
    (coordinateClass_mem_degreeOne A i) 1
    (coordinateClass A j - c • coordinateClass A i)
    (Submodule.sub_mem (quotientPiece A 1)
      (coordinateClass_mem_degreeOne A j)
      (Submodule.smul_mem (quotientPiece A 1) c
        (coordinateClass_mem_degreeOne A i)))

theorem coordinateDifferenceFraction_mem_carrier_iff
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (x : A) (i j : Fin (d + 1))
    (hi : x.1.rep i ≠ 0) (c : ℂ) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    let q : ProjectiveSpectrum (quotientPiece A) :=
      classicalPointToActualProjFixed A hA hNonempty x
    let qᵢ : {q : ProjectiveSpectrum (quotientPiece A) //
        q ∈ Proj.basicOpen (quotientPiece A) (coordinateClass A i)} :=
      ⟨q, (classicalPoint_mem_basicOpen_iff A hA x i).mpr hi⟩
    coordinateDifferenceFraction A hA hNonempty i j c ∈
      ProjIsoSpecTopComponent.ToSpec.carrier qᵢ ↔
      x.1.rep j = c * x.1.rep i := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  let q : ProjectiveSpectrum (quotientPiece A) :=
    classicalPointToActualProjFixed A hA hNonempty x
  let qᵢ : {q : ProjectiveSpectrum (quotientPiece A) //
      q ∈ Proj.basicOpen (quotientPiece A) (coordinateClass A i)} :=
    ⟨q, (classicalPoint_mem_basicOpen_iff A hA x i).mpr hi⟩
  change HomogeneousLocalization.mk
      (⟨1,
        ⟨coordinateClass A j - c • coordinateClass A i,
          Submodule.sub_mem (quotientPiece A 1)
            (coordinateClass_mem_degreeOne A j)
            (Submodule.smul_mem (quotientPiece A 1) c
              (coordinateClass_mem_degreeOne A i))⟩,
        ⟨(coordinateClass A i) ^ 1,
          SetLike.pow_mem_graded 1 (coordinateClass_mem_degreeOne A i)⟩,
        ⟨1, rfl⟩⟩ : HomogeneousLocalization.NumDenSameDeg
          (quotientPiece A) (.powers (coordinateClass A i))) ∈
      ProjIsoSpecTopComponent.ToSpec.carrier qᵢ ↔ _
  rw [ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier]
  change coordinateClass A j - c • coordinateClass A i ∈
    quotientLineHomogeneousPrime A hA x.1 x.2 ↔ _
  have hhom : SetLike.IsHomogeneousElem (quotientPiece A)
      (coordinateClass A j - c • coordinateClass A i) :=
    ⟨1, Submodule.sub_mem (quotientPiece A 1)
      (coordinateClass_mem_degreeOne A j)
      (Submodule.smul_mem (quotientPiece A 1) c
        (coordinateClass_mem_degreeOne A i))⟩
  have hiff : coordinateClass A j - c • coordinateClass A i ∈
      quotientLineHomogeneousPrime A hA x.1 x.2 ↔
      quotientLineEval A x.1 x.2
        (coordinateClass A j - c • coordinateClass A i) = 0 := by
    constructor
    · intro h
      exact (RingHom.mem_ker).mp
        ((Ideal.toIdeal_homogeneousCore_le
          (𝒜 := quotientPiece A) (I := quotientLinePrime A x.1 x.2)) h)
    · intro h
      exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem hhom
        ((RingHom.mem_ker).mpr h)
  rw [hiff]
  have hs : quotientLineEval A x.1 x.2 (c • coordinateClass A i) =
      Polynomial.C c * (Polynomial.C (x.1.rep i) * Polynomial.X) := by
    rw [Algebra.smul_def, map_mul]
    simp [coordinateClass, quotientLineEval, lineEval]
  rw [map_sub, hs]
  simp only [coordinateClass, quotientLineEval_mk, sub_eq_zero]
  simp only [lineEval, MvPolynomial.aeval_X]
  constructor
  · intro h
    have hc := congrArg (fun p : Polynomial ℂ => p.coeff 1) h
    simpa [mul_assoc] using hc
  · intro h
    rw [h]
    simp only [map_mul]
    ring

end
end QuaternionicSymmetry.ComplexProjectiveActualConeClassicalTranslatedCarrier
