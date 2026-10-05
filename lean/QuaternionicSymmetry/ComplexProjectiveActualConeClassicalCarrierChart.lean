import QuaternionicSymmetry.ComplexProjectiveActualConeClassicalCarrierEvaluation
import QuaternionicSymmetry.ComplexProjectiveChartedSpace

/-! The explicit affine-ratio hypothesis in the canonical Proj-to-Spec
carrier comparison is discharged by the actual analytic projective chart. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeClassicalCarrierChart

open AlgebraicGeometry ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalChartLocus ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeClassicalPointInjective
open ComplexProjectiveActualConeClassicalPointChart
open ComplexProjectiveActualConeStandardOpenAlgEquiv
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeClassicalCarrierEvaluation
open ComplexProjectiveActualConeChartClassicalSpecialization
noncomputable section

variable {d : ℕ}

theorem projectiveChart_ratio (x : Space d) (i : Fin (d + 1))
    (hi : x.rep i ≠ 0) (k : Fin d) :
    x.rep (i.succAbove k) =
      (projectiveChart d i x) k * x.rep i := by
  have hxi : x ∈ affineDomain d i := hi
  have hchart : (projectiveChart d i x) k =
      x.rep (i.succAbove k) / x.rep i := by
    rw [projectiveChart_apply d i x hxi]
    rfl
  rw [hchart]
  field_simp [hi]

theorem projectiveChart_mem_chartLocus
    (A : Set (Space d)) (x : A) (i : Fin (d + 1))
    (hi : x.1.rep i ≠ 0) :
    projectiveChart d i x.1 ∈ chartLocus A i := by
  have hxi : x.1 ∈ (projectiveChart d i).source := by
    rw [projectiveChart_source]
    exact hi
  change (projectiveChart d i).symm (projectiveChart d i x.1) ∈ A
  rw [(projectiveChart d i).left_inv hxi]
  exact x.2

theorem classicalCarrier_eq_projectiveChartEvalKernel
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (x : A) (i : Fin (d + 1))
    (hi : x.1.rep i ≠ 0) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    let q : ProjectiveSpectrum (quotientPiece A) :=
      classicalPointToActualProjFixed A hA hNonempty x
    let qᵢ : {q : ProjectiveSpectrum (quotientPiece A) //
        q ∈ Proj.basicOpen (quotientPiece A) (coordinateClass A i)} :=
      ⟨q, (classicalPoint_mem_basicOpen_iff A hA x i).mpr hi⟩
    Ideal.comap (standardOpenAlgEquiv A hA hNonempty i).symm.toRingHom
      (ProjIsoSpecTopComponent.ToSpec.carrier qᵢ) =
      RingHom.ker (chartPointEval A i (projectiveChart d i x.1)
        (projectiveChart_mem_chartLocus A x i hi)) := by
  exact classicalCarrier_eq_chartEvalKernel A hA hNonempty x i hi
    (projectiveChart d i x.1) (projectiveChart_mem_chartLocus A x i hi)
    (projectiveChart_ratio x.1 i hi)

end
end QuaternionicSymmetry.ComplexProjectiveActualConeClassicalCarrierChart
