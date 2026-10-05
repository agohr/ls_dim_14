import QuaternionicSymmetry.ComplexProjectiveActualConeProductClassicalPoint
import QuaternionicSymmetry.ComplexProjectiveActualConeProjChartIso

/-! The genuine Proj basic-open/affine-Spec isomorphism sends a classical
quotient-Proj point to evaluation at its actual analytic affine coordinates. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeClassicalChartIsoPoint

open AlgebraicGeometry CategoryTheory
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalChartLocus ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeProjChartIso
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeClassicalPointInjective
open ComplexProjectiveActualConeClassicalPointChart
open ComplexProjectiveActualConeClassicalCarrierChart
open ComplexProjectiveActualConeChartClassicalSpecialization
open ComplexProjectiveActualConeSpecEvaluationNaturality
noncomputable section

variable {d : ℕ}

theorem actualProjChartIso_classicalPoint
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (x : A) (i : Fin (d + 1))
    (hi : x.1.rep i ≠ 0) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    let q : ProjectiveSpectrum (quotientPiece A) :=
      classicalPointToActualProjFixed A hA hNonempty x
    let qᵢ : {q : ProjectiveSpectrum (quotientPiece A) //
        q ∈ Proj.basicOpen (quotientPiece A) (coordinateClass A i)} :=
      ⟨q, (classicalPoint_mem_basicOpen_iff A hA x i).mpr hi⟩
    (actualProjChartIso A hA hNonempty i).hom qᵢ =
      specEvaluationPoint (chartPointEval A i (projectiveChart d i x.1)
        (projectiveChart_mem_chartLocus A x i hi)) := by
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
  apply PrimeSpectrum.ext
  ext a
  have hcarrier := classicalCarrier_eq_projectiveChartEvalKernel
    A hA hNonempty x i hi
  simp only [actualProjChartIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op,
    Proj.basicOpenIsoSpec_hom, Scheme.Hom.comp_apply, Spec.map_apply]
  have hb : ((Proj.basicOpenToSpec (quotientPiece A) (coordinateClass A i)) qᵢ).asIdeal =
      ProjIsoSpecTopComponent.ToSpec.carrier qᵢ := by
    change ((ProjectiveSpectrum.Proj.toSpec (quotientPiece A)
      (coordinateClass A i)).base qᵢ).asIdeal = _
    rw [ProjectiveSpectrum.Proj.toSpec_base_apply_eq]
    rfl
  rw [PrimeSpectrum.comap_asIdeal, hb]
  change a ∈ Ideal.comap
    (ComplexProjectiveActualConeStandardOpenAlgEquiv.standardOpenAlgEquiv
      A hA hNonempty i).symm.toRingHom
      (ProjIsoSpecTopComponent.ToSpec.carrier qᵢ) ↔
    a ∈ RingHom.ker (chartPointEval A i (projectiveChart d i x.1)
      (projectiveChart_mem_chartLocus A x i hi))
  exact (congrArg (fun J => a ∈ J) hcarrier).to_iff

end
end QuaternionicSymmetry.ComplexProjectiveActualConeClassicalChartIsoPoint
