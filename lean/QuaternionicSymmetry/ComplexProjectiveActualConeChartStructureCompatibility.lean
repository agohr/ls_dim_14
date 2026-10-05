import QuaternionicSymmetry.ComplexProjectiveActualConeChartScalars
import QuaternionicSymmetry.ComplexProjectiveActualConeProjProductAction

/-! The chart `Spec ℂ` structure used in the literal product-domain action
is the restriction of the single global actual-cone-Proj structure map. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeChartStructureCompatibility

open AlgebraicGeometry CategoryTheory
open ComplexProjectiveTopology
open ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeProjChartIso
open ComplexProjectiveActualConeDegreeZeroScalars
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveActualConeChartScalars
open ComplexProjectiveActualConeProjProductAction
noncomputable section

variable {d : ℕ}

theorem chart_scalar_ringHom_eq (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    ((ComplexProjectiveActualConeStandardOpenEquiv.standardOpenEquiv A hA hNonempty i).toRingHom.comp
      (HomogeneousLocalization.fromZeroRingHom (quotientPiece A)
        (Submonoid.powers (coordinateClass A i)))).comp
      (scalarToDegreeZero A hA hNonempty) =
    algebraMap ℂ (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  ext c
  exact standardOpenToChart_scalar A hA hNonempty i c

theorem chartStructureMap_eq_globalRestriction (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    chartStructureMap A hA hNonempty i =
      (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
        actualConeProjToSpecComplex A hA hNonempty := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  let E := actualProjChartIso A hA hNonempty i
  change E.hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (MvPolynomial (Fin d) ℂ ⧸ chartVanishingIdeal A i))) = _
  rw [← cancel_epi E.inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hι : E.inv ≫ (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι =
      (Scheme.Spec.mapIso
        (ComplexProjectiveActualConeStandardOpenEquiv.standardOpenEquiv
          A hA hNonempty i).symm.toCommRingCatIso.op).inv ≫
        Proj.awayι (quotientPiece A) (coordinateClass A i)
          (coordinateClass_mem_degreeOne A i) (by omega) := by
    simp [E, actualProjChartIso, Iso.trans_inv, Category.assoc,
      Proj.basicOpenIsoSpec_inv_ι]
  rw [← Category.assoc, hι, actualConeProjToSpecComplex]
  simp only [Category.assoc]
  rw [Proj.awayι_toSpecZero_assoc]
  simp only [← Spec.map_comp]
  simpa [Scheme.Spec.mapIso_inv] using
    congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (chart_scalar_ringHom_eq A hA hNonempty i).symm

end
end QuaternionicSymmetry.ComplexProjectiveActualConeChartStructureCompatibility
