import QuaternionicSymmetry.ComplexProjectiveActualConeGlobalClassicalAction
import QuaternionicSymmetry.ComplexProjectiveActualConeProjProductCoverMap

/-! Chartwise classical ℂ-points of the literal global torus × cone-Proj
pullback, retaining both categorical projections. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeGlobalClassicalProductPoint

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeProjProductCoordinateCover
open ComplexProjectiveActualConeProjProductCoverMap
open ComplexProjectiveActualConeDirectClassicalProductPoint
open ComplexProjectiveActualConeClassicalPointInjective
open ComplexProjectiveActualConeClassicalPointChart
open CategoryPullbackProductOverlapIso
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

def globalClassicalProductPoint
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (z : ComplexTorus r) (x : A) (hi : x.1.rep i ≠ 0) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    ↥(pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
      (ComplexProjectiveActualConeComplexStructure.actualConeProjToSpecComplex
        A hA hNonempty) : Scheme) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  exact (actualConeTorusProductCoordinateCover (r := r) A hA hNonempty).f i
    (directClassicalProductPoint A hA hNonempty i z x hi)

theorem globalClassicalProductPoint_fst
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (z : ComplexTorus r) (x : A) (hi : x.1.rep i ≠ 0) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    (pullback.fst _ _ : _ ⟶ Spec (CommRingCat.of (TorusCoordinateRing r)))
      (globalClassicalProductPoint A hA hNonempty i z x hi) =
      ComplexProjectiveActualConeSpecEvaluationNaturality.specEvaluationPoint
        (evalTorus z) := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  rw [globalClassicalProductPoint,
    actualConeTorusProductCover_f_eq_baseChangedOpenMap]
  simpa only [← Scheme.Hom.comp_apply, baseChangedOpenMap, pullback.lift_fst] using
    (directClassicalProductPoint_fst A hA hNonempty i z x hi)

theorem globalClassicalProductPoint_snd
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (z : ComplexTorus r) (x : A) (hi : x.1.rep i ≠ 0) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    (pullback.snd _ _ : _ ⟶ Proj (quotientPiece A))
      (globalClassicalProductPoint A hA hNonempty i z x hi) =
      classicalPointToActualProjFixed A hA hNonempty x := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  rw [globalClassicalProductPoint,
    actualConeTorusProductCover_f_eq_baseChangedOpenMap]
  have h := directClassicalProductPoint_snd A hA hNonempty i z x hi
  have hh := congrArg
    (fun q : ↥(Proj.basicOpen (quotientPiece A) (coordinateClass A i)) =>
      (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι q) h
  simpa only [← Scheme.Hom.comp_apply, baseChangedOpenMap, pullback.lift_snd,
    Subtype.coe_mk] using hh

end
end QuaternionicSymmetry.ComplexProjectiveActualConeGlobalClassicalProductPoint
