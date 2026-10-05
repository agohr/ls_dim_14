import QuaternionicSymmetry.ComplexProjectiveActualConeGlobalClassicalProductPoint
import QuaternionicSymmetry.ComplexProjectiveActualConeGlobalClassicalAction

/-! Every analytic torus/projective-locus pair has a point in the literal
scheme product with the expected projections and regular action value. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeGlobalClassicalComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeProjProductCoordinateCover
open ComplexProjectiveActualConeGlobalClassicalProductPoint
open ComplexProjectiveActualConeGlobalClassicalAction
open ComplexProjectiveActualConeClassicalPointInjective
open ComplexProjectiveActualConeSpecEvaluationNaturality
open ComplexProjectiveActualConeGlobalSchemeAction
open ComplexProjectiveTorusPreservation
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

theorem exists_globalClassicalProductPoint_action
    (μ : Fin (d + 1) → Fin r → ℤ)
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (z : ComplexTorus r) (x : A) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    ∃ p : ↥(pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
        (ComplexProjectiveActualConeComplexStructure.actualConeProjToSpecComplex
          A hA hNonempty) : Scheme),
      (pullback.fst _ _ : _ ⟶ Spec (CommRingCat.of (TorusCoordinateRing r))) p =
          specEvaluationPoint (evalTorus z) ∧
      (pullback.snd _ _ : _ ⟶ Proj (quotientPiece A)) p =
          classicalPointToActualProjFixed A hA hNonempty x ∧
      (globalSchemeAction μ A hA hNonempty hCompact) p =
          classicalPointToActualProjFixed A hA hNonempty
            ⟨projectiveAction μ z x.1,
              mapsTo_of_compact μ A hA hCompact z x.2⟩ := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  obtain ⟨i, hi⟩ := exists_mem_affineDomain d x.1
  refine ⟨globalClassicalProductPoint A hA hNonempty i z x hi, ?_, ?_, ?_⟩
  · exact globalClassicalProductPoint_fst A hA hNonempty i z x hi
  · exact globalClassicalProductPoint_snd A hA hNonempty i z x hi
  · exact globalSchemeAction_classical_on_chart μ A hA hNonempty hCompact i z x hi

end
end QuaternionicSymmetry.ComplexProjectiveActualConeGlobalClassicalComparison
