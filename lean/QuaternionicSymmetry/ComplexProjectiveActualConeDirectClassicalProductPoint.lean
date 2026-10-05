import QuaternionicSymmetry.ComplexProjectiveActualConeClassicalAwaySpecPoint
import QuaternionicSymmetry.ComplexProjectiveActualConeDirectProductIsoProjection
import QuaternionicSymmetry.ComplexProjectiveActualConeProductEvaluationProjections

/-! The actual finite-cover product point is obtained from the literal
torus⊗Away evaluation point through the checked direct product iso. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDirectClassicalProductPoint

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAlgebraicCharts ComplexProjectiveDiagonalChartLocus
open ComplexProjectiveConeQuotientHomogeneousPieces ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeAwayComplexAlgebra
open ComplexProjectiveActualConeDirectLocalSchemeAction
open ComplexProjectiveActualConeDirectProductIsoProjection
open ComplexProjectiveActualConeLocalizedSchemeClassicalPoint
open ComplexProjectiveActualConeProductEvaluationProjections
open ComplexProjectiveActualConeClassicalAwaySpecPoint
open ComplexProjectiveActualConeSpecEvaluationNaturality
open ComplexProjectiveActualConeClassicalPointInjective
open ComplexProjectiveActualConeClassicalPointChart
open ComplexProjectiveActualConeClassicalCarrierChart
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
open scoped TensorProduct
noncomputable section

variable {r d : ℕ}

def directClassicalProductPoint
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (z : ComplexTorus r) (x : A) (hi : x.1.rep i ≠ 0) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    ↥(pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
      ((Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
        ComplexProjectiveActualConeComplexStructure.actualConeProjToSpecComplex
          A hA hNonempty) : Scheme) := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  exact (directBasicOpenProductIso (r := r) A hA hNonempty i).inv
    (specEvaluationPoint (actualProductEvaluation A hA hNonempty i z
      (projectiveChart d i x.1) (projectiveChart_mem_chartLocus A x i hi)))

theorem directClassicalProductPoint_fst
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (z : ComplexTorus r) (x : A) (hi : x.1.rep i ≠ 0) :
    letI : GradedAlgebra (quotientPiece A) :=
      quotientGradedAlgebra A hA hNonempty
    letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
      awayComplexAlgebra A hA hNonempty (coordinateClass A i)
    (pullback.fst _ _ : _ ⟶ Spec (CommRingCat.of (TorusCoordinateRing r)))
      (directClassicalProductPoint A hA hNonempty i z x hi) =
      specEvaluationPoint (evalTorus z) := by
  letI : GradedAlgebra (quotientPiece A) :=
    quotientGradedAlgebra A hA hNonempty
  letI : Algebra ℂ (HomogeneousLocalization.Away
      (quotientPiece A) (coordinateClass A i)) :=
    awayComplexAlgebra A hA hNonempty (coordinateClass A i)
  let e := directBasicOpenProductIso (r := r) A hA hNonempty i
  have hf := directBasicOpenProductIso_hom_fst (r := r) A hA hNonempty i
  calc
    (pullback.fst _ _ : _ ⟶ Spec (CommRingCat.of (TorusCoordinateRing r)))
        (directClassicalProductPoint A hA hNonempty i z x hi) =
      (e.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          TorusCoordinateRing r →+*
          TorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i))))
        (directClassicalProductPoint A hA hNonempty i z x hi) :=
          congrArg (fun f => f (directClassicalProductPoint A hA hNonempty i z x hi)) hf.symm
    _ = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          TorusCoordinateRing r →+*
          TorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)))
        (specEvaluationPoint (actualProductEvaluation A hA hNonempty i z
          (projectiveChart d i x.1) (projectiveChart_mem_chartLocus A x i hi))) := by
          simp [e, directClassicalProductPoint]
    _ = specEvaluationPoint (evalTorus z) := by
          rw [specMap_specEvaluationPoint]
          congr 1
          apply RingHom.ext
          intro t
          exact actualProductEvaluation_left A hA hNonempty i z
            (projectiveChart d i x.1) (projectiveChart_mem_chartLocus A x i hi) t

theorem directClassicalProductPoint_snd
    (A : Set (Space d)) (hA : HasHomogeneousEquations A)
    (hNonempty : A.Nonempty) (i : Fin (d + 1))
    (z : ComplexTorus r) (x : A) (hi : x.1.rep i ≠ 0) :
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
    (pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
      ((Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
        ComplexProjectiveActualConeComplexStructure.actualConeProjToSpecComplex
          A hA hNonempty))
      (directClassicalProductPoint A hA hNonempty i z x hi) = qᵢ := by
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
  let e := directBasicOpenProductIso (r := r) A hA hNonempty i
  have hs := directBasicOpenProductIso_hom_snd (r := r) A hA hNonempty i
  let eᵢ := Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
    (coordinateClass_mem_degreeOne A i) (by omega)
  suffices he : eᵢ.hom ((pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
      ((Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
        ComplexProjectiveActualConeComplexStructure.actualConeProjToSpecComplex
          A hA hNonempty))
        (directClassicalProductPoint A hA hNonempty i z x hi)) = eᵢ.hom qᵢ by
    have h := congrArg eᵢ.inv he
    simpa [eᵢ] using h
  change (Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
    (coordinateClass_mem_degreeOne A i) (by omega)).hom _ = _
  calc
    (Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
      (coordinateClass_mem_degreeOne A i) (by omega)).hom
        ((pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusCoordinateRing r))))
          ((Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι ≫
            ComplexProjectiveActualConeComplexStructure.actualConeProjToSpecComplex
              A hA hNonempty))
          (directClassicalProductPoint A hA hNonempty i z x hi)) =
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom :
          HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i) →+*
          TorusCoordinateRing r ⊗[ℂ]
            HomogeneousLocalization.Away (quotientPiece A) (coordinateClass A i)))
        (e.hom (directClassicalProductPoint A hA hNonempty i z x hi))) :=
          congrArg (fun f => f (directClassicalProductPoint A hA hNonempty i z x hi)) hs.symm
    _ = specEvaluationPoint (actualChartEvaluation A hA hNonempty i
          (projectiveChart d i x.1) (projectiveChart_mem_chartLocus A x i hi)) := by
          simp [e, directClassicalProductPoint]
          rw [specMap_specEvaluationPoint]
          congr 1
          apply RingHom.ext
          intro a
          exact actualProductEvaluation_right A hA hNonempty i z
            (projectiveChart d i x.1) (projectiveChart_mem_chartLocus A x i hi) a
    _ = (Proj.basicOpenIsoSpec (quotientPiece A) (coordinateClass A i)
          (coordinateClass_mem_degreeOne A i) (by omega)).hom qᵢ := by
          exact (basicOpenIsoSpec_classicalPoint A hA hNonempty x i hi).symm

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDirectClassicalProductPoint
