import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleLocalIteratedGeometric
import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleProductCoverMap
import QuaternionicSymmetry.ComplexProjectiveActualConeProjProductCoverMap
import QuaternionicSymmetry.ComplexProjectiveActualConeDoubleSecondFactorRestriction
import QuaternionicSymmetry.ComplexProjectiveActualConeGlobalSchemeAction

/-! The categorical iterated global Scheme morphism restricts on every
actual two-torus standard-open chart to the explicitly checked second-twist
affine map. This is the final local comparison for the global multiplication
law. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeDoubleIteratedRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveConeQuotientHomogeneousPieces
open ComplexProjectiveConeQuotientGrading
open ComplexProjectiveActualConeProjCoordinates
open ComplexProjectiveActualConeComplexStructure
open ComplexProjectiveActualConeProjProductCoordinateCover
open ComplexProjectiveActualConeProjProductCoverMap
open ComplexProjectiveActualConeDoubleProductCover
open ComplexProjectiveActualConeDoubleProductCoverMap
open ComplexProjectiveActualConeDoubleLocalSecondFactor
open ComplexProjectiveActualConeDirectLocalSchemeAction
open ComplexProjectiveActualConeDoubleSecondFactorRestriction
open ComplexProjectiveActualConeDoubleLocalIterated
open ComplexProjectiveActualConeDoubleLocalIteratedScheme
open ComplexProjectiveActualConeDoubleLocalIteratedGeometric
open ComplexProjectiveActualConeDoubleProductIteratedAction
open ComplexProjectiveActualConeGlobalSchemeAction
open CategoryPullbackProductOverlapIso
open ComplexTorusLaurentComultiplication
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ}

set_option maxRecDepth 2048 in
theorem actualConeDoubleProductIterated_restrict
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A) (hNonempty : A.Nonempty)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (i : Fin (d + 1)) :
    letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
    let 𝒰₂ := actualConeDoubleTorusProductCoordinateCover (r := r) A hA hNonempty
    let 𝒰₁ := actualConeTorusProductCoordinateCover (r := r) A hA hNonempty
    𝒰₂.f i ≫ actualConeDoubleProductIterated r μ A hA hNonempty hCompact =
      directBasicOpenDoubleIterated μ A hA hNonempty hCompact i ≫ 𝒰₁.f i := by
  letI : GradedAlgebra (quotientPiece A) := quotientGradedAlgebra A hA hNonempty
  let g := actualConeProjToSpecComplex A hA hNonempty
  let f₂ := Spec.map (CommRingCat.ofHom
    (algebraMap ℂ (DoubleTorusCoordinateRing r)))
  let f₁ := Spec.map (CommRingCat.ofHom
    (algebraMap ℂ (TorusCoordinateRing r)))
  let u := (Proj.basicOpen (quotientPiece A) (coordinateClass A i)).ι
  let 𝒰₂ := actualConeDoubleTorusProductCoordinateCover (r := r) A hA hNonempty
  let 𝒰₁ := actualConeTorusProductCoordinateCover (r := r) A hA hNonempty
  have h₂f : 𝒰₂.f i ≫ pullback.fst f₂ g = pullback.fst f₂ (u ≫ g) := by
    rw [actualConeDoubleTorusProductCover_f_eq_baseChangedOpenMap
      (r := r) A hA hNonempty i]
    rw [baseChangedOpenMap, pullback.lift_fst]
  have h₁f : 𝒰₁.f i ≫ pullback.fst f₁ g = pullback.fst f₁ (u ≫ g) := by
    rw [actualConeTorusProductCover_f_eq_baseChangedOpenMap
      (r := r) A hA hNonempty i]
    rw [baseChangedOpenMap, pullback.lift_fst]
  have h₁s : 𝒰₁.f i ≫ pullback.snd f₁ g = pullback.snd f₁ (u ≫ g) ≫ u := by
    rw [actualConeTorusProductCover_f_eq_baseChangedOpenMap
      (r := r) A hA hNonempty i]
    rw [baseChangedOpenMap, pullback.lift_snd]
  have hIf : actualConeDoubleProductIterated r μ A hA hNonempty hCompact ≫
      pullback.fst f₁ g = pullback.fst f₂ g ≫ doubleTorusFirstSpec r := by
    unfold actualConeDoubleProductIterated
    rw [pullback.lift_fst]
  have hIs : actualConeDoubleProductIterated r μ A hA hNonempty hCompact ≫
      pullback.snd f₁ g =
      actualConeDoubleProductSecondFactor r A hA hNonempty ≫
        globalSchemeAction μ A hA hNonempty hCompact := by
    unfold actualConeDoubleProductIterated
    rw [pullback.lift_snd]
  apply pullback.hom_ext
  · calc
      (𝒰₂.f i ≫ actualConeDoubleProductIterated r μ A hA hNonempty hCompact) ≫
          pullback.fst f₁ g =
        (𝒰₂.f i ≫ pullback.fst f₂ g) ≫ doubleTorusFirstSpec r := by
          simpa only [Category.assoc] using
            congrArg (fun q => 𝒰₂.f i ≫ q) hIf
      _ = pullback.fst f₂ (u ≫ g) ≫ doubleTorusFirstSpec r := by rw [h₂f]
      _ = directBasicOpenDoubleIterated μ A hA hNonempty hCompact i ≫
          pullback.fst f₁ (u ≫ g) :=
        (directBasicOpenDoubleIterated_fst μ A hA hNonempty hCompact i).symm
      _ = (directBasicOpenDoubleIterated μ A hA hNonempty hCompact i ≫
          𝒰₁.f i) ≫ pullback.fst f₁ g := by
        simp only [Category.assoc, h₁f]
  · calc
      (𝒰₂.f i ≫ actualConeDoubleProductIterated r μ A hA hNonempty hCompact) ≫
          pullback.snd f₁ g =
        (𝒰₂.f i ≫ actualConeDoubleProductSecondFactor r A hA hNonempty) ≫
          globalSchemeAction μ A hA hNonempty hCompact := by
            simpa only [Category.assoc] using
              congrArg (fun q => 𝒰₂.f i ≫ q) hIs
      _ = (directBasicOpenDoubleSecondFactor (r := r) A hA hNonempty i ≫
          𝒰₁.f i) ≫ globalSchemeAction μ A hA hNonempty hCompact := by
        rw [actualConeDoubleProductSecondFactor_restrict (r := r) A hA hNonempty i]
      _ = directBasicOpenDoubleSecondFactor (r := r) A hA hNonempty i ≫
          directBasicOpenProductAction μ A hA hNonempty hCompact i := by
        rw [Category.assoc,
          globalSchemeAction_restrict μ A hA hNonempty hCompact i]
        rfl
      _ = (directBasicOpenDoubleIterated μ A hA hNonempty hCompact i ≫
          pullback.snd f₁ (u ≫ g)) ≫ u := by
        rw [directBasicOpenDoubleIterated_snd μ A hA hNonempty hCompact i,
          Category.assoc,
          directBasicOpenActionToBasicOpen_comp_ι μ A hA hNonempty hCompact i]
      _ = (directBasicOpenDoubleIterated μ A hA hNonempty hCompact i ≫
          𝒰₁.f i) ≫ pullback.snd f₁ g := by
        simp only [Category.assoc, h₁s]

end
end QuaternionicSymmetry.ComplexProjectiveActualConeDoubleIteratedRestriction
