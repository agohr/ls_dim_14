import QuaternionicSymmetry.QuaternionicProjectiveStandardAdjoint
import QuaternionicSymmetry.QuaternionicManifoldSignedLocalLifts

/-! Smooth operator coordinates for the standard Hilbert representation of
the locally lifted adapted tangent transitions. -/

namespace QuaternionicSymmetry.QuaternionicManifoldStandardLocalOperator

open VectorBundleFrameTransitions
  QuaternionicManifoldLocalScalarLifts
  QuaternionicManifoldSmoothProductLifts
  QuaternionicManifoldSignedLocalLifts
  QuaternionicProjectiveStandardL2
  QuaternionicProjectiveStandardRepresentation
open scoped ContDiff Manifold Quaternion

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

private def starLinear : ℍ →ₗ[ℝ] ℍ where
  toFun := star
  map_add' a b := by simp
  map_smul' r a := by simp [Quaternion.star_smul]

def rightStarOperator (i j : atlas E M) (q : unitary ℍ) (y : M) :
    ℍ →L[ℝ] ℍ :=
  ((ContinuousLinearMap.mul ℝ ℍ).flip) (star (scalarLiftRaw Q i j q y))

theorem smooth_rightStarOperator (i j : atlas E M) (q : unitary ℍ) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℍ →L[ℝ] ℍ) ∞
      (rightStarOperator Q i j q) (liftNeighborhood Q i j q) := by
  have hstar : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℍ) ∞
      (fun y : M => star (scalarLiftRaw Q i j q y))
      (liftNeighborhood Q i j q) :=
    (starLinear.toContinuousLinearMap.contMDiff).comp_contMDiffOn
      (smooth_scalarLiftRaw Q i j q)
  exact ((ContinuousLinearMap.mul ℝ ℍ).flip).contMDiff.comp_contMDiffOn hstar

private def coordinateEquiv : StandardSpace (E := E) ≃L[ℝ] E × ℍ :=
  WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ

def localStandardOperator (i j : atlas E M) (q : unitary ℍ) (y : M) :
    StandardSpace (E := E) →L[ℝ] StandardSpace (E := E) :=
  (coordinateEquiv (E := E)).symm.toContinuousLinearMap.comp
    (((symplecticFactorOperator S Q i j q y).prodMap
      (rightStarOperator Q i j q y)).comp
        (coordinateEquiv (E := E)).toContinuousLinearMap)

theorem smooth_localStandardOperator (i j : atlas E M) (q : unitary ℍ) :
    ContMDiffOn 𝓘(ℝ, E)
      𝓘(ℝ, StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) ∞
      (localStandardOperator S Q i j q) (liftNeighborhood Q i j q) := by
  have hprod : ContMDiffOn 𝓘(ℝ, E)
      𝓘(ℝ, (E × ℍ) →L[ℝ] (E × ℍ)) ∞
      (fun y : M => (symplecticFactorOperator S Q i j q y).prodMap
        (rightStarOperator Q i j q y))
      (liftNeighborhood Q i j q) :=
    (smooth_symplecticFactorOperator S Q i j q).clm_prodMap
      (smooth_rightStarOperator Q i j q)
  have hright : ContMDiffOn 𝓘(ℝ, E)
      𝓘(ℝ, StandardSpace (E := E) →L[ℝ] E × ℍ) ∞
      (fun y : M => ((symplecticFactorOperator S Q i j q y).prodMap
        (rightStarOperator Q i j q y)).comp
          (coordinateEquiv (E := E)).toContinuousLinearMap)
      (liftNeighborhood Q i j q) :=
    hprod.clm_comp contMDiffOn_const
  exact contMDiffOn_const.clm_comp hright

theorem localStandardOperator_eq (i j : atlas E M)
    (q : unitary ℍ) (y : M)
    (hy : y ∈ liftNeighborhood Q i j q) :
    localStandardOperator S Q i j q y =
      (standardActionL2 S (localProductLift S Q i j q y hy)).toContinuousLinearMap := by
  ext z
  apply (coordinateEquiv (E := E)).injective
  apply Prod.ext
  · change (symplecticFactorOperator S Q i j q y) z.fst =
      (localProductLift S Q i j q y hy).1.1.1 z.fst
    rw [← localProductLift_operator S Q i j q y hy]
    simp
  · change z.snd * star (scalarLiftRaw Q i j q y) =
      z.snd * star ((scalarLiftUnit Q S i j q y hy : unitary ℍ) : ℍ)
    rfl

end
end QuaternionicSymmetry.QuaternionicManifoldStandardLocalOperator
