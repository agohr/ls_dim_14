import QuaternionicSymmetry.CompactSymplecticProjectorIsotropyRows

/-! The quaternionic tangent operators are the differentials of actual
compact-symplectic isotropy elements. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorIsotropyOperators

open Manifold
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorBaseTangentRange
open CompactSymplecticProjectorBaseQuaternionic
open CompactSymplecticProjectorIsotropyRows
open CompactSymplecticProjectorIsotropyUnits
open CompactSymplecticProjectorFirstBlockUnits
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section

private abbrev RModel (d : ℕ) := Fin d → ℝ

private theorem euclideanCoord
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    ∀ (v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n))
      (c : Fin n ⊕ Fin n),
      baseTangentEuclideanEquiv hDesc hImm n d e q g a hq v c =
        ((baseTangentUpperLinear hDesc n d e q g a) v).1 0 c := by
  letI := a.quotientCharts
  intro v c
  rfl

/-- The first transported tangent operator is exactly the derivative of
the explicit first-block compact-symplectic `i` element. -/
theorem baseI_eq_isotropy_derivative
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    ∀ v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      baseI hDesc hImm n d e q g a hq v =
        mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n (firstBlockLift n firstI).1) (baseCoset n) v := by
  letI := a.quotientCharts
  intro v
  let E := baseTangentEuclideanEquiv hDesc hImm n d e q g a hq
  apply E.injective
  ext c
  have hL : E (baseI hDesc hImm n d e q g a hq v) =
      QuaternionicMatrixModel.standardI n (E v) := by
    simp [E, baseI, baseTangentEuclideanEquiv]
  rw [hL, QuaternionicMatrixModel.standardI_apply]
  rw [euclideanCoord hDesc hImm n d e q g a hq]
  change Complex.I * E v c =
    ((baseTangentUpperLinear hDesc n d e q g a)
      (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
        (leftCosetAction n (firstBlockLift n firstI).1) (baseCoset n) v)).1 0 c
  rw [euclideanCoord hDesc hImm n d e q g a hq]
  exact (firstI_tangent_row hDesc n d e q g a v c).symm

/-- The second transported tangent operator is exactly the derivative of
the explicit first-block compact-symplectic `j` element. -/
theorem baseJ_eq_isotropy_derivative
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) (hq : q = 4 * n) :
    letI := a.quotientCharts
    ∀ v : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n),
      baseJ hDesc hImm n d e q g a hq v =
        mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel q)
          (leftCosetAction n (firstBlockLift n firstJ).1) (baseCoset n) v := by
  letI := a.quotientCharts
  intro v
  let E := baseTangentEuclideanEquiv hDesc hImm n d e q g a hq
  apply E.injective
  ext c
  have hL : E (baseJ hDesc hImm n d e q g a hq v) =
      QuaternionicMatrixModel.standardJ n (E v) := by
    simp [E, baseJ, baseTangentEuclideanEquiv]
  rw [hL]
  rcases c with j | j
  · rw [QuaternionicMatrixModel.standardJ_apply_inl]
    rw [euclideanCoord hDesc hImm n d e q g a hq]
    rw [euclideanCoord hDesc hImm n d e q g a hq]
    exact (firstJ_tangent_row_inl hDesc n d e q g a v j).symm
  · rw [QuaternionicMatrixModel.standardJ_apply_inr]
    rw [euclideanCoord hDesc hImm n d e q g a hq]
    rw [euclideanCoord hDesc hImm n d e q g a hq]
    exact (firstJ_tangent_row_inr hDesc n d e q g a v j).symm

end
end QuaternionicSymmetry.CompactSymplecticProjectorIsotropyOperators
