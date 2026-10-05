import QuaternionicSymmetry.CompactSymplecticProjectorQuaternionicUpperLinear

/-! The actual base-point projector differential fills the entire explicit
quaternionic off-diagonal block space. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorBaseTangentRange

open Matrix Manifold
open CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectorBaseTangent
open CompactSymplecticProjectorQuaternionicBlock
open CompactSymplecticProjectorQuaternionicUpperLinear
open CompactSymplecticProjectorSmoothAction
open CompactSymplecticProjectorRiemannianMetric
open CompactSymplecticClosedSubgroupSource
open CompactSymplecticHomogeneousAtlasSource
open scoped Matrix.Norms.Operator Manifold ContDiff
noncomputable section
set_option maxHeartbeats 1000000

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev J (n : ℕ) := Fin n ⊕ Fin n
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev BMat (n : ℕ) := Matrix (Fin 2) (J n) ℂ
private abbrev RModel (d : ℕ) := Fin d → ℝ

/-- Extract the upper mixed block after the explicit stabilizer reindexing;
this operation is real-linear. -/
private def upperBlockLinear (n : ℕ) : Mat n →ₗ[ℝ] BMat n where
  toFun X := (baseBlockMatrix n X).toBlocks₁₂
  map_add' := by intro X Y; rfl
  map_smul' := by intro r X; rfl

/-- The actual differential, followed by upper-block extraction, lands in
the checked quaternionic `4n`-dimensional real subspace. -/
def baseTangentUpperLinear
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    letI := a.quotientCharts
    TangentSpace 𝓘(ℝ, RModel q) (baseCoset n) →ₗ[ℝ] upperSubmodule n := by
  letI := a.quotientCharts
  let f : TangentSpace 𝓘(ℝ, RModel q) (baseCoset n) →ₗ[ℝ] BMat n :=
    (upperBlockLinear n).comp
      (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) (baseCoset n)).toLinearMap
  exact f.codRestrict (upperSubmodule n) (by
    intro v
    exact (mem_upperSubmodule_iff n _).2
      (base_tangent_upper_quaternionic hDesc n d e q g a v))

/-- No genuine tangent direction is lost by upper-block extraction:
Hermitianity and the projector equation reconstruct the full matrix. -/
theorem baseTangentUpperLinear_injective
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g) :
    letI := a.quotientCharts
    Function.Injective (baseTangentUpperLinear hDesc n d e q g a) := by
  letI := a.quotientCharts
  intro v w h
  have hB := congrArg (fun B : upperSubmodule n => B.1) h
  change (baseBlockMatrix n
      (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) (baseCoset n) v)).toBlocks₁₂ =
    (baseBlockMatrix n
      (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) (baseCoset n) w)).toBlocks₁₂ at hB
  have hv := base_tangent_eq_offDiagonal hDesc n d e q g a v
  have hw := base_tangent_eq_offDiagonal hDesc n d e q g a w
  have hBlock : baseBlockMatrix n
      (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) (baseCoset n) v) =
    baseBlockMatrix n
      (mfderiv 𝓘(ℝ, RModel q) 𝓘(ℝ, Mat n)
        (quotientOrbitProjector n) (baseCoset n) w) := by
    rw [hv, hw, hB]
  have hMat := (Matrix.reindexAlgEquiv ℂ ℂ
    (CompactSymplecticStabilizerIndex.blockIndexEquiv n)).injective hBlock
  exact (quotientOrbitProjector_mfderiv_injective hDesc hImm
    n d e q g a (baseCoset n)) hMat

/-- Once the actual quotient dimension is known to be `4n`, the checked
injective differential fills every quaternionic upper mixed block. -/
theorem baseTangentUpperLinear_surjective
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (hq : q = 4 * n) :
    letI := a.quotientCharts
    Function.Surjective (baseTangentUpperLinear hDesc n d e q g a) := by
  letI := a.quotientCharts
  letI := a.quotientManifold
  letI : FiniteDimensional ℝ
      (TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)) := by
    change FiniteDimensional ℝ (RModel q)
    infer_instance
  have hFin : Module.finrank ℝ
      (TangentSpace 𝓘(ℝ, RModel q) (baseCoset n)) =
      Module.finrank ℝ (upperSubmodule n) := by
    rw [upperSubmodule_real_finrank]
    simpa only [TangentSpace, Module.finrank_fin_fun] using hq
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hFin).mp
    (baseTangentUpperLinear_injective hDesc hImm n d e q g a)

/-- The true base tangent space is real-linearly identical to the full
quaternionic off-diagonal upper-block solution space. -/
def baseTangentUpperLinearEquiv
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (n d e q : ℕ) (g : EmbeddedRealLieAtlas n d)
    (a : SmoothHomogeneousAtlas n d e q g)
    (hq : q = 4 * n) :
    letI := a.quotientCharts
    TangentSpace 𝓘(ℝ, RModel q) (baseCoset n) ≃ₗ[ℝ] upperSubmodule n := by
  letI := a.quotientCharts
  exact LinearEquiv.ofBijective (baseTangentUpperLinear hDesc n d e q g a)
    ⟨baseTangentUpperLinear_injective hDesc hImm n d e q g a,
      baseTangentUpperLinear_surjective hDesc hImm n d e q g a hq⟩

/-- The source-constructed actual first-projector model has a canonical
base tangent identification with the entire `4(m+1)`-dimensional
quaternionic mixed-block space. -/
def FirstProjectorModel.baseTangentUpperEquiv (m : ℕ)
    (hDesc : GeneralSmoothMapSource.LeeSurjectiveSubmersionDescentTheorem)
    (hImm : GeneralSmoothMapSource.LeeEquivariantImmersionTheorem)
    (M : FirstProjectorModel m) :
    letI := M.quotientAtlas.quotientCharts
    TangentSpace 𝓘(ℝ, RModel M.q) (baseCoset (m + 1)) ≃ₗ[ℝ]
      upperSubmodule (m + 1) :=
  baseTangentUpperLinearEquiv hDesc hImm (m + 1) M.d M.e M.q
    M.groupAtlas M.quotientAtlas M.realDimension

end
end QuaternionicSymmetry.CompactSymplecticProjectorBaseTangentRange
