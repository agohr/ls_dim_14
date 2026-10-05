import QuaternionicSymmetry.QuaternionicManifoldStandardSolder
import QuaternionicSymmetry.QuaternionicManifoldStandardAffineOverlap
import QuaternionicSymmetry.QuaternionicManifoldProjectiveSmooth

/-! The genuine smooth affine path formed by adding the standard solder
form. Its parameter is kept explicit until the scalar-curvature
normalization is proved. -/
namespace QuaternionicSymmetry.QuaternionicManifoldCorrectedConnection
open QuaternionicManifoldStandardSolder QuaternionicManifoldProjectiveStandardConnection
open QuaternionicManifoldStandardAffineOverlap QuaternionicManifoldProjectiveSmooth
open QuaternionicManifoldStandardMaurerIdentity QuaternionicManifoldLocalScalarLifts
open QuaternionicProjectiveStandardL2 ManifoldQuaternionicConnection
open scoped Manifold ContDiff Quaternion
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance
local instance : NormedSpace ℝ
    (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) := inferInstance
local instance : NormedAlgebra ℝ
    (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) := inferInstance
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

def correctedConnection (t : ℝ) (p : M) :
    LocalConnection.Form (E := E)
      (A := StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) :=
  standardConnection S Q D p + t • standardSolder S Q p

theorem correctedConnection_smooth (t : ℝ) (p : M) :
    ContDiffOn ℝ ∞ (correctedConnection S Q D t p) (extChartAt 𝓘(ℝ,E) p).target :=
  (standardConnection_smooth S Q D p).add ((standardSolder_smooth S Q p).const_smul t)

theorem correctedConnection_affine_refined (t : ℝ) (p q : M) (lift : unitary ℍ)
    (y : E) (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
    (hx : (extChartAt 𝓘(ℝ,E) p).symm y ∈
      liftNeighborhood Q (achart E p) (achart E q) lift) :
    correctedConnection S Q D t p y =
      LocalConnectionGauge.transform
        (LocalConnectionCoordinatePullback.pullback (correctedConnection S Q D t q)
          (chartTransition (I := 𝓘(ℝ,E)) p q))
        (standardChart S Q p (achart E p) (achart E q) lift)
        (standardChartInverse S Q p (achart E p) (achart E q) lift) y := by
  apply ContinuousLinearMap.ext
  intro u
  change standardConnection S Q D p y u + t • standardSolder S Q p y u = _
  rw [standardConnection_affine_refined S Q D p q lift y hy hx,
    standardSolder_overlap S Q p q lift y u hy hx]
  apply ContinuousLinearMap.ext
  intro z
  simp only [LocalConnectionGauge.transform_apply,
    LocalConnectionCoordinatePullback.pullback, ContinuousLinearMap.comp_apply,
    correctedConnection, Pi.add_apply, Pi.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.mul_apply, map_add, map_smul]
  abel

theorem correctedConnection_curvature (t : ℝ) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    LocalConnection.curvature (correctedConnection S Q D t p) y =
      LocalConnection.curvature (standardConnection S Q D p) y +
        t • LocalConnection.covariantDerivative
          (standardConnection S Q D p) (standardSolder S Q p) y +
        t ^ 2 • LocalConnection.wedgeSquare (standardSolder S Q p) y := by
  apply LocalConnection.curvature_path
  · exact ((standardConnection_smooth S Q D p).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)
  · exact ((standardSolder_smooth S Q p).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)

end
end QuaternionicSymmetry.QuaternionicManifoldCorrectedConnection
