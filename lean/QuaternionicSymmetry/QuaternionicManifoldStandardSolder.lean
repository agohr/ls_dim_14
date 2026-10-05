import QuaternionicSymmetry.QuaternionicManifoldFixedSolder
import QuaternionicSymmetry.QuaternionicStandardSolderEquivariance
import QuaternionicSymmetry.QuaternionicManifoldProductRepresentationPointwise

/-! The smooth standard solder one-form and its homogeneous transition law
on the actual refined quaternionic chart overlaps. -/
namespace QuaternionicSymmetry.QuaternionicManifoldStandardSolder
open QuaternionicManifoldFixedSolder QuaternionicStandardSolderOperator
open QuaternionicStandardSolderEquivariance QuaternionicProjectiveStandardL2
open QuaternionicManifoldProductRepresentationPointwise
open QuaternionicManifoldStandardMaurerIdentity QuaternionicManifoldLocalScalarLifts
open QuaternionicManifoldSignedLocalLifts QuaternionicManifoldFixedConnectionOverlap
open ManifoldQuaternionicConnection
open scoped Manifold ContDiff Quaternion
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance
local instance : NormedSpace ℝ
    (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) := inferInstance

def standardSolder (p : M) (y : E) :
    E →L[ℝ] (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) :=
  (solderOperator S).comp (fixedSolder S Q p y)

omit [Nontrivial E] in
theorem standardSolder_smooth (p : M) :
    ContDiffOn ℝ ∞ (standardSolder S Q p) (extChartAt 𝓘(ℝ,E) p).target :=
  contDiffOn_const.clm_comp (fixedSolder_smooth S Q p)

set_option maxHeartbeats 800000 in
theorem standardSolder_intertwines (p q : M) (lift : unitary ℍ) (y u : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
    (hx : (extChartAt 𝓘(ℝ,E) p).symm y ∈
      liftNeighborhood Q (achart E p) (achart E q) lift) :
    standardSolder S Q q (chartTransition (I := 𝓘(ℝ,E)) p q y)
        (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y u) *
      standardChart S Q p (achart E p) (achart E q) lift y =
    standardChart S Q p (achart E p) (achart E q) lift y *
      standardSolder S Q p y u := by
  have hs := congrArg (fun T : E →L[ℝ] E => T u)
    (fixedSolder_chartTransition S Q p q y hy)
  simp only [ContinuousLinearMap.comp_apply] at hs
  unfold standardSolder
  simp only [ContinuousLinearMap.comp_apply]
  rw [hs, fixedGauge_eq_localProductLift S Q p q lift y hx,
    standardChart_eq_localProductLift S Q p q lift y hx]
  apply ContinuousLinearMap.ext
  intro z
  exact solderOperator_covariant S _ _ z

theorem standardSolder_overlap (p q : M) (lift : unitary ℍ) (y u : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
    (hx : (extChartAt 𝓘(ℝ,E) p).symm y ∈
      liftNeighborhood Q (achart E p) (achart E q) lift) :
    standardSolder S Q p y u =
      standardChartInverse S Q p (achart E p) (achart E q) lift y *
        standardSolder S Q q (chartTransition (I := 𝓘(ℝ,E)) p q y)
          (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y u) *
        standardChart S Q p (achart E p) (achart E q) lift y := by
  rw [mul_assoc, standardSolder_intertwines S Q p q lift y u hy hx,
    ← mul_assoc, standardChartInverse_mul_standardChart S Q p q lift y hx, one_mul]

end
end QuaternionicSymmetry.QuaternionicManifoldStandardSolder
