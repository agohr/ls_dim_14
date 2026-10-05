import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereCharted
import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereInverseLocal

/-! The independent native form charts have the genuine quaternionic
rank-three SO(3) transitions on overlaps. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereChartOverlap

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSmoothCore
open ManifoldQuaternionicFourNativeSphereBundleEquiv
open ManifoldQuaternionicFourNativeSphereLocalTrivialization
open ManifoldQuaternionicFourNativeSphereInverseLocal
open ManifoldQuaternionicFourNativeSphereLocalCharts
open ManifoldQuaternionicFourNativeSpherePartialChart
open ManifoldQuaternionicFourNativeSphereGeometricLocal
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorSphereCore
open ManifoldTwistorSphereBundle
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : TopologicalSpace (nativeTwoFormVectorCore Q).TotalSpace :=
  (nativeTwoFormVectorCore Q).toTopologicalSpace
local instance : TopologicalSpace (NativeSphereBundleTotal Q) := by
  unfold NativeSphereBundleTotal
  infer_instance
local instance (i : atlas E M) : TopologicalSpace (coefficientLocalDomain Q i) := by
  unfold coefficientLocalDomain
  infer_instance
local instance (i : atlas E M) : TopologicalSpace (nativeLocalSphereTotal Q i) := by
  unfold nativeLocalSphereTotal
  infer_instance

theorem nativeLocalToCoefficient_eq_localCoordinate (i : atlas E M)
    (p : NativeSphereBundleTotal Q)
    (hi : p.1.1 ∈ Q.frames.adaptedCore.baseSet i) :
    (nativeLocalToCoefficient Q hdim i ⟨p,hi⟩).1.2 =
      localCoordinate Q i (nativeSphereToTwistor Q hdim p)
        (by simpa [nativeSphereToTwistor_local,
          projection_pointOfLocal] using hi) := by
  simp only [nativeSphereToTwistor_local Q hdim i p hi,
    localCoordinate_pointOfLocal]
  rfl

theorem nativeCoefficient_transition (i j : atlas E M)
    (p : NativeSphereBundleTotal Q)
    (hi : p.1.1 ∈ Q.frames.adaptedCore.baseSet i)
    (hj : p.1.1 ∈ Q.frames.adaptedCore.baseSet j) :
    (nativeLocalToCoefficient Q hdim j ⟨p,hj⟩).1.2 =
      sphereTransition Q i j p.1.1 hi hj
        (nativeLocalToCoefficient Q hdim i ⟨p,hi⟩).1.2 := by
  rw [nativeLocalToCoefficient_eq_localCoordinate Q hdim i p hi,
    nativeLocalToCoefficient_eq_localCoordinate Q hdim j p hj]
  exact localTrivialization_transition Q i j
    (nativeSphereToTwistor Q hdim p) (by simpa using hi) (by simpa using hj)

theorem nativeSpherePartialChart_apply (i : atlas E M)
    (p₀ : nativeLocalSphereTotal Q i) (p : NativeSphereBundleTotal Q)
    (hi : p.1.1 ∈ Q.frames.adaptedCore.baseSet i) :
    nativeSpherePartialChart Q hdim i p₀ p =
      (p.1.1, coefficientSphereHomeomorph
        (nativeLocalToCoefficient Q hdim i ⟨p,hi⟩).1.2) := by
  letI : Nonempty {x // x ∈ nativeChartSource Q i} := ⟨⟨p₀.1,p₀.2⟩⟩
  have hsub :
      ((nativeChartSource_open Q i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph).symm p =
        (⟨p,hi⟩ : nativeLocalSphereTotal Q i) := by
    simpa using
      (nativeChartSource_open Q i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv
        (f := Subtype.val) (x := (⟨p,hi⟩ : nativeLocalSphereTotal Q i))
  simp [nativeSpherePartialChart, nativeGeometricLocalHomeomorph,
    coefficientGeometricLocalHomeomorph, hsub]
  constructor <;> rfl

theorem nativeSpherePartialChart_transition (i j : atlas E M)
    (pᵢ : nativeLocalSphereTotal Q i) (pⱼ : nativeLocalSphereTotal Q j)
    (p : NativeSphereBundleTotal Q)
    (hi : p.1.1 ∈ Q.frames.adaptedCore.baseSet i)
    (hj : p.1.1 ∈ Q.frames.adaptedCore.baseSet j) :
    nativeSpherePartialChart Q hdim j pⱼ p =
      (p.1.1, euclideanSphereCoordChange Q i j p.1.1
        (nativeSpherePartialChart Q hdim i pᵢ p).2) := by
  rw [nativeSpherePartialChart_apply Q hdim i pᵢ p hi,
    nativeSpherePartialChart_apply Q hdim j pⱼ p hj]
  congr 1
  rw [nativeCoefficient_transition Q hdim i j p hi hj]
  dsimp [euclideanSphereCoordChange]
  have hij : p.1.1 ∈ (Q.frames.adaptedCore.localTriv i).baseSet ∩
      (Q.frames.adaptedCore.localTriv j).baseSet := ⟨hi,hj⟩
  rw [dif_pos hij]
  simp

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereChartOverlap
