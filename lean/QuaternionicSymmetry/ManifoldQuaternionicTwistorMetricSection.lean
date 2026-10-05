import QuaternionicSymmetry.ManifoldQuaternionicTwistorMetricFrameSmooth
import QuaternionicSymmetry.ManifoldQuaternionicTwistorMetricBounded

/-! Smooth bundle section of the explicit horizontal/vertical metric on the
genuine twistor tangent bundle. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorMetricSection

open Bundle
open ManifoldQuaternionicTwistorMetricBilinear
open ManifoldQuaternionicTwistorMetricBounded
open ManifoldQuaternionicTwistorMetricFrameSmooth
open ManifoldQuaternionicTwistorSplitMetric
open ManifoldQuaternionicTwistorMetricEvaluationSmooth
open ManifoldFiniteDimensionalCLMSmooth
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff Bundle
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)
private abbrev F := E × EuclideanSpace ℝ (Fin 2)
private abbrev B := F (E := E) →L[ℝ] F (E := E) →L[ℝ] ℝ

private local instance : NormedAddCommGroup (B (E := E)) :=
  by
    change NormedAddCommGroup (F (E := E) →L[ℝ]
      (F (E := E) →L[ℝ] ℝ))
    exact ContinuousLinearMap.toNormedAddCommGroup
      (σ₁₂ := RingHom.id ℝ)
      (E := F (E := E))
      (F := F (E := E) →L[ℝ] ℝ)

private local instance : NormedSpace ℝ (B (E := E)) :=
  ContinuousLinearMap.toNormedSpace
    (σ₁₂ := RingHom.id ℝ)
    (E := F (E := E))
    (F := F (E := E) →L[ℝ] ℝ)
    (𝕜' := ℝ)

private local instance : TopologicalSpace
    (TotalSpace (F (E := E) →L[ℝ] ℝ)
      (fun z : SphereBundleTotal Q => TangentSpace (J (E := E)) z →L[ℝ] ℝ)) :=
  inferInstance

private local instance : FiberBundle (F (E := E) →L[ℝ] ℝ)
    (fun z : SphereBundleTotal Q => TangentSpace (J (E := E)) z →L[ℝ] ℝ) :=
  inferInstance

private local instance : VectorBundle ℝ (F (E := E) →L[ℝ] ℝ)
    (fun z : SphereBundleTotal Q => TangentSpace (J (E := E)) z →L[ℝ] ℝ) :=
  inferInstance

private local instance : TopologicalSpace
    (TotalSpace (B (E := E))
      (fun z : SphereBundleTotal Q => TangentSpace (J (E := E)) z →L[ℝ]
        TangentSpace (J (E := E)) z →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    (F (E := E)) (TangentSpace (J (E := E)))
    (F (E := E) →L[ℝ] ℝ)
    (fun z : SphereBundleTotal Q => TangentSpace (J (E := E)) z →L[ℝ] ℝ)

private local instance : FiberBundle (B (E := E))
    (fun z : SphereBundleTotal Q => TangentSpace (J (E := E)) z →L[ℝ]
      TangentSpace (J (E := E)) z →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    (F (E := E)) (TangentSpace (J (E := E)))
    (F (E := E) →L[ℝ] ℝ)
    (fun z : SphereBundleTotal Q => TangentSpace (J (E := E)) z →L[ℝ] ℝ)

private local instance (z : SphereBundleTotal Q) : Module ℝ
    (TangentSpace (J (E := E)) z →L[ℝ]
      TangentSpace (J (E := E)) z →L[ℝ] ℝ) :=
  ContinuousLinearMap.module

private local instance : VectorBundle ℝ (B (E := E))
    (fun z : SphereBundleTotal Q => TangentSpace (J (E := E)) z →L[ℝ]
      TangentSpace (J (E := E)) z →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    (F (E := E)) (TangentSpace (J (E := E)))
    (F (E := E) →L[ℝ] ℝ)
    (fun z : SphereBundleTotal Q => TangentSpace (J (E := E)) z →L[ℝ] ℝ)

private local instance : ContMDiffVectorBundle ∞ (B (E := E))
    (fun z : SphereBundleTotal Q => TangentSpace (J (E := E)) z →L[ℝ]
      TangentSpace (J (E := E)) z →L[ℝ] ℝ) (J (E := E)) :=
  ContMDiffVectorBundle.continuousLinearMap
    (𝕜 := ℝ) (n := ∞) (IB := J (E := E))
    (F₁ := F (E := E))
    (E₁ := TangentSpace (J (E := E)))
    (F₂ := F (E := E) →L[ℝ] ℝ)
    (E₂ := fun z : SphereBundleTotal Q => TangentSpace (J (E := E)) z →L[ℝ] ℝ)

private def tangentTriv (z₀ : SphereBundleTotal Q) :=
  trivializationAt (F (E := E)) (TangentSpace (J (E := E))) z₀

private def metricTriv (z₀ : SphereBundleTotal Q) :=
  trivializationAt (B (E := E))
    (fun z : SphereBundleTotal Q => TangentSpace (J (E := E)) z →L[ℝ]
      TangentSpace (J (E := E)) z →L[ℝ] ℝ) z₀

def metricCoordinates (z₀ z : SphereBundleTotal Q) : B (E := E) :=
  ((metricTriv Q z₀) ⟨z,splitMetricCLM Q D z⟩).2

theorem metricCoordinates_apply (z₀ z : SphereBundleTotal Q)
    (hz : z ∈ (tangentTriv Q z₀).baseSet)
    (a b : F (E := E)) :
    metricCoordinates Q D z₀ z a b =
      splitMetric Q D z (tangentFrameField Q z₀ a z)
        (tangentFrameField Q z₀ b z) := by
  change (trivializationAt (B (E := E))
    (fun z : SphereBundleTotal Q => TangentSpace (J (E := E)) z →L[ℝ]
      TangentSpace (J (E := E)) z →L[ℝ] ℝ) z₀
      ⟨z,splitMetricCLM Q D z⟩).2 a b = _
  rw [hom_trivializationAt_apply
    (σ := RingHom.id ℝ)
    (F₁ := F (E := E))
    (E₁ := TangentSpace (J (E := E)))
    (F₂ := F (E := E) →L[ℝ] ℝ)
    (E₂ := fun z : SphereBundleTotal Q => TangentSpace (J (E := E)) z →L[ℝ] ℝ)]
  rw [inCoordinates_apply_eq₂ (h₁x := hz) (h₂x := hz)
    (h₃x := by simp)]
  simp [tangentFrameField, splitMetricCLM_apply]

theorem metricCoordinates_smoothOn (z₀ : SphereBundleTotal Q) :
    let U := (tangentTriv Q z₀).baseSet ∩
      ((sphereCore Q).localTriv (achart E z₀.1)).toOpenPartialHomeomorph.source
    ContMDiffOn (J (E := E)) 𝓘(ℝ,B (E := E)) ∞
      (metricCoordinates Q D z₀) U := by
  let e := tangentTriv Q z₀
  let S := ((sphereCore Q).localTriv (achart E z₀.1)).toOpenPartialHomeomorph.source
  let U := e.baseSet ∩ S
  have hUopen : IsOpen U :=
    e.open_baseSet.inter
      ((sphereCore Q).localTriv (achart E z₀.1)).toOpenPartialHomeomorph.open_source
  have hscalar (a b : F (E := E)) :
      ContMDiffOn (J (E := E)) 𝓘(ℝ) ∞
        (fun z => metricCoordinates Q D z₀ z a b) U := by
    have ha : ContMDiffOn (J (E := E)) (J (E := E)).tangent ∞
        (fun z => (⟨z,tangentFrameField Q z₀ a z⟩ :
          TangentBundle (J (E := E)) (SphereBundleTotal Q))) U :=
      (tangentFrameField_smoothOn Q z₀ a).mono (Set.inter_subset_left)
    have hb : ContMDiffOn (J (E := E)) (J (E := E)).tangent ∞
        (fun z => (⟨z,tangentFrameField Q z₀ b z⟩ :
          TangentBundle (J (E := E)) (SphereBundleTotal Q))) U :=
      (tangentFrameField_smoothOn Q z₀ b).mono (Set.inter_subset_left)
    have hs : U ⊆ S := Set.inter_subset_right
    have h := splitMetric_eval_smoothOn_of_subset Q D z₀.1 U hs
      (tangentFrameField Q z₀ a) (tangentFrameField Q z₀ b) ha hb
    exact h.congr (by
      intro z hz
      exact metricCoordinates_apply Q D z₀ z hz.1 a b)
  change ContMDiffOn (J (E := E)) 𝓘(ℝ,B (E := E)) ∞
    (metricCoordinates Q D z₀) U
  apply (contMDiffOn_clm_apply_iff
    (I := J (E := E)) (A := F (E := E))
    (B := F (E := E) →L[ℝ] ℝ) hUopen).mpr
  intro a
  apply (contMDiffOn_clm_apply_iff
    (I := J (E := E)) (A := F (E := E))
    (B := ℝ) hUopen).mpr
  intro b
  exact hscalar a b

theorem splitMetricCLM_contMDiff :
    ContMDiff (J (E := E))
      ((J (E := E)).prod 𝓘(ℝ,B (E := E))) ∞
      (fun z : SphereBundleTotal Q =>
        (⟨z,splitMetricCLM Q D z⟩ : TotalSpace (B (E := E))
          (fun z : SphereBundleTotal Q => TangentSpace (J (E := E)) z →L[ℝ]
            TangentSpace (J (E := E)) z →L[ℝ] ℝ))) := by
  intro z₀
  let U := (tangentTriv Q z₀).baseSet ∩
    ((sphereCore Q).localTriv (achart E z₀.1)).toOpenPartialHomeomorph.source
  have hUopen : IsOpen U :=
    (tangentTriv Q z₀).open_baseSet.inter
      ((sphereCore Q).localTriv (achart E z₀.1)).toOpenPartialHomeomorph.open_source
  have hzbase : z₀ ∈ (tangentTriv Q z₀).baseSet :=
    mem_baseSet_trivializationAt _ _ _
  have hzsphere : z₀ ∈
      ((sphereCore Q).localTriv (achart E z₀.1)).toOpenPartialHomeomorph.source :=
    ((sphereCore Q).mem_localTriv_source (achart E z₀.1) z₀).mpr
      (by rw [← (sphereCore Q).baseSet_at]; exact (sphereCore Q).mem_baseSet_at z₀.1)
  have hzU : z₀ ∈ U := ⟨hzbase,hzsphere⟩
  have hcoord : ContMDiffAt (J (E := E)) 𝓘(ℝ,B (E := E)) ∞
      (metricCoordinates Q D z₀) z₀ :=
    ((metricCoordinates_smoothOn Q D z₀) z₀ hzU).contMDiffAt
      (hUopen.mem_nhds hzU)
  have hzmetric : z₀ ∈ (metricTriv Q z₀).baseSet :=
    mem_baseSet_trivializationAt _ _ _
  haveI : MemTrivializationAtlas (metricTriv Q z₀) := by
    dsimp [metricTriv]
    infer_instance
  exact ((metricTriv Q z₀).contMDiffAt_section_iff hzmetric).mpr hcoord

/-- The actual smooth Riemannian metric on the quaternionic twistor sphere
bundle, built from the Levi-Civita horizontal split and the round vertical
coefficient metric. No smoothness or invariance is supplied as input. -/
def smoothTwistorMetric : Bundle.ContMDiffRiemannianMetric
    (J (E := E)) ∞ (F (E := E))
      (TangentSpace (J (E := E)) : SphereBundleTotal Q → Type _) where
  inner := splitMetricCLM Q D
  symm := by
    intro z u v
    simpa only [splitMetricCLM_apply] using splitMetric_symm Q D z u v
  pos := by
    intro z v hv
    simpa only [splitMetricCLM_apply] using splitMetric_pos Q D z v hv
  isVonNBounded := splitMetricCLM_isVonNBounded Q D
  contMDiff := splitMetricCLM_contMDiff Q D

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorMetricSection
