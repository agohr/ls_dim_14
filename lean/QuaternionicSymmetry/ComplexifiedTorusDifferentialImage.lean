import QuaternionicSymmetry.ComplexifiedDerivativeRangeSpan
import QuaternionicSymmetry.CompactLieMaximalTorusTangentSource
import QuaternionicSymmetry.ManifoldQuaternionicTorusAction
import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-! Exact literal image equality for a smooth selected torus followed by
an actual real-smooth homomorphism into a complex Lie group. Its inputs
include only the independently proved real curve-velocity/range identity;
no toral Cartan or contact-field conclusion is assumed. -/

namespace QuaternionicSymmetry.ComplexifiedTorusDifferentialImage

open ComplexifiedDerivativeRangeSpan
open ComplexifiedLieCentralizerComponents
open RealToComplexTangentComplexification
open CompactLieTorusInputs CompactLieMaximalTorusTangentSource
open ManifoldQuaternionicTorusAction
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable {VR VC G K : Type}
  [NormedAddCommGroup VR] [NormedSpace ℝ VR]
  [CompleteSpace VR] [ENat.LEInfty (minSmoothness ℝ 3)]
  [Group G] [TopologicalSpace G] [ChartedSpace VR G]
  [LieGroup 𝓘(ℝ,VR) ∞ G]
  [NormedAddCommGroup VC] [NormedSpace ℂ VC]
  [CompleteSpace VC] [ENat.LEInfty (minSmoothness ℂ 3)]
  [Group K] [TopologicalSpace K] [ChartedSpace VC K]
  [LieGroup 𝓘(ℂ,VC) ∞ K]
  {r d : ℕ} (T : TorusEmbedding G r)
  (hChart : ChartedSpace (Fin d → ℝ) (Torus r))
  (hSmoothT : letI := hChart
    ContMDiff 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VR) ∞ T.hom)
  (f : G →* K)
  (hSmoothf : ContMDiff 𝓘(ℝ,VR) 𝓘(ℝ,VC) ∞ f)

include hSmoothT hSmoothf in
theorem mapped_complex_torus_span_eq_differential_generators
    (hRange : letI := hChart
      torusLieSpan (V := VR) T =
        LinearMap.range
          ((mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VR) T.hom 1).toLinearMap)) :
    letI := hChart
    let fder : GroupLieAlgebra 𝓘(ℝ,VR) G →ₗ[ℝ]
        GroupLieAlgebra 𝓘(ℂ,VC) K :=
      (mfderiv 𝓘(ℝ,VR) 𝓘(ℝ,VC) f 1).toLinearMap
    (complexSpan (L := GroupLieAlgebra 𝓘(ℝ,VR) G)
      (torusLieSpan (V := VR) (G := G) T)).map
        (complexifiedMapComplex fder) =
      Submodule.span ℂ (Set.range
        (fun w : Fin d → ℝ =>
          (show GroupLieAlgebra 𝓘(ℂ,VC) K from
            (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VC)
              (f.comp T.hom) 1) w))) := by
  letI : ChartedSpace (Fin d → ℝ) (Torus r) := hChart
  let g : GroupLieAlgebra 𝓘(ℝ,Fin d → ℝ) (Torus r) →ₗ[ℝ]
      GroupLieAlgebra 𝓘(ℝ,VR) G :=
    (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VR) T.hom 1).toLinearMap
  let fder : GroupLieAlgebra 𝓘(ℝ,VR) G →ₗ[ℝ]
      GroupLieAlgebra 𝓘(ℂ,VC) K :=
    (mfderiv 𝓘(ℝ,VR) 𝓘(ℝ,VC) f 1).toLinearMap
  have hcomp := mfderiv_comp (1 : Torus r)
    (hSmoothf.mdifferentiableAt (by simp))
    (hSmoothT.mdifferentiableAt (by simp))
  rw [map_one] at hcomp
  have hfun (w : Fin d → ℝ) :
      mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VC) (f.comp T.hom) 1 w =
        fder (g w) := by
    exact congrArg (fun F : (Fin d → ℝ) →L[ℝ] VC => F w) hcomp
  rw [hRange]
  change (complexSpan (L := GroupLieAlgebra 𝓘(ℝ,VR) G)
    (LinearMap.range g)).map (complexifiedMapComplex fder) = _
  rw [complexSpan_range_map_eq_span_composition g fder]
  congr 1
  ext z
  constructor
  · rintro ⟨w,rfl⟩
    exact ⟨w,hfun w⟩
  · rintro ⟨w,rfl⟩
    exact ⟨w,(hfun w).symm⟩

end
end QuaternionicSymmetry.ComplexifiedTorusDifferentialImage
