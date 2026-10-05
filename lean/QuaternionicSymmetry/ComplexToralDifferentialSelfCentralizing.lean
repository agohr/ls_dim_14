import QuaternionicSymmetry.ComplexifiedTorusDifferentialImage
import QuaternionicSymmetry.ComplexifiedLieImageSelfCentralizing

/-! The exact complex differential span of a composed compact-torus action
is self-centralizing when the real torus is self-centralizing and the
actual homomorphism has bijective bracket-preserving complexified tangent
map. This is an internal transport statement, not a Cartan source. -/

namespace QuaternionicSymmetry.ComplexToralDifferentialSelfCentralizing

open ComplexifiedTorusDifferentialImage
open ComplexifiedLieImageSelfCentralizing
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
theorem differential_span_selfCentralizing
    (hRange : letI := hChart
      torusLieSpan (V := VR) T =
        LinearMap.range
          ((mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VR) T.hom 1).toLinearMap))
    (hAb : ∀ x ∈ torusLieSpan (V := VR) T,
      ∀ y ∈ torusLieSpan (V := VR) T, ⁅x,y⁆ = 0)
    (hSelf : ∀ x : GroupLieAlgebra 𝓘(ℝ,VR) G,
      (∀ y ∈ torusLieSpan (V := VR) T, ⁅x,y⁆ = 0) →
        x ∈ torusLieSpan (V := VR) T)
    (hBij : Function.Bijective
      (complexifiedMapComplex
        (show GroupLieAlgebra 𝓘(ℝ,VR) G →ₗ[ℝ]
          GroupLieAlgebra 𝓘(ℂ,VC) K from
          (mfderiv 𝓘(ℝ,VR) 𝓘(ℝ,VC) f 1).toLinearMap)))
    (hBracket : ∀ x y : GroupLieAlgebra 𝓘(ℝ,VR) G,
      (show GroupLieAlgebra 𝓘(ℂ,VC) K from
        mfderiv 𝓘(ℝ,VR) 𝓘(ℝ,VC) f 1 ⁅x,y⁆) =
        ⁅(show GroupLieAlgebra 𝓘(ℂ,VC) K from
            mfderiv 𝓘(ℝ,VR) 𝓘(ℝ,VC) f 1 x),
          (show GroupLieAlgebra 𝓘(ℂ,VC) K from
            mfderiv 𝓘(ℝ,VR) 𝓘(ℝ,VC) f 1 y)⁆)
    (z : GroupLieAlgebra 𝓘(ℂ,VC) K) :
    letI := hChart
    let S : Submodule ℂ (GroupLieAlgebra 𝓘(ℂ,VC) K) :=
      Submodule.span ℂ (Set.range
        (fun w : Fin d → ℝ =>
          (show GroupLieAlgebra 𝓘(ℂ,VC) K from
            (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VC)
              (f.comp T.hom) 1) w)))
    z ∈ S ↔ ∀ w ∈ S, ⁅z,w⁆ = 0 := by
  letI : ChartedSpace (Fin d → ℝ) (Torus r) := hChart
  let fder : GroupLieAlgebra 𝓘(ℝ,VR) G →ₗ[ℝ]
      GroupLieAlgebra 𝓘(ℂ,VC) K :=
    (mfderiv 𝓘(ℝ,VR) 𝓘(ℝ,VC) f 1).toLinearMap
  have hImage := mapped_complex_torus_span_eq_differential_generators
    T hChart hSmoothT f hSmoothf hRange
  have hCentral := image_selfCentralizing
    (torusLieSpan (V := VR) T) hAb hSelf fder hBij hBracket z
  rw [← hImage]
  exact hCentral

end
end QuaternionicSymmetry.ComplexToralDifferentialSelfCentralizing
