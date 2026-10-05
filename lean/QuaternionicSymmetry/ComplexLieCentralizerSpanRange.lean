import QuaternionicSymmetry.ComplexLieCentralizerTangent
import QuaternionicSymmetry.ComplexifiedLieImageCentralizer

/-! An actual Lie centralizer's tangent lies in a self-centralizing
complexified derivative span. The statement exposes the exact derivative
comparison and span-generation hypotheses; applications must prove both for
their selected compact torus. -/

namespace QuaternionicSymmetry.ComplexLieCentralizerSpanRange

open QuaternionicSymmetry.ComplexLieCentralizerTangent
open QuaternionicSymmetry.ComplexifiedLieImageCentralizer
open QuaternionicSymmetry.ComplexifiedLieCentralizerComponents
open QuaternionicSymmetry.RealToComplexTangentComplexification
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable {E F V L G K : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [LieRing L] [LieAlgebra ℝ L]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [IsManifold 𝓘(ℝ,E) ∞ G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [Group K] [TopologicalSpace K] [ChartedSpace V K]
  [IsManifold 𝓘(ℂ,V) ∞ K] [LieGroup 𝓘(ℂ,V) ∞ K]
  [IsManifold 𝓘(ℝ,V) ∞ K] [LieGroup 𝓘(ℝ,V) ∞ K]

local instance realMin : ENat.LEInfty (minSmoothness ℝ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

local instance complexMin : ENat.LEInfty (minSmoothness ℂ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

theorem centralizer_subtype_derivative_range_le
    (H : Subgroup K)
    [ChartedSpace F H] [IsManifold 𝓘(ℝ,F) ∞ H]
    [LieGroup 𝓘(ℝ,F) ∞ H]
    (h : G →* K)
    (hH : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,V) ∞ H.subtype)
    (hh : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ h)
    (hComm : ∀ (a : H) (b : G), Commute (a : K) (h b))
    (T : Submodule ℝ L)
    (f : L →ₗ[ℝ] (GroupLieAlgebra 𝓘(ℂ,V) K))
    (g : E →ₗ[ℝ] L)
    (hRange : T = LinearMap.range g)
    (hDeriv : ∀ v : E,
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) h 1 v = f (g v))
    (hSelf : ∀ z : GroupLieAlgebra 𝓘(ℂ,V) K,
      z ∈ (complexSpan T).map (complexifiedMapComplex f) ↔
        ∀ s ∈ (complexSpan T).map (complexifiedMapComplex f), ⁅z,s⁆ = 0) :
    LinearMap.range
      ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) H.subtype 1).toLinearMap) ≤
      ((complexSpan T).map (complexifiedMapComplex f)).restrictScalars ℝ := by
  intro z hz
  obtain ⟨u, rfl⟩ := hz
  have hBr (v : E) :
      @Bracket.bracket (GroupLieAlgebra 𝓘(ℂ,V) K)
        (GroupLieAlgebra 𝓘(ℂ,V) K) inferInstance
        (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) H.subtype 1 u) (f (g v)) = 0 := by
    rw [← hDeriv]
    exact centralizer_derivative_bracket_zero H h hH hh hComm u v
  apply (hSelf _).2
  intro s hs
  exact centralizes_complexified_image_of_range T f g hRange _ hBr hs

end
end QuaternionicSymmetry.ComplexLieCentralizerSpanRange
