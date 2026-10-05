import QuaternionicSymmetry.ManifoldQuaternionicIsometryLocalDerivative

/-! Recenter the actual derivative of a map fixing chart centers, using only
the tangent-core cocycle. -/
namespace QuaternionicSymmetry.ManifoldFixedChartDerivativeTransport
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem fixedChartDerivative_transport (f : M → M)
    (x₀ x₁ y : M)
    (hfix₀ : f x₀ = x₀) (hfix₁ : f x₁ = x₁) (hfixy : f y = y)
    (hy₀ : y ∈ (chartAt E x₀).source)
    (hy₁ : y ∈ (chartAt E x₁).source) :
    ((tangentBundleCore 𝓘(ℝ,E) M).coordChange
      (achart E x₁) (achart E x₀) y).comp
      ((inTangentCoordinates 𝓘(ℝ,E) 𝓘(ℝ,E) id f
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f) x₁ y).comp
        ((tangentBundleCore 𝓘(ℝ,E) M).coordChange
          (achart E x₀) (achart E x₁) y)) =
      inTangentCoordinates 𝓘(ℝ,E) 𝓘(ℝ,E) id f
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f) x₀ y := by
  rw [inTangentCoordinates_eq id f
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f) hy₁
    (by simpa only [hfix₁,hfixy] using hy₁)]
  rw [inTangentCoordinates_eq id f
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f) hy₀
    (by simpa only [hfix₀,hfixy] using hy₀)]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, id_eq]
  have h₀ : y ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet (achart E x₀) :=
    hy₀
  have h₁ : y ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet (achart E x₁) :=
    hy₁
  have hy : y ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet (achart E y) :=
    (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at y
  simp only [hfix₀,hfix₁,hfixy]
  rw [(tangentBundleCore 𝓘(ℝ,E) M).coordChange_comp
    (achart E x₀) (achart E x₁) (achart E y) y ⟨⟨h₀,h₁⟩,hy⟩,
    (tangentBundleCore 𝓘(ℝ,E) M).coordChange_comp
      (achart E y) (achart E x₁) (achart E x₀) y ⟨⟨hy,h₁⟩,h₀⟩]

end
end QuaternionicSymmetry.ManifoldFixedChartDerivativeTransport
