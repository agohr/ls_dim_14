import QuaternionicSymmetry.ComplexTorusHolomorphicStructure

/-! The complex-torus open-unit charts are also real-smooth. -/

namespace QuaternionicSymmetry.ComplexTorusHolomorphicStructure

open scoped Manifold ContDiff
noncomputable section

instance (r : ℕ) : IsManifold 𝓘(ℝ, Fin r → ℂ) ∞
    (TorusLaurentRepresentation.ComplexTorus r) := by
  let h := torusVal_isOpenEmbedding r
  letI : ChartedSpace (Fin r → ℂ)
      (TorusLaurentRepresentation.ComplexTorus r) := h.singletonChartedSpace
  exact h.isManifold_singleton

end
end QuaternionicSymmetry.ComplexTorusHolomorphicStructure
