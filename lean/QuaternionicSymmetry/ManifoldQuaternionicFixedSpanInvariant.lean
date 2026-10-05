import QuaternionicSymmetry.ManifoldQuaternionicFixedTangentQuaternionic
import QuaternionicSymmetry.ManifoldQuaternionicSubmanifoldInput

/-! Actual fixed tangent spaces invariant under generators are invariant
under the entire quaternionic endomorphism span. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFixedSpanInvariant

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicFixedTangentDimension
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicFixedTangentQuaternionic
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (S : Subgroup (QuaternionicIsometries Q)) (x : M)
  (hx : x ∈ fixedPoints Q S)

theorem fixedTangentSpace_span_mem
    (hQ : ∀ f ∈ S, ∀ a : Fin 3 → ℝ, coefficientAction Q f x a = a)
    (B : TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hB : B ∈ tangentSpan Q x)
    (v : TangentSpace 𝓘(ℝ,E) x) (hv : v ∈ fixedTangentSpace Q S x hx) :
    B v ∈ fixedTangentSpace Q S x hx := by
  let W := fixedTangentSpace Q S x hx
  have h : ∀ B, B ∈ tangentSpan Q x → ∀ v ∈ W, B v ∈ W := by
    intro B hB
    induction hB using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨t, rfl⟩ := hB
      exact fun v hv => fixedTangentSpace_generator_mem Q S x hx hQ t hv
    | zero =>
      intro v _
      exact W.zero_mem
    | add B C _ _ hB hC =>
      intro v hv
      exact W.add_mem (hB v hv) (hC v hv)
    | smul c B _ hB =>
      intro v hv
      exact W.smul_mem c (hB v hv)
  exact h B hB v hv

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedSpanInvariant
