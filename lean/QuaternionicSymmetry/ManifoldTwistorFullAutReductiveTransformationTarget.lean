import QuaternionicSymmetry.ManifoldTwistorFullAutReductiveLieTarget

/-!
# A single reductive complex Lie transformation structure

Unlike separate existential Lie-atlas and transformation-group conclusions,
this target asks for joint holomorphic evaluation and a central Lie radical
in the *same* charted Lie group on the literal full automorphism group.
-/

namespace QuaternionicSymmetry.ManifoldTwistorFullAutReductiveTransformationTarget

open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorFullAutReductiveLieTarget
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)

/-- The full biholomorphism group acts jointly holomorphically and has
central complex Lie radical in one and the same Lie atlas. -/
def FullAutReductiveTransformationConclusion : Prop :=
  letI := B.charts
  letI := B.complexManifold
  let G := TwistorHolomorphicAutomorphisms Q D B
  ∃ (V : Type) (hNorm : NormedAddCommGroup V),
    letI : NormedAddCommGroup V := hNorm
    ∃ (hSpace : NormedSpace ℂ V) (hFinite : FiniteDimensional ℂ V)
      (hChart : ChartedSpace V G),
      letI : NormedSpace ℂ V := hSpace
      letI : FiniteDimensional ℂ V := hFinite
      letI : ChartedSpace V G := hChart
      ∃ hManifold : IsManifold 𝓘(ℂ,V) ∞ G,
        letI : IsManifold 𝓘(ℂ,V) ∞ G := hManifold
        ∃ hLie : LieGroup 𝓘(ℂ,V) ∞ G,
          letI : LieGroup 𝓘(ℂ,V) ∞ G := hLie
          ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
            𝓘(ℂ,ComplexTwistorModel n) ∞
            (fun p : G × SphereBundleTotal Q => p.1.1 p.2) ∧
          (letI : CompleteSpace V := FiniteDimensional.complete ℂ V
           letI : ENat.LEInfty (minSmoothness ℂ 3) := by
             simpa only [minSmoothness_of_isRCLikeNormedField] using
               (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
           letI : LieGroup 𝓘(ℂ,V) (minSmoothness ℂ 3) G :=
             LieGroup.of_le (ENat.LEInfty.out)
           LieAlgebra.HasCentralRadical ℂ (GroupLieAlgebra 𝓘(ℂ,V) G))

/-- Forget joint holomorphic evaluation without changing the Lie atlas
supporting the central-radical conclusion. -/
theorem reductiveLie_of_reductiveTransformation
    (h : FullAutReductiveTransformationConclusion Q D B) :
    FullAutReductiveLieConclusion Q D B := by
  obtain ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,_,hRad⟩ := h
  exact ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,hRad⟩

end
end QuaternionicSymmetry.ManifoldTwistorFullAutReductiveTransformationTarget
