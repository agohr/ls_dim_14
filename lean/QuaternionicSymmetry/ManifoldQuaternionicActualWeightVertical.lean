import QuaternionicSymmetry.ManifoldQuaternionicActualWeightHull

/-! The integral weights used by the actual convex hull are the genuine
vertical derivative weights used by the kernel fixed-component construction.
This checks the scalar/real-imaginary representation dictionary explicitly. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicActualWeightVertical

open ManifoldQuaternionicTorusAction ManifoldQuaternionicActualWeightHull
open ManifoldQuaternionicVerticalCircleCharacter ManifoldQuaternionicVerticalWeightKernel
open ManifoldQuaternionicVerticalComplexCharacter
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
  {r : ℕ} (A : ContinuousTorusAction Q r)

theorem hasVerticalWeight_of_character
    (z : SphereBundleTotal Q) (hz : ∀ t, A.representation t • z = z)
    (μ : Fin r → ℤ)
    (hchar : ∀ t, torusVerticalCircleCharacter Q hR3 A z hz t = weightCharacter μ t) :
    HasVerticalWeight Q A z hz μ := by
  intro t v
  have hs : verticalScalar Q z ⟨A.representation t,hz t⟩ =
      (weightCharacter μ t : ℂ) := by
    simpa only [torusVerticalCircleCharacter, verticalCircleCharacter,
      torusToTwistorIsotropy] using
      congrArg (fun c : Circle => (c : ℂ)) (hchar t)
  rw [isotropyVerticalRepresentation_eq_verticalScalar,hs]
  rfl

theorem actualIntegralWeight_has_vertical_witness {μ : Fin r → ℤ}
    (hμ : μ ∈ actualIntegralWeights Q hR3 A) :
    ∃ (z : SphereBundleTotal Q) (hz : ∀ t, A.representation t • z = z),
      HasVerticalWeight Q A z hz μ := by
  obtain ⟨z,hz,hchar⟩ := hμ
  exact ⟨z,hz,hasVerticalWeight_of_character Q hR3 A z hz μ hchar⟩

theorem actualExtreme_has_nonzero_vertical_witness {w : Fin r → ℝ}
    (hw : w ∈ (convexHull ℝ (actualRealWeights Q hR3 A)).extremePoints ℝ)
    (hne : w ≠ 0) :
    ∃ (μ : Fin r → ℤ) (z : SphereBundleTotal Q)
      (hz : ∀ t, A.representation t • z = z),
      μ ≠ 0 ∧ HasVerticalWeight Q A z hz μ ∧ (fun i => (μ i : ℝ)) = w := by
  obtain ⟨μ,z,hz,hchar,hreal⟩ := actual_extreme_has_fixed_point Q hR3 A hw
  refine ⟨μ,z,hz,?_,hasVerticalWeight_of_character Q hR3 A z hz μ hchar,hreal⟩
  intro hzero
  apply hne
  rw [← hreal,hzero]
  funext i
  simp

end
end QuaternionicSymmetry.ManifoldQuaternionicActualWeightVertical
