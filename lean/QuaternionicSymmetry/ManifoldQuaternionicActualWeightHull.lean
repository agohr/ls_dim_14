import QuaternionicSymmetry.ManifoldQuaternionicTwistorAntipodalCharacter
import QuaternionicSymmetry.SymmetricWeightHull

/-! The weights here are obtained from actual torus-fixed twistor points and
the constructed vertical character. Antipodal symmetry is geometric; full
affine span remains an explicit premise for the convex-hull conclusion. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicActualWeightHull

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicVerticalCircleCharacter
open ManifoldQuaternionicTwistorAntipodalWeight
open ManifoldQuaternionicTwistorAntipodalCharacter
open ManifoldTwistorSphereCore
open SymmetricWeightHull
open Set
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
variable {r : ℕ} (A : ContinuousTorusAction Q r)

/-- Integral weights realized by the genuine vertical character at some
twistor point fixed by the entire actual torus action. -/
def actualIntegralWeights : Set (Fin r → ℤ) :=
  {μ | ∃ (z : SphereBundleTotal Q)
      (hz : ∀ t, A.representation t • z = z),
      ∀ t, torusVerticalCircleCharacter Q hR3 A z hz t = weightCharacter μ t}

/-- The antipode of an actual fixed point realizes the negative weight. -/
theorem actualIntegralWeights_neg {μ : Fin r → ℤ}
    (hμ : μ ∈ actualIntegralWeights Q hR3 A) :
    -μ ∈ actualIntegralWeights Q hR3 A := by
  obtain ⟨z, hz, hweight⟩ := hμ
  let hza : ∀ t, A.representation t • sphereAntipodal Q z =
      sphereAntipodal Q z :=
    fun t => antipodal_fixed Q z (A.representation t) (hz t)
  refine ⟨sphereAntipodal Q z, hza, ?_⟩
  intro t
  exact torusVerticalCircleCharacter_negative_weight Q hR3 A z hz μ hweight t

/-- Real-coordinate image of the actual integral fixed-point weights. -/
def actualRealWeights : Set (Fin r → ℝ) :=
  (fun μ : Fin r → ℤ => fun i => (μ i : ℝ)) ''
    actualIntegralWeights Q hR3 A

theorem actualRealWeights_neg {w : Fin r → ℝ}
    (hw : w ∈ actualRealWeights Q hR3 A) :
    -w ∈ actualRealWeights Q hR3 A := by
  obtain ⟨μ, hμ, rfl⟩ := hw
  refine ⟨-μ, actualIntegralWeights_neg Q hR3 A hμ, ?_⟩
  funext i
  simp

/-- Under an explicit full-affine-span premise, every extreme point of the
convex hull of actual real weights is nonzero. -/
theorem actual_extreme_ne_zero (hr : 0 < r)
    (hspan : affineSpan ℝ (actualRealWeights Q hR3 A) = ⊤)
    {w : Fin r → ℝ}
    (hw : w ∈ (convexHull ℝ (actualRealWeights Q hR3 A)).extremePoints ℝ) :
    w ≠ 0 := by
  letI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  exact extreme_ne_zero_of_full_affine_span
    (fun w hw => actualRealWeights_neg Q hR3 A hw) hspan hw

/-- An extreme point is represented by a genuine integral character at an
actual torus-fixed twistor point. -/
theorem actual_extreme_is_integral_weight
    {w : Fin r → ℝ}
    (hw : w ∈ (convexHull ℝ (actualRealWeights Q hR3 A)).extremePoints ℝ) :
    ∃ μ ∈ actualIntegralWeights Q hR3 A,
      (fun i => (μ i : ℝ)) = w := by
  have hmem : w ∈ actualRealWeights Q hR3 A :=
    extremePoints_convexHull_subset hw
  exact hmem

/-- Unpack an extreme weight all the way to its actual fixed twistor point
and the character equality there. -/
theorem actual_extreme_has_fixed_point
    {w : Fin r → ℝ}
    (hw : w ∈ (convexHull ℝ (actualRealWeights Q hR3 A)).extremePoints ℝ) :
    ∃ (μ : Fin r → ℤ) (z : SphereBundleTotal Q)
      (hz : ∀ t, A.representation t • z = z),
      (∀ t, torusVerticalCircleCharacter Q hR3 A z hz t = weightCharacter μ t) ∧
        (fun i => (μ i : ℝ)) = w := by
  obtain ⟨μ, hμ, hreal⟩ := actual_extreme_is_integral_weight Q hR3 A hw
  obtain ⟨z, hz, hchar⟩ := hμ
  exact ⟨μ, z, hz, hchar, hreal⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicActualWeightHull
