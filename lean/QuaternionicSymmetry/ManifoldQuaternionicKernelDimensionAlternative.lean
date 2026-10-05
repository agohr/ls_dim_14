import QuaternionicSymmetry.ManifoldQuaternionicKernelQTriviality
import QuaternionicSymmetry.ManifoldQuaternionicZeroFixedComponent
import QuaternionicSymmetry.ManifoldQuaternionicVolume
import QuaternionicSymmetry.ManifoldQuaternionicKernelFourGeometry

/-! After a nontrivial connected twistor fixed set rules out dimension zero,
the actual lower-dimensional fixed component is either four-dimensional or
inherits a compact positive quaternionic-Kähler geometry. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicKernelDimensionAlternative
open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
open ManifoldQuaternionicKernelQTriviality
open ManifoldQuaternionicZeroFixedComponent
open ManifoldQuaternionicVolume
open ManifoldQuaternionicVerticalWeightKernel
open ManifoldRiemannianFixedComponentInput
open ManifoldRiemannianIsometryLieInput
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicFourSubmanifoldInput
open ManifoldQuaternionicKernelFourGeometry
open ManifoldPositiveTwistorCompatibleFourGeometry
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

/-- A genuine nonzero vertical weight and nontrivial connected fixed twistor
set give a strict lower-dimensional actual fixed atlas. The only exceptional
case not governed by T4 is quaternionic dimension one. -/
theorem exists_four_dimensional_or_induced_positive_component
    {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [CompactSpace M] [T3Space M] [SecondCountableTopology M]
    [PreconnectedSpace M] [Nonempty M]
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hR3 : IsometryLieSource.{0,0})
    (hT4 : PositiveQuaternionicSubmanifoldSource)
    (hjet : ManifoldRiemannianOneJetInput.RiemannianOneJetRigidityOnModel
      (E := E) (M := M))
    (hfixedSource : RiemannianFixedComponentOnModel (E := E) (M := M))
    {r : ℕ} (A : ContinuousTorusAction P.tangent r)
    (hA : A.Faithful) (hr : 2 ≤ r)
    (z : SphereBundleTotal P.tangent)
    (hz : ∀ t, A.representation t • z = z)
    (μ : Fin r → ℤ) (hμ : μ ≠ 0)
    (hweight : HasVerticalWeight P.tangent A z hz μ)
    (Y : Set (SphereBundleTotal P.tangent))
    (hY : IsPreconnected Y) (hzY : z ∈ Y) (hYnontrivial : Y.Nontrivial)
    (hfixed : ∀ w ∈ Y, ∀ t, A.representation t • w = w) :
    ∃ m : ℕ, 0 < m ∧ m < n ∧
      ∃ C : FixedComponentAtlas P.tangent
        (ContinuousTorusAction.connectedKernelImage P.tangent A μ) z.1 (4*m),
        m = 1 ∨
          ∃ hm : 2 ≤ m,
            letI : NeZero (4*m) := ⟨by omega⟩
            letI := C.charts
            letI := C.manifold
            ∃ R : CompactConnectedPositiveQuaternionicKahlerGeometry
                (E := EuclideanSpace ℝ (Fin (4*m)))
                (M := FixedComponent P.tangent
                  (ContinuousTorusAction.connectedKernelImage P.tangent A μ) z.1),
              IsInducedQuaternionicGeometry P
                R.toPositiveQuaternionicKahlerGeometry Subtype.val := by
  let R₀ := P.tangent.reduction.Q (achart E z.1)
  have hRdim : R₀.quaternionicDimension = n := by
    change (P.tangent.reduction.Q (achart E z.1)).quaternionicDimension = n
    rw [frame_dimension P.tangent, hDim]
    omega
  obtain ⟨m, hmpos, hmlt, ⟨C⟩⟩ :=
    exists_positive_smaller_fixedComponent P.tangent A z hz
      hjet hfixedSource hA hr μ hμ hweight Y hY hzY hYnontrivial
      hfixed R₀
  by_cases h1 : m = 1
  · exact ⟨m, hmpos, by omega, C, Or.inl h1⟩
  · have hm : 2 ≤ m := by omega
    obtain ⟨C', R, hR⟩ := verticalWeight_exists_induced_compact_positive_geometry P n m
      hn hm hDim hR3 hT4 A z hz μ hweight C
    exact ⟨m, hmpos, by omega, C', Or.inr ⟨hm, R, hR⟩⟩

/-- Full geometry-valued form of the fixed-component alternative: the
four-dimensional branch has its separate orientation-compatible Einstein
geometry, while every higher-dimensional branch is compact positive
quaternionic Kähler. No zero-dimensional branch remains. -/
theorem exists_lower_induced_component_four_or_higher
    {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [CompactSpace M] [T3Space M] [SecondCountableTopology M]
    [PreconnectedSpace M] [Nonempty M]
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hR3 : IsometryLieSource.{0,0})
    (hT4 : PositiveQuaternionicSubmanifoldSource)
    (hT4four : PositiveFourQuaternionicSubmanifoldSource)
    (hjet : ManifoldRiemannianOneJetInput.RiemannianOneJetRigidityOnModel
      (E := E) (M := M))
    (hfixedSource : RiemannianFixedComponentOnModel (E := E) (M := M))
    {r : ℕ} (A : ContinuousTorusAction P.tangent r)
    (hA : A.Faithful) (hr : 2 ≤ r)
    (z : SphereBundleTotal P.tangent)
    (hz : ∀ t, A.representation t • z = z)
    (μ : Fin r → ℤ) (hμ : μ ≠ 0)
    (hweight : HasVerticalWeight P.tangent A z hz μ)
    (Y : Set (SphereBundleTotal P.tangent))
    (hY : IsPreconnected Y) (hzY : z ∈ Y) (hYnontrivial : Y.Nontrivial)
    (hfixed : ∀ w ∈ Y, ∀ t, A.representation t • w = w) :
    ∃ m : ℕ, 0 < m ∧ m < n ∧
      ∃ C : FixedComponentAtlas P.tangent
        (ContinuousTorusAction.connectedKernelImage P.tangent A μ) z.1 (4*m),
        (∃ h1 : m = 1,
          letI : NeZero (4*m) := ⟨by omega⟩
          letI := C.charts
          letI := C.manifold
          ∃ R : CompactConnectedPositiveTwistorCompatibleFourGeometry
              (E := EuclideanSpace ℝ (Fin (4*m)))
              (M := FixedComponent P.tangent
                (ContinuousTorusAction.connectedKernelImage P.tangent A μ) z.1),
            IsInducedQuaternionicGeometry P
              R.toPositiveTwistorCompatibleFourGeometry.toPositiveQuaternionicKahlerGeometry
              Subtype.val) ∨
          (∃ hm : 2 ≤ m,
            letI : NeZero (4*m) := ⟨by omega⟩
            letI := C.charts
            letI := C.manifold
            ∃ R : CompactConnectedPositiveQuaternionicKahlerGeometry
                (E := EuclideanSpace ℝ (Fin (4*m)))
                (M := FixedComponent P.tangent
                  (ContinuousTorusAction.connectedKernelImage P.tangent A μ) z.1),
              IsInducedQuaternionicGeometry P
                R.toPositiveQuaternionicKahlerGeometry Subtype.val) := by
  obtain ⟨m, hmpos, hmlt, C, hcase⟩ :=
    exists_four_dimensional_or_induced_positive_component P n hn hDim
      hR3 hT4 hjet hfixedSource A hA hr z hz μ hμ hweight
      Y hY hzY hYnontrivial hfixed
  rcases hcase with h1 | hhigh
  · subst m
    obtain ⟨C', R, hR⟩ := verticalWeight_exists_induced_compact_four_geometry P n hn hDim
      hR3 hT4four A z hz μ hweight C
    exact ⟨1, hmpos, hmlt, C', Or.inl ⟨rfl, R, hR⟩⟩
  · exact ⟨m, hmpos, hmlt, C, Or.inr hhigh⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicKernelDimensionAlternative
