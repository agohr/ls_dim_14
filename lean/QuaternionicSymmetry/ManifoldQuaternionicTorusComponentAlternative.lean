import QuaternionicSymmetry.ManifoldQuaternionicKernelDimensionAlternative
import QuaternionicSymmetry.ManifoldQuaternionicTorusFixedComplexComponent
import QuaternionicSymmetry.ManifoldQuaternionicActualWeightVertical

/-! For a genuine nonzero weight, the literal full-torus fixed component
is a point or has a strictly lower-dimensional kernel component carrying
actual induced positive geometry. No arbitrary auxiliary fixed set is an
input, and the four-dimensional branch retains its separate geometry. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicTorusComponentAlternative

open ManifoldQuaternionicTorusAction ManifoldQuaternionicVerticalWeightKernel
open ManifoldQuaternionicKernelDimensionAlternative
open ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldQuaternionicTwistorLiftedFixedSet
open ManifoldRiemannianFixedComponentInput ManifoldRiemannianIsometryLieInput
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput ManifoldQuaternionicFourSubmanifoldInput
open ManifoldPositiveTwistorCompatibleFourGeometry ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]

theorem component_subsingleton_or_lower_induced_geometry
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
    (hweight : HasVerticalWeight P.tangent A z hz μ) :
    (component P.tangent A z).Subsingleton ∨
      ∃ m : ℕ, 0 < m ∧ m < n ∧
        ∃ C : FixedComponentAtlas P.tangent
          (A.connectedKernelImage P.tangent μ) z.1 (4*m),
          (∃ h1 : m = 1,
            letI : NeZero (4*m) := ⟨by omega⟩
            letI := C.charts
            letI := C.manifold
            ∃ R : CompactConnectedPositiveTwistorCompatibleFourGeometry
                (E := EuclideanSpace ℝ (Fin (4*m)))
                (M := FixedComponent P.tangent (A.connectedKernelImage P.tangent μ) z.1),
              IsInducedQuaternionicGeometry P
                R.toPositiveTwistorCompatibleFourGeometry.toPositiveQuaternionicKahlerGeometry
                Subtype.val) ∨
            (∃ hm : 2 ≤ m,
              letI : NeZero (4*m) := ⟨by omega⟩
              letI := C.charts
              letI := C.manifold
              ∃ R : CompactConnectedPositiveQuaternionicKahlerGeometry
                  (E := EuclideanSpace ℝ (Fin (4*m)))
                  (M := FixedComponent P.tangent (A.connectedKernelImage P.tangent μ) z.1),
                IsInducedQuaternionicGeometry P
                  R.toPositiveQuaternionicKahlerGeometry Subtype.val) := by
  by_cases hsingle : (component P.tangent A z).Subsingleton
  · exact Or.inl hsingle
  right
  have hzset : z ∈ fixedSpherePoints P.tangent A.imageSubgroup :=
    (mem_fixedSpherePoints_iff_torus P.tangent A z).mpr hz
  have hY : IsPreconnected (component P.tangent A z) :=
    isPreconnected_connectedComponentIn
  have hzY : z ∈ component P.tangent A z := mem_connectedComponentIn hzset
  have hfixed : ∀ w ∈ component P.tangent A z, ∀ t,
      A.representation t • w = w := by
    intro w hw
    exact (mem_fixedSpherePoints_iff_torus P.tangent A w).mp
      (connectedComponentIn_subset _ _ hw)
  exact exists_lower_induced_component_four_or_higher P n hn hDim
    hR3 hT4 hT4four hjet hfixedSource A hA hr z hz μ hμ hweight
    (component P.tangent A z) hY hzY (Set.not_subsingleton_iff.mp hsingle) hfixed

end
end QuaternionicSymmetry.ManifoldQuaternionicTorusComponentAlternative
