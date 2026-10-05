import QuaternionicSymmetry.GeneralHolomorphicTransitiveOrbitSource
import QuaternionicSymmetry.GeneralComplexContactHomogeneousAction

/-! From a genuine jointly holomorphic transitive Lie-group action to the
previously defined homogeneous-family data. The orbit-submersion conclusion
comes only from the explicitly passed, reviewed derived general Lee
corollary; no contact-line generation is put into that source. -/

namespace QuaternionicSymmetry.GeneralComplexContactHomogeneousLieBridge

open GeneralComplexContactData
open GeneralHolomorphicTransitiveOrbitSource
open ManifoldTwistorLeBrunComplexAtlas
open HolomorphicLineCorePullback
open scoped Manifold ContDiff

noncomputable section

variable {R H Z V G : Type}
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [TopologicalSpace H] [TopologicalSpace Z] [T2Space Z]
  [SecondCountableTopology Z] [ChartedSpace H Z]
  (IR : ModelWithCorners ℝ R H) [IsManifold IR ∞ Z]
  {n : ℕ} (C : ContactGeometry (IR := IR) (Z := Z) n)
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [TopologicalSpace G] [T2Space G] [SecondCountableTopology G]
  [ChartedSpace V G] [IsManifold 𝓘(ℂ,V) ∞ G]
  [Group G] [LieGroup 𝓘(ℂ,V) ∞ G]

/-- A transitive holomorphic Lie action supplies every field of the exact
contact homogeneous-family interface, including the true submersive orbit
map, without presupposing global generation. -/
def homogeneousFamily_of_transitive
    (hLee : LeeHolomorphicTransitiveOrbitSubmersion)
    (a : G × Z → Z)
    (hSmooth : letI := C.charts
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞ a)
    (hOne : ∀ z : Z, a (1,z) = z)
    (hMul : ∀ (g h : G) (z : Z), a (g*h,z) = a (g,a (h,z)))
    (hTrans : ∀ z w : Z, ∃ g : G, a (g,z) = w) :
    C.HolomorphicHomogeneousFamily (G := G) 𝓘(ℂ,V) := by
  letI := C.charts
  letI := C.complexManifold
  exact {
    action := a
    identity := 1
    smooth := hSmooth
    identity_action := hOne
    orbit_submersive := hLee a hSmooth hOne hMul hTrans }

/-- The genuine contact line is globally generated as an internal
differential consequence of the constructed homogeneous family. -/
theorem contactLine_generated_of_transitiveLieAction
    (hLee : LeeHolomorphicTransitiveOrbitSubmersion)
    (a : G × Z → Z)
    (hSmooth : letI := C.charts
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞ a)
    (hOne : ∀ z : Z, a (1,z) = z)
    (hMul : ∀ (g h : G) (z : Z), a (g*h,z) = a (g,a (h,z)))
    (hTrans : ∀ z w : Z, ∃ g : G, a (g,z) = w) :
    letI := C.charts
    GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n) C.contactLineCore := by
  exact C.contactLine_globallyGenerated_of_homogeneousFamily 𝓘(ℂ,V)
    (homogeneousFamily_of_transitive IR C hLee a hSmooth hOne hMul hTrans)

end
end QuaternionicSymmetry.GeneralComplexContactHomogeneousLieBridge
