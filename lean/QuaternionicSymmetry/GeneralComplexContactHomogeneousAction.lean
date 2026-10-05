import QuaternionicSymmetry.GeneralComplexContactFamilyGeneration

/-! An explicit action-level interface for a homogeneous complex-contact
manifold. This is not a classification axiom or a predicate equivalent to
global generation: it retains the actual jointly holomorphic family and the
submersive differential of every orbit. A source theorem asserting
homogeneity must still construct this data from its precise hypotheses.
The contact-line generation is then proved by differentiating the action. -/

namespace QuaternionicSymmetry.GeneralComplexContactData

open ManifoldTwistorLeBrunComplexAtlas
open HolomorphicLineCorePullback
open scoped Manifold ContDiff

noncomputable section

variable {R H Z : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
  {IR : ModelWithCorners ℝ R H} [IsManifold IR ∞ Z]
variable {n : ℕ} (C : ContactGeometry (IR := IR) (Z := Z) n)
variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace HG] [TopologicalSpace G] [ChartedSpace HG G]
  (IG : ModelWithCorners ℂ V HG) [IsManifold IG ∞ G]

/-- The concrete differential data produced by an actual transitive
holomorphic Lie-group action together with the standard orbit-submersion
theorem. The group law is not needed in the subsequent differentiation
argument; an action can be supplied without changing this interface. -/
structure ContactGeometry.HolomorphicHomogeneousFamily where
  action : G × Z → Z
  identity : G
  smooth : letI := C.charts
    ContMDiff (IG.prod 𝓘(ℂ,ComplexTwistorModel n))
      𝓘(ℂ,ComplexTwistorModel n) ∞ action
  identity_action : ∀ z : Z, action (identity,z) = z
  orbit_submersive : letI := C.charts
    ∀ z : Z, Function.Surjective
      (mfderiv IG 𝓘(ℂ,ComplexTwistorModel n)
        (fun g => action (g,z)) identity)

/-- The actual holomorphic family yields global generation of the *same*
contact line core carried by `C`; no ambient-line generation is assumed. -/
theorem ContactGeometry.contactLine_globallyGenerated_of_homogeneousFamily
    (A : C.HolomorphicHomogeneousFamily (G := G) IG) :
    letI := C.charts
    GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n) C.contactLineCore := by
  exact C.contactLine_globallyGenerated_of_family IG A.action A.identity
    A.smooth A.identity_action A.orbit_submersive

end
end QuaternionicSymmetry.GeneralComplexContactData
