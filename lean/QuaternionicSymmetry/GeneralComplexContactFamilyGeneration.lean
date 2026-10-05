import QuaternionicSymmetry.HolomorphicFamilyVectorFields

/-! An actual holomorphic family with surjective orbit differential
generates the contact line. The application to a homogeneous Wolf twistor
still requires its actual holomorphic action and orbit-submersion proof. -/
namespace QuaternionicSymmetry.GeneralComplexContactData
open ManifoldTwistorLeBrunComplexAtlas
open HolomorphicLineCorePullback HolomorphicFamilyVectorFields
open scoped Manifold ContDiff
noncomputable section

variable {R H Z : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
  {IR : ModelWithCorners ℝ R H} [IsManifold IR ∞ Z]
variable {n : ℕ} (C : ContactGeometry (IR := IR) (Z := Z) n)
variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace HG] [TopologicalSpace G] [ChartedSpace HG G]
  (IG : ModelWithCorners ℂ V HG) [IsManifold IG ∞ G]

theorem ContactGeometry.contactLine_globallyGenerated_of_family
    (a : G × Z → Z) (g₀ : G)
    (ha : letI := C.charts
      ContMDiff (IG.prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞ a)
    (hId : ∀ z : Z, a (g₀,z) = z)
    (hOrbit : letI := C.charts
      ∀ z : Z, Function.Surjective
        (mfderiv IG 𝓘(ℂ,ComplexTwistorModel n) (fun g => a (g,z)) g₀)) :
    letI := C.charts
    GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n) C.contactLineCore := by
  letI := C.charts
  letI := C.complexManifold
  apply C.contactLine_globallyGenerated
  intro z w
  exact tangent_sections_evaluation_surjective
    IG 𝓘(ℂ,ComplexTwistorModel n) a g₀ ha hId hOrbit z w

end
end QuaternionicSymmetry.GeneralComplexContactData
