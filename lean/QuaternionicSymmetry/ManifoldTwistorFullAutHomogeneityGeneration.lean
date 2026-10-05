import QuaternionicSymmetry.ManifoldTwistorBWW66ReductiveTransformationSource
import QuaternionicSymmetry.GeneralHolomorphicFullAutomorphismLieSource
import QuaternionicSymmetry.GeneralComplexContactHomogeneousLieBridge
import QuaternionicSymmetry.ManifoldTwistorGeneralContactInstantiation
import QuaternionicSymmetry.ManifoldTwistorFullAutomorphisms
import QuaternionicSymmetry.ManifoldTwistorLineCoreClasses
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry

/-! Contact-automorphism point transitivity is used only to make the
*full* biholomorphism action transitive. The contact line then becomes
globally generated from the general holomorphic homogeneous-family
argument; neither an NT contact-group atlas nor a Hamiltonian theorem is
used. -/

namespace QuaternionicSymmetry.ManifoldTwistorFullAutHomogeneityGeneration

open GeneralComplexContactData
open GeneralComplexContactHomogeneousLieBridge
open GeneralHolomorphicTransitiveOrbitSource
open GeneralHolomorphicFullAutomorphismLieSource
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLineCoreClasses
open ManifoldPositiveQuaternionicKahlerGeometry
open HolomorphicLineCorePullback
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

private abbrev RealModel := (𝓘(ℝ,E)).prod (𝓡 2)

/-- Source-only generation from transitivity of the full holomorphic
automorphism transformation group. No preservation of the contact
distribution by all biholomorphisms is needed. -/
theorem actual_contactLine_generated_of_fullAut_transitive
    (hLee : LeeHolomorphicTransitiveOrbitSubmersion)
    (hKob : KobayashiCompactAutomorphismTransformation)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    {n : ℕ} (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hTrans : ∀ z w : SphereBundleTotal P.tangent,
      ∃ f : TwistorHolomorphicAutomorphisms P.tangent P.connection A,
        f.1 z = w) :
    letI := A.charts
    GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore P.tangent P.connection C.contact.line) := by
  letI := A.charts
  letI := A.complexManifold
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : T2Space (SphereBundleTotal P.tangent) := inferInstance
  letI : CompactSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : PreconnectedSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : Nonempty (SphereBundleTotal P.tangent) := inferInstance
  letI : SecondCountableTopology (SphereBundleTotal P.tangent) := inferInstance
  letI : LocallyCompactSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : T2Space (TwistorHolomorphicAutomorphisms P.tangent P.connection A) :=
    by
      change T2Space
        (GeneralHolomorphicFullAutomorphisms.HolomorphicAutomorphisms
          (ComplexTwistorModel n) (SphereBundleTotal P.tangent))
      infer_instance
  letI : SecondCountableTopology
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := by
    change SecondCountableTopology
      (GeneralHolomorphicFullAutomorphisms.HolomorphicAutomorphisms
        (ComplexTwistorModel n) (SphereBundleTotal P.tangent))
    infer_instance
  obtain ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,hJoint⟩ :=
    hKob (W := ComplexTwistorModel n) (Z := SphereBundleTotal P.tangent)
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℂ V := hSpace
  letI : FiniteDimensional ℂ V := hFinite
  letI : ChartedSpace V
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hChart
  letI : IsManifold 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hManifold
  letI : LieGroup 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hLie
  let G := C.toGeneralContactGeometry
  have hOne : ∀ z : SphereBundleTotal P.tangent,
      (fun p : TwistorHolomorphicAutomorphisms P.tangent P.connection A ×
          SphereBundleTotal P.tangent => p.1.1 p.2) (1,z) = z := by
    intro z
    rfl
  have hMul : ∀ (g h : TwistorHolomorphicAutomorphisms
      P.tangent P.connection A) (z : SphereBundleTotal P.tangent),
      ((g*h).1 : SphereBundleTotal P.tangent → SphereBundleTotal P.tangent) z =
        g.1 (h.1 z) := by
    intro g h z
    rfl
  exact contactLine_generated_of_transitiveLieAction
    (IR := RealModel (E := E)) G hLee
    (fun p : TwistorHolomorphicAutomorphisms P.tangent P.connection A ×
      SphereBundleTotal P.tangent => p.1.1 p.2)
    hJoint hOne hMul hTrans

/-- The prior contact-transitive interface remains available: forgetting
contact preservation gives the full holomorphic transitivity used above. -/
theorem actual_contactLine_generated_of_contactAut_transitive
    (hLee : LeeHolomorphicTransitiveOrbitSubmersion)
    (hKob : KobayashiCompactAutomorphismTransformation)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    {n : ℕ} (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hTrans : ∀ z w : SphereBundleTotal P.tangent,
      ∃ f : ContactAutomorphisms P.tangent P.connection A C.contact.line,
        f.1 z = w) :
    letI := A.charts
    GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore P.tangent P.connection C.contact.line) := by
  have hFullTrans : ∀ z w : SphereBundleTotal P.tangent,
      ∃ f : TwistorHolomorphicAutomorphisms P.tangent P.connection A,
        f.1 z = w := by
    intro z w
    obtain ⟨f,hfw⟩ := hTrans z w
    exact ⟨contactForget P.tangent P.connection A C.contact.line f, hfw⟩
  exact actual_contactLine_generated_of_fullAut_transitive
    hLee hKob P A C hFullTrans

/-- Reuse the transformation atlas already present in the retained BWW contract. -/
theorem actual_contactLine_generated_of_fullAut_transitive_of_reductive
    (hLee : LeeHolomorphicTransitiveOrbitSubmersion)
    (hAutSource : ManifoldTwistorBWW66ReductiveTransformationSource.FullAutReductiveTransformationSource)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    {n : ℕ} (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hTrans : ∀ z w : SphereBundleTotal P.tangent,
      ∃ f : TwistorHolomorphicAutomorphisms P.tangent P.connection A,
        f.1 z = w) :
    letI := A.charts
    GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore P.tangent P.connection C.contact.line) := by
  letI := A.charts
  letI := A.complexManifold
  letI : CompactSpace M := ⟨P.compact⟩
  letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact E M
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : T2Space (SphereBundleTotal P.tangent) := inferInstance
  letI : CompactSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : PreconnectedSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : Nonempty (SphereBundleTotal P.tangent) := inferInstance
  letI : SecondCountableTopology (SphereBundleTotal P.tangent) := inferInstance
  letI : LocallyCompactSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : T2Space (TwistorHolomorphicAutomorphisms P.tangent P.connection A) :=
    by
      change T2Space
        (GeneralHolomorphicFullAutomorphisms.HolomorphicAutomorphisms
          (ComplexTwistorModel n) (SphereBundleTotal P.tangent))
      infer_instance
  letI : SecondCountableTopology
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := by
    change SecondCountableTopology
      (GeneralHolomorphicFullAutomorphisms.HolomorphicAutomorphisms
        (ComplexTwistorModel n) (SphereBundleTotal P.tangent))
    infer_instance
  obtain ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,hJoint,_hRad⟩ :=
    hAutSource P n hn hDim A
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℂ V := hSpace
  letI : FiniteDimensional ℂ V := hFinite
  letI : ChartedSpace V
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hChart
  letI : IsManifold 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hManifold
  letI : LieGroup 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hLie
  let G := C.toGeneralContactGeometry
  have hOne : ∀ z : SphereBundleTotal P.tangent,
      (fun p : TwistorHolomorphicAutomorphisms P.tangent P.connection A ×
          SphereBundleTotal P.tangent => p.1.1 p.2) (1,z) = z := by
    intro z
    rfl
  have hMul : ∀ (g h : TwistorHolomorphicAutomorphisms
      P.tangent P.connection A) (z : SphereBundleTotal P.tangent),
      ((g*h).1 : SphereBundleTotal P.tangent → SphereBundleTotal P.tangent) z =
        g.1 (h.1 z) := by
    intro g h z
    rfl
  exact contactLine_generated_of_transitiveLieAction
    (IR := RealModel (E := E)) G hLee
    (fun p : TwistorHolomorphicAutomorphisms P.tangent P.connection A ×
      SphereBundleTotal P.tangent => p.1.1 p.2)
    hJoint hOne hMul hTrans

/-- The prior contact-transitive interface remains available: forgetting
contact preservation gives the full holomorphic transitivity used above. -/
theorem actual_contactLine_generated_of_contactAut_transitive_of_reductive
    (hLee : LeeHolomorphicTransitiveOrbitSubmersion)
    (hAutSource : ManifoldTwistorBWW66ReductiveTransformationSource.FullAutReductiveTransformationSource)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    {n : ℕ} (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hTrans : ∀ z w : SphereBundleTotal P.tangent,
      ∃ f : ContactAutomorphisms P.tangent P.connection A C.contact.line,
        f.1 z = w) :
    letI := A.charts
    GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore P.tangent P.connection C.contact.line) := by
  have hFullTrans : ∀ z w : SphereBundleTotal P.tangent,
      ∃ f : TwistorHolomorphicAutomorphisms P.tangent P.connection A,
        f.1 z = w := by
    intro z w
    obtain ⟨f,hfw⟩ := hTrans z w
    exact ⟨contactForget P.tangent P.connection A C.contact.line f, hfw⟩
  exact actual_contactLine_generated_of_fullAut_transitive_of_reductive
    hLee hAutSource P A C hn hDim hFullTrans

end
end QuaternionicSymmetry.ManifoldTwistorFullAutHomogeneityGeneration
