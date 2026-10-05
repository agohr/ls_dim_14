import QuaternionicSymmetry.GeneralUniqueContactHamiltonianSource
import QuaternionicSymmetry.ManifoldTwistorContactFullLieDerivative
import QuaternionicSymmetry.ManifoldTwistorGeneralContractionMatch
import QuaternionicSymmetry.ManifoldTwistorNittaTakeuchiHamiltonianSource
import QuaternionicSymmetry.ManifoldTwistorBKKPicardUniquenessApplication
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff

/-! Source-faithful Picard-unique Hamiltonian route on the genuine twistor.
The universal NT-U input asserts only bijectivity of the canonical full-Aut
derivative-and-contraction map. All atlas choice, contact/full derivative
transport, field construction, and actual quotient-form matching are
internal. The old project-specific universal NT source is not used. -/

namespace QuaternionicSymmetry.ManifoldTwistorUniqueContactHamiltonianFromSources

open GeneralUniqueContactHamiltonianSource
open GeneralHolomorphicFullAutomorphismLieSource
open GeneralComplexContactData
open ManifoldTwistorNittaTakeuchiHamiltonianSource
open ManifoldTwistorBKKPicardUniquenessApplication
open ManifoldTwistorBKKPicardHomogeneityApplication
open ManifoldTwistorContactFullLieDerivative
open ManifoldTwistorGeneralContractionMatch
open ManifoldTwistorContactInfinitesimalAction
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorContactContraction
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses
open ManifoldPositiveQuaternionicKahlerGeometry
open HolomorphicVectorFieldPushforward
open HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineSheafClasses HolomorphicLineSheafClassGroup
open scoped Manifold ContDiff
noncomputable section
set_option maxHeartbeats 200000

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

private abbrev RealModel := (𝓘(ℝ,E)).prod (𝓡 2)

/-- The actual Hamiltonian map is bijective in the SAME supplied full-Aut
atlas transported to the contact group. This stronger endpoint retains
the chosen chart, unlike an existential group-atlas conclusion. -/
theorem contactHamiltonian_bijective_of_fullPreserves_atlas
    (hNTU : UniqueContactHamiltonianBijection)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 1 ≤ n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hPreserve : FullPreservesContact P.tangent P.connection A C.contact.line)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V]
    [hChart : ChartedSpace V
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hManifold : IsManifold 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hLie : LieGroup 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    (hJoint :
      letI := A.charts
      letI := A.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : TwistorHolomorphicAutomorphisms P.tangent P.connection A ×
          SphereBundleTotal P.tangent => p.1.1 p.2)) :
    letI := A.charts
    letI := A.complexManifold
    letI := contactCharts (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactManifold (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    letI := contactLieGroup (V := V)
      P.tangent P.connection A C.contact.line hPreserve
    Function.Bijective
      ((contraction P.tangent P.connection A C.contact).comp
        (contactInfinitesimalActionLinear (V := V)
          P.tangent P.connection A C.contact.line
          (contact_joint_holomorphic_of_full (V := V)
            P.tangent P.connection A C.contact.line hPreserve hJoint))) := by
  letI := A.charts
  letI := A.complexManifold
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : ConnectedSpace M := {
    toPreconnectedSpace := inferInstance
    toNonempty := inferInstance }
  letI : T2Space (SphereBundleTotal P.tangent) := inferInstance
  letI : CompactSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : PreconnectedSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : Nonempty (SphereBundleTotal P.tangent) := inferInstance
  letI : ConnectedSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : SecondCountableTopology (SphereBundleTotal P.tangent) := inferInstance
  let G := C.toGeneralContactGeometry
  have hKernel := actual_contact_kernel P.tangent P.connection A C
  letI : ChartedSpace V
      (letI := G.charts
       letI := G.complexManifold
       GeneralHolomorphicFullAutomorphisms.HolomorphicAutomorphisms
         (ComplexTwistorModel n) (SphereBundleTotal P.tangent)) := by
    change ChartedSpace V
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)
    exact hChart
  letI : IsManifold 𝓘(ℂ,V) ∞
      (letI := G.charts
       letI := G.complexManifold
       GeneralHolomorphicFullAutomorphisms.HolomorphicAutomorphisms
         (ComplexTwistorModel n) (SphereBundleTotal P.tangent)) := by
    change IsManifold 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)
    exact hManifold
  have hFullBij := hNTU (RealModel (E := E)) n hn G
    (contactDistribution P.tangent P.connection A C.contact.line)
    hKernel hPreserve hChart hManifold hLie hJoint
  let hContactChart := contactCharts (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI : ChartedSpace V
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) :=
    hContactChart
  let hContactManifold := contactManifold (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI : IsManifold 𝓘(ℂ,V) ∞
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) :=
    hContactManifold
  let hContactLie := contactLieGroup (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI : LieGroup 𝓘(ℂ,V) ∞
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) :=
    hContactLie
  let hContactJoint := contact_joint_holomorphic_of_full (V := V)
    P.tangent P.connection A C.contact.line hPreserve hJoint
  let field := contactInfinitesimalActionLinear (V := V)
    P.tangent P.connection A C.contact.line hContactJoint
  let df := mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V)
    (contactFullHomeomorph P.tangent P.connection A C.contact.line hPreserve)
    (1 : ContactAutomorphisms P.tangent P.connection A C.contact.line)
  have hdf : Function.Bijective df :=
    contactFull_mfderiv_bijective (V := V)
      P.tangent P.connection A C.contact.line hPreserve
  have hField (v : GroupLieAlgebra 𝓘(ℂ,V)
      (ContactAutomorphisms P.tangent P.connection A C.contact.line)) :
      field v = fullInfinitesimalActionLinear (V := V) G hJoint (df v) := by
    apply ContMDiffSection.ext
    intro z
    exact contact_orbit_derivative_eq_full (V := V)
      P.tangent P.connection A C.contact.line hPreserve hJoint v z
  have hComposite :
      (fun v : GroupLieAlgebra 𝓘(ℂ,V)
        (ContactAutomorphisms P.tangent P.connection A C.contact.line) =>
        contraction P.tangent P.connection A C.contact (field v)) =
      (fun w : GroupLieAlgebra 𝓘(ℂ,V)
        (TwistorHolomorphicAutomorphisms P.tangent P.connection A) =>
        G.sectionOfTangent (fullInfinitesimalActionLinear (V := V) G hJoint w)) ∘
          df := by
    funext v
    rw [hField]
    exact (general_sectionOfTangent_eq_contraction
      P.tangent P.connection A C
      (fullInfinitesimalActionLinear (V := V) G hJoint (df v))).symm
  have hBij : Function.Bijective
      ((contraction P.tangent P.connection A C.contact).comp field) := by
    change Function.Bijective
      (fun v => contraction P.tangent P.connection A C.contact (field v))
    rw [hComposite]
    exact hFullBij.comp hdf
  exact hBij

/-- Existential contact-group packaging, derived from the stronger
same-atlas bijection above. -/
theorem contactHamiltonian_of_fullPreserves_atlas
    (hNTU : UniqueContactHamiltonianBijection)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 1 ≤ n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hPreserve : FullPreservesContact P.tangent P.connection A C.contact.line)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V]
    [hChart : ChartedSpace V
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hManifold : IsManifold 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hLie : LieGroup 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    (hJoint :
      letI := A.charts
      letI := A.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : TwistorHolomorphicAutomorphisms P.tangent P.connection A ×
          SphereBundleTotal P.tangent => p.1.1 p.2)) :
    ContactHamiltonianConclusion P.tangent P.connection A C.contact := by
  letI := A.charts
  letI := A.complexManifold
  let hContactChart := contactCharts (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI : ChartedSpace V
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) :=
    hContactChart
  let hContactManifold := contactManifold (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI : IsManifold 𝓘(ℂ,V) ∞
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) :=
    hContactManifold
  let hContactLie := contactLieGroup (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI : LieGroup 𝓘(ℂ,V) ∞
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) :=
    hContactLie
  let hContactJoint := contact_joint_holomorphic_of_full (V := V)
    P.tangent P.connection A C.contact.line hPreserve hJoint
  let field := contactInfinitesimalActionLinear (V := V)
    P.tangent P.connection A C.contact.line hContactJoint
  have hBij : Function.Bijective
      ((contraction P.tangent P.connection A C.contact).comp field) :=
    contactHamiltonian_bijective_of_fullPreserves_atlas (V := V)
      hNTU P n hn A C hPreserve hJoint
  refine ⟨V,inferInstance,inferInstance,inferInstance,hContactChart,hContactManifold,
    hContactLie,hContactJoint,field,?_,hBij⟩
  intro v z
  exact contactInfinitesimalActionLinear_apply (V := V)
    P.tangent P.connection A C.contact.line hContactJoint v z

/-- Convenience specialization choosing the canonical compact-complex
transformation atlas; the supplied-atlas theorem above remains available
for a full-Aut atlas that also carries other structural data. -/
theorem contactHamiltonian_of_fullPreserves
    (hKob : KobayashiCompactAutomorphismTransformation)
    (hNTU : UniqueContactHamiltonianBijection)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 1 ≤ n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hPreserve : FullPreservesContact P.tangent P.connection A C.contact.line) :
    ContactHamiltonianConclusion P.tangent P.connection A C.contact := by
  letI := A.charts
  letI := A.complexManifold
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : T2Space (SphereBundleTotal P.tangent) := inferInstance
  letI : CompactSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : PreconnectedSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : Nonempty (SphereBundleTotal P.tangent) := inferInstance
  letI : SecondCountableTopology (SphereBundleTotal P.tangent) := inferInstance
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
  exact contactHamiltonian_of_fullPreserves_atlas (V := V)
    hNTU P n hn A C hPreserve hJoint

/-- Actual BKK Picard uniqueness provides the sole additional premise
needed to enter the full-preservation branch above. -/
theorem contactHamiltonian_of_analyticPicard_generator
    (hUnique : GeneralContactFanoPicardUniquenessSource.AnalyticContactPicardGeneratorPreservesDistribution)
    (hKob : KobayashiCompactAutomorphismTransformation)
    (hNTU : UniqueContactHamiltonianBijection)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 1 ≤ n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hAmple :
      letI := A.charts
      letI := A.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line))
    (hPic :
      letI := A.charts
      letI := A.complexManifold
      Function.Bijective (fun r : ℤ =>
        (classMulEquiv 𝓘(ℂ,ComplexTwistorModel n)
          (contactClass P.tangent P.connection C.contact.line) :
          SheafClass (B := SphereBundleTotal P.tangent)
            𝓘(ℂ,ComplexTwistorModel n)) ^ r)) :
    ContactHamiltonianConclusion P.tangent P.connection A C.contact := by
  exact contactHamiltonian_of_fullPreserves hKob hNTU P n hn A C
    (fullPreservesContact_of_analyticPicard_generator
      hUnique P n hn A C hAmple hPic)

end
end QuaternionicSymmetry.ManifoldTwistorUniqueContactHamiltonianFromSources
