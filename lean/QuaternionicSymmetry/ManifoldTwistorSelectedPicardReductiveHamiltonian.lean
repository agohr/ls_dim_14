import QuaternionicSymmetry.ManifoldTwistorContactFullSelectedRadical
import QuaternionicSymmetry.ManifoldTwistorUniqueContactHamiltonianEquivarianceFromSources
import QuaternionicSymmetry.ManifoldTwistorBKKPicardUniquenessApplication
import QuaternionicSymmetry.ManifoldTwistorBWW66ReductiveTransformationSource

/-! On the analytic Picard-generator branch, the same actual full-automorphism
Lie atlas supplied by T3-R carries the contact central radical and the NT-U
canonical Hamiltonian conjugation law. The contact atlas is literally the
transport of that selected full atlas; no second contact atlas is selected. -/

namespace QuaternionicSymmetry.ManifoldTwistorSelectedPicardReductiveHamiltonian

open ManifoldTwistorContactFullSelectedRadical
open ManifoldTwistorUniqueContactHamiltonianEquivarianceFromSources
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorBKKPicardUniquenessApplication
open ManifoldTwistorBWW66ReductiveTransformationSource
open ManifoldTwistorFullAutReductiveTransformationTarget
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses
open ManifoldPositiveQuaternionicKahlerGeometry
open GeneralContactFanoPicardUniquenessSource
open GeneralUniqueContactHamiltonianSource
open HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineSheafClasses HolomorphicLineSheafClassGroup
open scoped Manifold ContDiff
noncomputable section

variable {E M V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- The exact NT-U conjugation equation in the contact Lie atlas transported
from a *specified* full automorphism Lie atlas. -/
def SelectedHamiltonianConjugationLaw
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hPreserve : FullPreservesContact P.tangent P.connection A C.contact.line)
    [hChart : ChartedSpace V
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hManifold : IsManifold 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    [hLie : LieGroup 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A)]
    (hNTU : UniqueContactHamiltonianBijection) (hn : 1 ≤ n)
    (hJoint :
      letI := A.charts
      letI := A.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : TwistorHolomorphicAutomorphisms P.tangent P.connection A ×
          SphereBundleTotal P.tangent => p.1.1 p.2)) : Prop :=
  letI := A.charts
  letI := A.complexManifold
  letI := ManifoldTwistorUniqueContactFullLieTransfer.contactCharts (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := ManifoldTwistorUniqueContactFullLieTransfer.contactManifold (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI := ManifoldTwistorUniqueContactFullLieTransfer.contactLieGroup (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  ∀ (f : ContactAutomorphisms P.tangent P.connection A C.contact.line)
    (v : V),
    canonicalHamiltonianEquiv_of_fullPreserves_atlas (V := V)
      hNTU P n hn A C hPreserve hJoint
      ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V)
        (fun g : ContactAutomorphisms P.tangent P.connection A C.contact.line =>
          f * g * f⁻¹) 1) v) =
      ManifoldTwistorContactAutomorphismSections.contactSectionEquiv
        P.tangent P.connection A C.contact f
        (canonicalHamiltonianEquiv_of_fullPreserves_atlas (V := V)
          hNTU P n hn A C hPreserve hJoint v)

/-- Fixed-atlas version: T2-U selects literal contact preservation; T3-R's
central radical is transferred to that atlas; NT-U is equivariant there. -/
theorem selected_picard_radical_hamiltonian_of_full_atlas
    (hUnique : AnalyticContactPicardGeneratorPreservesDistribution)
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
            𝓘(ℂ,ComplexTwistorModel n)) ^ r))
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
          SphereBundleTotal P.tangent => p.1.1 p.2))
    (hRad :
      letI : CompleteSpace V := FiniteDimensional.complete ℂ V
      letI : ENat.LEInfty (minSmoothness ℂ 3) := by
        simpa only [minSmoothness_of_isRCLikeNormedField] using
          (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
      letI : LieGroup 𝓘(ℂ,V) (minSmoothness ℂ 3)
          (TwistorHolomorphicAutomorphisms P.tangent P.connection A) :=
        LieGroup.of_le (ENat.LEInfty.out)
      LieAlgebra.HasCentralRadical ℂ
        (GroupLieAlgebra 𝓘(ℂ,V)
          (TwistorHolomorphicAutomorphisms P.tangent P.connection A))) :
    ∃ hPreserve : FullPreservesContact
        P.tangent P.connection A C.contact.line,
      (letI : CompleteSpace V := FiniteDimensional.complete ℂ V
       letI := ManifoldTwistorUniqueContactFullLieTransfer.contactCharts (V := V)
         P.tangent P.connection A C.contact.line hPreserve
       letI := ManifoldTwistorUniqueContactFullLieTransfer.contactLieGroup (V := V)
         P.tangent P.connection A C.contact.line hPreserve
       letI : ENat.LEInfty (minSmoothness ℂ 3) := by
         simpa only [minSmoothness_of_isRCLikeNormedField] using
           (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
       letI : LieGroup 𝓘(ℂ,V) (minSmoothness ℂ 3)
           (ContactAutomorphisms P.tangent P.connection A C.contact.line) :=
         LieGroup.of_le (ENat.LEInfty.out)
       LieAlgebra.HasCentralRadical ℂ
         (GroupLieAlgebra 𝓘(ℂ,V)
           (ContactAutomorphisms P.tangent P.connection A C.contact.line))) ∧
      SelectedHamiltonianConjugationLaw (V := V)
        P n A C hPreserve hNTU hn hJoint := by
  letI : CompleteSpace V := FiniteDimensional.complete ℂ V
  let hPreserve := fullPreservesContact_of_analyticPicard_generator
    hUnique P n hn A C hAmple hPic
  refine ⟨hPreserve, ?_, ?_⟩
  · exact contact_hasCentralRadical_of_full_atlas (V := V)
      P.tangent P.connection A C.contact.line hPreserve hRad
  · intro f v
    exact canonicalHamiltonianEquiv_of_fullPreserves_conjugation
      (V := V) hNTU P n hn A C hPreserve hJoint f v

/-- The sourced actual Picard branch selects *one* full-automorphism Lie
atlas; the contact radical and Hamiltonian conjugation law are constructed in
its literally transported contact atlas. The full joint action is retained in
the same witness for subsequent weight/root arguments. -/
theorem exists_selected_picard_reductive_hamiltonian
    (hBWW : FullAutReductiveTransformationSource)
    (hUnique : AnalyticContactPicardGeneratorPreservesDistribution)
    (hNTU : UniqueContactHamiltonianBijection)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
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
    letI := A.charts
    letI := A.complexManifold
    ∃ (hPreserve : FullPreservesContact
        P.tangent P.connection A C.contact.line)
      (V : Type) (hNorm : NormedAddCommGroup V),
      letI : NormedAddCommGroup V := hNorm
      ∃ (hSpace : NormedSpace ℂ V) (hFinite : FiniteDimensional ℂ V)
        (hChart : ChartedSpace V
          (TwistorHolomorphicAutomorphisms P.tangent P.connection A)),
        letI : NormedSpace ℂ V := hSpace
        letI : FiniteDimensional ℂ V := hFinite
        letI : ChartedSpace V
          (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hChart
        ∃ (hManifold : IsManifold 𝓘(ℂ,V) ∞
            (TwistorHolomorphicAutomorphisms P.tangent P.connection A))
          (hLie : LieGroup 𝓘(ℂ,V) ∞
            (TwistorHolomorphicAutomorphisms P.tangent P.connection A)),
          letI : IsManifold 𝓘(ℂ,V) ∞
            (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hManifold
          letI : LieGroup 𝓘(ℂ,V) ∞
            (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hLie
          ∃ (hJoint : ContMDiff
                (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
                𝓘(ℂ,ComplexTwistorModel n) ∞
                (fun p : TwistorHolomorphicAutomorphisms
                    P.tangent P.connection A × SphereBundleTotal P.tangent =>
                  p.1.1 p.2)),
            (letI : CompleteSpace V := FiniteDimensional.complete ℂ V
             letI := ManifoldTwistorUniqueContactFullLieTransfer.contactCharts
               (V := V) P.tangent P.connection A C.contact.line hPreserve
             letI := ManifoldTwistorUniqueContactFullLieTransfer.contactLieGroup
               (V := V) P.tangent P.connection A C.contact.line hPreserve
             letI : ENat.LEInfty (minSmoothness ℂ 3) := by
               simpa only [minSmoothness_of_isRCLikeNormedField] using
                 (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
             letI : LieGroup 𝓘(ℂ,V) (minSmoothness ℂ 3)
                 (ContactAutomorphisms P.tangent P.connection A C.contact.line) :=
               LieGroup.of_le (ENat.LEInfty.out)
             LieAlgebra.HasCentralRadical ℂ
               (GroupLieAlgebra 𝓘(ℂ,V)
                 (ContactAutomorphisms P.tangent P.connection A C.contact.line))) ∧
            SelectedHamiltonianConjugationLaw (V := V)
              P n A C hPreserve hNTU (by omega) hJoint := by
  letI := A.charts
  letI := A.complexManifold
  obtain ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,hJoint,hRad⟩ :=
    hBWW P n hn hDim A
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℂ V := hSpace
  letI : FiniteDimensional ℂ V := hFinite
  letI : ChartedSpace V
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hChart
  letI : IsManifold 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hManifold
  letI : LieGroup 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hLie
  letI : CompleteSpace V := FiniteDimensional.complete ℂ V
  obtain ⟨hPreserve,hContactRad,hConj⟩ :=
    selected_picard_radical_hamiltonian_of_full_atlas (V := V)
      hUnique hNTU P n (by omega) A C hAmple hPic hJoint hRad
  exact ⟨hPreserve,V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,
    hJoint,hContactRad,hConj⟩

end
end QuaternionicSymmetry.ManifoldTwistorSelectedPicardReductiveHamiltonian
