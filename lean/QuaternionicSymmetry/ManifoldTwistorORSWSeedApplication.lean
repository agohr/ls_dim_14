import QuaternionicSymmetry.GeneralContactFanoORSWSource
import QuaternionicSymmetry.ManifoldTwistorBKKPicardHomogeneityApplication
import QuaternionicSymmetry.ManifoldTwistorContactAutomorphismTopology

/-! Conditional application of the reviewed universal analytic ORSW rank
corollary to one actual selected twistor, contact form and group. The compact
real form and rank witness remain explicit: this leaf does not claim the
source-only seed milestone is closed. -/
namespace QuaternionicSymmetry.ManifoldTwistorORSWSeedApplication

open GeneralContactFanoORSWSource
open ManifoldTwistorBKKPicardHomogeneityApplication
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorContactAutomorphisms ManifoldTwistorLineCoreClasses
open ManifoldPositiveQuaternionicKahlerGeometry
open HolomorphicLineCoreAmpleFiniteMap CompactLieTorusInputs
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- The actual contact group acts transitively in every seed dimension once
its genuine compact-real-form and rank hypotheses are supplied. No unrelated
atlas, contact line or projective action is selected during the application. -/
theorem contactAut_transitive_of_compactRealForm_rank_two
    (hORSW : AnalyticCompactRealFormRankHomogeneity)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hn7 : n ≤ 7)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hAmple : letI := A.charts
      letI := A.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line))
    (hPic : letI := A.charts
      letI := A.complexManifold
      Function.Bijective (fun q : ℤ =>
        (contactClass P.tangent P.connection C.contact.line) ^ q))
    {VC : Type} [NormedAddCommGroup VC] [NormedSpace ℂ VC]
    [FiniteDimensional ℂ VC]
    [ChartedSpace VC (ContactAutomorphisms P.tangent P.connection A C.contact.line)]
    [IsManifold 𝓘(ℂ,VC) ∞
      (ContactAutomorphisms P.tangent P.connection A C.contact.line)]
    [LieGroup 𝓘(ℂ,VC) ∞
      (ContactAutomorphisms P.tangent P.connection A C.contact.line)]
    (hJoint : letI := A.charts
      letI := A.complexManifold
      ContMDiff (𝓘(ℂ,VC).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : ContactAutomorphisms P.tangent P.connection A C.contact.line ×
          SphereBundleTotal P.tangent => p.1.1 p.2))
    {K VR : Type} [Group K] [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup VR] [NormedSpace ℝ VR] [FiniteDimensional ℝ VR]
    [ChartedSpace VR K] [IsManifold 𝓘(ℝ,VR) ∞ K] [LieGroup 𝓘(ℝ,VR) ∞ K]
    (ι : K →* ContactAutomorphisms P.tangent P.connection A C.contact.line)
    (hReal : IsCompactRealForm (VR := VR) (VC := VC) ι)
    (T : TorusEmbedding K 2) :
    ∀ z w : SphereBundleTotal P.tangent,
      ∃ f : ContactAutomorphisms P.tangent P.connection A C.contact.line,
        f.1 z = w := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : ConnectedSpace M := {
    toPreconnectedSpace := inferInstance
    toNonempty := inferInstance }
  letI := A.charts
  letI := A.complexManifold
  letI : ChartedSpace VC
      (GeneralHolomorphicDistributionAutomorphisms.Automorphisms
        (contactDistribution P.tangent P.connection A C.contact.line)) :=
    inferInstanceAs (ChartedSpace VC
      (ContactAutomorphisms P.tangent P.connection A C.contact.line))
  letI : IsManifold 𝓘(ℂ,VC) ∞
      (GeneralHolomorphicDistributionAutomorphisms.Automorphisms
        (contactDistribution P.tangent P.connection A C.contact.line)) :=
    inferInstanceAs (IsManifold 𝓘(ℂ,VC) ∞
      (ContactAutomorphisms P.tangent P.connection A C.contact.line))
  letI : LieGroup 𝓘(ℂ,VC) ∞
      (GeneralHolomorphicDistributionAutomorphisms.Automorphisms
        (contactDistribution P.tangent P.connection A C.contact.line)) :=
    inferInstanceAs (LieGroup 𝓘(ℂ,VC) ∞
      (ContactAutomorphisms P.tangent P.connection A C.contact.line))
  exact hORSW ((𝓘(ℝ,E)).prod (𝓡 2)) n (by omega)
    C.toGeneralContactGeometry
    (contactDistribution P.tangent P.connection A C.contact.line)
    (actual_contact_kernel P.tangent P.connection A C)
    hAmple hPic hJoint ι hReal 2 T (by omega)
    (rank_two_seed_threshold n hn7)

end
end QuaternionicSymmetry.ManifoldTwistorORSWSeedApplication
