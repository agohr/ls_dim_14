import QuaternionicSymmetry.GeneralContactFanoPicardHomogeneitySource
import QuaternionicSymmetry.RealToComplexTangentComplexification
import QuaternionicSymmetry.CompactLieTorusInputs
import QuaternionicSymmetry.GeneralHolomorphicAutomorphismSecondCountable

/-!
# Actual analytic compact-real-form interface for ORSW's rank theorem

Reviewed derived literature input, not an internal proof of ORSW.
Exact external derivation: Textbooks/STAGE2_SOURCE_REVIEW_20261001.md.
ORSW, Selecta Mathematica 27 (2021), article 10, Theorem 6.1,
publisher-layout p.30, requires a reductive algebraic group, not merely a
Lie algebra with central radical. The hypothesis below includes an actual
compact group, its literal injective homomorphism into the contact group,
and the bijective complexification of its actual differential.

The reviewed external derivation is Chow/GAGA for the same ample contact
manifold and line, linear algebraicity of its contact automorphism group,
compact-real-form reductivity, and ORSW 6.1. Compatibility of the complex
Lie atlas with the actual action is required by joint holomorphic evaluation.
The rank lower bound is a genuine continuous injective compact torus.
The source/type derivation has been reviewed on 1 October 2026; the final
global statement-fidelity and release audits remain separate obligations. No classification
premise about a quaternionic twistor is included.
-/
namespace QuaternionicSymmetry.GeneralContactFanoORSWSource

open GeneralComplexContactData GeneralContactFanoPicardHomogeneitySource
open ManifoldTwistorLeBrunComplexAtlas
open GeneralHolomorphicDistributionAutomorphisms
open HolomorphicLineCoreClasses HolomorphicLineCoreClassGroup
open HolomorphicLineCoreAmpleFiniteMap
open RealToComplexTangentComplexification CompactLieTorusInputs
open scoped Manifold ContDiff
noncomputable section

/-- A literal compact real form in specified compatible real/complex charts. -/
def IsCompactRealForm
    {K H VR VC : Type} [Group K] [TopologicalSpace K]
    [CompactSpace K] [NormedAddCommGroup VR] [NormedSpace ℝ VR]
    [FiniteDimensional ℝ VR] [ChartedSpace VR K]
    [IsManifold 𝓘(ℝ,VR) ∞ K] [LieGroup 𝓘(ℝ,VR) ∞ K]
    [Group H] [TopologicalSpace H]
    [NormedAddCommGroup VC] [NormedSpace ℂ VC]
    [ChartedSpace VC H]
    (ι : K →* H) : Prop :=
  Function.Injective ι ∧
  ContMDiff 𝓘(ℝ,VR) 𝓘(ℝ,VC) ∞ ι ∧
  IsInfinitesimalComplexification
    (show VR →ₗ[ℝ] VC from
      (mfderiv 𝓘(ℝ,VR) 𝓘(ℝ,VC) ι 1).toLinearMap)

/-- Reviewed universal analytic ORSW 6.1 corollary with concrete group
and rank hypotheses; algebraization is in the disclosed external derivation. -/
def AnalyticCompactRealFormRankHomogeneity : Prop :=
  ∀ {R H Z : Type}
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    [TopologicalSpace H] [TopologicalSpace Z] [ChartedSpace H Z]
    (IR : ModelWithCorners ℝ R H) [IsManifold IR ∞ Z]
    [CompactSpace Z] [T2Space Z] [SecondCountableTopology Z]
    [ConnectedSpace Z]
    (n : ℕ) (_hn : 1 ≤ n)
    (G : ContactGeometry (IR := IR) (Z := Z) n)
    (D : Z → Submodule ℂ (ComplexTwistorModel n)),
    ContactGeometry.IsComplexContactKernel IR G D →
    letI := G.charts
    letI := G.complexManifold
    AmpleCore 𝓘(ℂ,ComplexTwistorModel n) (ContactGeometry.lineCore IR G) →
    Function.Bijective (fun q : ℤ =>
      (Quotient.mk _ (ContactGeometry.lineCore IR G) :
        CoreClass.{0} (B := Z) 𝓘(ℂ,ComplexTwistorModel n)) ^ q) →
    ∀ {VC : Type} [NormedAddCommGroup VC] [NormedSpace ℂ VC]
      [FiniteDimensional ℂ VC] [ChartedSpace VC (Automorphisms D)]
      [IsManifold 𝓘(ℂ,VC) ∞ (Automorphisms D)]
      [LieGroup 𝓘(ℂ,VC) ∞ (Automorphisms D)],
      ContMDiff (𝓘(ℂ,VC).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : Automorphisms D × Z => p.1.1 p.2) →
      ∀ {K VR : Type} [Group K] [TopologicalSpace K]
        [CompactSpace K] [NormedAddCommGroup VR] [NormedSpace ℝ VR]
        [FiniteDimensional ℝ VR] [ChartedSpace VR K]
        [IsManifold 𝓘(ℝ,VR) ∞ K] [LieGroup 𝓘(ℝ,VR) ∞ K]
        (ι : K →* Automorphisms D),
        IsCompactRealForm (VR := VR) (VC := VC) ι →
        ∀ (r : ℕ) (_T : TorusEmbedding K r),
          2 ≤ r → n ≤ 2*r+3 →
          ∀ z w : Z, ∃ f : Automorphisms D, f.1 z = w

/-- Rank two meets the numerical threshold for every seed dimension. -/
theorem rank_two_seed_threshold (n : ℕ) (hn : n ≤ 7) : n ≤ 2*2+3 := by
  omega

end
end QuaternionicSymmetry.GeneralContactFanoORSWSource
