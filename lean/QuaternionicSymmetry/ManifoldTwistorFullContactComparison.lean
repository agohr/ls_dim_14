import QuaternionicSymmetry.ManifoldTwistorFullAutomorphismLift

/-! The exact internal bridge from full biholomorphisms to contact
automorphisms. The premise says *every* full biholomorphism preserves the
actual distribution; it is not established here and must be discharged by
the contact-structure uniqueness branch off the projective exception. -/

namespace QuaternionicSymmetry.ManifoldTwistorFullContactComparison

open GeneralHolomorphicDistributionAutomorphisms
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorContactAutomorphisms
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (L : HolomorphicContactLine Q D n B)

def AllBiholomorphismsPreserveContact : Prop :=
  letI := B.charts
  letI := B.complexManifold
  ∀ f : TwistorHolomorphicAutomorphisms Q D B,
    Preserves (contactDistribution Q D B L) f.1

theorem contactForget_surjective
    (hUnique : AllBiholomorphismsPreserveContact Q D B L) :
    Function.Surjective (contactForget Q D B L) := by
  letI := B.charts
  letI := B.complexManifold
  intro f
  exact ⟨⟨f.1, hUnique f⟩, by apply Subtype.ext; rfl⟩

def contactFullEquiv
    (hUnique : AllBiholomorphismsPreserveContact Q D B L) :
    ContactAutomorphisms Q D B L ≃*
      TwistorHolomorphicAutomorphisms Q D B :=
  MulEquiv.ofBijective (contactForget Q D B L)
    ⟨contactForget_injective Q D B L,
      contactForget_surjective Q D B L hUnique⟩

end
end QuaternionicSymmetry.ManifoldTwistorFullContactComparison
