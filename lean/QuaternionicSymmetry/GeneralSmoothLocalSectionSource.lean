import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-! A narrowly stated general differential-topological source boundary for
Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 4.26 (Local
Section Theorem), printed pp.88–89. It is used only for a smooth local
choice of representatives of an already proved surjective submersion.

The section is represented as a total function, with smoothness and the
right-inverse equation asserted only on its open local domain. Outside
that domain it is arbitrarily extended using the prescribed point `x`;
this is equivalent to Lee's ordinary `σ : U → M` formulation and avoids
introducing a subtype manifold chart in the source interface. -/

namespace QuaternionicSymmetry.GeneralSmoothLocalSectionSource

open Manifold
open scoped Manifold ContDiff

private abbrev RModel (d : ℕ) := Fin d → ℝ

/-- Lee 4.26, specialized only to boundary-free finite-dimensional real
manifolds with their standard regularity/separation hypotheses. It
postulates no group action, quotient, quaternionic structure, or model
geometry. A supplied instance is an explicitly audited general source
premise, not an unchecked theorem about the projector orbit. -/
def LeeLocalSectionTheorem : Prop :=
  ∀ {M N : Type} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [TopologicalSpace N] [T2Space N]
    [SecondCountableTopology N]
    (d q : ℕ) [ChartedSpace (RModel d) M]
    [IsManifold 𝓘(ℝ, RModel d) ∞ M]
    [ChartedSpace (RModel q) N]
    [IsManifold 𝓘(ℝ, RModel q) ∞ N]
    (π : M → N),
    ContMDiff 𝓘(ℝ, RModel d) 𝓘(ℝ, RModel q) ∞ π →
    (∀ x : M, Function.Surjective
      (mfderiv 𝓘(ℝ, RModel d) 𝓘(ℝ, RModel q) π x)) →
    ∀ x : M, ∃ U : Set N, IsOpen U ∧ π x ∈ U ∧
      ∃ σ : N → M,
        ContMDiffOn 𝓘(ℝ, RModel q) 𝓘(ℝ, RModel d) ∞ σ U ∧
        σ (π x) = x ∧
        ∀ y ∈ U, π (σ y) = y

end QuaternionicSymmetry.GeneralSmoothLocalSectionSource
