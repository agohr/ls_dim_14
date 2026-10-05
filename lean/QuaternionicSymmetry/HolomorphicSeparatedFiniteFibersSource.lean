import QuaternionicSymmetry.HolomorphicLineCoreProjectiveHolomorphic

/-! Demailly's analytic finiteness principle in a directly usable form.
Theorem (5.9) of Chapter II, §5.1 in *Complex Analytic and Differential
Geometry*, printed p.104, says that every compact analytic subset of a
complex space whose global holomorphic functions separate points is finite.
The fiber below is analytic because it is cut out locally by the finitely
many holomorphic affine coordinates of the genuine projective map. The
source premise states precisely this specialized consequence; it does not
assume any line is ample, generated, or has a numerical section count. -/

namespace QuaternionicSymmetry.HolomorphicSeparatedFiniteFibersSource

open QuaternionicSymmetry.ComplexProjectiveTopology
open scoped Manifold ContDiff
noncomputable section
universe uB uF

/-- Demailly II §5.1, Theorem (5.9), specialized to fibers of actual
holomorphic maps to finite-dimensional complex projective space. An open
subset of a boundaryless complex manifold is holomorphically separated when
actual scalar holomorphic functions on that open subset separate its points.
Compactness of each fiber is an explicit premise. -/
def SeparatedCompactProjectiveFiberFiniteTheorem : Prop :=
  ∀ {B : Type uB} {F : Type uF}
    [TopologicalSpace B] [T2Space B] [SecondCountableTopology B]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B]
    (U : Set B), IsOpen U →
    (∀ x y : B, x ∈ U → y ∈ U → x ≠ y →
      ∃ f : B → ℂ, ContMDiffOn 𝓘(ℂ,F) 𝓘(ℂ,ℂ) ∞ f U ∧ f x ≠ f y) →
    ∀ (d : ℕ) (g : B → Space d),
      ContMDiffOn 𝓘(ℂ,F) 𝓘(ℂ,Fin d → ℂ) ∞ g U →
      ∀ p : Space d, IsCompact (U ∩ g ⁻¹' {p}) →
        (U ∩ g ⁻¹' {p}).Finite

end
end QuaternionicSymmetry.HolomorphicSeparatedFiniteFibersSource
