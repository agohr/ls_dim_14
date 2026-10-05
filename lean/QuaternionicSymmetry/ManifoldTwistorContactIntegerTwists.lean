import QuaternionicSymmetry.HolomorphicLineIntegerPowers
import QuaternionicSymmetry.ManifoldTwistorLeBrunHolomorphicLine

/-! The full integer family of holomorphic powers of the actual twistor
contact line. Negative twists use the genuine dual line core. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

open QuaternionicSymmetry.HolomorphicLineIntegerPowers
open QuaternionicSymmetry.HolomorphicLinePowers
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

/-- The actual holomorphic line core for the integral twist `L^r`. -/
def HolomorphicContactLine.integerTwistCore {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) : VectorBundleCore ℂ (SphereBundleTotal Q) ℂ L.Index :=
  integerPowerCore L.core r

theorem HolomorphicContactLine.integerTwistCore_holomorphic {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) :
    letI := A.charts
    (L.integerTwistCore Q D r).IsContMDiff
      𝓘(ℂ, ComplexTwistorModel n) ∞ := by
  letI := A.charts
  letI : L.core.IsContMDiff 𝓘(ℂ, ComplexTwistorModel n) ∞ := L.holomorphic
  exact integerPowerCore_isContMDiff L.core r

theorem HolomorphicContactLine.integerTwistCore_natCast {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (k : ℕ) :
    L.integerTwistCore Q D (k : ℤ) = HolomorphicLinePowers.powerCore L.core k :=
  HolomorphicLineIntegerPowers.integerPowerCore_natCast L.core k

theorem HolomorphicContactLine.integerTwistCore_neg_natCast {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (k : ℕ) (hk : 0 < k) :
    L.integerTwistCore Q D (-(k : ℤ)) =
      HolomorphicLinePowers.powerCore (dualCore L.core) k :=
  HolomorphicLineIntegerPowers.integerPowerCore_neg_natCast L.core k hk

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
