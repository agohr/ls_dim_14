import QuaternionicSymmetry.ManifoldSymmetricPowerCharacterExpansion
import QuaternionicSymmetry.ManifoldTwistorHolomorphicComplexCohomology

set_option maxHeartbeats 120000
set_option synthInstance.maxHeartbeats 40000

/-! A normalization-transparent interface for Semmelmann--Weingart
Section 2, Eq. (2.2). The cited pushforward/index formula is supplied for
each permitted nonnegative symmetric power using source Chern--Weil classes.
The identifications of those classes with the analytic rank-three quarter
and normalized tangent half traces are *separate* geometric hypotheses.
Neither an unrestricted Laurent-character index nor a global local-H
bundle is asserted. -/
namespace QuaternionicSymmetry.ManifoldSWIndexCharacterComparison
open ManifoldTangentCharacterNumber ManifoldTangentTraceRootCandidates
open ManifoldEvenCharacteristicAlgebra ManifoldIntegratedDensityCertificates
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open CategoryTheory TopologicalSpace
open scoped Manifold ContDiff
noncomputable section

universe w
variable {E M : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [MeasurableSpace E] [BorelSpace E] [Nonempty M] [MeasurableSpace M]
  [BorelSpace M] [CompactSpace M] [T2Space M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

local instance : Algebra ℚ (Total (E := E) (M := M)) :=
  ManifoldTangentTraceRootCandidates.rationalAlgebra

/-- The source Chern--Weil number before identifying its formal `u` and
tangent power-sum classes with the reconstructed analytic representatives. -/
def sourceCharacteristicFunctional (k : ℕ)
    (hdim : 4*(k+1) = Module.finrank ℝ E)
    (uSource : Total (E := E) (M := M))
    (tSource : ℕ → Total (E := E) (M := M)) :
    LaurentPolynomial ℚ →ₗ[ℚ] ℝ :=
  (((integrateGrade Q k hdim).comp
    (DirectSum.component ℝ ℕ (Grade (E := E) (M := M)) (k+1))).restrictScalars ℚ).comp
      (TangentAhatCharacterDensity.characterDensity (k+1) uSource tSource)

theorem sourceCharacteristicFunctional_eq_actual (n k : ℕ)
    (hdim : 4*(k+1) = Module.finrank ℝ E)
    (uSource : Total (E := E) (M := M))
    (tSource : ℕ → Total (E := E) (M := M))
    (hu : uSource = quarterUTotal Q D)
    (ht : tSource = normalizedTangentHalfTrace Q D n) :
    sourceCharacteristicFunctional Q k hdim uSource tSource =
      characteristicFunctional Q D n k hdim := by
  subst uSource
  subst tSource
  rfl

variable [HasSheafify (Opens.grothendieckTopology
    (TopCat.of (SphereBundleTotal Q))) (ModuleCat ℂ)]
  [twistorHasExt : HasExt.{w} (TopCat.Sheaf (ModuleCat ℂ)
    (TopCat.of (SphereBundleTotal Q)))]

/-- A single permitted SW Eq. (2.2) instance, followed by explicit
Chern--Weil normalization, gives the actual analytic χ(q) number. The
source formula `hSW` is not asserted by the formal expansion alone. -/
theorem euler_eq_characteristic_of_SW_and_normalization
    (n : ℕ) (A : CompatibleComplexAtlas Q D n)
    (L : HolomorphicContactLine Q D n A)
    (r : ℤ) (hqr : 0 ≤ (n : ℤ) + 2*r)
    (hfinite : ∀ s, FiniteDimensional ℂ
      (holomorphicTwistComplexCohomology Q D L r s))
    (hdim : 4*(n-1+1) = Module.finrank ℝ E)
    (uSource : Total (E := E) (M := M))
    (tSource : ℕ → Total (E := E) (M := M))
    (hSW : (0 ≤ (n : ℤ) + 2*r) →
      ((holomorphicTwistComplexEulerCharacteristic Q D L r (2*n+1)
      hfinite : ℤ) : ℝ) =
        sourceCharacteristicFunctional Q (n-1) hdim uSource tSource
          (Characters.chi (((n : ℤ) + 2*r).toNat)))
    (hu : uSource = quarterUTotal Q D)
    (ht : tSource = normalizedTangentHalfTrace Q D n) :
    ((holomorphicTwistComplexEulerCharacteristic Q D L r (2*n+1)
      hfinite : ℤ) : ℝ) =
      characteristicFunctional Q D n (n-1) hdim
        (Characters.chi (((n : ℤ) + 2*r).toNat)) := by
  have hSW' := hSW hqr
  rw [sourceCharacteristicFunctional_eq_actual Q D n (n-1) hdim
    uSource tSource hu ht] at hSW'
  exact hSW'

end
end QuaternionicSymmetry.ManifoldSWIndexCharacterComparison
