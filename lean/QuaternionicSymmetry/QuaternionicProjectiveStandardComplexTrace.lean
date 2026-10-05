import QuaternionicSymmetry.QuaternionicComplexTrace
import QuaternionicSymmetry.QuaternionicManifoldProjectiveStandardConnection

/-! Real and complex trace conventions for the actual projective standard
representation, with the complex structure fixed by the first quaternionic
unit. -/
namespace QuaternionicSymmetry.QuaternionicProjectiveStandardComplexTrace

open QuaternionicComplexModule QuaternionicComplexTrace
open QuaternionicProjectiveStandardHilbertStructure
open QuaternionicProjectiveStandardL2
open scoped Quaternion
open scoped ContDiff Manifold
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] (S : QuaternionicStructure E)

private abbrev W := StandardSpace (E := E)

def standardComplexModule : Module ℂ (W (E := E)) :=
  complexModule (standardStructure S)

omit [Nontrivial E] in
theorem standard_real_finrank :
    Module.finrank ℝ (W (E := E)) = Module.finrank ℝ E + 4 := by
  rw [(WithLp.linearEquiv 2 ℝ (E × ℍ)).finrank_eq]
  simp [Module.finrank_prod, Quaternion.finrank_eq_four]

omit [Nontrivial E] in
theorem standard_complex_finrank :
    letI : Module ℂ (W (E := E)) := standardComplexModule S
    Module.finrank ℂ (W (E := E)) = 2 * (S.quaternionicDimension + 1) := by
  letI : Module ℂ (W (E := E)) := standardComplexModule S
  have hr := complex_finrank_double (standardStructure S)
  rw [standard_real_finrank (E := E), S.real_finrank] at hr
  change 4 * S.quaternionicDimension + 4 =
    2 * Module.finrank ℂ (W (E := E)) at hr
  omega

/-- Every standard quaternionic isometry is complex-linear for the fixed
left multiplication by `I`. -/
def standardActionComplexLinear
    (p : QuaternionicIsometryNormalizer.symplecticKernel S × unitary ℍ) :
    letI : Module ℂ (W (E := E)) := standardComplexModule S
    W (E := E) →ₗ[ℂ] W (E := E) :=
  complexLinearEnd (standardStructure S)
    ((standardSymplecticAction S p).1.toLinearEquiv.toLinearMap)
    (standardIsometryL2_commutes_I S p)

theorem standardAction_trace_re
    (p : QuaternionicIsometryNormalizer.symplecticKernel S × unitary ℍ) :
    LinearMap.trace ℝ (W (E := E))
      ((standardSymplecticAction S p).1.toLinearEquiv.toLinearMap) =
    2 * (letI : Module ℂ (W (E := E)) := standardComplexModule S
         letI : FiniteDimensional ℂ (W (E := E)) :=
           complex_finite (standardStructure S)
         LinearMap.trace ℂ (W (E := E)) (standardActionComplexLinear S p)).re :=
  real_trace_eq_two_complex_trace_re (standardStructure S) _
    (standardIsometryL2_commutes_I S p)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

theorem standardConnection_trace_re
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
    (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    LinearMap.trace ℝ (W (E := E))
      (QuaternionicManifoldProjectiveStandardConnection.standardConnection
        S Q D p y u).toLinearMap =
    2 * (letI : Module ℂ (W (E := E)) := standardComplexModule S
         letI : FiniteDimensional ℂ (W (E := E)) :=
           complex_finite (standardStructure S)
         LinearMap.trace ℂ (W (E := E))
           (complexLinearEnd (standardStructure S)
             (QuaternionicManifoldProjectiveStandardConnection.standardConnection
               S Q D p y u).toLinearMap
             (QuaternionicManifoldProjectiveStandardConnection.standardConnection_commutes_I
               S Q D p y u hy))).re :=
  real_trace_eq_two_complex_trace_re (standardStructure S) _
    (QuaternionicManifoldProjectiveStandardConnection.standardConnection_commutes_I
      S Q D p y u hy)

/-- The positive even-power trace of the real standard connection. For the
source convention `X = i F / (2π)`, one has `-X² = F² / (4π²)`. -/
theorem standardConnection_half_trace_even_power_re
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
    (D : QuaternionicSymmetry.ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (j : ℕ) :
    let X := (QuaternionicManifoldProjectiveStandardConnection.standardConnection
      S Q D p y u).toLinearMap
    (1 / 2 : ℝ) *
      (letI : Module ℂ (W (E := E)) := standardComplexModule S
       letI : FiniteDimensional ℂ (W (E := E)) :=
         complex_finite (standardStructure S)
       LinearMap.trace ℂ (W (E := E))
         (complexLinearEnd (standardStructure S) ((X ^ 2) ^ j)
           (commutes_I_pow (standardStructure S) (X ^ 2)
             (commutes_I_pow (standardStructure S) X
               (QuaternionicManifoldProjectiveStandardConnection.standardConnection_commutes_I
                 S Q D p y u hy) 2) j))).re =
    (1 / 4 : ℝ) * LinearMap.trace ℝ (W (E := E)) ((X ^ 2) ^ j) := by
  exact half_complex_trace_power_re_eq_quarter_real_trace (standardStructure S) _
    (QuaternionicManifoldProjectiveStandardConnection.standardConnection_commutes_I
      S Q D p y u hy) j

end
end QuaternionicSymmetry.QuaternionicProjectiveStandardComplexTrace
