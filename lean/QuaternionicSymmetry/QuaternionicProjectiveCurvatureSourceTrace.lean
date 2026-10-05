import QuaternionicSymmetry.QuaternionicProjectiveStandardCurvatureTrace
import QuaternionicSymmetry.QuaternionicComplexTraceReality

/-! The printed projective-standard curvature trace convention, evaluated on
the genuine smooth local standard connection. -/
namespace QuaternionicSymmetry.QuaternionicProjectiveCurvatureSourceTrace

open QuaternionicProjectiveStandardL2
  QuaternionicProjectiveStandardHilbertStructure
  QuaternionicProjectiveStandardComplexTrace
  QuaternionicProjectiveStandardCurvatureTrace
  QuaternionicComplexModule QuaternionicComplexTrace
  QuaternionicComplexTraceReality
  QuaternionicManifoldProjectiveStandardConnection
open scoped ContDiff Manifold Quaternion
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev W := StandardSpace (E := E)

def standardCurvature (p : M) (y u v : E) : W (E := E) →ₗ[ℝ] W (E := E) :=
  (LocalConnection.curvature (standardConnection S Q D p) y u v).toLinearMap

theorem standardCurvature_commutes (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (z : W (E := E)) :
    standardCurvature S Q D p y u v ((standardStructure S).I z) =
      (standardStructure S).I (standardCurvature S Q D p y u v z) :=
  standardCurvature_commutes_I S Q D p y u v hy z

theorem standardCurvature_isSkew (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (z w : W (E := E)) :
    inner ℝ (standardCurvature S Q D p y u v z) w +
      inner ℝ z (standardCurvature S Q D p y u v w) = 0 :=
  standardCurvature_skew S Q D p y u v hy z w

set_option maxHeartbeats 800000 in
theorem standardCurvature_complex_evenTrace_real (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (j : ℕ) :
    (let F := standardCurvature S Q D p y u v
     letI : Module ℂ (W (E := E)) := standardComplexModule S
     letI : FiniteDimensional ℂ (W (E := E)) :=
       complex_finite (standardStructure S)
     LinearMap.trace ℂ (W (E := E))
       (complexLinearEnd (standardStructure S) ((F ^ 2) ^ j)
         (commutes_I_pow (standardStructure S) (F ^ 2)
           (commutes_I_pow (standardStructure S) F
             (standardCurvature_commutes S Q D p y u v hy) 2) j))).im = 0 :=
  complex_trace_even_power_eq_real_of_skew (standardStructure S)
    (standardCurvature S Q D p y u v)
    (standardCurvature_commutes S Q D p y u v hy)
    (standardCurvature_isSkew S Q D p y u v hy) j

set_option maxHeartbeats 800000 in
/-- For the actual standard curvature `F`, the source substitution
`X = iF/(2π)` has `-X² = F²/(4π²)`. Its half-complex trace has the
printed quarter-real-trace normalization at every even power. -/
theorem standardCurvature_sourceHalfTrace_re (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (j : ℕ) :
    let F := standardCurvature S Q D p y u v
    letI : Module ℂ (W (E := E)) := standardComplexModule S;
    letI : FiniteDimensional ℂ (W (E := E)) :=
      complex_finite (standardStructure S);
    let A := complexLinearEnd (standardStructure S) F
      (standardCurvature_commutes S Q D p y u v hy)
    (1 / 2 : ℝ) *
      (LinearMap.trace ℂ (W (E := E))
        ((-((Complex.I / (2 * (Real.pi : ℂ))) • A) ^ 2) ^ j)).re =
      ((1 / (4 * Real.pi ^ 2) : ℝ) ^ j) *
        ((1 / 4 : ℝ) *
          LinearMap.trace ℝ (W (E := E)) ((F ^ 2) ^ j)) :=
  source_half_trace_power_re_eq_real_trace (standardStructure S)
    (standardCurvature S Q D p y u v)
    (standardCurvature_commutes S Q D p y u v hy) j

end
end QuaternionicSymmetry.QuaternionicProjectiveCurvatureSourceTrace
