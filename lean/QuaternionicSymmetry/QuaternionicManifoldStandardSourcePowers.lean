import QuaternionicSymmetry.QuaternionicManifoldStandardEvenTrace
import QuaternionicSymmetry.QuaternionicProjectiveCurvatureSourceTrace
import QuaternionicSymmetry.QuaternionicComplexSourceReality

/-! Pointwise higher source trace normalization of actual standard curvature.
The statement is numerical at one curvature pair, before exterior-form
polarization and Chern--Weil gluing. -/
namespace QuaternionicSymmetry.QuaternionicManifoldStandardSourcePowers
open QuaternionicProjectiveCurvatureSourceTrace
  QuaternionicManifoldStandardEvenTrace
  QuaternionicProjectiveStandardL2
  QuaternionicProjectiveStandardHilbertStructure
  QuaternionicProjectiveStandardComplexTrace
  QuaternionicComplexModule QuaternionicComplexTrace
  QuaternionicManifoldProjectiveStandardConnection
  ManifoldQuaternionicConnection
  ManifoldQuaternionicConnectionSplitting
  ManifoldQuaternionicAdjointConnection
  LocalEndomorphismTrace
open scoped ContDiff Manifold Quaternion
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

set_option maxHeartbeats 800000 in
theorem source_evenTrace_rankThree (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (j : ℕ) (hj : 0 < j) :
    let F := QuaternionicProjectiveCurvatureSourceTrace.standardCurvature S Q D p y u v
    letI : Module ℂ (StandardSpace (E := E)) :=
      standardComplexModule S;
    letI : FiniteDimensional ℂ (StandardSpace (E := E)) :=
      complex_finite (standardStructure S);
    let A := complexLinearEnd (standardStructure S) F
      (standardCurvature_commutes S Q D p y u v hy)
    (4 : ℝ) ^ j * ((1 / 2 : ℝ) *
      (LinearMap.trace ℂ (StandardSpace (E := E))
        ((-((Complex.I / (2 * (Real.pi : ℂ))) • A) ^ 2) ^ j)).re) =
      ((1 / (4 * Real.pi ^ 2) : ℝ) ^ j) * (1 / 4 : ℝ) *
        ((4 : ℝ) ^ j * traceCLM
          ((LocalConnection.curvature (symplecticConnection Q D p) y u v) ^ (2 * j)) +
          2 * traceCLM ((inducedCurvature Q D p y u v) ^ (2 * j))) := by
  letI : Module ℂ (StandardSpace (E := E)) := standardComplexModule S
  letI : FiniteDimensional ℂ (StandardSpace (E := E)) :=
    complex_finite (standardStructure S)
  let C := LocalConnection.curvature (standardConnection S Q D p) y u v
  have hpow (m : ℕ) : (C ^ m).toLinearMap = C.toLinearMap ^ m := by
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [pow_succ, pow_succ]
        apply LinearMap.ext
        intro z
        exact congrArg (fun L : StandardSpace (E := E) →ₗ[ℝ]
          StandardSpace (E := E) => L (C z)) ih
  have hs := standardCurvature_sourceHalfTrace_re S Q D p y u v hy j
  have hlin : LinearMap.trace ℝ (StandardSpace (E := E))
      (((QuaternionicProjectiveCurvatureSourceTrace.standardCurvature S Q D p y u v) ^ 2) ^ j) =
      traceCLM ((LocalConnection.curvature (standardConnection S Q D p) y u v) ^ (2 * j)) := by
    rw [traceCLM_apply, ← pow_mul]
    change LinearMap.trace ℝ (StandardSpace (E := E))
      (C.toLinearMap ^ (2 * j)) =
      LinearMap.trace ℝ (StandardSpace (E := E)) ((C ^ (2 * j)).toLinearMap)
    rw [hpow]
  dsimp only at hs
  rw [hlin] at hs
  have hn := standardCurvature_even_trace_rankThree S Q D p y u v hy j hj
  change (4 : ℝ) ^ j * ((1 / 2 : ℝ) * _) = _
  rw [hs]
  rw [← hn]
  ring

end
end QuaternionicSymmetry.QuaternionicManifoldStandardSourcePowers
