import QuaternionicSymmetry.ManifoldQuaternionicIsometrySplitDerivative
import QuaternionicSymmetry.ManifoldQuaternionicIsometryOrientation
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! The actual horizontal-base plus vertical-sphere metric on twistor
tangent fibers, and its preservation by derivative-induced isometries. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorSplitMetric

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometrySplitDerivative
open ManifoldQuaternionicIsometryOrientation
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

/-- The pointwise twistor metric obtained from the checked Levi-Civita
horizontal splitting and the Euclidean metric on the actual vertical
coefficient plane. -/
def splitMetric (z : SphereBundleTotal Q)
    (u v : TangentSpace (J (E := E)) z) : ℝ :=
  Q.tangentMetricForm z.1 (connectionTangentEquiv Q D z u).1
    (connectionTangentEquiv Q D z v).1 +
  ((connectionTangentEquiv Q D z u).2).1 ⬝ᵥ
    ((connectionTangentEquiv Q D z v).2).1

theorem splitMetric_symm (z : SphereBundleTotal Q)
    (u v : TangentSpace (J (E := E)) z) :
    splitMetric Q D z u v = splitMetric Q D z v u := by
  unfold splitMetric
  rw [Q.tangentMetricForm_symm, dotProduct_comm]

theorem splitMetric_add_right (z : SphereBundleTotal Q)
    (u v w : TangentSpace (J (E := E)) z) :
    splitMetric Q D z u (v + w) =
      splitMetric Q D z u v + splitMetric Q D z u w := by
  simp [splitMetric, map_add, dotProduct_add]
  abel

theorem splitMetric_smul_right (z : SphereBundleTotal Q)
    (c : ℝ) (u v : TangentSpace (J (E := E)) z) :
    splitMetric Q D z u (c • v) = c * splitMetric Q D z u v := by
  simp [splitMetric, map_smul, dotProduct_smul, smul_eq_mul, mul_add]

theorem splitMetric_pos (z : SphereBundleTotal Q)
    (v : TangentSpace (J (E := E)) z) (hv : v ≠ 0) :
    0 < splitMetric Q D z v v := by
  let w := connectionTangentEquiv Q D z v
  have hw : w ≠ 0 := by
    intro h
    exact hv ((connectionTangentEquiv Q D z).map_eq_zero_iff.mp h)
  have hbase : 0 ≤ Q.tangentMetricForm z.1 w.1 w.1 := by
    by_cases hb : w.1 = 0
    · simp [hb]
    · exact le_of_lt (Q.tangentMetricForm_pos z.1 w.1 hb)
  have hvertical : 0 ≤ w.2.1 ⬝ᵥ w.2.1 :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg (w.2.1 i))
  change 0 < Q.tangentMetricForm z.1 w.1 w.1 + w.2.1 ⬝ᵥ w.2.1
  by_cases hb : w.1 = 0
  · have hwv : w.2.1 ≠ 0 := by
      intro hv0
      apply hw
      apply Prod.ext hb
      exact Subtype.ext hv0
    have hdotNe : w.2.1 ⬝ᵥ w.2.1 ≠ 0 := by
      intro he
      exact hwv (dotProduct_self_eq_zero.mp he)
    have hdot : 0 < w.2.1 ⬝ᵥ w.2.1 :=
      lt_of_le_of_ne hvertical hdotNe.symm
    exact add_pos_of_nonneg_of_pos hbase hdot
  · exact add_pos_of_pos_of_nonneg
      (Q.tangentMetricForm_pos z.1 w.1 hb) hvertical

/-- Every genuine quaternionic metric isometry preserves the actual split
twistor tangent metric. -/
theorem splitMetric_sphereTotalMap
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q)
    (u v : TangentSpace (J (E := E)) z) :
    splitMetric Q D (sphereTotalMap Q f z)
      (mfderiv (J (E := E)) (J (E := E)) (sphereTotalMap Q f) z u)
      (mfderiv (J (E := E)) (J (E := E)) (sphereTotalMap Q f) z v) =
    splitMetric Q D z u v := by
  unfold splitMetric
  rw [connectionTangentEquiv_mfderiv_fst Q D f z u,
    connectionTangentEquiv_mfderiv_fst Q D f z v,
    connectionTangentEquiv_mfderiv_snd_coefficients Q D f z u,
    connectionTangentEquiv_mfderiv_snd_coefficients Q D f z v]
  change Q.tangentMetricForm (f.1 z.1) _ _ + _ = _ + _
  rw [f.2.1 z.1,
    coefficientAction_dot Q f z.1]

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorSplitMetric
