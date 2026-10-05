import QuaternionicSymmetry.QuaternionicProjectiveStandardComplexTrace
import QuaternionicSymmetry.QuaternionicProjectiveStandardSkew
import QuaternionicSymmetry.QuaternionicManifoldProjectiveSmooth
import QuaternionicSymmetry.LocalConnectionSkewCurvature

/-! Curvature of the actual smooth metric standard connection preserves the
fixed complex structure and is real skew-adjoint. -/
namespace QuaternionicSymmetry.QuaternionicProjectiveStandardCurvatureTrace

open QuaternionicProjectiveStandardL2
  QuaternionicProjectiveStandardHilbertStructure
  QuaternionicManifoldProjectiveStandardConnection
  QuaternionicManifoldProjectiveSmooth
  QuaternionicProjectiveStandardSkew
  ManifoldQuaternionicAdjointConnection
  ContinuousLinearConstraintDerivative
open scoped ContDiff Manifold Topology Quaternion
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance
local instance : NormedSpace ℝ
    (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) := inferInstance
local instance : NormedSpace ℝ
    (E →L[ℝ] (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E))) := inferInstance

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev W := StandardSpace (E := E)

private def standardIEnd : W (E := E) →L[ℝ] W (E := E) :=
  (standardStructure S).I.toContinuousLinearEquiv.toContinuousLinearMap

private theorem standardConnection_commutes_IEnd (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    standardConnection S Q D p y u * standardIEnd S =
      standardIEnd S * standardConnection S Q D p y u := by
  ext z
  exact standardConnection_commutes_I S Q D p y u hy z

set_option maxHeartbeats 800000 in
theorem standardCurvature_commutes_I (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (z : W (E := E)) :
    LocalConnection.curvature (standardConnection S Q D p) y u v
        ((standardStructure S).I z) =
      (standardStructure S).I
        (LocalConnection.curvature (standardConnection S Q D p) y u v z) := by
  let T := standardIEnd S
  let Γ := standardConnection S Q D p
  have hd : DifferentiableAt ℝ Γ y :=
    ((standardConnection_smooth S Q D p).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy)
  have hder (a b : E) :
      fderiv ℝ Γ y a b * T = T * fderiv ℝ Γ y a b := by
    let L : (E →L[ℝ] (W (E := E) →L[ℝ] W (E := E))) →L[ℝ]
        (W (E := E) →L[ℝ] W (E := E)) :=
      (commutatorMap.flip T).comp
        (ContinuousLinearMap.apply ℝ (W (E := E) →L[ℝ] W (E := E)) b)
    have hz := annihilates_fderiv L Γ y a hd (by
      filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy]
        with x hx
      change Γ x b * T - T * Γ x b = 0
      exact sub_eq_zero.mpr (standardConnection_commutes_IEnd S Q D p x b hx))
    exact sub_eq_zero.mp hz
  have hcomm : (Γ y u * Γ y v - Γ y v * Γ y u) * T =
      T * (Γ y u * Γ y v - Γ y v * Γ y u) := by
    have hu := standardConnection_commutes_IEnd S Q D p y u hy
    have hv := standardConnection_commutes_IEnd S Q D p y v hy
    calc
      _ = Γ y u * (Γ y v * T) - Γ y v * (Γ y u * T) := by
        simp only [sub_mul, mul_assoc]
      _ = Γ y u * (T * Γ y v) - Γ y v * (T * Γ y u) := by rw [hv, hu]
      _ = (Γ y u * T) * Γ y v - (Γ y v * T) * Γ y u := by
        simp only [mul_assoc]
      _ = (T * Γ y u) * Γ y v - (T * Γ y v) * Γ y u := by rw [hu, hv]
      _ = _ := by simp only [mul_sub, mul_assoc]
  have hcur : LocalConnection.curvature Γ y u v * T =
      T * LocalConnection.curvature Γ y u v := by
    rw [LocalConnection.curvature_apply]
    have hshape : ∀ A B C D : W (E := E) →L[ℝ] W (E := E),
        A - B + C - D = (A - B) + (C - D) := by intros; abel
    rw [hshape]
    rw [add_mul, sub_mul, hder u v, hder v u, hcomm]
    simp only [mul_add, mul_sub]
  have hz := congrArg (fun A : W (E := E) →L[ℝ] W (E := E) => A z) hcur
  exact hz

theorem standardCurvature_skew (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (z w : W (E := E)) :
    inner ℝ (LocalConnection.curvature (standardConnection S Q D p) y u v z) w +
      inner ℝ z (LocalConnection.curvature (standardConnection S Q D p) y u v w) = 0 := by
  have hd : DifferentiableAt ℝ (standardConnection S Q D p) y :=
    ((standardConnection_smooth S Q D p).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy)
  apply LocalConnection.curvature_skew _ y u v hd
  filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy]
    with x hx t a b
  exact standardConnection_skew S Q D p x t hx a b

end
end QuaternionicSymmetry.QuaternionicProjectiveStandardCurvatureTrace
