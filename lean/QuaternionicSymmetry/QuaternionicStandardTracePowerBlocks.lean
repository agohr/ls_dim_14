import QuaternionicSymmetry.ContinuousBlockTracePowers
import QuaternionicSymmetry.QuaternionicManifoldStandardCurvatureRepresentation
import QuaternionicSymmetry.QuaternionicScalarLineTracePowerForm
import QuaternionicSymmetry.QuaternionicFixedModelAdjointTrace
import QuaternionicSymmetry.QuaternionicActualScalarAdjointTracePowers

/-! Actual local projective-standard curvature trace powers split into the
fixed-model symplectic and quaternionic-line blocks in every wedge degree. -/
namespace QuaternionicSymmetry.QuaternionicStandardTracePowerBlocks
open ContinuousBlockTracePowers ContinuousAlgebraWedgePowers
  QuaternionicManifoldStandardCurvatureRepresentation
  QuaternionicManifoldModelProjection
  QuaternionicManifoldProjectiveStandardConnection
  QuaternionicProjectiveStandardLie
  QuaternionicLieAlgebraProjection
  QuaternionicScalarLineTracePowerForm
  ManifoldQuaternionicConnection ManifoldQuaternionicAdjointConnection LocalChernWeilTracePowers
  QuaternionicProjectiveStandardL2
open scoped Quaternion ContDiff Manifold
noncomputable section
set_option maxHeartbeats 1000000

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

private def fixedCurvatureForm (p : M) (y : E) :
    E [⋀^Fin 2]→L[ℝ] (E →L[ℝ] E) :=
  (fixedTangentConjugation S Q p).compContinuousAlternatingMap
    (LocalConnectionForms.curvatureForm (D.form p) y)

private def fixedSymplecticCurvatureForm (p : M) (y : E) :
    E [⋀^Fin 2]→L[ℝ] (E →L[ℝ] E) :=
  (symplecticProjection S).compContinuousAlternatingMap
    (fixedCurvatureForm S Q D p y)

private def fixedScalarLineCurvatureForm (p : M) (y : E) :
    E [⋀^Fin 2]→L[ℝ] (ℍ →L[ℝ] ℍ) :=
  (scalarLineLie S).compContinuousAlternatingMap
    (fixedCurvatureForm S Q D p y)

private theorem standardCurvatureForm_blocks (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    LocalConnectionForms.curvatureForm (standardConnection S Q D p) y =
    blockCLM.compContinuousAlternatingMap
      ((fixedSymplecticCurvatureForm S Q D p y).prod
        (fixedScalarLineCurvatureForm S Q D p y)) := by
  apply ContinuousAlternatingMap.ext
  intro w
  have hw : w = ![w 0, w 1] := by
    funext t
    fin_cases t <;> rfl
  rw [hw]
  apply ContinuousLinearMap.ext
  intro z
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
  rw [LocalConnectionForms.curvatureForm_apply]
  change (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ)
    ((LocalConnection.curvature (standardConnection S Q D p) y (w 0) (w 1)) z) =
    (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ)
      ((blockCLM
        ((fixedSymplecticCurvatureForm S Q D p y) ![w 0,w 1],
         (fixedScalarLineCurvatureForm S Q D p y) ![w 0,w 1])) z)
  rw [blockCLM_apply]
  dsimp only [fixedSymplecticCurvatureForm,
    fixedScalarLineCurvatureForm, fixedCurvatureForm]
  have hsp :
      ((symplecticProjection S).compContinuousAlternatingMap
        ((fixedTangentConjugation S Q p).compContinuousAlternatingMap
          (LocalConnectionForms.curvatureForm (D.form p) y))) ![w 0,w 1] =
      symplecticProjection S (fixedTangentConjugation S Q p
        (D.curvature Q p y (w 0) (w 1))) := by
    simp [ContinuousLinearMap.compContinuousAlternatingMap,
      LocalConnectionForms.curvatureForm_apply, CompatibleTangentConnection.curvature]
  have hline :
      ((scalarLineLie S).compContinuousAlternatingMap
        ((fixedTangentConjugation S Q p).compContinuousAlternatingMap
          (LocalConnectionForms.curvatureForm (D.form p) y))) ![w 0,w 1] =
      scalarLineLie S (fixedTangentConjugation S Q p
        (D.curvature Q p y (w 0) (w 1))) := by
    simp [ContinuousLinearMap.compContinuousAlternatingMap,
      LocalConnectionForms.curvatureForm_apply, CompatibleTangentConnection.curvature]
  rw [hsp, hline]
  change (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ)
      ((LocalConnection.curvature (standardConnection S Q D p) y (w 0) (w 1)) z) =
    ((symplecticProjection S (fixedTangentConjugation S Q p
      (D.curvature Q p y (w 0) (w 1))))
        ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ) z).1,
     scalarLineLie S (fixedTangentConjugation S Q p
      (D.curvature Q p y (w 0) (w 1)))
        ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ) z).2)
  rw [standardCurvature_eq_representation S Q D p y (w 0) (w 1) hy]
  exact standardLie_blocks S _ z


/-- Every normalized trace power of the actual standard connection is the
sum of its fixed-model symplectic and scalar-line trace powers. -/
theorem standard_tracePowerForm_blocks (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (k : ℕ) :
    tracePowerForm LocalEndomorphismTrace.traceCLM
      (standardConnection S Q D p) k y =
    LocalEndomorphismTrace.traceCLM.compContinuousAlternatingMap
      (power (fixedSymplecticCurvatureForm S Q D p y) k) +
    LocalEndomorphismTrace.traceCLM.compContinuousAlternatingMap
      (power (fixedScalarLineCurvatureForm S Q D p y) k) := by
  change LocalEndomorphismTrace.traceCLM.compContinuousAlternatingMap
    (curvaturePowerForm (standardConnection S Q D p) k y) = _
  rw [← power_curvatureForm]
  rw [standardCurvatureForm_blocks S Q D p y hy]
  exact trace_power_block _ _ k

/-- The fixed model change preserves the scalar-line curvature operator
itself on valid chart points, because the named rank-three coordinates are
carried without rotation. -/
theorem fixedScalarLineCurvatureForm_eq_actual (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    fixedScalarLineCurvatureForm S Q D p y =
      scalarLineCurvatureForm Q D p y := by
  apply ContinuousAlternatingMap.ext
  intro w
  have hw : w = ![w 0, w 1] := by
    funext t
    fin_cases t <;> rfl
  rw [hw]
  have hop : scalarLineLie S (fixedTangentConjugation S Q p
      (D.curvature Q p y (w 0) (w 1))) =
    scalarLineLie (Q.reduction.Q (achart E p))
      (D.curvature Q p y (w 0) (w 1)) := by
    simp only [scalarLineLie, ContinuousLinearMap.comp_apply]
    have hr := QuaternionicFixedModelAdjointTrace.adjointRepresentation_fixedConjugation
      S (Q.reduction.Q (achart E p)) (D.curvature Q p y (w 0) (w 1))
      (ManifoldQuaternionicCurvaturePreservesSpan.tangentCurvature_preservesSpan
        Q D p y (w 0) (w 1) hy)
    change adjointRepresentation S (fixedTangentConjugation S Q p
      (D.curvature Q p y (w 0) (w 1))) =
        adjointRepresentation (Q.reduction.Q (achart E p))
          (D.curvature Q p y (w 0) (w 1)) at hr
    rw [hr]
  simpa [fixedScalarLineCurvatureForm, fixedCurvatureForm,
    scalarLineCurvatureForm, ContinuousLinearMap.compContinuousAlternatingMap,
    LocalConnectionForms.curvatureForm_apply, CompatibleTangentConnection.curvature]
    using hop


/-- The fixed symplectic block is the actual local symplectic curvature
conjugated by the constant model gauge. -/
theorem fixedSymplecticCurvatureForm_eq_conjugate (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    fixedSymplecticCurvatureForm S Q D p y =
      (fixedTangentConjugation S Q p).compContinuousAlternatingMap
        (LocalConnectionForms.curvatureForm
          (ManifoldQuaternionicConnectionSplitting.symplecticConnection Q D p) y) := by
  apply ContinuousAlternatingMap.ext
  intro w
  have hw : w = ![w 0, w 1] := by
    funext t
    fin_cases t <;> rfl
  rw [hw]
  let T := Q.reduction.Q (achart E p)
  let A := D.curvature Q p y (w 0) (w 1)
  have hcomm (a : Fin 3 → ℝ) :
      symplecticProjection T A * VectorBundleFrameTransitions.QuaternionicFrameReduction.synth T a =
      VectorBundleFrameTransitions.QuaternionicFrameReduction.synth T a *
        symplecticProjection T A := by
    rw [← ManifoldQuaternionicCurvatureProjection.symplecticCurvature_eq_projection
      Q D p y (w 0) (w 1) hy]
    exact ManifoldQuaternionicSymplecticCurvature.symplecticCurvature_commutes
      Q D p y (w 0) (w 1) hy a
  have hop := QuaternionicManifoldModelProjection.symplecticProjection_modelGauge
    S T A hcomm
  rw [← ManifoldQuaternionicCurvatureProjection.symplecticCurvature_eq_projection
    Q D p y (w 0) (w 1) hy] at hop
  simpa [fixedSymplecticCurvatureForm, fixedCurvatureForm,
    ContinuousLinearMap.compContinuousAlternatingMap,
    LocalConnectionForms.curvatureForm_apply, CompatibleTangentConnection.curvature,
] using hop

local instance : NormedRing (E →L[ℝ] E) := inferInstance
local instance : NormedAlgebra ℝ (E →L[ℝ] E) := inferInstance

/-- Constant fixed-model conjugation leaves every normalized local
symplectic curvature trace form unchanged. -/
theorem fixedSymplectic_tracePowerForm_eq_actual (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (k : ℕ) :
    LocalEndomorphismTrace.traceCLM.compContinuousAlternatingMap
      (power (fixedSymplecticCurvatureForm S Q D p y) k) =
    tracePowerForm LocalEndomorphismTrace.traceCLM
      (ManifoldQuaternionicConnectionSplitting.symplecticConnection Q D p)
      k y := by
  rw [fixedSymplecticCurvatureForm_eq_conjugate S Q D p y hy]
  let C := fixedTangentConjugation S Q p
  let F := LocalConnectionForms.curvatureForm
    (ManifoldQuaternionicConnectionSplitting.symplecticConnection Q D p) y
  apply ContinuousAlternatingMap.ext
  intro w
  have hm := congrArg (fun H : E [⋀^Fin (powerDegree k)]→L[ℝ]
      (E →L[ℝ] E) => H w)
    (map_power C (fixedTangentConjugation_mul S Q p) F k)
  change C (power F k w) = power (C.compContinuousAlternatingMap F) k w at hm
  change LocalEndomorphismTrace.traceCLM (power (C.compContinuousAlternatingMap F) k w) =
    LocalEndomorphismTrace.traceCLM
      (curvaturePowerForm
        (ManifoldQuaternionicConnectionSplitting.symplecticConnection Q D p) k y w)
  rw [← hm, ← power_curvatureForm]
  exact QuaternionicFixedModelAdjointTrace.traceCLM_fixedConjugation
    S (Q.reduction.Q (achart E p)) (power F k w)

/-- Exact all-degree splitting of actual standard Chern--Weil trace forms
into the actual symplectic and scalar quaternionic-line connections. -/
theorem standard_tracePowerForm_actual_blocks (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (k : ℕ) :
    tracePowerForm LocalEndomorphismTrace.traceCLM
      (standardConnection S Q D p) k y =
    tracePowerForm LocalEndomorphismTrace.traceCLM
      (ManifoldQuaternionicConnectionSplitting.symplecticConnection Q D p) k y +
    LocalEndomorphismTrace.traceCLM.compContinuousAlternatingMap
      (power (scalarLineCurvatureForm Q D p y) k) := by
  rw [standard_tracePowerForm_blocks S Q D p y hy k,
    fixedSymplectic_tracePowerForm_eq_actual S Q D p y hy k,
    fixedScalarLineCurvatureForm_eq_actual S Q D p y hy]

/-- At every positive even curvature power, the standard trace form is
the symplectic trace plus the precisely scaled induced rank-three trace. -/
theorem standard_even_tracePowerForm_rankThree (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (j : ℕ) (hj : 0 < j) :
    (4 : ℝ) ^ j • tracePowerForm LocalEndomorphismTrace.traceCLM
      (standardConnection S Q D p) (2 * j - 1) y =
    (4 : ℝ) ^ j • tracePowerForm LocalEndomorphismTrace.traceCLM
      (ManifoldQuaternionicConnectionSplitting.symplecticConnection Q D p)
      (2 * j - 1) y +
    (2 : ℝ) • tracePowerForm LocalEndomorphismTrace.traceCLM
      (inducedForm Q D p) (2 * j - 1) y := by
  rw [standard_tracePowerForm_actual_blocks S Q D p y hy (2 * j - 1),
    smul_add]
  congr 1
  exact QuaternionicActualScalarAdjointTracePowers.scalarLine_induced_tracePower_ratio
    Q D p y hy j hj

end
end QuaternionicSymmetry.QuaternionicStandardTracePowerBlocks
