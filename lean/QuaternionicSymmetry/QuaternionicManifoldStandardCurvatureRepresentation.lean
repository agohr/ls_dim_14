import QuaternionicSymmetry.QuaternionicManifoldStandardLieComparison
import QuaternionicSymmetry.QuaternionicProjectiveStandardLieBracket
import QuaternionicSymmetry.LocalConnectionLieMap

/-! Curvature of the actual local standard connection is the infinitesimal
standard representation of actual tangent curvature. -/
namespace QuaternionicSymmetry.QuaternionicManifoldStandardCurvatureRepresentation
open QuaternionicManifoldStandardLieComparison QuaternionicManifoldModelProjection
  QuaternionicManifoldProjectiveStandardConnection QuaternionicProjectiveStandardLie
  QuaternionicProjectiveStandardLieBracket QuaternionicLieAlgebraProjection
  QuaternionicIsometryNormalizer ManifoldQuaternionicConnectionSplitting
  ManifoldQuaternionicConnection QuaternionicProjectiveStandardL2
  LocalConnectionLieMap VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped ContDiff Manifold Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance
local instance : NormedRing
    (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) := inferInstance
local instance : NormedAlgebra ℝ
    (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) := inferInstance
local instance : NormedSpace ℝ
    (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) := inferInstance
local instance : NormedSpace ℝ
    (E →L[ℝ] (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E))) := inferInstance
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞)) (D : CompatibleTangentConnection Q)

theorem fixed_symplecticConnection_commutes (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) (a : Fin 3 → ℝ) :
    symplecticProjection S (fixedTangentConjugation S Q p (D.form p y u)) * synth S a =
      synth S a * symplecticProjection S (fixedTangentConjugation S Q p (D.form p y u)) := by
  let T := Q.reduction.Q (achart E p)
  have hp := symplecticProjection_modelGauge S T (D.form p y u)
    (fun b => symplecticConnection_commutes Q D p y u hy b)
  have hc := modelGauge_symm_conjugation_commutes S T _
    (fun b => symplecticConnection_commutes Q D p y u hy b) a
  exact (congrArg (fun B => B * synth S a) hp).trans
    (hc.trans (congrArg (fun B => synth S a * B) hp.symm))

omit [Nontrivial E] in
theorem fixedTangentConjugation_mul (p : M) (A B : E →L[ℝ] E) :
    fixedTangentConjugation S Q p (A * B) =
      fixedTangentConjugation S Q p A * fixedTangentConjugation S Q p B := by
  exact conjugation_product
    (QuaternionicManifoldFixedNormalizer.modelGauge S (Q.reduction.Q (achart E p))).symm A B

theorem standardLie_fixed_bracket (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    standardLie S (fixedTangentConjugation S Q p
      (D.form p y u * D.form p y v - D.form p y v * D.form p y u)) =
    standardLie S (fixedTangentConjugation S Q p (D.form p y u)) *
      standardLie S (fixedTangentConjugation S Q p (D.form p y v)) -
    standardLie S (fixedTangentConjugation S Q p (D.form p y v)) *
      standardLie S (fixedTangentConjugation S Q p (D.form p y u)) := by
  rw [map_sub, fixedTangentConjugation_mul, fixedTangentConjugation_mul]
  exact standardLie_bracket S _ _
    (fixed_symplecticConnection_commutes S Q D p y u hy)
    (fixed_symplecticConnection_commutes S Q D p y v hy)

set_option maxHeartbeats 800000 in
theorem standardCurvature_eq_representation (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    LocalConnection.curvature (standardConnection S Q D p) y u v =
      standardLie S (fixedTangentConjugation S Q p (D.curvature Q p y u v)) := by
  let C : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) := fixedTangentConjugation S Q p
  let L : (E →L[ℝ] E) →L[ℝ]
      (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) := (standardLie S).comp C
  have he : standardConnection S Q D p =ᶠ[𝓝 y] mapForm L (D.form p) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy] with z hz
    apply ContinuousLinearMap.ext
    intro w
    exact standardConnection_eq_standardLie S Q D p z w hz
  have hd : DifferentiableAt ℝ (D.form p) y :=
    ((D.smooth_form p).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy)
  rw [curvature_congr_germ _ _ y he]
  dsimp only [L, C, CompatibleTangentConnection.curvature]
  apply curvature_map_composite (fixedTangentConjugation S Q p) (standardLie S)
    (D.form p) y u v hd
  exact standardLie_fixed_bracket S Q D p y u v hy

end
end QuaternionicSymmetry.QuaternionicManifoldStandardCurvatureRepresentation
