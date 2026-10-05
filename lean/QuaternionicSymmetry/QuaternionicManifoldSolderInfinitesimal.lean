import QuaternionicSymmetry.QuaternionicStandardSolderInfinitesimal
import QuaternionicSymmetry.QuaternionicManifoldFixedConnectionOverlap
import QuaternionicSymmetry.QuaternionicManifoldStandardLieComparison
import QuaternionicSymmetry.QuaternionicManifoldStandardSolder

/-! The actual manifold standard connection acts infinitesimally on the
standard solder by the fixed-model tangent connection. -/
namespace QuaternionicSymmetry.QuaternionicManifoldSolderInfinitesimal
open QuaternionicStandardSolderInfinitesimal
open QuaternionicManifoldFixedConnectionOverlap
open QuaternionicManifoldStandardLieComparison
open QuaternionicManifoldStandardSolder
open QuaternionicManifoldFixedSolder
open QuaternionicProjectiveStandardLie
open QuaternionicManifoldProjectiveStandardConnection
open QuaternionicLieAlgebraProjection
open QuaternionicInfinitesimalSplitting
open ManifoldQuaternionicConnection
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff Quaternion
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (QuaternionicProjectiveStandardL2.StandardSpace (E := E)) := inferInstance
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

omit [Nontrivial E] in
private theorem fixedForm_skew (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v w : E) :
    inner ℝ (fixedForm S Q D p y u v) w +
      inner ℝ v (fixedForm S Q D p y u w) = 0 := by
  let g := QuaternionicManifoldFixedNormalizer.modelGauge S
    (Q.reduction.Q (achart E p))
  have h := D.metric p y u (g v) (g w) hy
  have h1 : inner ℝ (fixedForm S Q D p y u v) w =
      inner ℝ ((D.form p y u) (g v)) (g w) := by
    change inner ℝ (g.symm ((D.form p y u) (g v))) w = _
    rw [← g.inner_map_map, g.apply_symm_apply]
  have h2 : inner ℝ v (fixedForm S Q D p y u w) =
      inner ℝ (g v) ((D.form p y u) (g w)) := by
    change inner ℝ v (g.symm ((D.form p y u) (g w))) = _
    rw [← g.inner_map_map, g.apply_symm_apply]
  rw [h1, h2]
  exact h

private theorem fixedForm_symplectic_skew (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v w : E) :
    inner ℝ ((symplecticProjection S (fixedForm S Q D p y u)) v) w +
      inner ℝ v ((symplecticProjection S (fixedForm S Q D p y u)) w) = 0 := by
  let A := fixedForm S Q D p y u
  have hs := scalarPart_skew S
    (fun i j => ManifoldQuaternionicAdjointConnection.adjointRepresentation S A
      (Pi.basisFun ℝ (Fin 3) j) i) v w
  have ha := fixedForm_skew S Q D p y u hy v w
  change inner ℝ ((A - scalarProjection S A) v) w +
    inner ℝ v ((A - scalarProjection S A) w) = 0
  rw [scalarProjection_apply]
  simp only [ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
  linarith

private theorem fixedForm_symplectic_commutes_I (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v : E) :
    (symplecticProjection S (fixedForm S Q D p y u)) (S.I v) =
      S.I ((symplecticProjection S (fixedForm S Q D p y u)) v) := by
  have hc := fixedForm_symplectic_commutes S Q D p y u hy
    (Pi.basisFun ℝ (Fin 3) 0)
  have hv := congrArg (fun F : E →L[ℝ] E => F v) hc
  simpa only [ManifoldQuaternionicRankThreeOrthogonal.synth_basis,
    VectorBundleFrameTransitions.quaternionicGenerator] using hv

private theorem fixedForm_symplectic_commutes_J (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (v : E) :
    (symplecticProjection S (fixedForm S Q D p y u)) (S.J v) =
      S.J ((symplecticProjection S (fixedForm S Q D p y u)) v) := by
  have hc := fixedForm_symplectic_commutes S Q D p y u hy
    (Pi.basisFun ℝ (Fin 3) 1)
  have hv := congrArg (fun F : E →L[ℝ] E => F v) hc
  simpa only [ManifoldQuaternionicRankThreeOrthogonal.synth_basis,
    VectorBundleFrameTransitions.quaternionicGenerator] using hv

set_option maxHeartbeats 800000 in
theorem standardConnection_commutator_solder (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    standardConnection S Q D p y u *
        QuaternionicStandardSolderOperator.solderOperator S v -
      QuaternionicStandardSolderOperator.solderOperator S v *
        standardConnection S Q D p y u =
      QuaternionicStandardSolderOperator.solderOperator S
        (fixedForm S Q D p y u v) := by
  rw [standardConnection_eq_standardLie S Q D p y u hy,
    ← fixedForm_apply S Q D p y u]
  apply standardLie_commutator_solder S
  · exact fixedForm_symplectic_commutes_I S Q D p y u hy
  · exact fixedForm_symplectic_commutes_J S Q D p y u hy
  · exact fixedForm_symplectic_skew S Q D p y u hy

end
end QuaternionicSymmetry.QuaternionicManifoldSolderInfinitesimal
