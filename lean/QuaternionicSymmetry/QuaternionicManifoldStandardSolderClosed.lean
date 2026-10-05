import QuaternionicSymmetry.QuaternionicManifoldSolderInfinitesimal
import QuaternionicSymmetry.QuaternionicManifoldCorrectedConnection

/-! Torsion freeness of the tangent connection makes the genuine standard
solder covariantly closed. -/
namespace QuaternionicSymmetry.QuaternionicManifoldStandardSolderClosed
open QuaternionicManifoldSolderInfinitesimal
open QuaternionicManifoldFixedSolder
open QuaternionicManifoldStandardSolder
open QuaternionicManifoldFixedConnectionOverlap
open QuaternionicManifoldProjectiveStandardConnection
open QuaternionicStandardSolderOperator
open ManifoldQuaternionicConnection
open scoped Manifold ContDiff Quaternion
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (QuaternionicProjectiveStandardL2.StandardSpace (E := E)) := inferInstance
local instance : NormedSpace ℝ
    (QuaternionicProjectiveStandardL2.StandardSpace (E := E) →L[ℝ]
      QuaternionicProjectiveStandardL2.StandardSpace (E := E)) := inferInstance
local instance : NormedAddCommGroup
    (E →L[ℝ] (QuaternionicProjectiveStandardL2.StandardSpace (E := E) →L[ℝ]
      QuaternionicProjectiveStandardL2.StandardSpace (E := E))) := inferInstance
local instance : NormedSpace ℝ
    (E →L[ℝ] (QuaternionicProjectiveStandardL2.StandardSpace (E := E) →L[ℝ]
      QuaternionicProjectiveStandardL2.StandardSpace (E := E))) := inferInstance
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

omit [Nontrivial E] in
private theorem fderiv_fixedSolder (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    fderiv ℝ (fixedSolder S Q p) y u v =
      (QuaternionicManifoldFixedNormalizer.modelGauge S
        (Q.reduction.Q (achart E p))).symm
          (fderiv ℝ (solder Q p) y u v) := by
  let g := QuaternionicManifoldFixedNormalizer.modelGauge S
    (Q.reduction.Q (achart E p))
  have hs : DifferentiableAt ℝ (solder Q p) y :=
    (((ManifoldTwistorGlobalAlmostComplex.frameTo_chart_smooth Q p).congr
      (fun z hz => solder_eq_toFrame Q p z hz)).differentiableOn
        (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)
  let L : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    ContinuousLinearMap.compL ℝ E E E g.symm.toContinuousLinearMap
  have hd : fderiv ℝ (fun z => L (solder Q p z)) y =
      L.comp (fderiv ℝ (solder Q p) y) :=
    (L.hasFDerivAt.comp y hs.hasFDerivAt).fderiv
  have he := congrArg (fun F : E →L[ℝ] (E →L[ℝ] E) => F u v) hd
  simpa only [fixedSolder, L, ContinuousLinearMap.comp_apply] using he

set_option maxHeartbeats 800000 in
omit [Nontrivial E] in
private theorem fderiv_standardSolder (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    fderiv ℝ (standardSolder S Q p) y u v =
      solderOperator S (fderiv ℝ (fixedSolder S Q p) y u v) := by
  have hs : DifferentiableAt ℝ (fixedSolder S Q p) y :=
    ((fixedSolder_smooth S Q p).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)
  let L : (E →L[ℝ] E) →L[ℝ]
      (E →L[ℝ] (QuaternionicProjectiveStandardL2.StandardSpace (E := E) →L[ℝ]
        QuaternionicProjectiveStandardL2.StandardSpace (E := E))) :=
    ContinuousLinearMap.compL ℝ E E _ (solderOperator S)
  have hd : fderiv ℝ (fun z => L (fixedSolder S Q p z)) y =
      L.comp (fderiv ℝ (fixedSolder S Q p) y) :=
    (L.hasFDerivAt.comp y hs.hasFDerivAt).fderiv
  have he := congrArg (fun F : E →L[ℝ] (E →L[ℝ]
    (QuaternionicProjectiveStandardL2.StandardSpace (E := E) →L[ℝ]
      QuaternionicProjectiveStandardL2.StandardSpace (E := E))) => F u v) hd
  simpa only [standardSolder, L, ContinuousLinearMap.comp_apply] using he

set_option maxHeartbeats 800000 in
theorem standardSolder_covariantly_closed (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    LocalConnection.covariantDerivative
      (standardConnection S Q D p) (standardSolder S Q p) y = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  have ht := D.torsion p y u v hy
  have hf : fderiv ℝ (fixedSolder S Q p) y u v -
      fderiv ℝ (fixedSolder S Q p) y v u +
      fixedForm S Q D p y u (fixedSolder S Q p y v) -
      fixedForm S Q D p y v (fixedSolder S Q p y u) = 0 := by
    rw [fderiv_fixedSolder S Q p y u v hy,
      fderiv_fixedSolder S Q p y v u hy]
    let g := QuaternionicManifoldFixedNormalizer.modelGauge S
      (Q.reduction.Q (achart E p))
    have hc := congrArg g.symm ht
    change g.symm (fderiv ℝ (solder Q p) y u v) -
      g.symm (fderiv ℝ (solder Q p) y v u) +
      g.symm (D.form p y u (g (g.symm (solder Q p y v)))) -
      g.symm (D.form p y v (g (g.symm (solder Q p y u)))) = 0
    rw [g.apply_symm_apply, g.apply_symm_apply]
    simpa only [map_add, map_sub, map_zero] using hc
  have hc1 := standardConnection_commutator_solder S Q D p y u
    (fixedSolder S Q p y v) hy
  have hc2 := standardConnection_commutator_solder S Q D p y v
    (fixedSolder S Q p y u) hy
  have hzero := congrArg (solderOperator S) hf
  rw [LocalConnection.covariantDerivative_apply,
    fderiv_standardSolder S Q p y u v hy,
    fderiv_standardSolder S Q p y v u hy]
  change
    solderOperator S (fderiv ℝ (fixedSolder S Q p) y u v) -
      solderOperator S (fderiv ℝ (fixedSolder S Q p) y v u) +
      standardConnection S Q D p y u *
        solderOperator S (fixedSolder S Q p y v) -
      standardConnection S Q D p y v *
        solderOperator S (fixedSolder S Q p y u) +
      solderOperator S (fixedSolder S Q p y u) *
        standardConnection S Q D p y v -
      solderOperator S (fixedSolder S Q p y v) *
        standardConnection S Q D p y u = 0
  calc
    _ = solderOperator S (fderiv ℝ (fixedSolder S Q p) y u v) -
          solderOperator S (fderiv ℝ (fixedSolder S Q p) y v u) +
        (standardConnection S Q D p y u *
          solderOperator S (fixedSolder S Q p y v) -
          solderOperator S (fixedSolder S Q p y v) *
            standardConnection S Q D p y u) -
        (standardConnection S Q D p y v *
          solderOperator S (fixedSolder S Q p y u) -
          solderOperator S (fixedSolder S Q p y u) *
            standardConnection S Q D p y v) := by noncomm_ring
    _ = 0 := by
      rw [hc1, hc2]
      simpa only [map_sub, map_add, map_zero] using hzero

end
end QuaternionicSymmetry.QuaternionicManifoldStandardSolderClosed
