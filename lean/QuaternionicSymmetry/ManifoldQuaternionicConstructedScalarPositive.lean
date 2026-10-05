import QuaternionicSymmetry.ManifoldQuaternionicConstructedCurvature
import QuaternionicSymmetry.QuaternionicImmersionScalarCoefficient
import QuaternionicSymmetry.ManifoldQuaternionicKSWEq38Derived

/-! Positivity of the actual scalar contraction for the explicitly
constructed quaternionic submanifold connection. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicConstructedScalarPositive
open ManifoldQuaternionicInducedConnectionConstruction ManifoldQuaternionicConstructedCurvature
open ManifoldQuaternionicConnection ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicImmersionCharts ManifoldQuaternionicInducedTotalGeodesy
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicKSWScalarInput
open ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicKSWEq38Derived
open ManifoldQuaternionicFixedCurvatureAlgebra ManifoldQuaternionicKSWEinsteinAdapted
open QuaternionicManifoldFixedNormalizer QuaternionicAlgebraicKSWDecomposition
open QuaternionicImmersionScalarCoefficient
open scoped Manifold ContDiff Topology
noncomputable section
variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

private theorem fixed_decomposition (S : QuaternionicStructure E)
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞)) (D : CompatibleTangentConnection Q)
    (hn : 2 ≤ S.quaternionicDimension) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    ∃ W, HyperWeylFiber S W ∧ ∀ u v, curvatureBilinear S Q D p y hy u v =
      scalarRatio S Q D p y hy • QuaternionicKSWModelRicci.scalarModelR0 S u v + W u v := by
  obtain ⟨lam,W,hW,he⟩ := QuaternionicAlgebraicKSWDecomposition.decomposition S
    (curvatureBilinear S Q D p y hy) hn
    (skew_first S Q D p y hy) (skew_last S Q D p y hy)
    (first_bianchi S Q D p y hy) (symplectic_commutes S Q D p y hy)
  refine ⟨W,hW,?_⟩
  rw [scalarRatio_eq_of_decomposition S Q D p y hy lam W hW he]
  exact he

variable {P : PositiveQuaternionicKahlerGeometry (E := E) (M := M)}
  {Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,F)) (M := N) (n := ∞)} {ι : N → M}
  (L : LocalFrames P Q ι) (hι : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)

theorem scalarRatio_eq (p : N) (y : F)
    (hy : y ∈ (extChartAt 𝓘(ℝ,F) p).target)
    (hn : 2 ≤ (P.tangent.reduction.Q (achart E (L.ambientPoint p))).quaternionicDimension)
    (hm : 2 ≤ (Q.reduction.Q (achart F p)).quaternionicDimension) :
    scalarRatio (Q.reduction.Q (achart F p)) Q (connection L hι) p y hy =
      scalarRatio (P.tangent.reduction.Q (achart E (L.ambientPoint p)))
        P.tangent P.connection (L.ambientPoint p) (localBaseMap ι p (L.ambientPoint p) y)
        ((extChartAt 𝓘(ℝ,E) (L.ambientPoint p)).map_source (L.target p y hy)) := by
  let S := Q.reduction.Q (achart F p)
  let T := P.tangent.reduction.Q (achart E (L.ambientPoint p))
  let gs := modelGauge S S
  let gt := modelGauge T T
  let B : F →L[ℝ] E := gt.symm.toContinuousLinearEquiv.toContinuousLinearMap |>.comp
    ((L.embedding p y).comp gs.toContinuousLinearEquiv.toContinuousLinearMap)
  let f := localBaseMap (E := E) (F := F) ι p (L.ambientPoint p)
  have hfy := (extChartAt 𝓘(ℝ,E) (L.ambientPoint p)).map_source (L.target p y hy)
  have hB (v w : F) : inner ℝ (B v) (B w) = inner ℝ v w := by
    change inner ℝ (gt.symm (L.embedding p y (gs v))) (gt.symm (L.embedding p y (gs w))) = _
    rw [gt.symm.inner_map_map,L.inner_embedding p y hy,gs.inner_map_map]
  have hI (v : F) : B (S.I v) = T.I (B v) := by
    apply gt.injective
    change gt (gt.symm (L.embedding p y (gs (S.I v)))) = gt (T.I (B v))
    rw [gt.apply_symm_apply,modelGauge_I,modelGauge_I,L.intertwines_I p y hy]
    congr 1
    exact (gt.apply_symm_apply _).symm
  have hJ (v : F) : B (S.J v) = T.J (B v) := by
    apply gt.injective
    change gt (gt.symm (L.embedding p y (gs (S.J v)))) = gt (T.J (B v))
    rw [gt.apply_symm_apply,modelGauge_J,modelGauge_J,L.intertwines_J p y hy]
    congr 1
    exact (gt.apply_symm_apply _).symm
  obtain ⟨W,hW,he⟩ := fixed_decomposition S Q (connection L hι) hm p y hy
  obtain ⟨V,hV,he'⟩ := fixed_decomposition T P.tangent P.connection hn (L.ambientPoint p) (f y) hfy
  apply coefficient_eq S T B hB hI hJ _ W _ V _ _ hW hV he he'
  intro u v w
  simp only [curvatureBilinear_apply,fixedCurvature_apply_adapted]
  change gt.symm (adaptedCurvature P.tangent P.connection (L.ambientPoint p) (f y) hfy
      (gt (B u)) (gt (B v)) (gt (B w))) =
    gt.symm (L.embedding p y (gs (gs.symm (adaptedCurvature Q (connection L hι) p y hy
      (gs u) (gs v) (gs w)))))
  simp only [B,ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe,gt.apply_symm_apply,gs.apply_symm_apply]
  exact congrArg gt.symm (adaptedCurvature_embedding L hι p y (gs u) (gs v) (gs w) hy)

theorem scalar_pos (hn : 8 ≤ Module.finrank ℝ E) (hm : 8 ≤ Module.finrank ℝ F)
    (p : N) (y : F) (hy : y ∈ (extChartAt 𝓘(ℝ,F) p).target) :
    0 < localScalarCurvature Q (connection L hι) p y hy := by
  let S := Q.reduction.Q (achart F p)
  let T := P.tangent.reduction.Q (achart E (L.ambientPoint p))
  have hs : 2 ≤ S.quaternionicDimension := by have h := S.real_finrank; omega
  have ht : 2 ≤ T.quaternionicDimension := by have h := T.real_finrank; omega
  have hs' : (0 : ℝ) < S.quaternionicDimension := by exact_mod_cast (by omega : 0 < S.quaternionicDimension)
  have ht' : (0 : ℝ) < T.quaternionicDimension := by exact_mod_cast (by omega : 0 < T.quaternionicDimension)
  have hratio : 0 < scalarRatio S Q (connection L hι) p y hy := by
    rw [scalarRatio_eq L hι p y hy ht hs]
    exact div_pos (P.scalar_pos _ _ _) (by change 0 < 16 * (T.quaternionicDimension : ℝ) * (_ + 2); positivity)
  change 0 < localScalarCurvature Q (connection L hι) p y hy /
    (16 * (S.quaternionicDimension : ℝ) * ((S.quaternionicDimension : ℝ) + 2)) at hratio
  rcases div_pos_iff.mp hratio with h | h
  · exact h.1
  · have hd : 0 < 16 * (S.quaternionicDimension : ℝ) * ((S.quaternionicDimension : ℝ) + 2) := by positivity
    linarith [h.2]

end
end QuaternionicSymmetry.ManifoldQuaternionicConstructedScalarPositive
