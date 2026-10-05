import QuaternionicSymmetry.ManifoldMetricTorsionConnectionGluing
import QuaternionicSymmetry.ManifoldQuaternionicImmersionCharts
import QuaternionicSymmetry.QuaternionicProjectedSecondFundamental

/-! Construct the induced connection from smooth local orthonormal
immersion frames. All connection equations, including overlap, are proved. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedConnectionConstruction
open ManifoldQuaternionicConnection ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicCoordinateConnection
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicImmersionCharts
open ManifoldQuaternionicInducedTotalGeodesy ManifoldMetricTorsionConnectionGluing
open Filter
open scoped Manifold ContDiff Topology
noncomputable section
variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,F)) (M := N) (n := ∞)) (ι : N → M)

structure LocalFrames where
  ambientPoint : N → M
  target : ∀ p y, y ∈ (extChartAt 𝓘(ℝ,F) p).target →
    ι ((extChartAt 𝓘(ℝ,F) p).symm y) ∈ (extChartAt 𝓘(ℝ,E) (ambientPoint p)).source
  embedding : N → F → F →L[ℝ] E
  smooth_embedding : ∀ p, ContDiffOn ℝ ∞ (embedding p) (extChartAt 𝓘(ℝ,F) p).target
  inner_embedding : ∀ p y, y ∈ (extChartAt 𝓘(ℝ,F) p).target →
    ∀ v w, inner ℝ (embedding p y v) (embedding p y w) = inner ℝ v w
  intertwines_I : ∀ p y, y ∈ (extChartAt 𝓘(ℝ,F) p).target → ∀ v,
    embedding p y ((Q.reduction.Q (achart F p)).I v) =
      (P.tangent.reduction.Q (achart E (ambientPoint p))).I (embedding p y v)
  intertwines_J : ∀ p y, y ∈ (extChartAt 𝓘(ℝ,F) p).target → ∀ v,
    embedding p y ((Q.reduction.Q (achart F p)).J v) =
      (P.tangent.reduction.Q (achart E (ambientPoint p))).J (embedding p y v)
  solder_eq : ∀ p y, y ∈ (extChartAt 𝓘(ℝ,F) p).target →
    (embedding p y).comp (solder Q p y) =
      LocalSolderPullback.solder (solder P.tangent (ambientPoint p))
        (localBaseMap (E := E) (F := F) ι p (ambientPoint p)) y

variable {P Q ι} (L : LocalFrames P Q ι)

def ambientForm (p : N) (y : F) : F →L[ℝ] E →L[ℝ] E :=
  (P.connection.form (L.ambientPoint p) (localBaseMap ι p (L.ambientPoint p) y)).comp
    (fderiv ℝ (localBaseMap (E := E) (F := F) ι p (L.ambientPoint p)) y)

def form (p : N) : F → F →L[ℝ] F →L[ℝ] F :=
  QuaternionicProjectedConnection.form (ambientForm L p) (L.embedding p)

theorem ambientForm_smooth (hι : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι) (p : N) :
    ContDiffOn ℝ ∞ (ambientForm L p) (extChartAt 𝓘(ℝ,F) p).target := by
  intro y hy
  have hf := localBaseMap_contDiffAt ι hι p (L.ambientPoint p) y ⟨hy,L.target p y hy⟩
  have hfy := (extChartAt 𝓘(ℝ,E) (L.ambientPoint p)).map_source (L.target p y hy)
  have hΓ := (P.connection.smooth_form (L.ambientPoint p)).contDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) (L.ambientPoint p)).mem_nhds hfy)
  exact ((hΓ.comp y hf).clm_comp (hf.fderiv_right (m := ∞) (by simp))).contDiffWithinAt

theorem form_smooth (hι : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι) (p : N) :
    ContDiffOn ℝ ∞ (form L p) (extChartAt 𝓘(ℝ,F) p).target :=
  QuaternionicProjectedConnection.smooth_form _ _ _ (isOpen_extChartAt_target p)
    (ambientForm_smooth L hι p) (L.smooth_embedding p)

theorem form_metric (p : N) (y u v w : F) (hy : y ∈ (extChartAt 𝓘(ℝ,F) p).target) :
    inner ℝ (form L p y u v) w + inner ℝ v (form L p y u w) = 0 := by
  have hn := (isOpen_extChartAt_target (I := 𝓘(ℝ,F)) p).mem_nhds hy
  apply QuaternionicProjectedConnection.metric (ambientForm L p) (L.embedding p) y
    (((L.smooth_embedding p).contDiffAt hn).differentiableAt (by simp))
    (Filter.Eventually.mono hn (fun z hz => L.inner_embedding p z hz))
  intro a b c
  exact P.connection.metric (L.ambientPoint p) _ _ b c
    ((extChartAt 𝓘(ℝ,E) (L.ambientPoint p)).map_source (L.target p y hy))

theorem form_quaternionic (p : N) (y u : F) (t : Fin 3)
    (hy : y ∈ (extChartAt 𝓘(ℝ,F) p).target) :
    (form L p y u).comp (VectorBundleFrameTransitions.quaternionicGenerator (Q.reduction.Q (achart F p)) t) -
    (VectorBundleFrameTransitions.quaternionicGenerator (Q.reduction.Q (achart F p)) t).comp (form L p y u) ∈
      VectorBundleFrameTransitions.quaternionicSpan (Q.reduction.Q (achart F p)) := by
  have hn := (isOpen_extChartAt_target (I := 𝓘(ℝ,F)) p).mem_nhds hy
  apply QuaternionicProjectedConnection.quaternionic (Q.reduction.Q (achart F p))
    (P.tangent.reduction.Q (achart E (L.ambientPoint p))) (ambientForm L p) (L.embedding p) y
    (((L.smooth_embedding p).contDiffAt hn).differentiableAt (by simp)) (L.inner_embedding p y hy)
    (Filter.Eventually.mono hn (fun z hz => L.intertwines_I p z hz))
    (Filter.Eventually.mono hn (fun z hz => L.intertwines_J p z hz))
  intro a k
  exact P.connection.quaternionic (L.ambientPoint p) _ _ k
    ((extChartAt 𝓘(ℝ,E) (L.ambientPoint p)).map_source (L.target p y hy))

theorem form_torsion (hι : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
    (p : N) (y u v : F) (hy : y ∈ (extChartAt 𝓘(ℝ,F) p).target) :
    fderiv ℝ (solder Q p) y u v - fderiv ℝ (solder Q p) y v u +
      form L p y u (solder Q p y v) - form L p y v (solder Q p y u) = 0 := by
  let f := localBaseMap (E := E) (F := F) ι p (L.ambientPoint p)
  let A := LocalSolderPullback.solder (solder P.tangent (L.ambientPoint p)) f
  have hn := (isOpen_extChartAt_target (I := 𝓘(ℝ,F)) p).mem_nhds hy
  have hf := (localBaseMap_contDiffAt ι hι p (L.ambientPoint p) y ⟨hy,L.target p y hy⟩).of_le
    (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast)
  have hfy := (extChartAt 𝓘(ℝ,E) (L.ambientPoint p)).map_source (L.target p y hy)
  have ht := (solder_contDiffAt P.tangent (L.ambientPoint p) (f y) hfy).differentiableAt (by simp)
  have hA : A =ᶠ[𝓝 y] fun z => (L.embedding p z).comp (solder Q p z) :=
    Filter.Eventually.mono hn (fun z hz => (L.solder_eq p z hz).symm)
  exact QuaternionicProjectedConnectionTorsion.torsion (ambientForm L p) (L.embedding p)
    (solder Q p) A y (((L.smooth_embedding p).contDiffAt hn).differentiableAt (by simp))
    ((solder_contDiffAt Q p y hy).differentiableAt (by simp)) (L.inner_embedding p y hy) hA
    (LocalSolderPullback.torsion (solder P.tangent (L.ambientPoint p)) f y
      (P.connection.form (L.ambientPoint p) (f y)) ht hf
      (fun a b => P.connection.torsion (L.ambientPoint p) (f y) a b hfy)) u v

def connection (hι : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι) : CompatibleTangentConnection Q :=
  ofLocalForms Q (form L) (form_smooth L hι) (form_metric L) (form_quaternionic L) (form_torsion L hι)

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedConnectionConstruction
