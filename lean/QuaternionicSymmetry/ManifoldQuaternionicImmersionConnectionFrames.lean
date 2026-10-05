import QuaternionicSymmetry.ManifoldQuaternionicImmersionMetricIdentification
import QuaternionicSymmetry.ManifoldQuaternionicInducedConnectionConstruction

/-! The local Gram-Schmidt gauges supply every hypothesis of the induced
connection constructor on the compatible refined atlas. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicImmersionConnectionFrames
open ManifoldQuaternionicImmersionLocalGauge ManifoldQuaternionicImmersionGaugeAtlas
open ManifoldQuaternionicImmersionRange ManifoldQuaternionicImmersionHermitianTangent
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicConnection
open ManifoldQuaternionicInducedConnectionConstruction ManifoldQuaternionicImmersionCharts
open ManifoldQuaternionicInducedTotalGeodesy ManifoldChartRefinementSmoothness
open scoped Manifold ContDiff Topology
noncomputable section
variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [old : ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable {P : PositiveQuaternionicKahlerGeometry (E := E) (M := M)} {ι : N → M}
  (G : ∀ c, LocalGauge (F := F) P ι c)

def localFrames
    (hι : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x)) :
    letI := charts G; letI := charts_manifold (old := old) G
    LocalFrames P (tangent (old := old) G) ι := by
  let i : N → Index G := fun p => by
    letI := charts G
    exact achart F p
  let c : N → N := fun p => chartCenter G (i p)
  let a : N → M := fun p => ι (c p)
  let W : N → Set N := fun p => (G (c p)).domain
  let b : N → N → F →L[ℝ] E := fun p => (G (c p)).embedding
  let t : N → N → F →L[ℝ] F := fun p => (G (c p)).toFrame
  let D : N → N → F →L[ℝ] E := fun p =>
    ManifoldQuaternionicInducedLocalIntertwining.localDerivative ι (achart F (c p)) (achart E (a p))
  let S : N → QuaternionicStructure F := fun p => (G (c p)).Q
  have hWopen (p : N) : IsOpen (W p) := (G (c p)).isOpen_domain
  have hW (p x : N) (hx : x ∈ (i p).1.source) : x ∈ W p := mem_domain G (i p) x hx
  have htarget (p x : N) (hx : x ∈ W p) : ι x ∈ (chartAt E (a p)).source := (G (c p)).target hx
  have hbs (p : N) : letI := charts G
      ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] E) ∞ (b p) (W p) :=
    (contMDiffOn_restrictedCharts_iff (fun c => (G c).domain)
      (fun c => (G c).isOpen_domain) (fun c => (G c).mem_domain) _ _).mpr (G (c p)).smooth_embedding
  have hinner (p x : N) (hx : x ∈ W p) := (G (c p)).inner_embedding x hx
  have hi (p x : N) (hx : x ∈ W p) : ∀ v, b p x ((S p).I v) =
      (P.tangent.reduction.Q (achart E (a p))).I (b p x v) := (G (c p)).intertwines_I x hx
  have hj (p x : N) (hx : x ∈ W p) : ∀ v, b p x ((S p).J v) =
      (P.tangent.reduction.Q (achart E (a p))).J (b p x v) := (G (c p)).intertwines_J x hx
  have hinc (p x : N) (hx : x ∈ W p) (v : F) :
      b p x (t p x v) = P.tangent.frames.toFrame (achart E (a p)) (ι x) (D p x v) :=
    (G (c p)).inclusion x hx v
  have hD (p x : N) : letI := charts G; letI := charts_manifold (old := old) G
      ManifoldQuaternionicInducedLocalIntertwining.localDerivative ι (i p) (achart E (a p)) x = D p x :=
    localDerivative_refined_eq G hι (i p) (achart E (a p)) x
  have hNew := (compatibleAtlas G hι hinj).inclusion_smooth
  letI := charts G
  letI := charts_manifold (old := old) G
  have hx (p : N) (y : F) (hy : y ∈ (extChartAt 𝓘(ℝ,F) p).target) :
      (extChartAt 𝓘(ℝ,F) p).symm y ∈ W p := by
    apply hW
    simpa only [i,coe_achart,← extChartAt_source 𝓘(ℝ,F)] using
      (extChartAt 𝓘(ℝ,F) p).map_target hy
  refine {
    ambientPoint := a
    target := fun p y hy => by
      simpa only [extChartAt_source] using htarget p _ (hx p y hy)
    embedding := fun p y => b p ((extChartAt 𝓘(ℝ,F) p).symm y)
    smooth_embedding := ?_
    inner_embedding := fun p y hy => hinner p _ (hx p y hy)
    intertwines_I := fun p y hy => hi p _ (hx p y hy)
    intertwines_J := fun p y hy => hj p _ (hx p y hy)
    solder_eq := ?_ }
  · intro p y hy
    have hb := (hbs p).contMDiffAt ((hWopen p).mem_nhds (hx p y hy))
    have he := (contMDiffOn_extChartAt_symm (n := ∞) p).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) p).mem_nhds hy)
    exact (hb.comp y he).contDiffAt.contDiffWithinAt
  · intro p y hy
    have hyt : ι ((extChartAt 𝓘(ℝ,F) p).symm y) ∈ (extChartAt 𝓘(ℝ,E) (a p)).source := by
      simpa only [extChartAt_source] using htarget p _ (hx p y hy)
    have hf := localBaseMap_fderiv ι hNew p (a p) y ⟨hy,hyt⟩
    have hfy := (extChartAt 𝓘(ℝ,E) (a p)).map_source hyt
    rw [LocalSolderPullback.solder,solder_eq_toFrame _ p y hy,hf,hD]
    dsimp only [localBaseMap]
    rw [solder_eq_toFrame P.tangent (a p) _ hfy]
    simp only [(extChartAt 𝓘(ℝ,E) (a p)).left_inv hyt]
    ext v
    exact hinc p _ (hx p y hy) v

end
end QuaternionicSymmetry.ManifoldQuaternionicImmersionConnectionFrames
