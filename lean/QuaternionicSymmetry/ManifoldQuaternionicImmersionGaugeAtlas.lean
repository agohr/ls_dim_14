import QuaternionicSymmetry.ManifoldQuaternionicImmersionLocalGauge
import QuaternionicSymmetry.ManifoldChartRefinementCenter
import QuaternionicSymmetry.ManifoldChartRefinementDifferential
import QuaternionicSymmetry.ManifoldChartRefinementSmoothness

/-! Assemble the constructed local immersion gauges on a compatible
restriction of the original atlas. The inclusion derivative is unchanged. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicImmersionGaugeAtlas
open ManifoldQuaternionicImmersionLocalGauge ManifoldQuaternionicSubmanifoldInput
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicReduction
open ManifoldChartRefinement ManifoldChartRefinementSmoothness
open ManifoldChartRefinementCenter ManifoldChartRefinementDifferential
open scoped Manifold ContDiff Topology
noncomputable section
variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [old : ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable {P : PositiveQuaternionicKahlerGeometry (E := E) (M := M)} {ι : N → M}
  (G : ∀ c, LocalGauge (F := F) P ι c)

def charts : ChartedSpace F N :=
  restrictedCharts (fun c => (G c).domain) (fun c => (G c).isOpen_domain) (fun c => (G c).mem_domain)

theorem charts_manifold : letI := charts G; IsManifold 𝓘(ℝ,F) ∞ N :=
  restrictedCharts_isManifold (I := 𝓘(ℝ,F)) (fun c => (G c).domain)
    (fun c => (G c).isOpen_domain) (fun c => (G c).mem_domain)

abbrev Index := @atlas F _ N _ (charts G)

def chartCenter (i : Index G) : N :=
  center (fun c => (G c).domain) (fun c => (G c).isOpen_domain) (fun c => (G c).mem_domain) i

theorem chart_eq (i : Index G) :
    i.1 = (chartAt F (chartCenter G i)).restr ((G (chartCenter G i)).domain) :=
  chart_eq_restr (fun c => (G c).domain) (fun c => (G c).isOpen_domain)
    (fun c => (G c).mem_domain) i

theorem mem_domain (i : Index G) (x : N) (hx : x ∈ i.1.source) :
    x ∈ (G (chartCenter G i)).domain :=
  mem_neighborhood_of_mem_source (fun c => (G c).domain) (fun c => (G c).isOpen_domain)
    (fun c => (G c).mem_domain) i x hx

def compatibleAtlas (hι : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x)) :
    CompatibleSubmanifoldAtlas (E := E) (F := F) old ι where
  charts := charts G
  atlas_compatible := by
    rintro _ ⟨c,rfl⟩
    exact restr_mem_maximalAtlas (contDiffGroupoid ∞ 𝓘(ℝ,F))
      (IsManifold.chart_mem_maximalAtlas c) (G c).isOpen_domain
  manifold := charts_manifold G
  inclusion_smooth := by
    have hh : letI := charts G; ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι Set.univ :=
      (contMDiffOn_restrictedCharts_iff (fun c => (G c).domain)
        (fun c => (G c).isOpen_domain) (fun c => (G c).mem_domain) ι Set.univ).mpr hι.contMDiffOn
    letI := charts G
    exact contMDiffOn_univ.mp hh
  inclusion_injective_derivative := by
    intro x
    rw [mfderiv_restrictedCharts_eq (fun c => (G c).domain)
      (fun c => (G c).isOpen_domain) (fun c => (G c).mem_domain) ι x
        (hι.mdifferentiableAt (by simp))]
    exact hinj x
  tangent_range := by
    dsimp only
    intro x
    rw [mfderiv_restrictedCharts_eq (fun c => (G c).domain)
      (fun c => (G c).isOpen_domain) (fun c => (G c).mem_domain) ι x
        (hι.mdifferentiableAt (by simp))]

def frames : letI := charts G; letI := charts_manifold (old := old) G
    TangentFrameGauge 𝓘(ℝ,F) (M := N) (n := ∞) := by
  let toF : Index G → N → F →L[ℝ] F := fun i => (G (chartCenter G i)).toFrame
  let fromF : Index G → N → F →L[ℝ] F := fun i => (G (chartCenter G i)).fromFrame
  have hto (i : Index G) :
      letI := charts G
      ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] F) ∞ (toF i) i.1.source :=
    (contMDiffOn_restrictedCharts_iff (fun c => (G c).domain)
      (fun c => (G c).isOpen_domain) (fun c => (G c).mem_domain) _ _).mpr
        ((G (chartCenter G i)).smooth_to.mono (fun x hx => mem_domain G i x hx))
  have hfrom (i : Index G) :
      letI := charts G
      ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] F) ∞ (fromF i) i.1.source :=
    (contMDiffOn_restrictedCharts_iff (fun c => (G c).domain)
      (fun c => (G c).isOpen_domain) (fun c => (G c).mem_domain) _ _).mpr
        ((G (chartCenter G i)).smooth_from.mono (fun x hx => mem_domain G i x hx))
  have htf (i : Index G) (x : N) (hx : x ∈ i.1.source) (v : F) :
      toF i x (fromF i x v) = v :=
    (G (chartCenter G i)).to_from x (mem_domain G i x hx) v
  have hft (i : Index G) (x : N) (hx : x ∈ i.1.source) (v : F) :
      fromF i x (toF i x v) = v :=
    (G (chartCenter G i)).from_to x (mem_domain G i x hx) v
  letI := charts G
  letI := charts_manifold (old := old) G
  exact {
    toFrame := toF
    fromFrame := fromF
    to_from := htf
    from_to := hft
    smooth_to := hto
    smooth_from := hfrom }

theorem coreTransition_eq (i j : Index G) (x : N) :
    let C := (tangentBundleCore 𝓘(ℝ,F) N).coordChange
      (achart F (chartCenter G i)) (achart F (chartCenter G j)) x
    letI := charts G
    letI := charts_manifold (old := old) G
    (tangentBundleCore 𝓘(ℝ,F) N).coordChange i j x = C := by
  have hi := chart_eq G i
  have hj := chart_eq G j
  letI := charts G
  letI := charts_manifold (old := old) G
  dsimp only
  simp only [tangentBundleCore_coordChange,hi,hj,mfld_simps]

theorem frameTransition_eq (i j : Index G) (x : N) :
    let T := (G (chartCenter G j)).toFrame x
    let U := (G (chartCenter G i)).fromFrame x
    let C := (tangentBundleCore 𝓘(ℝ,F) N).coordChange
      (achart F (chartCenter G i)) (achart F (chartCenter G j)) x
    letI := charts G
    letI := charts_manifold (old := old) G
    (frames (old := old) G).coordChange i j x = T.comp (C.comp U) := by
  have hC := coreTransition_eq G i j x
  letI := charts G
  letI := charts_manifold (old := old) G
  dsimp only
  change ((frames (old := old) G).toFrame j x).comp
    (((tangentBundleCore 𝓘(ℝ,F) N).coordChange i j x).comp
      ((frames (old := old) G).fromFrame i x)) = _
  rw [hC]
  rfl

theorem coreTransition_from_preferred (i : Index G) (x : N) :
    let C := (tangentBundleCore 𝓘(ℝ,F) N).coordChange
      (achart F x) (achart F (chartCenter G i)) x
    letI := charts G
    letI := charts_manifold (old := old) G
    (tangentBundleCore 𝓘(ℝ,F) N).coordChange (achart F x) i x = C := by
  have hi := chart_eq G i
  letI := charts G
  letI := charts_manifold (old := old) G
  dsimp only
  simp only [tangentBundleCore_coordChange,hi,charts,ManifoldChartRefinement.restrictedCharts,mfld_simps]
  rfl

theorem coreTransition_to_preferred (i : Index G) (x : N) :
    let C := (tangentBundleCore 𝓘(ℝ,F) N).coordChange
      (achart F (chartCenter G i)) (achart F x) x
    letI := charts G
    letI := charts_manifold (old := old) G
    (tangentBundleCore 𝓘(ℝ,F) N).coordChange i (achart F x) x = C := by
  have hi := chart_eq G i
  letI := charts G
  letI := charts_manifold (old := old) G
  dsimp only
  simp only [tangentBundleCore_coordChange,hi,charts,ManifoldChartRefinement.restrictedCharts,mfld_simps]
  rfl

theorem localDerivative_refined_eq
    (hι : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι) (i : Index G) (j : atlas E M) (x : N) :
    let D := ManifoldQuaternionicInducedLocalIntertwining.localDerivative ι
      (achart F (chartCenter G i)) j x
    letI := charts G
    letI := charts_manifold (old := old) G
    ManifoldQuaternionicInducedLocalIntertwining.localDerivative ι i j x = D := by
  have hd := mfderiv_restrictedCharts_eq (fun c => (G c).domain)
    (fun c => (G c).isOpen_domain) (fun c => (G c).mem_domain) ι x
      (hι.mdifferentiableAt (by simp))
  have hc := coreTransition_to_preferred G i x
  letI := charts G
  letI := charts_manifold (old := old) G
  dsimp only
  unfold ManifoldQuaternionicInducedLocalIntertwining.localDerivative
  rw [hd,hc]

end
end QuaternionicSymmetry.ManifoldQuaternionicImmersionGaugeAtlas
