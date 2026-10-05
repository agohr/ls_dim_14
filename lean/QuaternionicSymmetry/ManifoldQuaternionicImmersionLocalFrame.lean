import QuaternionicSymmetry.ManifoldQuaternionicImmersionRange
import QuaternionicSymmetry.QuaternionicSmoothRangeFrame

/-! Smooth local orthonormal quaternionic frames for the actual tangent
range of a quaternionic immersion, without a submanifold literature input. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicImmersionLocalFrame
open ManifoldQuaternionicImmersionRange ManifoldQuaternionicSubmanifoldInput
open ManifoldPositiveQuaternionicKahlerGeometry QuaternionicSmoothRangeFrame Filter
open scoped Manifold ContDiff Topology
noncomputable section
variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

theorem exists_local_frame
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M)) (ι : N → M)
    (hι : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
    (hQ : QuaternionicTangentRange (F := F) P ι) (c : N) :
    ∃ (S : QuaternionicStructure F) (B : N → F →L[ℝ] E),
      ∀ᶠ x in 𝓝 c,
        ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] E) ∞ B x ∧
        (∀ v w, inner ℝ (B x v) (B x w) = inner ℝ v w) ∧
        LinearMap.range (B x).toLinearMap =
          LinearMap.range (adaptedDerivative P ι (achart F c) (achart E (ι c)) x).toLinearMap ∧
        (∀ v, B x (S.I v) = (P.tangent.reduction.Q (achart E (ι c))).I (B x v)) ∧
        (∀ v, B x (S.J v) = (P.tangent.reduction.Q (achart E (ι c))).J (B x v)) := by
  let e := extChartAt 𝓘(ℝ,F) c
  let i := achart F c
  let j := achart E (ι c)
  let a := e c
  let A : F → F →L[ℝ] E := fun y => adaptedDerivative P ι i j (e.symm y)
  have ha : a ∈ e.target := e.map_source (mem_extChartAt_source c)
  have he : e.symm a = c := e.left_inv (mem_extChartAt_source c)
  have hecont : ContinuousAt e.symm a :=
    (continuousOn_extChartAt_symm c).continuousAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) c).mem_nhds ha)
  have hdom : ∀ᶠ y in 𝓝 a, y ∈ e.target ∧ ι (e.symm y) ∈ j.1.source := by
    have hj : ι (e.symm a) ∈ j.1.source := by simpa only [he] using mem_chart_source E (ι c)
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,F)) c).mem_nhds ha,
      (hι.continuous.continuousAt.comp hecont).preimage_mem_nhds
        (j.1.open_source.mem_nhds hj)] with y hy hz
    exact ⟨hy,hz⟩
  have hsource (y : F) (hy : y ∈ e.target) : e.symm y ∈ i.1.source := by
    simpa only [e,i,coe_achart,extChartAt_source] using e.map_target hy
  have hA : ∀ᶠ y in 𝓝 a, ContDiffAt ℝ ∞ A y := by
    filter_upwards [hdom] with y hy
    have hsymm : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F) ∞ e.symm y :=
      (contMDiffOn_extChartAt_symm c).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) c).mem_nhds hy.1)
    exact ((adaptedDerivative_contMDiffAt P ι hι i j (e.symm y)
      (hsource y hy.1) hy.2).comp y hsymm).contDiffAt
  have hInj : ∀ᶠ y in 𝓝 a, Function.Injective (A y) := hdom.mono fun y hy =>
    adaptedDerivative_injective P ι hinj i j (e.symm y) (hsource y hy.1) hy.2
  have hI : ∀ᶠ y in 𝓝 a, ∀ z ∈ LinearMap.range (A y).toLinearMap,
      (P.tangent.reduction.Q j).I z ∈ LinearMap.range (A y).toLinearMap :=
    hdom.mono fun y hy z hz =>
      adaptedDerivative_range_generator P ι hQ i j (e.symm y) (hsource y hy.1) hy.2 0 z hz
  have hJ : ∀ᶠ y in 𝓝 a, ∀ z ∈ LinearMap.range (A y).toLinearMap,
      (P.tangent.reduction.Q j).J z ∈ LinearMap.range (A y).toLinearMap :=
    hdom.mono fun y hy z hz =>
      adaptedDerivative_range_generator P ι hQ i j (e.symm y) (hsource y hy.1) hy.2 1 z hz
  obtain ⟨S,B,hBs,hB⟩ := exists_smooth_range_frame (P.tangent.reduction.Q j) A a hA hInj hI hJ
  refine ⟨S,fun x => B (e x),?_⟩
  have hc : ContinuousAt e c := (continuousOn_extChartAt c).continuousAt
    ((isOpen_extChartAt_source (I := 𝓘(ℝ,F)) c).mem_nhds (mem_extChartAt_source c))
  filter_upwards [hc.preimage_mem_nhds (hBs.and hB),
    (isOpen_extChartAt_source (I := 𝓘(ℝ,F)) c).mem_nhds (mem_extChartAt_source c)] with x hx hxe
  have hex : e.symm (e x) = x := e.left_inv hxe
  have hxchart : x ∈ (chartAt F c).source := by simpa only [extChartAt_source] using hxe
  refine ⟨(hx.1.contMDiffAt).comp x (contMDiffAt_extChartAt' hxchart),hx.2.1,?_,hx.2.2.2⟩
  simpa only [A,hex] using hx.2.2.1

end
end QuaternionicSymmetry.ManifoldQuaternionicImmersionLocalFrame
