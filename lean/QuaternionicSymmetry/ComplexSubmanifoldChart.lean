import QuaternionicSymmetry.ComplexSubmanifoldLinear
import QuaternionicSymmetry.SmoothInverseChart
import QuaternionicSymmetry.ManifoldComplexHolomorphicFactorization

/-! Holomorphic graph charts obtained from invariant real tangent spaces. -/
namespace QuaternionicSymmetry.ComplexSubmanifoldChart
open ComplexSubmanifoldLinear SmoothInverseChart
open ManifoldComplexHolomorphicFactorization
open ComplexSmoothRealDerivativeField ComplexSmoothRealInfinity
open scoped Manifold ContDiff Topology
open Filter Function Set IsManifold
noncomputable section

variable {E F V : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {N B : Type} [TopologicalSpace N] [ChartedSpace E N]
  [IsManifold 𝓘(ℝ,E) ∞ N]
  [TopologicalSpace B] [ChartedSpace F B]
  [IsManifold 𝓘(ℝ,F) ∞ B] [IsManifold 𝓘(ℂ,F) ∞ B]

theorem invariant_range_chart_comp {ι : N → B}
    (hι : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ ι)
    (hI : ∀ x (v : F), v ∈ LinearMap.range
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) ι x).toLinearMap →
      Complex.I • v ∈ LinearMap.range
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) ι x).toLinearMap)
    (b : B) {x : N} (hx : ι x ∈ (chartAt F b).source) :
    ∀ (v : F), v ∈ LinearMap.range
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (chartAt F b ∘ ι) x).toLinearMap →
      Complex.I • v ∈ LinearMap.range
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (chartAt F b ∘ ι) x).toLinearMap := by
  have hc : ContMDiffAt 𝓘(ℂ,F) 𝓘(ℂ,F) ∞ (chartAt F b) (ι x) :=
    contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas b) hx
  have hcr : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F) ∞ (chartAt F b) (ι x) :=
    contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas b) hx
  have hlin (v : F) : mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) (chartAt F b) (ι x) (Complex.I • v) =
      Complex.I • (show F from mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) (chartAt F b) (ι x) v) := by
    have hd := hc.mdifferentiableAt (by simp)
    have hr := hcr.mdifferentiableAt (by simp)
    have hdc : DifferentiableAt ℂ
        (chartAt F b ∘ (chartAt F (ι x)).symm) (chartAt F (ι x) (ι x)) := by
      simpa [writtenInExtChartAt, extChartAt, differentiableWithinAt_univ]
        using hd.differentiableWithinAt_writtenInExtChartAt
    have hder : mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) (chartAt F b) (ι x) =
        fderiv ℝ (chartAt F b ∘ (chartAt F (ι x)).symm) (chartAt F (ι x) (ι x)) := by
      simpa [writtenInExtChartAt, extChartAt] using hr.mfderiv
    rw [hder, hdc.fderiv_restrictScalars ℝ]
    exact (fderiv ℂ (chartAt F b ∘ (chartAt F (ι x)).symm)
      (chartAt F (ι x) (ι x))).map_smul Complex.I v
  rw [mfderiv_comp x (hcr.mdifferentiableAt (by simp))
    (hι.mdifferentiableAt (by simp))]
  rintro v ⟨u,rfl⟩
  obtain ⟨w,hw⟩ := hI x _ ⟨u,rfl⟩
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) ι x w =
    Complex.I • (show F from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) ι x u) at hw
  refine ⟨w,?_⟩
  change mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) (chartAt F b) (ι x)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) ι x w) = _
  rw [hw,hlin]
  rfl

/-- A right inverse to a complex projection with invariant real derivative
range is holomorphic. -/
theorem graph_holomorphic {g : V → F} {U : Set V} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (L : F →L[ℂ] V)
    (hL : Set.EqOn (L ∘ g) id U)
    (hI : ∀ x ∈ U, ∀ v, v ∈ LinearMap.range (fderiv ℝ g x).toLinearMap →
      Complex.I • v ∈ LinearMap.range (fderiv ℝ g x).toLinearMap) :
    ContDiffOn ℂ ∞ g U := by
  apply contDiffOn_infty_of_real_complex hU hg
  intro x hx
  have hd := (hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hleft : ∀ v, L (fderiv ℝ g x v) = v := by
    have heq : L ∘ g =ᶠ[𝓝 x] id := hL.eventuallyEq_of_mem (hU.mem_nhds hx)
    have he := heq.fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ ((L.restrictScalars ℝ) ∘ g) x = fderiv ℝ id x at he
    rw [fderiv_comp x (L.restrictScalars ℝ).differentiableAt hd,
      (L.restrictScalars ℝ).fderiv, fderiv_id] at he
    intro v
    exact congrArg (fun A : V →L[ℝ] V => A v) he
  have hi : ∀ v, fderiv ℝ g x (Complex.I • v) = Complex.I • fderiv ℝ g x v := by
    intro v
    obtain ⟨w,hw⟩ := hI x hx _ ⟨v,rfl⟩
    change fderiv ℝ g x w = Complex.I • fderiv ℝ g x v at hw
    have hw' : w = Complex.I • v := by
      simpa only [map_smul, hleft] using congrArg L hw
    simpa only [hw'] using hw
  exact ((differentiableAt_iff_restrictScalars ℝ hd).2
    ⟨complexifyCommutingMap (fderiv ℝ g x) hi,
      complexifyCommutingMap_restrictScalars _ hi⟩).differentiableWithinAt

theorem invariant_range_inverse_chart (e : OpenPartialHomeomorph N V)
    (he : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ,V) 𝓘(ℝ,E) ∞ e.symm e.target)
    {f : N → F} (hf : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f e.source)
    (hI : ∀ x ∈ e.source, ∀ (v : F), v ∈ LinearMap.range
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x).toLinearMap →
      Complex.I • v ∈ LinearMap.range
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x).toLinearMap) :
    ∀ y ∈ e.target, ∀ v, v ∈ LinearMap.range (fderiv ℝ (f ∘ e.symm) y).toLinearMap →
      Complex.I • v ∈ LinearMap.range (fderiv ℝ (f ∘ e.symm) y).toLinearMap := by
  intro y hy
  have hz := e.symm_mapsTo hy
  have heD := (he.contMDiffAt (e.open_source.mem_nhds hz)).mdifferentiableAt (by simp)
  have hiD := (hei.contMDiffAt (e.open_target.mem_nhds hy)).mdifferentiableAt (by simp)
  have hfD := (hf.contMDiffAt (e.open_source.mem_nhds hz)).mdifferentiableAt (by simp)
  have hiD' : MDifferentiableAt 𝓘(ℝ,V) 𝓘(ℝ,E) e.symm (e (e.symm y)) := by
    rwa [e.right_inv hy]
  have heq : e.symm ∘ e =ᶠ[𝓝 (e.symm y)] id := by
    filter_upwards [e.open_source.mem_nhds hz] with z hz
    exact e.left_inv hz
  have hback := heq.mfderiv_eq (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E))
  rw [mfderiv_comp _ hiD' heD, mfderiv_id, e.right_inv hy] at hback
  rw [← mfderiv_eq_fderiv, mfderiv_comp y hfD hiD]
  rintro v ⟨u,rfl⟩
  obtain ⟨w,hw⟩ := hI (e.symm y) hz _
    ⟨mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) e.symm y u,rfl⟩
  refine ⟨mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) e (e.symm y) w,?_⟩
  have hb := congrArg (fun A : E →L[ℝ] E => A w) hback
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f (e.symm y)
    (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) e.symm y
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) e (e.symm y) w)) = _
  change mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) e.symm y
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) e (e.symm y) w) = w at hb
  rw [hb]
  exact hw

/-- A graph chart whose coordinates are restrictions of ambient holomorphic
linear coordinates. -/
structure AdaptedChart (ι : N → B) (m : ℕ) where
  chart : OpenPartialHomeomorph N (EuclideanSpace ℂ (Fin m))
  point : B
  projection : F →L[ℂ] EuclideanSpace ℂ (Fin m)
  source_in_chart : ∀ x ∈ chart.source, ι x ∈ (chartAt F point).source
  eq_projection : Set.EqOn chart (projection ∘ chartAt F point ∘ ι) chart.source
  smooth_to : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,EuclideanSpace ℂ (Fin m)) ∞ chart chart.source
  smooth_inv : ContMDiffOn 𝓘(ℝ,EuclideanSpace ℂ (Fin m)) 𝓘(ℝ,E) ∞ chart.symm chart.target
  holomorphic_inv : ContMDiffOn 𝓘(ℂ,EuclideanSpace ℂ (Fin m)) 𝓘(ℂ,F) ∞
    (ι ∘ chart.symm) chart.target

theorem holomorphic_inverse_of_projection {ι : N → B}
    (hι : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ ι)
    (hI : ∀ x (v : F), v ∈ LinearMap.range
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) ι x).toLinearMap →
      Complex.I • v ∈ LinearMap.range
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) ι x).toLinearMap)
    (e : OpenPartialHomeomorph N V) (b : B) (L : F →L[ℂ] V)
    (hs : ∀ x ∈ e.source, ι x ∈ (chartAt F b).source)
    (hp : Set.EqOn e (L ∘ chartAt F b ∘ ι) e.source)
    (he : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ,V) 𝓘(ℝ,E) ∞ e.symm e.target) :
    ContMDiffOn 𝓘(ℂ,V) 𝓘(ℂ,F) ∞ (ι ∘ e.symm) e.target := by
  have hf : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ (chartAt F b ∘ ι) e.source :=
    contMDiffOn_chart.comp hι.contMDiffOn hs
  have hg : ContDiffOn ℝ ∞ (chartAt F b ∘ ι ∘ e.symm) e.target :=
    (hf.comp hei e.symm_mapsTo).contDiffOn
  have hlin : Set.EqOn (L ∘ (chartAt F b ∘ ι ∘ e.symm)) id e.target := by
    intro y hy
    exact (hp (e.symm_mapsTo hy)).symm.trans (e.right_inv hy)
  have hhol := graph_holomorphic e.open_target hg L hlin
    (invariant_range_inverse_chart e he hei hf
      (fun x hx => invariant_range_chart_comp hι hI b (hs x hx)))
  intro y hy
  have hcont := (hι.contMDiffOn.comp hei e.symm_mapsTo).continuousOn.continuousAt
    (e.open_target.mem_nhds hy)
  apply ContMDiffAt.contMDiffWithinAt
  apply (contMDiffAt_iff_target_of_mem_source (f := ι ∘ e.symm)
    (I := 𝓘(ℂ,V)) (I' := 𝓘(ℂ,F)) (hs _ (e.symm_mapsTo hy))).2
  refine ⟨hcont,?_⟩
  simpa using (hhol.contDiffAt (e.open_target.mem_nhds hy)).contMDiffAt

theorem exists_adapted_chart {ι : N → B}
    (hι : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ ι)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) ι x))
    (hI : ∀ x (v : F), v ∈ LinearMap.range
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) ι x).toLinearMap →
      Complex.I • v ∈ LinearMap.range
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) ι x).toLinearMap)
    (x : N) : ∃ (m : ℕ) (e : AdaptedChart (E := E) (F := F) ι m),
      Module.finrank ℝ E = 2 * m ∧ x ∈ e.chart.source := by
  let c := chartAt F (ι x)
  let U := ι ⁻¹' c.source
  let f := c ∘ ι
  have hU : IsOpen U := c.open_source.preimage hι.continuous
  have hx : x ∈ U := mem_chart_source F (ι x)
  have hf : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f U :=
    contMDiffOn_chart.comp hι.contMDiffOn (fun _ hy => hy)
  have hcd := (mdifferentiable_chart (I := 𝓘(ℝ,F)) (ι x)).mdifferentiableAt hx
  have hD : Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x) := by
    rw [show f = c ∘ ι from rfl, mfderiv_comp x hcd (hι.mdifferentiableAt (by simp))]
    exact ((mdifferentiable_chart (I := 𝓘(ℝ,F)) (ι x)).mfderiv_injective hx).comp (hinj x)
  obtain ⟨m,L,D,hDim,hLD⟩ := projection_of_invariant_range (E := E) (F := F)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x) hD (invariant_range_chart_comp hι hI (ι x) hx)
  have hp : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,EuclideanSpace ℂ (Fin m)) ∞ (L ∘ f) U :=
    (L.restrictScalars ℝ).contDiff.contMDiff.comp_contMDiffOn hf
  have hpD : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,EuclideanSpace ℂ (Fin m)) (L ∘ f) x =
      (D : E →L[ℝ] EuclideanSpace ℂ (Fin m)) := by
    change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,EuclideanSpace ℂ (Fin m))
      ((L.restrictScalars ℝ) ∘ f) x = _
    rw [mfderiv_comp x (((L.restrictScalars ℝ).contDiff (n := ∞)).contMDiff.mdifferentiableAt
      (by simp)) ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)),
      mfderiv_eq_fderiv, (L.restrictScalars ℝ).fderiv]
    · apply ContinuousLinearMap.ext
      exact hLD
  obtain ⟨e,hxe,heU,heq,he,hei⟩ := exists_manifold_inverse_chart hU hp hx D hpD
  have hs : ∀ y ∈ e.source, ι y ∈ c.source := fun _ hy => heU hy
  refine ⟨m,⟨e,ι x,L,hs,heq,he,hei,?_⟩,hDim,hxe⟩
  exact holomorphic_inverse_of_projection hι hI e (ι x) L hs heq he hei

end
end QuaternionicSymmetry.ComplexSubmanifoldChart
