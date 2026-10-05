import QuaternionicSymmetry.CompactActionFixedTangent
import QuaternionicSymmetry.CompactManifoldActionCoordinates
import QuaternionicSymmetry.BoundarylessCenteredChart
import QuaternionicSymmetry.LinearSubspaceComponentChart
import QuaternionicSymmetry.SubmanifoldLocalChartAtlas
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Smooth embedded manifolds on the literal common fixed components of a
smooth action of a compact Lie group. -/
namespace QuaternionicSymmetry.CompactActionFixedComponentManifold
open Set MeasureTheory SubspaceSubmanifoldChart SubmanifoldChartDimension
open SubmanifoldLocalChartAtlas CompactActionFixedLocalChart CompactActionFixedTangent
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 800000

variable {A E H K M : Type}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [ChartedSpace A K] [IsManifold 𝓘(ℝ,A) ∞ K] [LieGroup 𝓘(ℝ,A) ∞ K]
  [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]

include μ in
lemma local_component_charts
    (a : K × M → M) (ha : ContMDiff (𝓘(ℝ,A).prod I) I ∞ a)
    (h1 : ∀ x, a (1,x) = x)
    (hmul : ∀ g h x, a (g,a (h,x)) = a (g*h,x))
    (x : M) (y : connectedComponentIn {x : M | ∀ g, a (g,x) = x} x) :
    ∃ k, ∃ C : LocalChart (I := I)
      (connectedComponentIn {x : M | ∀ g, a (g,x) = x} x) k,
      y ∈ C.chart.source ∧ Module.finrank ℝ (fixedDerivatives (I := I) a y.1) = k := by
  have hy : ∀ g, a (g,y.1) = y.1 := connectedComponentIn_subset _ _ y.2
  obtain ⟨c,hc,hc0,hcs,hci⟩ := BoundarylessCenteredChart.exists_centered_chart I y.1
  obtain ⟨ρ,e,hye,hec,he0,he,hei,hinv,heq,hfix⟩ :=
    CompactManifoldActionCoordinates.exists_linearizing_chart μ a ha h1 hmul y.1 hy
      c hc hc0 hcs hci
  have hImage : e.IsImage {x : M | ∀ g, a (g,x) = x} (fixedSubspace ρ : Set E) :=
    fun z hz => (hfix z hz).symm
  obtain ⟨C,hC⟩ := LinearSubspaceComponentChart.exists_component_chart y.2 e (fixedSubspace ρ)
    he hei hye he0 hImage
  exact ⟨_,C,hC,fixed_derivative_finrank a ha ρ e he hei heq hye hy⟩

include μ in
lemma exists_fixed_component_manifold
    (a : K × M → M) (ha : ContMDiff (𝓘(ℝ,A).prod I) I ∞ a)
    (h1 : ∀ x, a (1,x) = x)
    (hmul : ∀ g h x, a (g,a (h,x)) = a (g*h,x))
    (x : M) (hx : ∀ g, a (g,x) = x) :
    ∃ (k : ℕ) (c : ChartedSpace (EuclideanSpace ℝ (Fin k))
      (connectedComponentIn {x : M | ∀ g, a (g,x) = x} x)),
      letI := c
      IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) ∞
        (connectedComponentIn {x : M | ∀ g, a (g,x) = x} x) ∧
      ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) I ∞
        (Subtype.val : (connectedComponentIn {x : M | ∀ g, a (g,x) = x} x) → M) ∧
      (∀ y, Function.Injective (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) I
        (Subtype.val : (connectedComponentIn {x : M | ∀ g, a (g,x) = x} x) → M) y)) ∧
      ∀ y, LinearMap.range (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) I
        (Subtype.val : (connectedComponentIn {x : M | ∀ g, a (g,x) = x} x) → M) y).toLinearMap =
          fixedDerivatives (I := I) a y.1 := by
  let S := connectedComponentIn {x : M | ∀ g, a (g,x) = x} x
  let x0 : S := ⟨x,mem_connectedComponentIn hx⟩
  letI : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponentIn
  choose d C hC hDim using local_component_charts μ a ha h1 hmul x
  have hd (y : S) : d y = d x0 := dimension_constant d C hC y x0
  let D : S → LocalChart (I := I) S (d x0) := fun y => (hd y) ▸ C y
  have cast_mem {j k : ℕ} (h : j = k) (C : LocalChart (I := I) S j)
      {y : S} (hy : y ∈ C.chart.source) : y ∈ (h ▸ C).chart.source := by
    subst k
    exact hy
  have hD (y : S) : y ∈ (D y).chart.source := cast_mem (hd y) (C y) (hC y)
  refine ⟨d x0,charts D hD,manifold D hD,inclusion_smooth D hD,
    inclusion_injective_derivative D hD,?_⟩
  letI := charts D hD
  letI := manifold D hD
  let i : S → M := Subtype.val
  have hi := inclusion_smooth D hD
  intro y
  let di : EuclideanSpace ℝ (Fin (d x0)) →ₗ[ℝ] E :=
    (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin (d x0))) I i y).toLinearMap
  have hsub : di.range ≤ fixedDerivatives (I := I) a y.1 := by
    rintro v ⟨w,rfl⟩ g
    have heq : (fun z => a (g,z)) ∘ i = i := by
      funext z
      exact connectedComponentIn_subset _ _ z.2 g
    have hag : MDifferentiableAt I I (fun z => a (g,z)) (i y) :=
      (ha.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (by simp)
    have hc := mfderiv_comp y hag (hi.mdifferentiableAt (by simp))
    rw [heq] at hc
    exact congrArg (fun B : EuclideanSpace ℝ (Fin (d x0)) →L[ℝ] E => B w) hc.symm
  have hdim : Module.finrank ℝ di.range = Module.finrank ℝ (fixedDerivatives (I := I) a y.1) := by
    have hinj : Function.Injective di := inclusion_injective_derivative D hD y
    rw [LinearMap.finrank_range_of_inj hinj]
    simpa only [finrank_euclideanSpace,Fintype.card_fin] using ((hDim y).trans (hd y)).symm
  change di.range = fixedDerivatives (I := I) a y.1
  exact Submodule.eq_of_le_of_finrank_eq hsub hdim


end
end QuaternionicSymmetry.CompactActionFixedComponentManifold
