import QuaternionicSymmetry.FiberBundleCompactHausdorff
import QuaternionicSymmetry.ManifoldJointSpatialTangentContinuousAt
import QuaternionicSymmetry.CompactActionFixedTangent
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-! Passing from a subgroup to its closure preserves fixed points and fixed
tangent vectors of a smooth action. -/
namespace QuaternionicSymmetry.SmoothActionFixedClosure
open Set Manifold
open scoped Manifold ContDiff
noncomputable section

lemma fixed_on_closure_iff {G Y : Type} [TopologicalSpace G]
    [TopologicalSpace Y] [T2Space Y] {S : Set G} {f : G → Y}
    (hf : Continuous f) (y : Y) :
    (∀ g ∈ closure S, f g = y) ↔ ∀ g ∈ S, f g = y := by
  constructor
  · intro h g hg
    exact h g (subset_closure hg)
  · intro h g hg
    exact closure_minimal h (isClosed_eq hf continuous_const) hg

variable {A E H G M : Type}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace A G] [IsManifold 𝓘(ℝ,A) ∞ G]

lemma fixed_points_closure_iff
    (a : G × M → M) (ha : ContMDiff (𝓘(ℝ,A).prod I) I ∞ a)
    (S : Subgroup G) (x : M) :
    (∀ g ∈ S.topologicalClosure, a (g,x) = x) ↔ ∀ g ∈ S, a (g,x) = x :=
  fixed_on_closure_iff (ha.continuous.comp (continuous_id.prodMk continuous_const)) x

lemma spatial_tangent_continuous
    (a : G × M → M) (ha : ContMDiff (𝓘(ℝ,A).prod I) I ∞ a)
    (v : TangentBundle I M) :
    Continuous (fun g : G => tangentMap I I (fun x => a (g,x)) v) := by
  rw [continuous_iff_continuousAt]
  intro g
  have h := ManifoldJointSpatialTangentContinuousAt.continuousAt_spatialTangentFamily
    (ha.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞) (g,v.1))
  exact ContinuousAt.comp (f := fun g : G => (g,v)) h
    (continuousAt_id.prodMk continuousAt_const)

lemma fixed_derivatives_closure_iff
    (a : G × M → M) (ha : ContMDiff (𝓘(ℝ,A).prod I) I ∞ a)
    (S : Subgroup G) (x : M) (hx : ∀ g ∈ S, a (g,x) = x) (v : E) :
    (∀ g ∈ S.topologicalClosure, mfderiv I I (fun y => a (g,y)) x v = v) ↔
      ∀ g ∈ S, mfderiv I I (fun y => a (g,y)) x v = v := by
  constructor
  · intro h g hg
    exact h g (S.le_topologicalClosure hg)
  · intro h g hg
    let w : TangentBundle I M := ⟨x,v⟩
    have htan : ∀ f ∈ S, tangentMap I I (fun y => a (f,y)) w = w := by
      intro f hf
      apply Bundle.TotalSpace.ext (hx f hf)
      exact heq_of_eq (h f hf)
    letI : T2Space (TangentBundle I M) :=
      FiberBundleCompactHausdorff.totalSpace_t2 (TangentSpace I : M → Type _)
    have hall := (fixed_on_closure_iff (spatial_tangent_continuous a ha w) w).mpr htan g hg
    have hfix := (fixed_points_closure_iff a ha S x).mpr hx g hg
    have hh := congrArg (fun t : TangentBundle I M => t.2) hall
    simpa only [tangentMap,eq_rec_constant] using hh

end
end QuaternionicSymmetry.SmoothActionFixedClosure
