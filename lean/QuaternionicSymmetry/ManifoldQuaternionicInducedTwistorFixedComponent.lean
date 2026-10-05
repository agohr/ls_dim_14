import QuaternionicSymmetry.ManifoldQuaternionicInducedTwistorSmooth
import QuaternionicSymmetry.ManifoldQuaternionicTwistorLiftedFixedSet
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff

/-! Identify the actual image of the induced twistor immersion with the
actual lifted fixed component, when the base is the genuine fixed component
and the subgroup acts trivially on its quaternionic coefficient plane. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicInducedTwistorFixedComponent

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicTwistorLiftedFixedSet
open ManifoldQuaternionicTwistorVerticalAction
open ManifoldQuaternionicInducedTwistorMap
open ManifoldTwistorSphereCore
open ManifoldTwistorCoefficientSphere
open Topology
open scoped Manifold ContDiff
noncomputable section

section LiftedProjection

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- Trivial quaternionic isotropy fixes the entire actual sphere fiber. -/
theorem sphere_fixed_of_coefficient_trivial
    (S : Subgroup (QuaternionicIsometries Q)) (z : SphereBundleTotal Q)
    (hz : z.1 ∈ fixedPoints Q S)
    (hQ : ∀ f ∈ S, ∀ a : Fin 3 → ℝ, coefficientAction Q f z.1 a = a) :
    z ∈ fixedSpherePoints Q S := by
  apply (mem_fixedSpherePoints_iff Q S z).mpr
  intro f hf
  apply Bundle.TotalSpace.ext
  · exact (ManifoldQuaternionicTwistorIsometryAction.sphereTotalMap_base Q f z).trans
      (hz f hf)
  apply heq_of_eq
  apply coefficientSphereHomeomorph.symm.injective
  rw [sphereTotalMap_coefficient]
  apply Subtype.ext
  exact hQ f hf _

/-- Continuous projection sends the genuine lifted connected component
into the genuine base connected component. -/
theorem fixedSphereComponent_projects
    (S : Subgroup (QuaternionicIsometries Q))
    (z : SphereBundleTotal Q) (hz : z ∈ fixedSpherePoints Q S) :
    Set.MapsTo (fun w : SphereBundleTotal Q => w.1)
      (connectedComponentIn (fixedSpherePoints Q S) z)
      (connectedComponentIn (fixedPoints Q S) z.1) := by
  have hp : Continuous (fun w : SphereBundleTotal Q => w.1) :=
    FiberBundle.continuous_proj geometricSphere (sphereCore Q).Fiber
  have hm : (fun w : SphereBundleTotal Q => w.1) '' fixedSpherePoints Q S ⊆
      fixedPoints Q S := by
    rintro x ⟨w,hw,rfl⟩
    exact fixedSpherePoints_base_fixed Q S w hw
  intro w hw
  exact connectedComponentIn_mono z.1 hm (hp.mapsTo_connectedComponentIn hz hw)

end LiftedProjection

variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (R : PositiveQuaternionicKahlerGeometry (E := F) (M := N))
  (ι : N → M)
  (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
  (hR : IsInducedQuaternionicGeometry P R ι)

/-- The induced twistor map covers the whole sphere over every included
base point, not a selected proper subset of that sphere. -/
theorem range_sphereTotalMap :
    Set.range (sphereTotalMap P R ι hι hR) =
      (fun z : SphereBundleTotal P.tangent => z.1) ⁻¹' Set.range ι := by
  ext z
  constructor
  · rintro ⟨w,rfl⟩
    exact ⟨w.1,rfl⟩
  · rcases z with ⟨x,a⟩
    rintro ⟨y,hy⟩
    change ι y = x at hy
    subst x
    obtain ⟨b,hb⟩ := sphereTotalMap_fiber_surjective P R ι hι hR y a
    exact ⟨⟨y,b⟩,hb⟩

/-- On a compact source, the genuine induced twistor immersion is also
a closed topological embedding whenever its base inclusion is injective. -/
theorem sphereTotalMap_isClosedEmbedding [CompactSpace N] [T2Space M]
    (hSmooth : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
    (hInj : Function.Injective ι) :
    IsClosedEmbedding (sphereTotalMap P R ι hι hR) :=
  (ManifoldQuaternionicInducedTwistorSmooth.sphereTotalMap_continuous
    P R ι hSmooth hι hR).isClosedEmbedding
      (sphereTotalMap_injective P R ι hι hR hInj)

/-- The induced twistor image is exactly the lifted fixed component.
The only range hypothesis concerns the base inclusion; for the actual
subtype inclusion this is its defining connected component. -/
theorem range_eq_liftedFixedComponent [PreconnectedSpace N]
    (hSmooth : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
    (S : Subgroup (QuaternionicIsometries P.tangent))
    (z : SphereBundleTotal R.tangent)
    (hRange : Set.range ι = connectedComponentIn (fixedPoints P.tangent S) (ι z.1))
    (hQ : ∀ x ∈ Set.range ι, ∀ f ∈ S, ∀ a : Fin 3 → ℝ,
      coefficientAction P.tangent f x a = a) :
    Set.range (sphereTotalMap P R ι hι hR) =
      connectedComponentIn (fixedSpherePoints P.tangent S)
        (sphereTotalMap P R ι hι hR z) := by
  have hSub : Set.range (sphereTotalMap P R ι hι hR) ⊆
      fixedSpherePoints P.tangent S := by
    rintro w ⟨v,rfl⟩
    apply sphere_fixed_of_coefficient_trivial P.tangent S
    · apply connectedComponentIn_subset _ _
      rw [← hRange]
      exact ⟨v.1,rfl⟩
    · exact hQ (ι v.1) ⟨v.1,rfl⟩
  have hz : sphereTotalMap P R ι hι hR z ∈ fixedSpherePoints P.tangent S :=
    hSub ⟨z,rfl⟩
  apply Set.Subset.antisymm
  · have hc : Continuous (sphereTotalMap P R ι hι hR) :=
      ManifoldQuaternionicInducedTwistorSmooth.sphereTotalMap_continuous
        P R ι hSmooth hι hR
    exact (isPreconnected_range hc).subset_connectedComponentIn ⟨z,rfl⟩ hSub
  · intro w hw
    rw [range_sphereTotalMap]
    have hp := fixedSphereComponent_projects P.tangent S _ hz hw
    change w.1 ∈ connectedComponentIn (fixedPoints P.tangent S) (ι z.1) at hp
    simpa only [Set.mem_preimage, hRange] using hp

/-- The actual induced twistor space is homeomorphic to the actual lifted
fixed component through the very same inclusion map. Holomorphicity of the
inverse is a further differential statement, not claimed here. -/
def fixedComponentHomeomorph [CompactSpace N] [PreconnectedSpace N] [T2Space M]
    (hSmooth : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι) (hInj : Function.Injective ι)
    (S : Subgroup (QuaternionicIsometries P.tangent))
    (z : SphereBundleTotal R.tangent)
    (hRange : Set.range ι = connectedComponentIn (fixedPoints P.tangent S) (ι z.1))
    (hQ : ∀ x ∈ Set.range ι, ∀ f ∈ S, ∀ a : Fin 3 → ℝ,
      coefficientAction P.tangent f x a = a) :
    SphereBundleTotal R.tangent ≃ₜ
      ↥(connectedComponentIn (fixedSpherePoints P.tangent S)
        (sphereTotalMap P R ι hι hR z)) :=
  (sphereTotalMap_isClosedEmbedding P R ι hι hR hSmooth hInj).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr
      (range_eq_liftedFixedComponent P R ι hι hR hSmooth S z hRange hQ))

theorem fixedComponentHomeomorph_apply [CompactSpace N] [PreconnectedSpace N] [T2Space M]
    (hSmooth : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι) (hInj : Function.Injective ι)
    (S : Subgroup (QuaternionicIsometries P.tangent))
    (z : SphereBundleTotal R.tangent)
    (hRange : Set.range ι = connectedComponentIn (fixedPoints P.tangent S) (ι z.1))
    (hQ : ∀ x ∈ Set.range ι, ∀ f ∈ S, ∀ a : Fin 3 → ℝ,
      coefficientAction P.tangent f x a = a)
    (w : SphereBundleTotal R.tangent) :
    (fixedComponentHomeomorph P R ι hι hR hSmooth hInj S z hRange hQ w).1 =
      sphereTotalMap P R ι hι hR w := rfl

/-- Specialization to the genuine base-component subtype. Its range and
connectedness are derived here, not supplied as extra geometric premises. -/
theorem actual_fixedComponent_range
    {k : ℕ} [NeZero k]
    (S : Subgroup (QuaternionicIsometries P.tangent)) (x : M)
    (A : ManifoldRiemannianFixedComponentInput.FixedComponentAtlas P.tangent S x k)
    (R : letI := A.charts; letI := A.manifold
      PositiveQuaternionicKahlerGeometry
        (E := EuclideanSpace ℝ (Fin k))
        (M := ManifoldRiemannianFixedComponentInput.FixedComponent P.tangent S x))
    (hR : letI := A.charts; letI := A.manifold
      IsInducedQuaternionicGeometry P R Subtype.val)
    (hQ : ∀ y : ManifoldRiemannianFixedComponentInput.FixedComponent P.tangent S x,
      ∀ f ∈ S, ∀ a : Fin 3 → ℝ, coefficientAction P.tangent f y.1 a = a) :
    letI := A.charts
    letI := A.manifold
    ∀ z : SphereBundleTotal R.tangent,
      Set.range (sphereTotalMap P R Subtype.val A.inclusion_injective_derivative hR) =
        connectedComponentIn (fixedSpherePoints P.tangent S)
          (sphereTotalMap P R Subtype.val A.inclusion_injective_derivative hR z) := by
  letI := A.charts
  letI := A.manifold
  letI : PreconnectedSpace
      (ManifoldRiemannianFixedComponentInput.FixedComponent P.tangent S x) :=
    Subtype.preconnectedSpace isPreconnected_connectedComponentIn
  intro z
  apply range_eq_liftedFixedComponent P R Subtype.val
    A.inclusion_injective_derivative hR A.inclusion_smooth S z
  · rw [Subtype.range_val]
    exact connectedComponentIn_eq z.1.2
  · rintro y ⟨v,rfl⟩
    exact hQ v

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedTwistorFixedComponent
