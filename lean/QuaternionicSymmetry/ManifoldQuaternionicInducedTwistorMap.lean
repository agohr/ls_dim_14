import QuaternionicSymmetry.ManifoldQuaternionicInducedCoefficientMap
import QuaternionicSymmetry.ManifoldTwistorSphereCore

/-! The induced quaternionic tangent-span relation defines an actual map
between the twistor sphere bundles. This file proves its fiberwise meaning
and injectivity, not its smoothness or contact compatibility. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedTwistorMap
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedCoefficientMap
open ManifoldQuaternionicInducedTwistorFiber
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldTwistorSphereBundle
open ManifoldTwistorSphereCore
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorVerticalComplex
open scoped Manifold ContDiff
noncomputable section

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

/-- The induced orientation-preserving coefficient isometry restricts to
the actual coefficient tangent plane of each unit sphere. -/
def verticalCoefficientMap (x : N) (a : coefficientSphere) :
    verticalSubmodule a →ₗ[ℝ]
      verticalSubmodule (coefficientSphereMap P R ι hι hR x a) where
  toFun v := ⟨coefficientMap P R ι hι hR x v.1, by
    change (coefficientMap P R ι hι hR x a.1) ⬝ᵥ
      (coefficientMap P R ι hι hR x v.1) = 0
    rw [coefficientMap_dot]
    exact v.2⟩
  map_add' u v := by
    apply Subtype.ext
    exact (coefficientMap P R ι hι hR x).map_add u.1 v.1
  map_smul' c v := by
    apply Subtype.ext
    exact (coefficientMap P R ι hι hR x).map_smul c v.1

/-- The fiberwise map respects the intrinsic vertical complex rotation.
Identification with the total map's manifold derivative remains separate. -/
theorem verticalCoefficientMap_complex (x : N) (a : coefficientSphere)
    (v : verticalSubmodule a) :
    verticalCoefficientMap P R ι hι hR x a (verticalComplex a v) =
      verticalComplex (coefficientSphereMap P R ι hι hR x a)
        (verticalCoefficientMap P R ι hι hR x a v) := by
  apply Subtype.ext
  exact coefficientMap_cross P R ι hι hR x a.1 v.1

theorem verticalCoefficientMap_injective (x : N) (a : coefficientSphere) :
    Function.Injective (verticalCoefficientMap P R ι hι hR x a) := by
  intro u v h
  apply Subtype.ext
  exact coefficientMap_injective P R ι hι hR x (congrArg Subtype.val h)

/-- The derivative-induced map on the genuine smooth sphere-bundle points. -/
def sphereTotalMap (z : SphereBundleTotal R.tangent) : SphereBundleTotal P.tangent :=
  ⟨ι z.1, coefficientSphereHomeomorph
    (coefficientSphereMap P R ι hι hR z.1
      (coefficientSphereHomeomorph.symm z.2))⟩

theorem sphereTotalMap_base (z : SphereBundleTotal R.tangent) :
    (sphereTotalMap P R ι hι hR z).1 = ι z.1 := rfl

/-- On each fiber the map is exactly the unique ambient quaternionic
complex structure intertwined by the actual inclusion derivative. -/
theorem sphereTotalMap_intrinsic (z : SphereBundleTotal R.tangent) :
    toIntrinsicFiber P.tangent
      (toOriginalSphere P.tangent (sphereTotalMap P R ι hι hR z)) =
    intrinsicFiberMap P R ι hι hR z.1
      (toIntrinsicFiber R.tangent (toOriginalSphere R.tangent z)) := by
  change preferredToIntrinsic P.tangent (ι z.1)
      (coefficientSphereHomeomorph.symm
        (coefficientSphereHomeomorph
          (coefficientSphereMap P R ι hι hR z.1
            (coefficientSphereHomeomorph.symm z.2)))) = _
  rw [coefficientSphereHomeomorph.symm_apply_apply]
  exact preferredToIntrinsic_coefficientSphereMap P R ι hι hR z.1
    (coefficientSphereHomeomorph.symm z.2)

theorem sphereTotalMap_injective (hInj : Function.Injective ι) :
    Function.Injective (sphereTotalMap P R ι hι hR) := by
  intro z w h
  have hx : z.1 = w.1 := hInj (congrArg Bundle.TotalSpace.proj h)
  rcases z with ⟨x,a⟩
  rcases w with ⟨y,b⟩
  dsimp at hx
  subst y
  have hc := congrArg (fun q : SphereBundleTotal P.tangent => q.2) h
  change coefficientSphereHomeomorph
      (coefficientSphereMap P R ι hι hR x (coefficientSphereHomeomorph.symm a)) =
    coefficientSphereHomeomorph
      (coefficientSphereMap P R ι hι hR x (coefficientSphereHomeomorph.symm b)) at hc
  have hab := (coefficientSphereEquiv P R ι hι hR x).injective
    (coefficientSphereHomeomorph.injective hc)
  have hab' := coefficientSphereHomeomorph.symm.injective hab
  cases hab'
  rfl

/-- Every ambient twistor point over an included base point is attained:
the smaller quaternionic manifold still has the entire two-sphere fiber. -/
theorem sphereTotalMap_fiber_surjective (x : N) (a : geometricSphere) :
    ∃ b : geometricSphere,
      sphereTotalMap P R ι hι hR ⟨x,b⟩ = ⟨ι x,a⟩ := by
  refine ⟨coefficientSphereHomeomorph
    ((coefficientSphereEquiv P R ι hι hR x).symm
      (coefficientSphereHomeomorph.symm a)), ?_⟩
  apply Bundle.TotalSpace.ext
  · rfl
  apply heq_of_eq
  change coefficientSphereHomeomorph
    ((coefficientSphereEquiv P R ι hι hR x)
      (coefficientSphereHomeomorph.symm
        (coefficientSphereHomeomorph
          ((coefficientSphereEquiv P R ι hι hR x).symm
            (coefficientSphereHomeomorph.symm a))))) = a
  rw [coefficientSphereHomeomorph.symm_apply_apply,
    (coefficientSphereEquiv P R ι hι hR x).apply_symm_apply,
    coefficientSphereHomeomorph.apply_symm_apply]

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedTwistorMap
