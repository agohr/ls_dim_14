import QuaternionicSymmetry.ManifoldQuaternionicInducedTwistorSmooth
import QuaternionicSymmetry.ManifoldTwistorVerticalTangent

/-! Fixed-base differential of the actual induced twistor sphere map. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedFiberDerivative
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedCoefficientMap
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicInducedTwistorSmooth
open ManifoldTwistorSphereCore
open ManifoldTwistorSphereBundle
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

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

def euclideanCoefficientMap (x : N) : EuclideanThree →L[ℝ] EuclideanThree :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.comp
    ((coefficientMap P R ι hι hR x).toContinuousLinearMap.comp
      (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap)

theorem euclideanCoefficientMap_sphere (x : N) (u : geometricSphere) :
    euclideanCoefficientMap P R ι hι hR x u.1 ∈
      Metric.sphere (0 : EuclideanThree) 1 := by
  apply (mem_geometricSphere _).2
  change squareNorm (coefficientMap P R ι hι hR x
    (EuclideanSpace.equiv (Fin 3) ℝ u.1)) = 1
  rw [coefficientMap_squareNorm]
  exact (mem_geometricSphere _).1 u.2

def geometricFiberMap (x : N) : geometricSphere → geometricSphere :=
  fun u => coefficientSphereHomeomorph
    (coefficientSphereMap P R ι hι hR x (coefficientSphereHomeomorph.symm u))

theorem geometricFiberMap_smooth (x : N) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (geometricFiberMap P R ι hι hR x) := by
  let T := euclideanCoefficientMap P R ι hι hR x
  have hT : ContMDiff (𝓡 2) 𝓘(ℝ,EuclideanThree) ∞
      (fun u : geometricSphere => T u.1) :=
    T.contMDiff.comp contMDiff_coe_sphere
  have hsphere : ∀ u : geometricSphere,
      T u.1 ∈ Metric.sphere (0 : EuclideanThree) 1 :=
    euclideanCoefficientMap_sphere P R ι hι hR x
  exact (hT.codRestrict_sphere (n := 2) hsphere).congr (by
    intro u
    apply Subtype.ext
    rfl)

theorem sphereTangentMap_geometricFiberMap
    (x : N) (u : geometricSphere) (v : TangentSpace (𝓡 2) u) :
    sphereTangentMap (geometricFiberMap P R ι hι hR x u)
      (mfderiv (𝓡 2) (𝓡 2) (geometricFiberMap P R ι hι hR x) u v) =
        euclideanCoefficientMap P R ι hι hR x (sphereTangentMap u v) := by
  let T := euclideanCoefficientMap P R ι hι hR x
  let g := geometricFiberMap P R ι hι hR x
  let e : geometricSphere → EuclideanThree := Subtype.val
  have hfun : e ∘ g = T ∘ e := by
    funext w
    rfl
  have hderiv := congrArg
    (fun H : geometricSphere → EuclideanThree =>
      mfderiv (𝓡 2) 𝓘(ℝ,EuclideanThree) H u v) hfun
  change mfderiv (𝓡 2) 𝓘(ℝ,EuclideanThree) (e ∘ g) u v =
    mfderiv (𝓡 2) 𝓘(ℝ,EuclideanThree) (T ∘ e) u v at hderiv
  have heg : MDifferentiableAt (𝓡 2) 𝓘(ℝ,EuclideanThree) e (g u) :=
    (contMDiff_coe_sphere (n := 2) (m := ∞)).mdifferentiable (by simp) (g u)
  have hg : MDifferentiableAt (𝓡 2) (𝓡 2) g u :=
    (geometricFiberMap_smooth P R ι hι hR x).mdifferentiable (by simp) u
  have hTsmooth : ContMDiff 𝓘(ℝ,EuclideanThree) 𝓘(ℝ,EuclideanThree)
      ∞ T := T.contMDiff
  have hT : MDifferentiableAt 𝓘(ℝ,EuclideanThree) 𝓘(ℝ,EuclideanThree)
      T (e u) := hTsmooth.mdifferentiable (by simp) (e u)
  have he : MDifferentiableAt (𝓡 2) 𝓘(ℝ,EuclideanThree) e u :=
    (contMDiff_coe_sphere (n := 2) (m := ∞)).mdifferentiable (by simp) u
  rw [mfderiv_comp u heg hg, mfderiv_comp u hT he] at hderiv
  change sphereTangentMap (g u)
      (mfderiv (𝓡 2) (𝓡 2) g u v) =
    (mfderiv 𝓘(ℝ,EuclideanThree) 𝓘(ℝ,EuclideanThree) T (e u))
      (sphereTangentMap u v) at hderiv
  simpa only [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] using hderiv

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedFiberDerivative
