import QuaternionicSymmetry.ManifoldQuaternionicVerticalWeightKernel
import QuaternionicSymmetry.TorusWeightHalfTurn
import QuaternionicSymmetry.QuaternionicSphereHalfTurn
import Mathlib.Topology.Separation.Connected

/-! A nonzero vertical weight leaves at most two fixed points in one
actual twistor fiber. Consequently a connected fixed set over one base
point is a singleton, the zero-dimensional-base branch of induction. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFixedFiberFinite

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
open ManifoldQuaternionicIsometryCoefficients ManifoldQuaternionicTwistorIsotropyWeight
open ManifoldQuaternionicVerticalWeightKernel
open ManifoldTwistorSphereCore ManifoldTwistorCoefficientSphere
open ManifoldTwistorVerticalComplex
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable {r : ℕ} (A : ContinuousTorusAction Q r)
  (z : SphereBundleTotal Q) (hz : ∀ t, A.representation t • z = z)

theorem fixed_fiber_coefficient_eq_or_neg
    (μ : Fin r → ℤ) (hμ : μ ≠ 0)
    (hweight : HasVerticalWeight Q A z hz μ)
    (w : SphereBundleTotal Q) (hbase : w.1 = z.1)
    (hw : ∀ t, A.representation t • w = w) :
    (coefficientSphereHomeomorph.symm w.2).1 =
        (coefficientSphereHomeomorph.symm z.2).1 ∨
      (coefficientSphereHomeomorph.symm w.2).1 =
        -(coefficientSphereHomeomorph.symm z.2).1 := by
  obtain ⟨t, ht⟩ := TorusWeightHalfTurn.exists_halfTurn μ hμ
  apply QuaternionicSphereHalfTurn.fixed_unit_eq_axis_or_neg
    (coefficientSphereHomeomorph.symm z.2)
    (coefficientSphereHomeomorph.symm w.2)
    (coefficientAction Q (A.representation t) z.1)
  · exact congrArg Subtype.val
      (isotropy_fixes_coefficient Q z ⟨A.representation t, hz t⟩)
  · intro v
    have h := congrArg Subtype.val (hweight t v)
    simpa [ht] using h
  · have h := congrArg Subtype.val
      (isotropy_fixes_coefficient Q w ⟨A.representation t, hw t⟩)
    change coefficientAction Q (A.representation t) w.1
      (coefficientSphereHomeomorph.symm w.2).1 = _ at h
    rwa [hbase] at h

theorem finite_fixed_set_in_fiber
    (μ : Fin r → ℤ) (hμ : μ ≠ 0)
    (hweight : HasVerticalWeight Q A z hz μ)
    (Y : Set (SphereBundleTotal Q))
    (hbase : ∀ w ∈ Y, w.1 = z.1)
    (hfixed : ∀ w ∈ Y, ∀ t, A.representation t • w = w) : Y.Finite := by
  let φ : SphereBundleTotal Q → (Fin 3 → ℝ) := fun w =>
    (coefficientSphereHomeomorph.symm w.2).1
  have hmap : Set.MapsTo φ Y {φ z, -φ z} := by
    intro w hw
    exact (Set.mem_insert_iff.mpr
      ((fixed_fiber_coefficient_eq_or_neg Q A z hz μ hμ hweight w
        (hbase w hw) (hfixed w hw)).imp id Set.mem_singleton_iff.mpr))
  have hinj : Set.InjOn φ Y := by
    intro w hw v hv h
    rcases w with ⟨x, a⟩
    rcases v with ⟨y, b⟩
    have hxy : x = y := (hbase ⟨x,a⟩ hw).trans (hbase ⟨y,b⟩ hv).symm
    subst y
    have hab : a = b := coefficientSphereHomeomorph.symm.injective (Subtype.ext h)
    cases hab
    rfl
  exact ((Set.finite_singleton (-φ z)).insert (φ z)).of_injOn hmap hinj

theorem connected_fixed_set_in_fiber_subsingleton [T1Space (SphereBundleTotal Q)]
    (μ : Fin r → ℤ) (hμ : μ ≠ 0)
    (hweight : HasVerticalWeight Q A z hz μ)
    (Y : Set (SphereBundleTotal Q)) (hY : IsPreconnected Y)
    (hbase : ∀ w ∈ Y, w.1 = z.1)
    (hfixed : ∀ w ∈ Y, ∀ t, A.representation t • w = w) :
    Y.Subsingleton := by
  have hf := finite_fixed_set_in_fiber Q A z hz μ hμ hweight Y hbase hfixed
  by_contra h
  exact (hY.infinite_of_nontrivial (Set.not_subsingleton_iff.mp h)) hf

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedFiberFinite
