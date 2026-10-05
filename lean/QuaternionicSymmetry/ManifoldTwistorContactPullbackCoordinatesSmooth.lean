import QuaternionicSymmetry.ManifoldTwistorContactPullbackCoordinates

/-! The combined fixed sphere chart and pullback tangent-bundle fiber
coordinate is smooth on the true common chart domain. This is the source
coordinate map for the smooth horizontal-lift atlas proof. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

open Bundle
open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev I := (𝓘(ℝ,E)).prod (𝓡 2)
private abbrev J := I (E := E) |>.prod 𝓘(ℝ,E)

def contactPullbackChartDomain (p : M) :
    Set (Bundle.TotalSpace E (contactPullbackFiber Q)) :=
  (fun t => t.1) ⁻¹'
    ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source ∩
    (contactPullbackTrivialization Q p).source

theorem contactPullbackChartDomain_open (p : M) :
    IsOpen (contactPullbackChartDomain Q p) := by
  exact ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.open_source.preimage
    (FiberBundle.continuous_proj E (contactPullbackFiber Q)) |>.inter
      (contactPullbackTrivialization Q p).open_source

theorem contactPullbackCoordinates_smoothOn (p : M) :
    ContMDiffOn (J (E := E)) (I (E := E) |>.prod 𝓘(ℝ,E)) ∞
      (contactPullbackCoordinates Q p)
      (contactPullbackChartDomain Q p) := by
  let U := contactPullbackChartDomain Q p
  let e := contactBaseTrivialization (E := E) p
  let e' := contactPullbackTrivialization Q p
  letI : ContMDiffVectorBundle ∞ E (contactPullbackFiber Q) (I (E := E)) :=
    contactPullbackSmoothBundle Q
  haveI : MemTrivializationAtlas e := by
    exact ⟨⟨achart E p,rfl⟩⟩
  haveI : MemTrivializationAtlas e' := ⟨⟨e,inferInstance,rfl⟩⟩
  have hπ : ContMDiff (J (E := E)) (I (E := E)) ∞
      (fun t : Bundle.TotalSpace E (contactPullbackFiber Q) => t.1) :=
    Bundle.contMDiff_proj (contactPullbackFiber Q)
  have hfixed : ContMDiffOn (J (E := E)) (I (E := E)) ∞
      (fun t : Bundle.TotalSpace E (contactPullbackFiber Q) =>
        fixedRawChart Q p t.1) U :=
    (fixedRawChart_smoothOn Q p).comp hπ.contMDiffOn (by
      intro t ht
      exact ht.1)
  have htriv : ContMDiffOn (J (E := E)) (J (E := E)) ∞
      e' U := (e'.contMDiffOn).mono (by intro t ht; exact ht.2)
  simpa only [contactPullbackCoordinates, e'] using
    hfixed.prodMk (contMDiff_snd.comp_contMDiffOn htriv)

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
