import QuaternionicSymmetry.ManifoldTwistorSphereCore

/-! Local smoothness of the rotating sphere transitions. Mathlib supplies
`ContMDiff.codRestrict_sphere` globally; this module records the on-open-set
version needed for sphere-bundle overlap charts. -/

namespace QuaternionicSymmetry.ManifoldTwistorSphereSmoothTransition

open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open scoped Manifold ContDiff InnerProductSpace

noncomputable section

theorem contMDiffOn_codRestrict_sphere
    {E F H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {I : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    {m : WithTop ℕ∞} [IsManifold I m M] {n : ℕ}
    [Fact (Module.finrank ℝ E = n + 1)] {s : Set M} {f : M → E}
    (hf : ContMDiffOn I 𝓘(ℝ, E) m f s)
    (hf' : ∀ x, f x ∈ Metric.sphere (0 : E) 1) :
    ContMDiffOn I (𝓡 n) m
      (Set.codRestrict f (Metric.sphere (0 : E) 1) hf') s := by
  rw [contMDiffOn_iff_target]
  have hcont : ContinuousOn
      (Set.codRestrict f (Metric.sphere (0 : E) 1) hf') s := by
    rw [continuousOn_iff_continuous_restrict]
    exact (continuousOn_iff_continuous_restrict.mp hf.continuousOn).subtype_mk _
  refine ⟨hcont, ?_⟩
  intro v
  let U : _ ≃ₗᵢ[ℝ] _ :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton
      n (ne_zero_of_mem_unit_sphere (-v))).repr
  have h : ContDiffOn ℝ ω _ Set.univ := U.contDiff.contDiffOn
  have H₁ := (h.comp_inter contDiffOn_stereoToFun).contMDiffOn
  have H₂ : ContMDiffOn _ _ _ _ s := hf
  convert (H₁.of_le le_top).comp' H₂ using 1
  ext x
  have hfxv : f x = -↑v ↔ ⟪f x, -↑v⟫_ℝ = 1 := by
    have hfx : ‖f x‖ = 1 := by simpa using hf' x
    rw [inner_eq_one_iff_of_norm_eq_one hfx]
    exact norm_eq_of_mem_sphere (-v)
  simp [chartAt, ChartedSpace.chartAt, Subtype.ext_iff, hfxv, real_inner_comm]

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

/-- The actual rotating S² coordinate change is smooth on every adapted
chart overlap, viewed as a map on the base–sphere product. -/
theorem sphereCoordChange_contMDiffOn (i j : atlas E M) :
    ContMDiffOn (𝓘(ℝ, E).prod (𝓡 2)) (𝓡 2) ∞
      (fun p : M × geometricSphere => euclideanSphereCoordChange Q i j p.1 p.2)
      ((Q.frames.adaptedCore.baseSet i ∩
        Q.frames.adaptedCore.baseSet j) ×ˢ Set.univ) := by
  haveI : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) :=
    ⟨by simp [EuclideanThree]⟩
  let S : Set (M × geometricSphere) :=
    (Q.frames.adaptedCore.baseSet i ∩ Q.frames.adaptedCore.baseSet j) ×ˢ Set.univ
  let J := 𝓘(ℝ, E).prod (𝓡 2)
  have hbase : ContMDiffOn J 𝓘(ℝ, E) ∞ (fun p : M × geometricSphere => p.1) S :=
    contMDiffOn_fst
  have hoperator : ContMDiffOn J
      𝓘(ℝ, (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) ∞
      (fun p : M × geometricSphere => Q.reduction.rankThreeCoordChange i j p.1) S :=
    (Q.smooth_rankThreeCoordChange i j).comp hbase (by
      intro p hp
      exact hp.1)
  have hsnd : ContMDiffOn J (𝓡 2) ∞
      (fun p : M × geometricSphere => p.2) S := contMDiffOn_snd
  have hcoe : ContMDiffOn J 𝓘(ℝ, EuclideanThree) ∞
      (fun p : M × geometricSphere => (p.2 : EuclideanThree)) S :=
    (contMDiff_coe_sphere (E := EuclideanThree) (n := 2)).comp_contMDiffOn hsnd
  have hcoeff : ContMDiffOn J 𝓘(ℝ, Fin 3 → ℝ) ∞
      (fun p : M × geometricSphere =>
        (EuclideanSpace.equiv (Fin 3) ℝ) (p.2 : EuclideanThree)) S :=
    ((EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.contMDiff).comp_contMDiffOn hcoe
  have happly : ContMDiffOn J 𝓘(ℝ, Fin 3 → ℝ) ∞
      (fun p : M × geometricSphere =>
        Q.reduction.rankThreeCoordChange i j p.1
          ((EuclideanSpace.equiv (Fin 3) ℝ) (p.2 : EuclideanThree))) S :=
    hoperator.clm_apply hcoeff
  have hambient : ContMDiffOn J 𝓘(ℝ, EuclideanThree) ∞
      (fun p : M × geometricSphere =>
        toEuclidean (Q.reduction.rankThreeCoordChange i j p.1
          ((EuclideanSpace.equiv (Fin 3) ℝ) (p.2 : EuclideanThree)))) S :=
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.contMDiff).comp_contMDiffOn happly
  let f : M × geometricSphere → EuclideanThree :=
    fun p => (euclideanSphereCoordChange Q i j p.1 p.2).1
  have hf : ContMDiffOn J 𝓘(ℝ, EuclideanThree) ∞ f S := by
    apply hambient.congr
    intro p hp
    have hij : p.1 ∈ (Q.frames.adaptedCore.localTriv i).baseSet ∩
      (Q.frames.adaptedCore.localTriv j).baseSet := hp.1
    change (euclideanSphereCoordChange Q i j p.1 p.2).1 =
      toEuclidean (Q.reduction.rankThreeCoordChange i j p.1
        ((EuclideanSpace.equiv (Fin 3) ℝ) (p.2 : EuclideanThree)))
    dsimp [euclideanSphereCoordChange]
    rw [dif_pos hij]
    rfl
  have hf' : ∀ p, f p ∈ Metric.sphere (0 : EuclideanThree) 1 :=
    fun p => (euclideanSphereCoordChange Q i j p.1 p.2).2
  have htarget := contMDiffOn_codRestrict_sphere
    (I := J) (n := 2) hf hf'
  exact htarget.congr (by intro p hp; rfl)

theorem sphereCore_trivChange_contMDiffOn (i j : atlas E M) :
    ContMDiffOn (𝓘(ℝ, E).prod (𝓡 2)) (𝓘(ℝ, E).prod (𝓡 2)) ∞
      (fun p : M × geometricSphere =>
        (p.1, (sphereCore Q).coordChange i j p.1 p.2))
      (((sphereCore Q).baseSet i ∩ (sphereCore Q).baseSet j) ×ˢ Set.univ) :=
  contMDiffOn_fst.prodMk (sphereCoordChange_contMDiffOn Q i j)

end
end QuaternionicSymmetry.ManifoldTwistorSphereSmoothTransition
