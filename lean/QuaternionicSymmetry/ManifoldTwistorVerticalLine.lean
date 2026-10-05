import QuaternionicSymmetry.ManifoldTwistorGlobalComplexSmooth

/-! The real two-plane tangent to each twistor sphere is the kernel of the
derivative of the actual sphere-bundle projection. Its complex rotation is
the restriction of the globally smooth twistor almost-complex field. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldTwistorSphereManifold
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldTwistorVerticalComplex
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

private abbrev I := (𝓘(ℝ,E)).prod (𝓡 2)

/-- The vertical tangent plane in the genuine tangent fiber, defined by its
zero base component in the preferred sphere-bundle trivialization. -/
def verticalTangentSubmodule (z : SphereBundleTotal Q) :
    Submodule ℝ (TangentSpace (I (E := E)) z) :=
  LinearMap.ker ((LinearMap.fst ℝ E
    (verticalSubmodule (coefficientSphereHomeomorph.symm z.2))).comp
      (preferredTangentEquiv Q z).toLinearMap)

theorem mem_verticalTangentSubmodule_iff (z : SphereBundleTotal Q)
    (v : TangentSpace (I (E := E)) z) :
    v ∈ verticalTangentSubmodule Q z ↔
      (preferredTangentEquiv Q z v).1 = 0 := Iff.rfl

/-- The differential of the actual sphere-bundle projection is the base
component of the preferred tangent chart. -/
theorem sphereProjection_mfderiv (z : SphereBundleTotal Q) :
    mfderiv (I (E := E)) 𝓘(ℝ,E)
      (fun w : SphereBundleTotal Q => w.1) z =
      ContinuousLinearMap.fst ℝ E (EuclideanSpace ℝ (Fin 2)) := by
  let f := fixedRawChart Q z.1
  let e := extChartAt 𝓘(ℝ,E) z.1
  let π : SphereBundleTotal Q → M := fun w => w.1
  have hz : z ∈ ((sphereCore Q).localTriv (achart E z.1)).toOpenPartialHomeomorph.source :=
    ((sphereCore Q).mem_localTriv_source (achart E z.1) z).mpr
      (by rw [← (sphereCore Q).baseSet_at]; exact (sphereCore Q).mem_baseSet_at z.1)
  have hf : MDifferentiableAt (I (E := E)) (I (E := E)) f z :=
    ((fixedRawChart_smoothOn Q z.1).contMDiffAt
      (((sphereCore Q).localTriv (achart E z.1)).toOpenPartialHomeomorph.open_source.mem_nhds hz)).mdifferentiableAt (by simp)
  have he : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) e z.1 := by
    have hs : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e z.1 := contMDiffAt_extChartAt
    exact hs.mdifferentiableAt (by simp)
  have hπ : MDifferentiableAt (I (E := E)) 𝓘(ℝ,E) π z :=
    (sphereProjection_smooth Q).contMDiffAt.mdifferentiableAt (by simp)
  have h₁ : mfderiv (I (E := E)) 𝓘(ℝ,E) (Prod.fst ∘ f) z =
      ContinuousLinearMap.fst ℝ E (EuclideanSpace ℝ (Fin 2)) := by
    rw [mfderiv_comp z mdifferentiableAt_fst hf,
      fixedRawChart_center_mfderiv Q z]
    rw [mfderiv_fst]
    rfl
  have h₂ : mfderiv (I (E := E)) 𝓘(ℝ,E) (Prod.fst ∘ f) z =
      mfderiv (I (E := E)) 𝓘(ℝ,E) π z := by
    change mfderiv (I (E := E)) 𝓘(ℝ,E) (e ∘ π) z = _
    calc
      _ = (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e z.1).comp
          (mfderiv (I (E := E)) 𝓘(ℝ,E) π z) := by
        simpa only [π] using (mfderiv_comp z he hπ)
      _ = _ := by
        rw [mfderiv_extChartAt_center z.1]
        exact ContinuousLinearMap.id_comp _
  exact h₂.symm.trans h₁

/-- The preferred-chart plane is exactly the kernel of the derivative of
the genuine twistor projection. -/
theorem verticalTangentSubmodule_eq_projection_ker (z : SphereBundleTotal Q) :
    verticalTangentSubmodule Q z =
      LinearMap.ker
        (mfderiv (I (E := E)) 𝓘(ℝ,E)
          (fun w : SphereBundleTotal Q => w.1) z).toLinearMap := by
  ext v
  rw [mem_verticalTangentSubmodule_iff, LinearMap.mem_ker,
    sphereProjection_mfderiv Q z]
  rfl

/-- The genuine vertical tangent plane is linearly equivalent to the
orthogonal coefficient plane of the twistor sphere. -/
def verticalTangentEquiv (z : SphereBundleTotal Q) :
    verticalTangentSubmodule Q z ≃ₗ[ℝ]
      verticalSubmodule (coefficientSphereHomeomorph.symm z.2) := by
  let e := preferredTangentEquiv Q z
  let F : verticalTangentSubmodule Q z →ₗ[ℝ]
      verticalSubmodule (coefficientSphereHomeomorph.symm z.2) :=
    { toFun := fun v => (e v.1).2
      map_add' := by intro u v; exact congrArg Prod.snd (e.map_add u.1 v.1)
      map_smul' := by intro r v; exact congrArg Prod.snd (e.map_smul r v.1) }
  refine LinearEquiv.ofBijective F ⟨?_, ?_⟩
  · intro u v huv
    apply Subtype.ext
    apply e.injective
    apply Prod.ext
    · exact (mem_verticalTangentSubmodule_iff Q z u.1).mp u.2 |>.trans
        ((mem_verticalTangentSubmodule_iff Q z v.1).mp v.2).symm
    · exact huv
  · intro w
    refine ⟨⟨e.symm (0,w), ?_⟩, ?_⟩
    · rw [mem_verticalTangentSubmodule_iff]
      change (e (e.symm (0,w))).1 = 0
      rw [e.apply_symm_apply]
    · simp [F]

theorem verticalTangent_finrank (z : SphereBundleTotal Q) :
    Module.finrank ℝ (verticalTangentSubmodule Q z) = 2 := by
  have h := (verticalTangentEquiv Q z).finrank_eq
  rw [h]
  let a := coefficientSphereHomeomorph.symm z.2
  have h' := (sphereTangentVerticalEquiv a).finrank_eq
  rw [← h']
  change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2
  simp

theorem tangentComplex_mem_verticalTangentSubmodule
    (z : SphereBundleTotal Q)
    (v : TangentSpace (I (E := E)) z)
    (hv : v ∈ verticalTangentSubmodule Q z) :
    tangentComplex Q D z v ∈ verticalTangentSubmodule Q z := by
  rw [mem_verticalTangentSubmodule_iff] at hv ⊢
  simp only [tangentComplex, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply]
  simp [ManifoldTwistorLocalAlmostComplex.localTwistorComplex,
    ManifoldTwistorLocalAlmostComplex.chartSplitComplex,
    ManifoldTwistorHorizontalConnection.connectionSplit, hv]

/-- The complex rotation on the actual vertical kernel of the twistor
projection. This is the smooth contact-line candidate at the real tangent
level; holomorphic contact geometry requires the T1 integrability input. -/
def verticalTangentComplex (z : SphereBundleTotal Q) :
    verticalTangentSubmodule Q z →ₗ[ℝ] verticalTangentSubmodule Q z where
  toFun v := ⟨tangentComplex Q D z v.1,
    tangentComplex_mem_verticalTangentSubmodule Q D z v.1 v.2⟩
  map_add' u v := by
    apply Subtype.ext
    exact (tangentComplex Q D z).map_add u.1 v.1
  map_smul' r v := by
    apply Subtype.ext
    exact (tangentComplex Q D z).map_smul r v.1

theorem verticalTangentComplex_sq (z : SphereBundleTotal Q)
    (v : verticalTangentSubmodule Q z) :
    verticalTangentComplex Q D z (verticalTangentComplex Q D z v) = -v := by
  apply Subtype.ext
  exact tangentComplex_sq Q D z v.1

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
