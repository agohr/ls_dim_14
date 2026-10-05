import QuaternionicSymmetry.ManifoldQuaternionicIsometryDerivativeSkew

/-! Smoothness and infinitesimal orthogonality of the genuine adapted
derivative on fixed-chart overlaps. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryChartFields

open Filter
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryLocalDerivative
open ManifoldQuaternionicLocalDerivativeEquivariance
open ManifoldQuaternionicIsometryAdaptedOrthogonal
open ManifoldQuaternionicConnectionIsometrySolder
open QuaternionicSymmetry.ManifoldQuaternionicIsometryDerivativeSkew
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- The adapted matrix, written in coordinates of its center chart, is
smooth at that center. This is the local derivative field entering the
isometry pullback of the Levi-Civita connection. -/
theorem localAdaptedDerivative_coordinate_smoothAt_center
    (f : QuaternionicIsometries Q) (p : M) :
    ContDiffAt ℝ ∞
      (fun y : E => localAdaptedDerivative Q f p
        ((extChartAt 𝓘(ℝ,E) p).symm y))
      (extChartAt 𝓘(ℝ,E) p p) := by
  have hy : extChartAt 𝓘(ℝ,E) p p ∈
      (extChartAt 𝓘(ℝ,E) p).target :=
    (extChartAt 𝓘(ℝ,E) p).map_source (by simp)
  have hs : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞
      (extChartAt 𝓘(ℝ,E) p).symm (extChartAt 𝓘(ℝ,E) p p) :=
    (contMDiffOn_extChartAt_symm (n := ∞) p _ hy).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hy)
  have hp : (extChartAt 𝓘(ℝ,E) p).symm
      (extChartAt 𝓘(ℝ,E) p p) = p :=
    (extChartAt 𝓘(ℝ,E) p).left_inv (by simp)
  have hA : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞
      (localAdaptedDerivative Q f p)
      ((extChartAt 𝓘(ℝ,E) p).symm (extChartAt 𝓘(ℝ,E) p p)) := by
    simpa only [hp] using localAdaptedDerivative_smoothAt Q f p
  have h := hA.comp (extChartAt 𝓘(ℝ,E) p p) hs
  exact h.contDiffAt

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Orthogonality of the adapted isometry matrix holds on a genuine
neighborhood of the center in coordinate space. -/
theorem localAdaptedDerivative_coordinate_orthogonal_eventually
    (f : QuaternionicIsometries Q) (p : M) :
    ∀ᶠ y in nhds (extChartAt 𝓘(ℝ,E) p p), ∀ u v : E,
      inner ℝ
        (localAdaptedDerivative Q f p ((extChartAt 𝓘(ℝ,E) p).symm y) u)
        (localAdaptedDerivative Q f p ((extChartAt 𝓘(ℝ,E) p).symm y) v) =
          inner ℝ u v := by
  let y₀ := extChartAt 𝓘(ℝ,E) p p
  let σ := (extChartAt 𝓘(ℝ,E) p).symm
  have hσp : σ y₀ = p :=
    (extChartAt 𝓘(ℝ,E) p).left_inv (by simp)
  have hσ : ContinuousAt σ y₀ := by
    have hy : y₀ ∈ (extChartAt 𝓘(ℝ,E) p).target :=
      (extChartAt 𝓘(ℝ,E) p).map_source (by simp)
    exact ((contMDiffOn_extChartAt_symm (n := ∞) p _ hy).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hy)).continuousAt
  have hf : ContinuousAt (fun y : E => f • σ y) y₀ :=
    ((by simpa only [hσp] using (f.1.contMDiff p).continuousAt :
      ContinuousAt (f.1 : M → M) (σ y₀))).comp hσ
  have hsrc : ∀ᶠ y in nhds y₀, σ y ∈ (chartAt E p).source :=
    hσ.eventually ((chartAt E p).open_source.mem_nhds (by simp [hσp]))
  have htgt : ∀ᶠ y in nhds y₀,
      f • σ y ∈ (chartAt E (f • p)).source :=
    hf.eventually ((chartAt E (f • p)).open_source.mem_nhds
      (by simp [hσp]))
  filter_upwards [hsrc, htgt] with y hy hz u v
  exact localAdaptedDerivative_inner_on_overlap Q f p (σ y) hy hz u v

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Infinitesimal metric compatibility of the *actual* fixed-chart
isometry matrix. This is the skew term in connection naturality. -/
theorem localAdaptedDerivative_coordinate_skew_center
    (f : QuaternionicIsometries Q) (p : M) (u v w : E) :
    let U : E → (E →L[ℝ] E) := fun y =>
      localAdaptedDerivative Q f p ((extChartAt 𝓘(ℝ,E) p).symm y)
    let y₀ := extChartAt 𝓘(ℝ,E) p p
    inner ℝ ((fderiv ℝ U y₀ u) v) (U y₀ w) +
      inner ℝ (U y₀ v) ((fderiv ℝ U y₀ u) w) = 0 := by
  dsimp only
  exact fderiv_orthogonal_skew _ _
    ((localAdaptedDerivative_coordinate_smoothAt_center Q f p).differentiableAt
      (by norm_num))
    (localAdaptedDerivative_coordinate_orthogonal_eventually Q f p) u v w

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- The genuine isometry between fixed manifold charts has second-order
regularity at its center, as required for symmetric second derivatives. -/
theorem localIsometryChartMap_contDiffAt_center
    (f : QuaternionicIsometries Q) (p : M) :
    ContDiffAt ℝ 2 (localIsometryChartMap Q f p)
      (extChartAt 𝓘(ℝ,E) p p) := by
  let y₀ := extChartAt 𝓘(ℝ,E) p p
  have hy : y₀ ∈ (extChartAt 𝓘(ℝ,E) p).target :=
    (extChartAt 𝓘(ℝ,E) p).map_source (by simp)
  have hs : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞
      (extChartAt 𝓘(ℝ,E) p).symm y₀ :=
    (contMDiffOn_extChartAt_symm (n := ∞) p _ hy).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hy)
  have hp : (extChartAt 𝓘(ℝ,E) p).symm y₀ = p :=
    (extChartAt 𝓘(ℝ,E) p).left_inv (by simp)
  have hf : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (f.1 : M → M)
      ((extChartAt 𝓘(ℝ,E) p).symm y₀) := by
    simpa only [hp] using f.1.contMDiff p
  have ht : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞
      (extChartAt 𝓘(ℝ,E) (f • p))
      (f • ((extChartAt 𝓘(ℝ,E) p).symm y₀)) := by
    simpa only [hp] using
      (contMDiffAt_extChartAt' (n := ∞) (by simp :
        f • p ∈ (chartAt E (f • p)).source))
  have h := ht.comp y₀ (hf.comp y₀ hs)
  have h' : ContDiffAt ℝ ∞ (localIsometryChartMap Q f p) y₀ := h.contDiffAt
  exact h'.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- A fixed source chart remains valid, and its isometric image remains in
the fixed target chart, on a neighborhood of the center coordinate. -/
theorem localIsometryChart_overlap_eventually
    (f : QuaternionicIsometries Q) (p : M) :
    ∀ᶠ y in nhds (extChartAt 𝓘(ℝ,E) p p),
      y ∈ (extChartAt 𝓘(ℝ,E) p).target ∧
      (extChartAt 𝓘(ℝ,E) p).symm y ∈ (chartAt E p).source ∧
      f • ((extChartAt 𝓘(ℝ,E) p).symm y) ∈
        (chartAt E (f • p)).source := by
  let y₀ := extChartAt 𝓘(ℝ,E) p p
  let σ := (extChartAt 𝓘(ℝ,E) p).symm
  have hσp : σ y₀ = p :=
    (extChartAt 𝓘(ℝ,E) p).left_inv (by simp)
  have hy : y₀ ∈ (extChartAt 𝓘(ℝ,E) p).target :=
    (extChartAt 𝓘(ℝ,E) p).map_source (by simp)
  have hσ : ContinuousAt σ y₀ :=
    ((contMDiffOn_extChartAt_symm (n := ∞) p _ hy).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hy)).continuousAt
  have hf : ContinuousAt (fun y : E => f • σ y) y₀ :=
    ((by simpa only [hσp] using (f.1.contMDiff p).continuousAt :
      ContinuousAt (f.1 : M → M) (σ y₀))).comp hσ
  have hsrc : ∀ᶠ y in nhds y₀, σ y ∈ (chartAt E p).source :=
    hσ.eventually ((chartAt E p).open_source.mem_nhds (by simp [hσp]))
  have htgt : ∀ᶠ y in nhds y₀,
      f • σ y ∈ (chartAt E (f • p)).source :=
    hf.eventually ((chartAt E (f • p)).open_source.mem_nhds
      (by simp [hσp]))
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hy, hsrc, htgt]
    with y h₁ h₂ h₃
  exact ⟨h₁, h₂, h₃⟩

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- The reverse adapted matrix in source chart coordinates is smooth at
the center as well. -/
theorem localAdaptedInverseDerivative_coordinate_smoothAt_center
    (f : QuaternionicIsometries Q) (p : M) :
    ContDiffAt ℝ ∞
      (fun y : E => localAdaptedInverseDerivative Q f p
        ((extChartAt 𝓘(ℝ,E) p).symm y))
      (extChartAt 𝓘(ℝ,E) p p) := by
  have hy : extChartAt 𝓘(ℝ,E) p p ∈
      (extChartAt 𝓘(ℝ,E) p).target :=
    (extChartAt 𝓘(ℝ,E) p).map_source (by simp)
  have hs : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞
      (extChartAt 𝓘(ℝ,E) p).symm (extChartAt 𝓘(ℝ,E) p p) :=
    (contMDiffOn_extChartAt_symm (n := ∞) p _ hy).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hy)
  have hp : (extChartAt 𝓘(ℝ,E) p).symm
      (extChartAt 𝓘(ℝ,E) p p) = p :=
    (extChartAt 𝓘(ℝ,E) p).left_inv (by simp)
  have hB : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞
      (localAdaptedInverseDerivative Q f p)
      ((extChartAt 𝓘(ℝ,E) p).symm (extChartAt 𝓘(ℝ,E) p p)) := by
    simpa only [hp] using localAdaptedInverseDerivative_smoothAt Q f p
  exact (hB.comp (extChartAt 𝓘(ℝ,E) p p) hs).contDiffAt

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- The reverse and forward adapted matrices cancel on a coordinate
neighborhood of the center, not merely at the center itself. -/
theorem localAdaptedInverse_forward_eventually
    (f : QuaternionicIsometries Q) (p : M) :
    ∀ᶠ y in nhds (extChartAt 𝓘(ℝ,E) p p), ∀ z : E,
      localAdaptedInverseDerivative Q f p
          ((extChartAt 𝓘(ℝ,E) p).symm y)
        (localAdaptedDerivative Q f p
          ((extChartAt 𝓘(ℝ,E) p).symm y) z) = z := by
  filter_upwards [localIsometryChart_overlap_eventually Q f p]
    with y ⟨_, hx, hy⟩ z
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  have hback : f⁻¹ • (f • x) ∈
      (chartAt E (f⁻¹ • (f • p))).source := by
    simpa only [inv_smul_smul] using hx
  have h := localAdaptedDerivative_inverse_on_overlap Q f⁻¹ (f • p)
    (f • x) hy hback z
  simpa only [localAdaptedInverseDerivative, inv_inv, inv_smul_smul] using h

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryChartFields
