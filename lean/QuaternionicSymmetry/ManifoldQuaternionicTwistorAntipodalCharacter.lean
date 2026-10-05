import QuaternionicSymmetry.ManifoldQuaternionicTwistorAntipodalEquivariance
import QuaternionicSymmetry.ManifoldQuaternionicVerticalCircleCharacter

/-! The antipode preserves each underlying real vertical plane and reverses
its preferred complex structure. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorAntipodalCharacter

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicTwistorIsotropyWeight
open ManifoldQuaternionicTwistorAntipodalWeight
open ManifoldQuaternionicTwistorAntipodalEquivariance
open ManifoldQuaternionicVerticalComplexCharacter
open ManifoldQuaternionicVerticalCircleCharacter
open ManifoldQuaternionicTorusAction
open ManifoldTwistorSphereCore ManifoldTwistorSphereBundle
open ManifoldTwistorVerticalComplex ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff Matrix ComplexConjugate
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem verticalSubmodule_antipodal (a : coefficientSphere) :
    verticalSubmodule (coefficientAntipodal a) = verticalSubmodule a := by
  ext v
  change (-a.1) ⬝ᵥ v = 0 ↔ a.1 ⬝ᵥ v = 0
  rw [neg_dotProduct]
  exact neg_eq_zero

theorem verticalComplex_antipodal (a : coefficientSphere)
    (v : verticalSubmodule (coefficientAntipodal a)) :
    (verticalComplex (coefficientAntipodal a) v).1 =
      -(a.1 ⨯₃ v.1) := by
  change (-a.1) ⨯₃ v.1 = -(a.1 ⨯₃ v.1)
  funext i
  fin_cases i <;> simp [cross_apply, Pi.neg_apply]

/-- A stabilizer element fixes the antipodal twistor point as well. -/
theorem antipodal_fixed (z : SphereBundleTotal Q)
    (f : QuaternionicIsometries Q)
    (hf : f • z = z) : f • sphereAntipodal Q z = sphereAntipodal Q z := by
    change sphereTotalMap Q f (sphereAntipodal Q z) = sphereAntipodal Q z
    rw [← sphereAntipodal_commutes Q f z]
    exact congrArg (sphereAntipodal Q) hf

/-- The actual vertical character is complex-conjugated at the antipodal
fixed point of the same isometry. -/
theorem verticalScalar_antipodal (z : SphereBundleTotal Q)
    (f : QuaternionicIsometries Q) (hz : f • z = z) :
    verticalScalar Q (sphereAntipodal Q z)
      ⟨f, antipodal_fixed Q z f hz⟩ =
        star (verticalScalar Q z ⟨f, hz⟩) := by
  let a := coefficientSphereHomeomorph.symm z.2
  letI := coefficientVerticalComplexModule a
  letI : Nontrivial (verticalSubmodule a) :=
    Module.nontrivial_of_finrank_pos (by
      rw [coefficientVerticalComplex_finrank Q z]
      omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : verticalSubmodule a)
  have hdot : v.1 ⬝ᵥ v.1 ≠ 0 := by
    intro h
    apply hv
    apply Subtype.ext
    exact dotProduct_self_eq_zero.mp h
  let va : verticalSubmodule
      (coefficientSphereHomeomorph.symm (sphereAntipodal Q z).2) := by
    refine ⟨v.1, ?_⟩
    rw [sphereAntipodal_coefficient]
    change (-a.1) ⬝ᵥ v.1 = 0
    rw [neg_dotProduct, neg_eq_zero]
    exact v.2
  have hva : va.1 = v.1 := rfl
  have haction :
      (isotropyVerticalRepresentation Q (sphereAntipodal Q z)
        ⟨f, antipodal_fixed Q z f hz⟩ va).1 =
      (isotropyVerticalRepresentation Q z ⟨f, hz⟩ v).1 := by
    change coefficientAction Q f (sphereAntipodal Q z).1 va.1 =
      coefficientAction Q f z.1 v.1
    rw [sphereAntipodal_base, hva]
  have hr := verticalScalar_re_mul_dot Q z ⟨f, hz⟩ v
  have hra := verticalScalar_re_mul_dot Q (sphereAntipodal Q z)
    ⟨f, antipodal_fixed Q z f hz⟩ va
  rw [hva, haction] at hra
  have hre : (verticalScalar Q (sphereAntipodal Q z)
      ⟨f, antipodal_fixed Q z f hz⟩).re =
      (verticalScalar Q z ⟨f, hz⟩).re :=
    mul_right_cancel₀ hdot (hra.trans hr.symm)
  have hi := verticalScalar_im_mul_dot Q z ⟨f, hz⟩ v
  have hia := verticalScalar_im_mul_dot Q (sphereAntipodal Q z)
    ⟨f, antipodal_fixed Q z f hz⟩ va
  have hcross :
      (coefficientSphereHomeomorph.symm (sphereAntipodal Q z).2).1 ⨯₃ va.1 =
        -(a.1 ⨯₃ v.1) := by
    have hc :
        (coefficientSphereHomeomorph.symm (sphereAntipodal Q z).2).1 = -a.1 := by
      exact (congrArg Subtype.val (sphereAntipodal_coefficient Q z)).trans rfl
    calc
      _ = (-a.1) ⨯₃ va.1 := congrArg (fun u => u ⨯₃ va.1) hc
      _ = (-a.1) ⨯₃ v.1 := by rw [hva]
      _ = -(a.1 ⨯₃ v.1) := by
        funext i
        fin_cases i <;> simp [cross_apply, Pi.neg_apply]
  rw [hva, haction, hcross, dotProduct_neg] at hia
  have him : (verticalScalar Q (sphereAntipodal Q z)
      ⟨f, antipodal_fixed Q z f hz⟩).im =
      -(verticalScalar Q z ⟨f, hz⟩).im := by
    apply mul_right_cancel₀ hdot
    rw [neg_mul]
    exact hia.trans (congrArg Neg.neg hi).symm
  apply Complex.ext
  · simpa only [Complex.star_def, Complex.conj_re] using hre
  · simpa only [Complex.star_def, Complex.conj_im] using him

theorem weightCharacter_neg {r : ℕ} (μ : Fin r → ℤ)
    (t : Torus r) :
    weightCharacter (-μ) t = (weightCharacter μ t)⁻¹ := by
  simp [weightCharacter, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]

/-- The actual torus character on the antipodal vertical/contact quotient
is the inverse character, hence the negative integral weight. -/
theorem torusVerticalCircleCharacter_antipodal
    [CompactSpace M] [T3Space M] [SecondCountableTopology M]
    [PreconnectedSpace M] [Nonempty M]
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    {r : ℕ} (A : ContinuousTorusAction Q r)
    (z : SphereBundleTotal Q)
    (hz : ∀ t, A.representation t • z = z) (t : Torus r) :
    let hza : ∀ s, A.representation s • sphereAntipodal Q z =
        sphereAntipodal Q z := fun s => antipodal_fixed Q z (A.representation s) (hz s)
    torusVerticalCircleCharacter Q hR3 A (sphereAntipodal Q z) hza t =
      (torusVerticalCircleCharacter Q hR3 A z hz t)⁻¹ := by
  dsimp
  apply Circle.ext
  change verticalScalar Q (sphereAntipodal Q z)
      ⟨A.representation t, antipodal_fixed Q z (A.representation t) (hz t)⟩ =
    ↑((torusVerticalCircleCharacter Q hR3 A z hz t)⁻¹)
  rw [Circle.coe_inv_eq_conj]
  change _ = conj (verticalScalar Q z ⟨A.representation t, hz t⟩)
  rw [← Complex.star_def]
  exact verticalScalar_antipodal Q z (A.representation t) (hz t)

theorem torusVerticalCircleCharacter_negative_weight
    [CompactSpace M] [T3Space M] [SecondCountableTopology M]
    [PreconnectedSpace M] [Nonempty M]
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    {r : ℕ} (A : ContinuousTorusAction Q r)
    (z : SphereBundleTotal Q)
    (hz : ∀ t, A.representation t • z = z)
    (μ : Fin r → ℤ)
    (hμ : ∀ t, torusVerticalCircleCharacter Q hR3 A z hz t =
      weightCharacter μ t) (t : Torus r) :
    let hza : ∀ s, A.representation s • sphereAntipodal Q z =
        sphereAntipodal Q z := fun s => antipodal_fixed Q z (A.representation s) (hz s)
    torusVerticalCircleCharacter Q hR3 A (sphereAntipodal Q z) hza t =
      weightCharacter (-μ) t := by
  dsimp
  rw [torusVerticalCircleCharacter_antipodal Q hR3 A z hz t,
    hμ t, weightCharacter_neg]

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorAntipodalCharacter
