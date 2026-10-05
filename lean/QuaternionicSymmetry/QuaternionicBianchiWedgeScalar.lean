import QuaternionicSymmetry.QuaternionicBianchiWedgeBlocks
import QuaternionicSymmetry.QuaternionicEigenbasisFinite
import QuaternionicSymmetry.VectorBundleFrameTransitions

/-! In quaternionic dimension at least two, the three skew two-forms in
the algebraic Bianchi wedge identities are a common scalar multiple of
the actual metric quaternionic forms. -/
namespace QuaternionicSymmetry.QuaternionicBianchiWedgeScalar
open QuaternionicBianchiWedgeEight QuaternionicBianchiWedgeBlocks
open VectorBundleFrameTransitions
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def metricForm (S : QuaternionicStructure E) (t : Fin 3) :
    E →L[ℝ] E →L[ℝ] ℝ := (innerSL ℝ).comp (quaternionicGenerator S t)

theorem exists_scalar (S : QuaternionicStructure E)
    (hn : 2 ≤ S.quaternionicDimension)
    (a : Fin 3 → E →L[ℝ] E →L[ℝ] ℝ)
    (hsk : ∀ t u v, a t u v = -a t v u)
    (h : ∀ s t u v w z, wedge (fun u v => a s u v) (fun u v => metricForm S t u v) u v w z =
      wedge (fun u v => a t u v) (fun u v => metricForm S s u v) u v w z) :
    ∃ c : ℝ, ∀ t u v, a t u v = c * inner ℝ (quaternionicGenerator S t u) v := by
  classical
  obtain ⟨vals, v, b, hb, _⟩ :=
    S.exists_eigenOrthonormalBasis_fin 0 S.skewCentralizer.zero_mem
  letI : Nontrivial (Fin S.quaternionicDimension) := Fin.nontrivial_iff_two_le.mpr hn
  have horth : Orthonormal ℝ (fun p : Fin S.quaternionicDimension × Fin 4 =>
      S.frame (v p.1) p.2) := by
    simpa only [← hb] using b.orthonormal
  have hω (t : Fin 3) (p q : Fin S.quaternionicDimension × Fin 4) :
      metricForm S t (b p) (b q) = blockOmega t p q := by
    rcases p with ⟨i,k⟩
    rcases q with ⟨j,l⟩
    rw [hb, hb]
    fin_cases t
    · exact S.I_coordinate v horth i j k l
    · exact S.J_coordinate v horth i j k l
    · exact S.K_coordinate v horth i j k l
  let A : Fin 3 → (Fin S.quaternionicDimension × Fin 4) →
      (Fin S.quaternionicDimension × Fin 4) → ℝ := fun t p q => a t (b p) (b q)
  have hA : ∀ s t p q r u, wedge (A s) (blockOmega t) p q r u =
      wedge (A t) (blockOmega s) p q r u := by
    intro s t p q r u
    have he := h s t (b p) (b q) (b r) (b u)
    simpa only [wedge, hω, A] using he
  let i₀ : Fin S.quaternionicDimension := ⟨0, by omega⟩
  let c := A 0 (i₀,0) (i₀,1)
  have hcoeff := QuaternionicBianchiWedgeBlocks.coefficients A
    (fun t p q => hsk t (b p) (b q)) hA i₀
  refine ⟨c, ?_⟩
  intro t u w
  have heq : a t = c • metricForm S t := by
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro p
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro q
    change a t (b p) (b q) = c * metricForm S t (b p) (b q)
    rw [hω]
    exact hcoeff t p q
  have he := congrArg (fun f : E →L[ℝ] E →L[ℝ] ℝ => f u w) heq
  exact he

end
end QuaternionicSymmetry.QuaternionicBianchiWedgeScalar
