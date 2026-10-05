import QuaternionicSymmetry.BilinearExterior
import QuaternionicSymmetry.ExteriorDuality
import QuaternionicSymmetry.QuaternionicStructure
import QuaternionicSymmetry.EvenForms

/-! The quaternionic skew centralizer as actual exterior two-forms.

The metric identifies a skew endomorphism with a bilinear form; its exterior
representative is verified through the canonical pairing. The image subspace
in the commutative even exterior algebra is suitable for Gaussian averaging.
-/

namespace QuaternionicSymmetry.HyperholomorphicExterior

open Module

noncomputable section

variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def innerBilinear : (V →ₗ[ℝ] V) →ₗ[ℝ] (V →ₗ[ℝ] V →ₗ[ℝ] ℝ) where
  toFun A := (innerₗ V).comp A
  map_add' A B := by ext v w; simp [innerₗ]
  map_smul' r A := by ext v w; simp [innerₗ]

@[simp] theorem innerBilinear_apply (A : V →ₗ[ℝ] V) (v w : V) :
    innerBilinear A v w = inner ℝ (A v) w := rfl

/-- The degree-two exterior covector associated to an endomorphism. -/
def form (b : Basis ι ℝ V) : (V →ₗ[ℝ] V) →ₗ[ℝ]
    ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V) :=
  (BilinearExterior.ofBilinearLinear b).comp innerBilinear

theorem form_basis_independent {κ : Type*} [Fintype κ]
    (b : Basis ι ℝ V) (c : Basis κ ℝ V) (A : V →ₗ[ℝ] V) : form b A = form c A :=
  ExteriorDuality.ofBilinear_basis_independent b c (innerBilinear A)

theorem evaluate_form (b : Basis ι ℝ V) (A : V →ₗ[ℝ] V)
    (hA : ∀ v w, inner ℝ (A v) w = -inner ℝ v (A w)) (v w : V) :
    BilinearExterior.evaluate v w (form b A) = inner ℝ (A v) w := by
  apply BilinearExterior.evaluate_of_skew
  intro x y
  change inner ℝ (A x) y = -inner ℝ (A y) x
  rw [hA x y]
  rw [real_inner_comm (A y) x]

/-- The exterior representation is faithful on skew-adjoint endomorphisms. -/
theorem form_injective_on_skew (b : Basis ι ℝ V) (A B : V →ₗ[ℝ] V)
    (hA : ∀ v w, inner ℝ (A v) w = -inner ℝ v (A w))
    (hB : ∀ v w, inner ℝ (B v) w = -inner ℝ v (B w))
    (h : form b A = form b B) : A = B := by
  ext v
  apply ext_inner_right ℝ
  intro w
  rw [← evaluate_form b A hA, ← evaluate_form b B hB, h]

private def toEven : ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V) →ₗ[ℝ]
    EvenForms.evenSubalgebra ℝ (Module.Dual ℝ V) where
  toFun := EvenForms.ofTwoForm
  map_add' x y := by ext; rfl
  map_smul' r x := by ext; rfl

def evenForm (b : Basis ι ℝ V) : (V →ₗ[ℝ] V) →ₗ[ℝ]
    EvenForms.evenSubalgebra ℝ (Module.Dual ℝ V) := toEven.comp (form b)

theorem evenForm_basis_independent {κ : Type*} [Fintype κ]
    (b : Basis ι ℝ V) (c : Basis κ ℝ V) : evenForm b = evenForm c := by
  apply LinearMap.ext
  intro A
  change toEven (form b A) = toEven (form c A)
  rw [form_basis_independent b c A]

/-- The actual subspace of exterior forms arising from the quaternionic skew centralizer. -/
def formSpace (Q : QuaternionicStructure V) (b : Basis ι ℝ V) :
    Submodule ℝ (EvenForms.evenSubalgebra ℝ (Module.Dual ℝ V)) :=
  Q.skewCentralizer.map (evenForm b)

theorem formSpace_basis_independent {κ : Type*} [Fintype κ]
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V) (c : Basis κ ℝ V) :
    formSpace Q b = formSpace Q c := by
  unfold formSpace
  rw [evenForm_basis_independent b c]

theorem evenForm_mem (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (A : V →ₗ[ℝ] V) (hA : A ∈ Q.skewCentralizer) : evenForm b A ∈ formSpace Q b :=
  Submodule.mem_map.mpr ⟨A, hA, rfl⟩

theorem formSpace_mem_iff (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (θ : EvenForms.evenSubalgebra ℝ (Module.Dual ℝ V)) :
    θ ∈ formSpace Q b ↔ ∃ A ∈ Q.skewCentralizer, evenForm b A = θ :=
  Submodule.mem_map

theorem evaluate_form_I (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (A : V →ₗ[ℝ] V) (hA : A ∈ Q.skewCentralizer) (v w : V) :
    BilinearExterior.evaluate (Q.I v) (Q.I w) (form b A) =
      BilinearExterior.evaluate v w (form b A) := by
  rw [evaluate_form b A hA.1, evaluate_form b A hA.1, hA.2.1]
  exact Q.I.inner_map_map (A v) w

theorem evaluate_form_J (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (A : V →ₗ[ℝ] V) (hA : A ∈ Q.skewCentralizer) (v w : V) :
    BilinearExterior.evaluate (Q.J v) (Q.J w) (form b A) =
      BilinearExterior.evaluate v w (form b A) := by
  rw [evaluate_form b A hA.1, evaluate_form b A hA.1, hA.2.2]
  exact Q.J.inner_map_map (A v) w

theorem evaluate_form_K (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (A : V →ₗ[ℝ] V) (hA : A ∈ Q.skewCentralizer) (v w : V) :
    BilinearExterior.evaluate (Q.K v) (Q.K w) (form b A) =
      BilinearExterior.evaluate v w (form b A) := by
  rw [evaluate_form b A hA.1, evaluate_form b A hA.1, Q.commute_K A hA.2.1 hA.2.2]
  exact Q.K.inner_map_map (A v) w

end
end QuaternionicSymmetry.HyperholomorphicExterior
