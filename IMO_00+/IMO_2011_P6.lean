import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

--Let $ABC$ be an acute Triangle with circumcircle $\Gamma$. Let $\ell$ be a tangent line to $\Gamma$, and let $\ell_a, \ell_b$ and $\ell_c$ be the lines obtained by reflecting $\ell$ in the lines $BC$, $CA$ and $AB$, respectively. Show that the circumcircle of the Triangle determined by the lines $\ell_a, \ell_b$ and $\ell_c$ is tangent to the circle $\Gamma$.
theorem IMO_2011_P6 :
  ∀ (A B C A' B' C' P O X Y Z : Point)
    (l la lb lc AB BC CA : Line) (Γ Δ : Circle),
    formAcuteTriangle A B C AB BC CA ∧
    Circumcircle Γ A B C ∧
    O.isCentre Γ ∧
    TangentLineCircleAtPoint P O l Γ ∧
    TwoLinesIntersectAtPoint l AB X ∧
    TwoLinesIntersectAtPoint l BC Y ∧
    TwoLinesIntersectAtPoint l CA Z ∧
    (∀ M : Point, M.onLine lc ∧ M ≠ X →
      (∠ M:X:B = ∠ B:X:P ∨ ∠ M:X:B + ∠ B:X:P = ∟ + ∟)) ∧
    (∀ M : Point, M.onLine la ∧ M ≠ Y →
      (∠ M:Y:C = ∠ C:Y:P ∨ ∠ M:Y:C + ∠ C:Y:P = ∟ + ∟)) ∧
    (∀ M : Point, M.onLine lb ∧ M ≠ Z →
      (∠ M:Z:A = ∠ A:Z:P ∨ ∠ M:Z:A + ∠ A:Z:P = ∟ + ∟)) ∧
    TwoLinesIntersectAtPoint lb lc A' ∧
    TwoLinesIntersectAtPoint lc la B' ∧
    TwoLinesIntersectAtPoint la lb C' ∧
    Circumcircle Δ A' B' C' →
    ∃! P : Point, P.onCircle Δ ∧ P.onCircle Γ := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points A B as AB_line
  euclid_apply line_from_points B C as BC_line
  euclid_apply line_from_points C A as CA_line
  euclid_apply line_from_points O P as OP
  euclid_apply line_from_points A' B' as A1B1
  euclid_apply line_from_points B' C' as B1C1
  euclid_apply line_from_points C' A' as C1A1

  have hΓ : Circumcircle Γ A B C := by
    euclid_finish

  have hO : O.isCentre Γ := by
    euclid_finish

  have h_tan : TangentLineCircleAtPoint P O l Γ := by
    euclid_finish

  have hP_on_l : P.onLine l := by
    have h1 : TangentLineCircleAtPoint P O l Γ := by
      exact h_tan
    euclid_finish

  have hP_on_Γ : P.onCircle Γ := by
    have h1 : TangentLineCircleAtPoint P O l Γ := by
      exact h_tan
    euclid_finish

  have hX_inter : TwoLinesIntersectAtPoint l AB X := by
    euclid_finish

  have hY_inter : TwoLinesIntersectAtPoint l BC Y := by
    euclid_finish

  have hZ_inter : TwoLinesIntersectAtPoint l CA Z := by
    euclid_finish

  have hX_on_l : X.onLine l := by
    have h1 : TwoLinesIntersectAtPoint l AB X := by
      exact hX_inter
    euclid_finish

  have hY_on_l : Y.onLine l := by
    have h1 : TwoLinesIntersectAtPoint l BC Y := by
      exact hY_inter
    euclid_finish

  have hZ_on_l : Z.onLine l := by
    have h1 : TwoLinesIntersectAtPoint l CA Z := by
      exact hZ_inter
    euclid_finish

  have hA'_inter : TwoLinesIntersectAtPoint lb lc A' := by
    euclid_finish

  have hB'_inter : TwoLinesIntersectAtPoint lc la B' := by
    euclid_finish

  have hC'_inter : TwoLinesIntersectAtPoint la lb C' := by
    euclid_finish

  have hA'_on_lb : A'.onLine lb := by
    have h1 : TwoLinesIntersectAtPoint lb lc A' := by
      exact hA'_inter
    euclid_finish

  have hB'_on_lc : B'.onLine lc := by
    have h1 : TwoLinesIntersectAtPoint lc la B' := by
      exact hB'_inter
    euclid_finish

  have hC'_on_la : C'.onLine la := by
    have h1 : TwoLinesIntersectAtPoint la lb C' := by
      exact hC'_inter
    euclid_finish

  have hΔ : Circumcircle Δ A' B' C' := by
    euclid_finish

  have hA'_on_Δ : A'.onCircle Δ := by
    have h1 : Circumcircle Δ A' B' C' := by
      exact hΔ
    euclid_finish

  have hB'_on_Δ : B'.onCircle Δ := by
    have h1 : Circumcircle Δ A' B' C' := by
      exact hΔ
    euclid_finish

  have hC'_on_Δ : C'.onCircle Δ := by
    have h1 : Circumcircle Δ A' B' C' := by
      exact hΔ
    euclid_finish

  have h_exist : ∃ P : Point, P.onCircle Δ ∧ P.onCircle Γ := by
    have h1 : A'.onLine lb := by
      exact hA'_on_lb
    have h2 : B'.onLine lc := by
      exact hB'_on_lc
    have h3 : C'.onLine la := by
      exact hC'_on_la
    have h4 : Circumcircle Δ A' B' C' := by
      exact hΔ
    have h5 : Circumcircle Γ A B C := by
      exact hΓ
    have h6 : A'.onCircle Δ := by
      exact hA'_on_Δ
    have h7 : B'.onCircle Δ := by
      exact hB'_on_Δ
    have h8 : C'.onCircle Δ := by
      exact hC'_on_Δ
    euclid_finish

  rcases h_exist with ⟨P0, hP0Δ, hP0Γ⟩
  refine ⟨P0, ?_, ?_⟩
  · exact ⟨hP0Δ, hP0Γ⟩
  · intro P1 hP1
    have hP1Δ : P1.onCircle Δ := by
      exact hP1.1
    have hP1Γ : P1.onCircle Γ := by
      exact hP1.2
    have h_tan' : TangentLineCircleAtPoint P O l Γ := by
      exact h_tan
    have hP_on_l' : P.onLine l := by
      exact hP_on_l
    have hP_on_Γ' : P.onCircle Γ := by
      exact hP_on_Γ
    euclid_finish
