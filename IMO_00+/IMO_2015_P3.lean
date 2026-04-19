import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABC$ be an acute Triangle with $AB > AC$. Let $\Gamma $ be its circumcircle, $H$ its orthocenter, and $F$ the Foot of the altitude from $A$. Let $M$ be the MidPoint of $BC$. Let $Q$ be the point on $\Gamma$ such that $\angle HQA = 90^{\circ}$ and let $K$ be the point on $\Gamma$ such that $\angle HKQ = 90^{\circ}$. Assume that the points $A$, $B$, $C$, $K$ and $Q$ are all different and lie on $\Gamma$ in this order. Prove that the circumcircles of triangles $KQH$ and $FKM$ are tangent to each other.
theorem IMO_2015_P3 :
  ∀ (A B C H F M K Q D E O₁ O₂ : Point) (AB BC CA l AK KQ QA: Line) (Γ Δ Θ : Circle),
    formAcuteTriangle A B C AB BC CA ∧
    |(A─B)| > |(A─C)| ∧
    Circumcircle Γ A B C ∧
    Orthocentre H A B C D E F AB BC CA ∧
    MidPoint B M C ∧
    Q.onCircle Γ ∧ ∠ H:Q:A = ∟ ∧
    K.onCircle Γ ∧ ∠ H:K:Q = ∟ ∧
    formQuadrilateral A C K Q CA CK KQ QA ∧
    Circumcircle Δ K Q H ∧
    Circumcircle Θ F K M → (∃!(P: Point), P.onCircle Δ ∧ P.onCircle Θ) := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points A B as AB_line
  euclid_apply line_from_points B C as BC_line
  euclid_apply line_from_points C A as CA_line
  euclid_apply line_from_points K Q as KQ_line
  euclid_apply line_from_points K H as KH
  euclid_apply line_from_points Q H as QH
  euclid_apply line_from_points F K as FK
  euclid_apply line_from_points F M as FM

  have h_tri : formAcuteTriangle A B C AB BC CA := by
    euclid_apply line_from_points A C as AC0
    euclid_finish

  have h_circ : Circumcircle Γ A B C := by
    euclid_apply circumcircle_from_points A B C as Γ0
    euclid_finish

  have h_orth : Orthocentre H A B C D E F AB BC CA := by
    euclid_apply line_from_points A B as AB0
    euclid_finish

  have h_mid : MidPoint B M C := by
    euclid_apply line_from_points B C as BC0
    euclid_finish

  have hQ_on_Γ : Q.onCircle Γ := by
    have hΓ : Circumcircle Γ A B C := by
      exact h_circ
    euclid_finish

  have hK_on_Γ : K.onCircle Γ := by
    have hΓ : Circumcircle Γ A B C := by
      exact h_circ
    euclid_finish

  have h_angle_HQA : ∠ H:Q:A = ∟ := by
    euclid_apply rightAngle_eq_pi_div_two
    euclid_finish

  have h_angle_HKQ : ∠ H:K:Q = ∟ := by
    euclid_apply rightAngle_eq_pi_div_two
    euclid_finish

  have h_quad : formQuadrilateral A C K Q CA CK KQ QA := by
    euclid_apply line_from_points C K as CK0
    euclid_finish

  have hΔ : Circumcircle Δ K Q H := by
    euclid_apply circumcircle_from_points K Q H as Δ0
    euclid_finish

  have hΘ : Circumcircle Θ F K M := by
    euclid_apply circumcircle_from_points F K M as Θ0
    euclid_finish

  have h_touch : ∃! P : Point, P.onCircle Δ ∧ P.onCircle Θ := by
    have h1 : Circumcircle Δ K Q H := by
      exact hΔ
    have h2 : Circumcircle Θ F K M := by
      exact hΘ
    euclid_finish

  exact h_touch
