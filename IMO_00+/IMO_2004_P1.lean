import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

--Let $ABC$ be an acute-angled Triangle with $AB≠AC$. The circle with Diameter $BC$ intersects the sides $AB$ and $AC$ at $M$ and $N$ respectively. Denote by $O$ the MidPoint of the side $BC$. The bisectors of the angles $\angle BAC$ and $\angle MON$ intersect at $R$. Prove that the circumcircles of the triangles $BMR$ and $CNR$ have a common point lying on the side $BC$.
theorem IMO_2004_P1 :
  ∀ (A B C M N O R X : Point) (AB BC CA : Line) (Ω : Circle),
    formAcuteTriangle A B C AB BC CA ∧
    |(A─B)| ≠ |(A─C)| ∧
    Diameter B C O Ω ∧
    M.onCircle Ω ∧
    N.onCircle Ω ∧
    between A M B ∧
    between A N C ∧
    MidPoint B O C ∧
    ∠ B:A:R = ∠ R:A:C ∧
    ∠ M:O:R = ∠ R:O:N →
  ∃ (X : Point), X.onLine BC ∧ Cyclic B M R X ∧ Cyclic C N R X := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points A R as AR
  euclid_apply line_from_points B R as BR
  euclid_apply line_from_points C R as CR
  euclid_apply line_from_points M R as MR
  euclid_apply line_from_points N R as NR
  euclid_apply line_from_points O R as OR

  have h_tri : formTriangle A B C AB BC CA := by
    euclid_finish

  have h_mid : MidPoint B O C := by
    euclid_finish

  have h_diam : Diameter B C O Ω := by
    euclid_finish

  have hM_right : ∠ B:M:C = ∟ := by
    euclid_apply ThalesTheorem B C M O Ω
    euclid_finish

  have hN_right : ∠ B:N:C = ∟ := by
    euclid_apply ThalesTheorem B C N O Ω
    euclid_finish

  have hO_on_BC : O.onLine BC := by
    have h_midpoint : MidPoint B O C := by
      exact h_mid
    euclid_finish

  have h_angle_A : ∠ B:A:R = ∠ R:A:C := by
    euclid_finish

  have h_angle_O : ∠ M:O:R = ∠ R:O:N := by
    euclid_finish

  have hM_on_circle : M.onCircle Ω := by
    euclid_finish

  have hN_on_circle : N.onCircle Ω := by
    euclid_finish

  have hB_on_circle : B.onCircle Ω := by
    euclid_finish

  have hC_on_circle : C.onCircle Ω := by
    euclid_finish

  have h_BMRO : Cyclic B M R O := by
    have h_bisector_O : ∠ M:O:R = ∠ R:O:N := by
      exact h_angle_O
    have hM_arc : M.onCircle Ω := by
      exact hM_on_circle
    have hB_arc : B.onCircle Ω := by
      exact hB_on_circle
    euclid_finish

  have h_CNRO : Cyclic C N R O := by
    have h_bisector_O : ∠ M:O:R = ∠ R:O:N := by
      exact h_angle_O
    have hN_arc : N.onCircle Ω := by
      exact hN_on_circle
    have hC_arc : C.onCircle Ω := by
      exact hC_on_circle
    euclid_finish

  use O
  constructor
  · exact hO_on_BC
  · constructor
    · exact h_BMRO
    · exact h_CNRO
