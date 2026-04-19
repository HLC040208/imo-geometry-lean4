import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

--Given Triangle $ABC$ the point $J$ is the centre of the excircle opposite the vertex $A$. This excircle is tangent to the side $BC$ at $M$, and to the lines $AB$ and $AC$ at $K$ and $L$, respectively. The lines $LM$ and $BJ$ meet at $F$, and the lines $KM$ and $CJ$ meet at $G$. Let $S$ be the point of intersection of the lines $AF$ and $BC$, and let $T$ be the point of intersection of the lines $AG$ and $BC$. Prove that $M$ is the MidPoint of $ST$. (The excircle of $ABC$ opposite the vertex $A$ is the circle that is tangent to the line segment $BC$, to the ray $AB$ beyond $B$, and to the ray $AC$ beyond $C$.)
theorem IMO_2012_P1 :
  ∀ (A B C J K L M F G S T : Point)
    (AB BC CA LM BJ KM CJ AF AG : Line)
    (Ω : Circle),
    formTriangle A B C AB BC CA ∧
    Excentre J A B C ∧
    J.isCentre Ω ∧
    TangentLineCircleAtPoint M J BC Ω ∧
    TangentLineCircleAtPoint K J AB Ω ∧
    TangentLineCircleAtPoint L J AC Ω ∧
    distinctPointsOnLine L M LM ∧
    distinctPointsOnLine B J BJ ∧
    F.onLine LM ∧
    F.onLine BJ ∧
    distinctPointsOnLine K M KM ∧
    distinctPointsOnLine C J CJ ∧
    G.onLine KM ∧
    G.onLine CJ ∧
    distinctPointsOnLine A F AF ∧
    S.onLine AF ∧
    S.onLine BC ∧
    distinctPointsOnLine A G AG ∧
    T.onLine AG ∧
    T.onLine BC →
    MidPoint S M T := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points B C as BC_line
  euclid_apply line_from_points A M as AM
  euclid_apply line_from_points B M as BM
  euclid_apply line_from_points C M as CM
  euclid_apply line_from_points A F as AF_line
  euclid_apply line_from_points A G as AG_line

  have h_excentre : Excentre J A B C := by
    euclid_finish

  have hJ_center : J.isCentre Ω := by
    euclid_finish

  have hM_tan : TangentLineCircleAtPoint M J BC Ω := by
    euclid_finish

  have hM_on_BC : M.onLine BC := by
    euclid_apply tangent_point_on_line M J BC Ω
    euclid_finish

  have hK_tan : TangentLineCircleAtPoint K J AB Ω := by
    euclid_finish

  have hK_on_AB : K.onLine AB := by
    euclid_apply tangent_point_on_line K J AB Ω
    euclid_finish

  have hL_tan : TangentLineCircleAtPoint L J AC Ω := by
    euclid_finish

  have hL_on_AC : L.onLine AC := by
    euclid_apply tangent_point_on_line L J AC Ω
    euclid_finish

  have hF_def : F.onLine LM ∧ F.onLine BJ := by
    euclid_finish

  have hF_on_LM : F.onLine LM := by
    exact hF_def.1

  have hF_on_BJ : F.onLine BJ := by
    exact hF_def.2

  have hG_def : G.onLine KM ∧ G.onLine CJ := by
    euclid_finish

  have hG_on_KM : G.onLine KM := by
    exact hG_def.1

  have hG_on_CJ : G.onLine CJ := by
    exact hG_def.2

  have hS_def : S.onLine AF ∧ S.onLine BC := by
    euclid_finish

  have hS_on_AF : S.onLine AF := by
    exact hS_def.1

  have hS_on_BC : S.onLine BC := by
    exact hS_def.2

  have hT_def : T.onLine AG ∧ T.onLine BC := by
    euclid_finish

  have hT_on_AG : T.onLine AG := by
    exact hT_def.1

  have hT_on_BC : T.onLine BC := by
    exact hT_def.2

  have h_col_ST : S.onLine BC ∧ T.onLine BC := by
    euclid_finish

  have h_mid_goal : MidPoint S M T := by
    have hS : S.onLine BC := by
      exact hS_on_BC
    have hT : T.onLine BC := by
      exact hT_on_BC
    have hM_on_BC' : M.onLine BC := by
      exact hM_on_BC
    have h_between_SMT : between S M T := by
      euclid_finish
    have hSM_eq_TM : |(S─M)| = |(M─T)| := by
      euclid_finish
    euclid_finish

  exact h_mid_goal
