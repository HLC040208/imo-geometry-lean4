import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABC$ be an acute Triangle with orthocenter $H$, and let $W$ be a point on the side $BC$, lying strictly between $B$ and $C$. The points $M$ and $N$ are the feet of the altitudes from $B$ and $C$, respectively. Denote by $\omega_1$ is the circumcircle of $BWN$, and let $X$ be the point on $\omega_1$ such that $WX$ is a Diameter of $\omega_1$. Analogously, denote by $\omega_2$ the circumcircle of Triangle $CWM$, and let $Y$ be the point such that $WY$ is a Diameter of $\omega_2$. Prove that $X,Y$ and $H$ are collinear.
theorem IMO_2013_P4 :
  ∀ (A B C H W M N X Y O1 O2 : Point) (AB BC CA : Line) (ω1 ω2 : Circle),
    formAcuteTriangle A B C AB BC CA ∧
    between B W C ∧
    Foot B M CA ∧
    Foot C N AB ∧
    Coll B H M ∧
    Coll C H N ∧
    Circumcircle ω1 B W N ∧
    Diameter W X O1 ω1 ∧
    Circumcircle ω2 C W M ∧
    Diameter W Y O2 ω2 →
    Coll X H Y := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points B C as BC_line
  euclid_apply line_from_points B H as BH
  euclid_apply line_from_points C H as CH
  euclid_apply line_from_points W X as WX
  euclid_apply line_from_points W Y as WY

  have h_tri : formAcuteTriangle A B C AB BC CA := by
    euclid_apply line_from_points A B as AB0
    euclid_finish

  have hW_between : between B W C := by
    euclid_apply line_from_points B C as BC0
    euclid_finish

  have hM_foot : Foot B M CA := by
    euclid_apply line_from_points C A as CA0
    euclid_finish

  have hN_foot : Foot C N AB := by
    euclid_apply line_from_points A B as AB1
    euclid_finish

  have h_between_CMA : between C M A := by
    euclid_apply acuteTriangle_foot_between B C A M CA
    euclid_finish

  have h_between_ANB : between A N B := by
    euclid_apply acuteTriangle_foot_between C A B N AB
    euclid_finish

  have hBH : Coll B H M := by
    euclid_apply line_from_points B H as BH0
    euclid_finish

  have hCH : Coll C H N := by
    euclid_apply line_from_points C H as CH0
    euclid_finish

  have hω1 : Circumcircle ω1 B W N := by
    euclid_apply line_from_points B W as BW0
    euclid_finish

  have hω2 : Circumcircle ω2 C W M := by
    euclid_apply line_from_points C W as CW0
    euclid_finish

  have hWX_diam : Diameter W X O1 ω1 := by
    euclid_apply line_from_points W X as WX0
    euclid_finish

  have hWY_diam : Diameter W Y O2 ω2 := by
    euclid_apply line_from_points W Y as WY0
    euclid_finish

  have hX_on_ω1 : X.onCircle ω1 := by
    have h_diam : Diameter W X O1 ω1 := by
      exact hWX_diam
    have hω1' : Circumcircle ω1 B W N := by
      exact hω1
    euclid_finish

  have hY_on_ω2 : Y.onCircle ω2 := by
    have h_diam : Diameter W Y O2 ω2 := by
      exact hWY_diam
    have hω2' : Circumcircle ω2 C W M := by
      exact hω2
    euclid_finish

  have hW_on_ω1 : W.onCircle ω1 := by
    have h_diam : Diameter W X O1 ω1 := by
      exact hWX_diam
    have hω1' : Circumcircle ω1 B W N := by
      exact hω1
    euclid_finish

  have hW_on_ω2 : W.onCircle ω2 := by
    have h_diam : Diameter W Y O2 ω2 := by
      exact hWY_diam
    have hω2' : Circumcircle ω2 C W M := by
      exact hω2
    euclid_finish

  have h_col : Coll X H Y := by
    have hBH' : Coll B H M := by
      exact hBH
    have hCH' : Coll C H N := by
      exact hCH
    have hM_on_CA : M.onLine CA := by
      euclid_finish
    have hN_on_AB : N.onLine AB := by
      euclid_finish
    euclid_finish

  exact h_col
