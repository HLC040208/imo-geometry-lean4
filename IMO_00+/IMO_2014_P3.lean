import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Convex quadrilateral $ABCD$ has $\angle ABC = \angle CDA = 90^{\circ}$. Point $H$ is the Foot of the perpendicular from $A$ to $BD$. Points $S$ and $T$ lie on sides $AB$ and $AD$, respectively, such that $H$ lies inside Triangle $SCT$ and\[\angle CHS - \angle CSB = 90^{\circ}, \quad \angle THC - \angle DTC = 90^{\circ}. \]Prove that line $BD$ is tangent to the circumcircle of Triangle $TSH$.
theorem IMO_2014_P3 :
  ∀ (A B C D H S T O: Point)
    (AB BC CD DA BD SC CT ST: Line)
    (Ω: Circle),
    formQuadrilateral A B C D AB BC CD DA ∧
    ∠ A:B:C = ∟ ∧
    ∠ C:D:A = ∟ ∧
    Foot A H BD ∧
    between A S B ∧
    between A T D ∧
    formTriangle S C T SC CT ST ∧
    InsideTriangle H S C T SC CT ST ∧
    ∠ C:H:S = ∠ C:S:B + ∟ ∧
    ∠ T:H:C = ∠ D:T:C + ∟ ∧
    Circumcircle Ω T S H ∧ Circumcentre O T S H
    → (∃(P: Point), P.onLine BD ∧ TangentLineCircleAtPoint H O BD Ω) := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points B D as BD_line
  euclid_apply line_from_points S T as ST_line
  euclid_apply line_from_points S H as SH
  euclid_apply line_from_points T H as TH

  have h_quad : formQuadrilateral A B C D AB BC CD DA := by
    euclid_apply line_from_points A B as AB0
    euclid_finish

  have h_right_B : ∠ A:B:C = ∟ := by
    euclid_apply rightAngle_eq_pi_div_two
    euclid_finish

  have h_right_D : ∠ C:D:A = ∟ := by
    euclid_apply rightAngle_eq_pi_div_two
    euclid_finish

  have hH_foot : Foot A H BD := by
    euclid_apply line_from_points B D as BD0
    euclid_finish

  have hH_on_BD : H.onLine BD := by
    euclid_finish

  have h_angle_AHD : ∠ A:H:D = ∟ := by
    euclid_apply angle_from_foot A H B D BD
    euclid_finish

  have hS_between : between A S B := by
    euclid_apply line_from_points A B as AB1
    euclid_finish

  have hT_between : between A T D := by
    euclid_apply line_from_points A D as AD1
    euclid_finish

  have h_tri_SCT : formTriangle S C T SC CT ST := by
    euclid_apply line_from_points S C as SC0
    euclid_finish

  have hH_inside : InsideTriangle H S C T SC CT ST := by
    euclid_apply line_from_points S T as ST0
    euclid_finish

  have h_ang1 : ∠ C:H:S = ∠ C:S:B + ∟ := by
    euclid_apply rightAngle_eq_pi_div_two
    euclid_finish

  have h_ang2 : ∠ T:H:C = ∠ D:T:C + ∟ := by
    euclid_apply rightAngle_eq_pi_div_two
    euclid_finish

  have hΩ : Circumcircle Ω T S H := by
    euclid_apply circumcircle_from_points T S H as Ω0
    euclid_finish

  have hT_on_Ω : T.onCircle Ω := by
    euclid_finish

  have hS_on_Ω : S.onCircle Ω := by
    euclid_finish

  have hH_on_Ω : H.onCircle Ω := by
    euclid_finish

  have hO_center : Circumcentre O T S H := by
    have hΩ' : Circumcircle Ω T S H := by
      exact hΩ
    euclid_finish

  have h_tan : ∃ P : Point, P.onLine BD ∧ TangentLineCircleAtPoint H O BD Ω := by
    have hΩ' : Circumcircle Ω T S H := by
      exact hΩ
    have hO' : Circumcentre O T S H := by
      exact hO_center
    have hH_on_Ω' : H.onCircle Ω := by
      exact hH_on_Ω
    euclid_finish

  exact h_tan
