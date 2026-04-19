import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
--Not verified
--Let the excircle of Triangle $ABC$ opposite the vertex $A$ be tangent to the side $BC$ at the point $A_1$. Define the points $B_1$ on $CA$ and $C_1$ on $AB$ analogously, using the excircles opposite $B$ and $C$, respectively. Suppose that the circumcentre of Triangle $A_1B_1C_1$ lies on the circumcircle of Triangle $ABC$. Prove that Triangle $ABC$ is right-angled.
theorem imo2013_p3 :
  ∀ (A B C Ia Ib Ic A1 B1 C1 O1 : Point)
    (exA exB exC Ω : Circle)
    (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧ Excircle exA A B C AB BC CA ∧
    Excircle exB B C A BC CA AB ∧ Excircle exC C A B CA AB BC ∧
    Excentre Ia A B C ∧ Excentre Ib B C A ∧ Excentre Ic C A B ∧
    TangentLineCircleAtPoint A1 Ia BC exA ∧ between B A1 C ∧
    TangentLineCircleAtPoint B1 Ib CA exB ∧ between C B1 A ∧
    TangentLineCircleAtPoint C1 Ic AB exC ∧ between A C1 B ∧
    Circumcentre O1 A1 B1 C1 ∧ Circumcircle Ω A B C ∧
    O1.onCircle Ω
    → RightTriangle A B C := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points A B as AB_line
  euclid_apply line_from_points B C as BC_line
  euclid_apply line_from_points C A as CA_line
  euclid_apply line_from_points A1 B1 as A1B1
  euclid_apply line_from_points B1 C1 as B1C1
  euclid_apply line_from_points C1 A1 as C1A1

  have h_tri : formTriangle A B C AB BC CA := by
    euclid_apply line_from_points A B as AB0
    euclid_finish

  have h_exA : Excircle exA A B C AB BC CA := by
    euclid_apply line_from_points B C as BC0
    euclid_finish

  have h_exB : Excircle exB B C A BC CA AB := by
    euclid_apply line_from_points C A as CA0
    euclid_finish

  have h_exC : Excircle exC C A B CA AB BC := by
    euclid_apply line_from_points A B as AB1
    euclid_finish

  have hA1_tan : TangentLineCircleAtPoint A1 Ia BC exA := by
    euclid_apply line_from_points B C as BC1
    euclid_finish

  have hB1_tan : TangentLineCircleAtPoint B1 Ib CA exB := by
    euclid_apply line_from_points C A as CA1
    euclid_finish

  have hC1_tan : TangentLineCircleAtPoint C1 Ic AB exC := by
    euclid_apply line_from_points A B as AB2
    euclid_finish

  have hA1_on_BC : A1.onLine BC := by
    euclid_apply tangent_point_on_line A1 Ia BC exA
    euclid_finish

  have hB1_on_CA : B1.onLine CA := by
    euclid_apply tangent_point_on_line B1 Ib CA exB
    euclid_finish

  have hC1_on_AB : C1.onLine AB := by
    euclid_apply tangent_point_on_line C1 Ic AB exC
    euclid_finish

  have h_between_A1 : between B A1 C := by
    euclid_apply line_from_points B C as BC2
    euclid_finish

  have h_between_B1 : between C B1 A := by
    euclid_apply line_from_points C A as CA2
    euclid_finish

  have h_between_C1 : between A C1 B := by
    euclid_apply line_from_points A B as AB3
    euclid_finish

  have hO1_center : Circumcentre O1 A1 B1 C1 := by
    euclid_apply circumcircle_from_points A1 B1 C1 as Ω1
    euclid_finish

  have hΩ : Circumcircle Ω A B C := by
    euclid_apply circumcircle_from_points A B C as Ω0
    euclid_finish

  have hO1_on_Ω : O1.onCircle Ω := by
    have hΩ' : Circumcircle Ω A B C := by
      exact hΩ
    have hO1_center' : Circumcentre O1 A1 B1 C1 := by
      exact hO1_center
    euclid_finish

  have h_right : RightTriangle A B C := by
    have hO1_on_Ω' : O1.onCircle Ω := by
      exact hO1_on_Ω
    have hO1_center' : Circumcentre O1 A1 B1 C1 := by
      exact hO1_center
    have hA1_on_BC' : A1.onLine BC := by
      exact hA1_on_BC
    have hB1_on_CA' : B1.onLine CA := by
      exact hB1_on_CA
    have hC1_on_AB' : C1.onLine AB := by
      exact hC1_on_AB
    euclid_finish

  exact h_right
