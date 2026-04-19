import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
--Let $I$ be the incentre of acute Triangle $ABC$ with $AB ≠ AC$. The incircle $\omega$ of $ABC$ is tangent to sides $BC, CA$, and $AB$ at $D, E,$ and $F$, respectively. The line through $D$ perpendicular to $EF$ meets $\omega$ at $R$. Line $AR$ meets $\omega$ again at $P$. The circumcircles of Triangle $PCE$ and $PBF$ meet again at $Q$. Prove that lines $DI$ and $PQ$ meet on the line through $A$ perpendicular to $AI$.
theorem IMO_2019_P6 :
  ∀ (A B C I D E F R P Q X : Point)
    (ω : Circle)
    (BC CA AB EF Ld ARline AIline DIline PQline Lperp : Line),
    formAcuteTriangle A B C AB BC CA ∧
    |(A─B)| ≠ |(A─C)| ∧
    Incircle ω A B C AB BC CA ∧
    Incentre I A B C ∧
    TangentLineCircleAtPoint D I BC ω ∧
    TangentLineCircleAtPoint E I CA ω ∧
    TangentLineCircleAtPoint F I AB ω ∧
    distinctPointsOnLine E F EF ∧
    distinctPointsOnLine D R Ld ∧
    PerpLineAtPoint Ld EF D ∧
    R.onCircle ω ∧
    distinctPointsOnLine A R ARline ∧
    P.onLine ARline ∧
    P.onCircle ω ∧
    P ≠ R ∧
    Cyclic P C E Q ∧
    Cyclic P B F Q ∧
    Q ≠ P ∧
    distinctPointsOnLine A I AIline ∧
    distinctPointsOnLine D I DIline ∧
    distinctPointsOnLine P Q PQline ∧
    TwoLinesIntersectAtPoint DIline PQline X ∧
    PerpLineAtPoint Lperp AIline A
    → X.onLine Lperp :=
  by
  euclid_intros
  have h_tri : formAcuteTriangle A B C AB BC CA := by
    euclid_apply line_from_points A B as AB0
    euclid_finish

  have h_inc : Incircle ω A B C AB BC CA := by
    euclid_apply line_from_points A C as AC0
    euclid_finish

  have h_incentre : Incentre I A B C := by
    euclid_apply line_from_points B C as BC0
    euclid_finish

  have h_tan_D : TangentLineCircleAtPoint D I BC ω := by
    euclid_apply line_from_points B C as BC1
    euclid_finish

  have h_tan_E : TangentLineCircleAtPoint E I CA ω := by
    euclid_apply line_from_points C A as CA0
    euclid_finish

  have h_tan_F : TangentLineCircleAtPoint F I AB ω := by
    euclid_apply line_from_points A B as AB1
    euclid_finish

  have hD_on_BC : D.onLine BC := by
    euclid_apply tangent_point_on_line D I BC ω
    euclid_finish

  have hE_on_CA : E.onLine CA := by
    euclid_apply tangent_point_on_line E I CA ω
    euclid_finish

  have hF_on_AB : F.onLine AB := by
    euclid_apply tangent_point_on_line F I AB ω
    euclid_finish

  have h_perp_DE : PerpLineAtPoint Ld EF D := by
    euclid_apply line_from_points E F as EF0
    euclid_finish

  have hD_on_Ld : D.onLine Ld := by
    euclid_apply line_from_points D R as DR0
    euclid_finish

  have h_R_on : R.onCircle ω := by
    euclid_apply line_from_points A R as AR1
    euclid_finish

  have h_P_on : P.onCircle ω := by
    euclid_apply line_from_points A P as AP1
    euclid_finish

  have h_cyc_PCE : Cyclic P C E Q := by
    euclid_apply circumcircle_from_points P C E as ω3
    euclid_finish

  have h_cyc_PBF : Cyclic P B F Q := by
    euclid_apply circumcircle_from_points P B F as ω4
    euclid_finish

  have h_inter : TwoLinesIntersectAtPoint DIline PQline X := by
    euclid_apply line_from_points D I as DI1
    euclid_finish

  have h_perp_AI : PerpLineAtPoint Lperp AIline A := by
    euclid_apply line_from_points A I as AI1
    euclid_finish

  have h_goal : X.onLine Lperp := by
    euclid_apply line_from_points P Q as PQ1
    euclid_finish

  exact h_goal
