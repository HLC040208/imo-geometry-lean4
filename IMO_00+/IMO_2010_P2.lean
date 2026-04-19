import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

--Given a Triangle $ABC$, with $I$ as its incenter and $\Gamma$ as its circumcircle, $AI$ intersects $\Gamma$ again at $D$. Let $E$ be a point on the arc $BDC$, and $F$ a point on the segment $BC$, such that $\angle BAF=\angle CAE < \dfrac12\angle BAC$. If $G$ is the MidPoint of $IF$, prove that the meeting point of the lines $EI$ and $DG$ lies on $\Gamma$.
theorem IMO_2010_P2 :
  ∀ (A B C D E F G I X : Point) (Γ : Circle) (AB BC CA AI EI DG : Line),
    formTriangle A B C AB BC CA ∧
    Incentre I A B C ∧
    Circumcircle Γ A B C ∧
    distinctPointsOnLine A I AI ∧
    D.onCircle Γ ∧
    D.onLine AI ∧
    D ≠ A ∧
    distinctPointsOnLine E I EI ∧
    E.onCircle Γ ∧
    E.opposingSides A BC ∧
    between B F C ∧
    ∠ B:A:F = ∠ C:A:E ∧
    (∠ B:A:F + ∠ B:A:F < ∠ B:A:C) ∧
    MidPoint I G F ∧
    distinctPointsOnLine D G DG ∧
    X.onLine EI ∧
    X.onLine DG →
    X.onCircle Γ := by
  euclid_intros
  euclid_apply line_from_points A E as AE
  euclid_apply line_from_points A F as AF
  euclid_apply line_from_points E F as EF
  euclid_apply line_from_points I F as IF
  euclid_apply line_from_points A D as AD
  euclid_apply line_from_points B D as BD
  euclid_apply line_from_points C D as CD
  euclid_apply line_from_points B C as BC_line
  euclid_apply line_from_points E X as EX
  euclid_apply line_from_points D X as DX

  have h_A_bisects_FAE : ∠ F:A:I = ∠ I:A:E := by
    have h_bisector_AI : ∠ B:A:I = ∠ I:A:C := by
      euclid_apply incentre_angle_property I A B C
      euclid_finish
    have h_given_FAE : ∠ B:A:F = ∠ C:A:E := by
      euclid_finish
    euclid_finish

  have h_D_on_bisector : ∠ F:A:D = ∠ D:A:E := by
    have h_collinear_AID : Coll A I D := by
      euclid_finish
    have h_angle_FAI : ∠ F:A:I = ∠ I:A:E := by
      exact h_A_bisects_FAE
    euclid_finish

  have h_D_on_A_bisector_BAC : ∠ D:A:B = ∠ C:A:D := by
    have h_bisector_AI : ∠ B:A:I = ∠ I:A:C := by
      euclid_apply incentre_angle_property I A B C
      euclid_finish
    have h_collinear_AID : Coll A I D := by
      euclid_finish
    euclid_finish

  have h_DB_eq_DC : |(D─B)| = |(D─C)| := by
    have h_eq_angles : ∠ D:B:C = ∠ B:C:D := by
      have h1 : ∠ D:B:C = ∠ D:A:C := by
        euclid_apply cyclic_eq_angles C D B A CD Γ
        euclid_finish
      have h2 : ∠ B:C:D = ∠ B:A:D := by
        euclid_apply cyclic_eq_angles B D C A BD Γ
        euclid_finish
      euclid_finish
    euclid_apply isoTriangle_if_eq_angles D B C
    euclid_finish

  have h_BDC_supp_A : ∠ B:D:C + ∠ B:A:C = ∟ + ∟ := by
    euclid_apply cyclic_supp_angles B C D A BC Γ
    euclid_finish

  have h_DAF_eq_EAD : ∠ D:A:F = ∠ E:A:D := by
    have h_bisector_D : ∠ F:A:D = ∠ D:A:E := by
      exact h_D_on_bisector
    euclid_finish

  have h_mid_IF : |(G─I)| = |(G─F)| := by
    have h_midpoint : MidPoint I G F := by
      euclid_finish
    euclid_finish

  have h_EI_X : Coll E I X := by
    have hX_on_EI : X.onLine EI := by
      euclid_finish
    have hE_on_EI : E.onLine EI := by
      euclid_finish
    have hI_on_EI : I.onLine EI := by
      euclid_finish
    euclid_finish

  have h_DG_X : Coll D G X := by
    have hX_on_DG : X.onLine DG := by
      euclid_finish
    have hD_on_DG : D.onLine DG := by
      euclid_finish
    have hG_on_DG : G.onLine DG := by
      euclid_finish
    euclid_finish

  have h_goal_supp : ∠ B:X:C + ∠ B:D:C = ∟ + ∟ := by
    have h_collinear_AID : Coll A I D := by
      euclid_finish
    have h_collinear_BFC : Coll B F C := by
      euclid_finish
    have h_collinear_EIX : Coll E I X := by
      exact h_EI_X
    have h_collinear_DGX : Coll D G X := by
      exact h_DG_X
    have h_midpoint_G : MidPoint I G F := by
      euclid_finish
    have h_angle_bisector_D : ∠ D:A:F = ∠ E:A:D := by
      exact h_DAF_eq_EAD
    have h_supp_BDC : ∠ B:D:C + ∠ B:A:C = ∟ + ∟ := by
      exact h_BDC_supp_A
    euclid_finish

  have hB_on_circle : B.onCircle Γ := by
    euclid_finish

  have hC_on_circle : C.onCircle Γ := by
    euclid_finish

  have h_X_opposing_D_BC : X.opposingSides D BC := by
    euclid_finish

  euclid_apply cyclic_if_supp_angles B C D X BC Γ
  · euclid_finish
  · exact h_goal_supp
  · euclid_finish
