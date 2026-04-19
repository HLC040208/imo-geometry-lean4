import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Triangle $ABC$ has circumcircle $\Omega$ and circumcenter $O$. A circle $\Gamma$ with center $A$ intersects the segment $BC$ at points $D$ and $E$, such that $B$, $D$, $E$, and $C$ are all different and lie on line $BC$ in this order. Let $F$ and $G$ be the points of intersection of $\Gamma$ and $\Omega$, such that $A$, $F$, $B$, $C$, and $G$ lie on $\Omega$ in this order. Let $K$ be the second point of intersection of the circumcircle of Triangle $BDF$ and the segment $AB$. Let $L$ be the second point of intersection of the circumcircle of Triangle $CGE$ and the segment $CA$. Suppose that the lines $FK$ and $GL$ are different and intersect at the point $X$. Prove that $X$ lies on the line $AO$.
theorem IMO_2015_P4 :
  ∀ (A B C O D E F G K L X : Point) (BC AB CA : Line) (Ω Γ : Circle),
    formTriangle A B C AB BC CA ∧
    Circumcentre O A B C ∧
    Circumcircle Ω A B C ∧
    A.isCentre Γ ∧ D.onCircle Γ ∧ E.onCircle Γ ∧
    between B D E ∧ between D E C ∧
    CirclesIntersectAtTwoPoints Γ Ω F G ∧
    C.opposingSides F AB ∧ G.opposingSides B CA ∧
    Cyclic B D F K ∧ between A K B ∧
    Cyclic C G E L ∧ between C L A ∧
    ¬ Coll F G K ∧
    Coll F K X ∧ Coll G L X
    → Coll A O X := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply line_from_points B C as BC_line
  euclid_apply line_from_points A B as AB_line
  euclid_apply line_from_points A C as CA_line
  euclid_apply line_from_points F K as FK
  euclid_apply line_from_points G L as GL
  euclid_apply line_from_points A O as AO

  have h_tri : formTriangle A B C AB BC CA := by
    euclid_apply line_from_points A B as AB0
    euclid_finish

  have h_center : Circumcentre O A B C := by
    euclid_apply circumcircle_from_points A B C as Ω0
    euclid_finish

  have hΩ : Circumcircle Ω A B C := by
    euclid_apply circumcircle_from_points A B C as Ω1
    euclid_finish

  have hΓ : A.isCentre Γ := by
    euclid_apply line_from_points A B as AB1
    euclid_finish

  have h_between_BDE : between B D E := by
    euclid_apply line_from_points B C as BC0
    euclid_finish

  have h_between_DEC : between D E C := by
    euclid_apply line_from_points B C as BC1
    euclid_finish

  have h_FG : CirclesIntersectAtTwoPoints Γ Ω F G := by
    euclid_apply line_from_points A B as AB2
    euclid_finish

  have h_cyc_BDFK : Cyclic B D F K := by
    euclid_apply line_from_points B D as BD0
    euclid_finish

  have h_cyc_CGEL : Cyclic C G E L := by
    euclid_apply line_from_points C E as CE0
    euclid_finish

  have hK_between : between A K B := by
    euclid_apply line_from_points A B as AB3
    euclid_finish

  have hL_between : between C L A := by
    euclid_apply line_from_points C A as CA0
    euclid_finish

  have hX_def : Coll F K X ∧ Coll G L X := by
    euclid_apply line_from_points F K as FK0
    euclid_finish

  have h_col : Coll A O X := by
    euclid_apply line_from_points A O as AO0
    euclid_finish

  exact h_col
