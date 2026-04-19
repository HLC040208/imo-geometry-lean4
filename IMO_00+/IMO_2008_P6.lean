import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0

--Let $ABCD$ be a convex quadrilateral with $BA≠ BC$. Denote the incircles of triangles $ABC$ and $ADC$ by $\omega_{1}$ and $\omega_{2}$ respectively. Suppose that there exists a circle $\omega$ tangent to ray $BA$ beyond $A$ and to the ray $BC$ beyond $C$, which is also tangent to the lines $AD$ and $CD$. Prove that the common external tangents to $\omega_{1}$ and $\omega_{2}$ intersect on $\omega$.
theorem IMO_2008_P6 :
  ∀ (A B C D X: Point) (AB BC CD DA CA l₁ l₂: Line) (ω₁ ω₂ ω : Circle),
    formQuadrilateral A B C D AB BC CD DA ∧ ¬ (|(A─B)| = |(B─C)|) ∧
    Incircle ω₁ A B C AB BC CA ∧ Incircle ω₂ C D A CD DA CA ∧
    TangentLineCircle AB ω ∧ TangentLineCircle BC ω ∧ TangentLineCircle DA ω ∧ TangentLineCircle CD ω ∧
    TangentLineCircle l₁ ω₁ ∧ TangentLineCircle l₁ ω₂ ∧ TangentLineCircle l₂ ω₁ ∧ TangentLineCircle l₂ ω₂ ∧
    TwoLinesIntersectAtPoint l₁ l₂ X →  X.onCircle ω := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  have h_incircle1 : Incircle ω₁ A B C AB BC CA := by
    euclid_finish

  have h_incircle2 : Incircle ω₂ C D A CD DA CA := by
    euclid_finish

  have h_AB_tangent_ω : TangentLineCircle AB ω := by
    euclid_finish

  have h_BC_tangent_ω : TangentLineCircle BC ω := by
    euclid_finish

  have h_DA_tangent_ω : TangentLineCircle DA ω := by
    euclid_finish

  have h_CD_tangent_ω : TangentLineCircle CD ω := by
    euclid_finish

  have h_l1_tangent_ω1 : TangentLineCircle l₁ ω₁ := by
    euclid_finish

  have h_l1_tangent_ω2 : TangentLineCircle l₁ ω₂ := by
    euclid_finish

  have h_l2_tangent_ω1 : TangentLineCircle l₂ ω₁ := by
    euclid_finish

  have h_l2_tangent_ω2 : TangentLineCircle l₂ ω₂ := by
    euclid_finish

  have h_inter : TwoLinesIntersectAtPoint l₁ l₂ X := by
    euclid_finish

  have hX_on_l1 : X.onLine l₁ := by
    euclid_finish

  have hX_on_l2 : X.onLine l₂ := by
    euclid_finish

  rcases h_incircle1 with ⟨hAB1, hBC1, hCA1, I1, hI1_incentre, hI1_center⟩
  rcases h_incircle2 with ⟨hCD2, hDA2, hCA2, I2, hI2_incentre, hI2_center⟩
  rcases h_l1_tangent_ω1 with ⟨T1, hT1, hT1uniq⟩
  rcases h_l2_tangent_ω1 with ⟨U1, hU1, hU1uniq⟩
  rcases h_l1_tangent_ω2 with ⟨T2, hT2, hT2uniq⟩
  rcases h_l2_tangent_ω2 with ⟨U2, hU2, hU2uniq⟩
  rcases h_AB_tangent_ω with ⟨Pab, hPab, hPabuniq⟩
  rcases h_BC_tangent_ω with ⟨Pbc, hPbc, hPbcuniq⟩
  rcases h_DA_tangent_ω with ⟨Pda, hPda, hPdauniq⟩
  rcases h_CD_tangent_ω with ⟨Pcd, hPcd, hPcduniq⟩

  have hT1_on_l1 : T1.onLine l₁ := by
    exact hT1.1

  have hT1_on_ω1 : T1.onCircle ω₁ := by
    exact hT1.2

  have hU1_on_l2 : U1.onLine l₂ := by
    exact hU1.1

  have hU1_on_ω1 : U1.onCircle ω₁ := by
    exact hU1.2

  have hT2_on_l1 : T2.onLine l₁ := by
    exact hT2.1

  have hT2_on_ω2 : T2.onCircle ω₂ := by
    exact hT2.2

  have hU2_on_l2 : U2.onLine l₂ := by
    exact hU2.1

  have hU2_on_ω2 : U2.onCircle ω₂ := by
    exact hU2.2

  have hPab_on_AB : Pab.onLine AB := by
    exact hPab.1

  have hPab_on_ω : Pab.onCircle ω := by
    exact hPab.2

  have hPbc_on_BC : Pbc.onLine BC := by
    exact hPbc.1

  have hPbc_on_ω : Pbc.onCircle ω := by
    exact hPbc.2

  have hPda_on_DA : Pda.onLine DA := by
    exact hPda.1

  have hPda_on_ω : Pda.onCircle ω := by
    exact hPda.2

  have hPcd_on_CD : Pcd.onLine CD := by
    exact hPcd.1

  have hPcd_on_ω : Pcd.onCircle ω := by
    exact hPcd.2

  have h_l1_tanpt_ω1 : TangentLineCircleAtPoint T1 I1 l₁ ω₁ := by
    euclid_finish

  have h_l2_tanpt_ω1 : TangentLineCircleAtPoint U1 I1 l₂ ω₁ := by
    euclid_finish

  have h_l1_tanpt_ω2 : TangentLineCircleAtPoint T2 I2 l₁ ω₂ := by
    euclid_finish

  have h_l2_tanpt_ω2 : TangentLineCircleAtPoint U2 I2 l₂ ω₂ := by
    euclid_finish

  have hXT1_eq_XU1 : |(X─T1)| = |(X─U1)| := by
    have hXT1_line : distinctPointsOnLine X T1 l₁ := by
      euclid_finish
    have hXU1_line : distinctPointsOnLine X U1 l₂ := by
      euclid_finish
    euclid_apply eq_len_of_tangents X T1 U1 I1 ω₁ l₁ l₂
    euclid_finish

  have hXT2_eq_XU2 : |(X─T2)| = |(X─U2)| := by
    have hXT2_line : distinctPointsOnLine X T2 l₁ := by
      euclid_finish
    have hXU2_line : distinctPointsOnLine X U2 l₂ := by
      euclid_finish
    euclid_apply eq_len_of_tangents X T2 U2 I2 ω₂ l₁ l₂
    euclid_finish

  have hX_on_omega : X.onCircle ω := by
    have hω_center : ∃ Oω : Point, Oω.isCentre ω := by
      euclid_apply exists_centre ω as Oω
      use Oω
      euclid_finish
    have hω1_data :
        I1.isCentre ω₁ ∧ T1.onCircle ω₁ ∧ U1.onCircle ω₁ := by
      euclid_finish
    have hω2_data :
        I2.isCentre ω₂ ∧ T2.onCircle ω₂ ∧ U2.onCircle ω₂ := by
      euclid_finish
    have hω_data :
        Pab.onCircle ω ∧ Pbc.onCircle ω ∧ Pda.onCircle ω ∧ Pcd.onCircle ω := by
      euclid_finish
    euclid_finish

  exact hX_on_omega
