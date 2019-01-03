Require Import Reals Qreals Psatz.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat ssrfun.
Require Import Rstruct.
From rlzrs Require Import mf_set.
From Coquelicot Require Import Coquelicot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.
Section mean_value_theorem.
  Arguments limit_in {X} {X'}.
  Lemma derivable_pt_lim_id x: derivable_pt_lim id x 1.
  Proof.
    move => eps eg0; exists (mkposreal _ eg0) => h neq /= ineq.
    have ->: (x + h - x) / h = 1 by field.
    by split_Rabs; lra.
  Qed.

  Lemma derive_pt_unique f x P Q: derive_pt f x P = derive_pt f x Q.
  Proof. by apply/derive_pt_eq; move: Q => [f'x lim]. Qed.
  
  Definition cnst_ext f a b x: R :=
    match Rleb x a with
    | true => f a
    | false => match Rleb x b with
               | true => f x
               | false => f b
               end
    end.
  
  Lemma cont_cext (f: Base R_met -> Base R_met) a b x:
    a <= b ->
    limit_in f (fun c => a <= c <= b) x (f x) ->
    continuity_pt (cnst_ext f a b) x.
  Proof.
    move => alb lmt eps eg0; rewrite /cnst_ext.
    case: (total_order_T a x) => [xla | alx]; last first.
    - exists (a - x); split => [ | y [[_ neq]]]; first by lra.
      rewrite /dist /=/R_dist/= => dst.
      have ->: Rleb x a = true by apply/RlebP; lra.
      have ->: Rleb y a = true by apply/RlebP; split_Rabs; lra.
      split_Rabs; lra.
    case: (total_order_T x b) => [blx | xlb]; last first.
    - exists (x - b); split => [ | y [[_ neq]]]; first by lra.
      rewrite /dist /=/R_dist/= => dst.
      have ->: Rleb x a = false by apply/RlebP; lra.
      have ->: Rleb y a = false by apply/RlebP; split_Rabs; lra.
      have ->: Rleb x b = false by apply/RlebP; lra.
      have ->: Rleb y b = false by apply/RlebP; split_Rabs; lra.
      by split_Rabs; lra.
    have [delta [dg0 prp]]:= lmt eps eg0.
    exists delta; split => // y [[_ neq]].
    rewrite /dist/=/R_dist/= => dst.
    case: xla => [ineq | eq]; last first.
    - rewrite -eq; rewrite /dist/=/R_dist/= -eq in prp.
      have ->: (Rleb a a) by apply/RlebP; lra.
      case: ifP => [ | /RlebP ineq]; first by split_Rabs; lra.
      by case: ifP => /RleP ineq'; apply/prp; split_Rabs; lra.
    have ->: Rleb x a = false by apply/RleP; lra.
    case: ifP => /RlebP ineq'.
    - case: ifP => [/RlebP ineq'' | /RlebP/Rnot_le_lt]; last by case: blx; lra.
      by apply/prp; rewrite /dist/=/R_dist/=; split_Rabs; try lra.
    have ->: (Rleb x b = true) by apply/RlebP; case: blx; lra.
    case: ifP => [/RlebP ineq'' | /RlebP/Rnot_le_lt ineq'']; apply/prp.
    - by split; [case: blx; lra | apply/dst].
    split; first by case: blx; lra.
    have: x <= b by case: blx; lra.
    by rewrite /dist/=/R_dist/=; split_Rabs; lra.
  Qed.

  Lemma diff_cext f a b x y:
    a < x < b -> derivable_pt_lim f x y -> derivable_pt_lim (cnst_ext f a b) x y.
  Proof.
    move => ineqs diff eps eg0.
    have [[/=delta dg0] cnd]:= diff eps eg0.
    have ineq : 0 < (Rmin (Rmin delta (x - a)) (b - x)).
    - by apply/Rmin_pos; first apply/Rmin_pos; lra.
    exists (mkposreal _ ineq) => h hneq /= hl.
    rewrite /cnst_ext.
    have hlbx: Rabs h < b - x by apply/Rlt_le_trans; [apply/hl | apply/Rmin_r].
    have hlxa: Rabs h < x - a.
    - apply/Rlt_le_trans; first exact/hl.
      apply/Rle_trans; first exact/Rmin_l.
      exact/Rmin_r.
    have hld: Rabs h < delta.
    - apply/Rlt_le_trans; first exact/hl.
      apply/Rle_trans; first exact/Rmin_l.
      exact/Rmin_l.
    have ->: Rleb x a = false by apply/RlebP; lra.
    have ->: Rleb x b = true by apply/RlebP; lra.
    have -> : Rleb (x + h) a = false by apply/RlebP/Rlt_not_le; split_Rabs; lra.
    have ->: Rleb (x + h) b = true by apply/RlebP;split_Rabs; lra.
    exact/cnd.
  Qed.

  Theorem mean_value_theorem (f: Base R_met -> Base R_met) a b: a < b ->
    (forall c, a < c < b -> derivable_pt f c) ->
    (forall x, limit_in f (fun c => a <= c <= b) x (f x)) ->
    exists c, a < c < b /\ forall y, derivable_pt_lim f c y -> (f b - f a) = y * (b - a).
  Proof.
    move => alb deriv cont.
    have cont': forall x, a <= x <= b -> continuity_pt (cnst_ext f a b) x.
    - by move => x ineq; apply/cont_cext/cont; lra.
    have diff: forall x, a < x < b -> derivable_pt (cnst_ext f a b) x.
    - by move => x ineqs; have [f'x diff]:= deriv x ineqs; exists f'x; apply/diff_cext.
    have diff': forall x, a < x < b -> derivable_pt id x.
    - by move => x ineqs; exists 1; apply/derivable_pt_lim_id.
    have [ | | | x [ineqs eq]]//:= MVT (cnst_ext f a b) id a b diff diff'.
    - by move => x ineqs; apply/derivable_continuous_pt; exists 1; apply/derivable_pt_lim_id.
    exists x; split => // y deriv'.
    have <-: derive_pt (cnst_ext f a b) x (diff x ineqs) = y.
    - by apply/derive_pt_eq/diff_cext.
    rewrite Rmult_comm eq.
    have ->: derive_pt id x (diff' x ineqs) = 1.
    - by apply/derive_pt_eq/derivable_pt_lim_id.
    rewrite Rmult_1_r /cnst_ext.
    by do 3 (case: ifP => /RlebP; intros; try lra).
  Qed.
End mean_value_theorem.