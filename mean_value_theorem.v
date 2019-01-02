Require Import Reals Qreals Psatz.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat ssrfun.
Require Import Rstruct.
From Coquelicot Require Import Coquelicot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.
Section mean_value_theorem.
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
    limit_in _ _ f (fun c => a <= c <= b) x (f x) ->
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
    (forall x, limit_in _ _ f (fun c => a <= c <= b) x (f x)) ->
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
  
Section concave.
  Definition concave_on A f :=
    forall x y z, A x -> A y -> A z -> x < y < z ->
                  (f z - f y) / (z - y) <= (f y - f x) / (y - x).

  Lemma cncv_subs A B f: (forall x, A x -> B x) -> concave_on B f -> concave_on A f.
  Proof. by move => subs conc x y z /subs bx /subs yb /subs zb; apply/conc. Qed.

  Lemma cncv_prp f a b: a < b -> concave_on (fun x => a <= x <= b) f ->
                         forall r, 0 < r < 1 -> r * f b + (1 - r) * f a <= f (r * b + (1 - r) * a).
  Proof.
    move => alb conc r ineq.
    suff: (1 - r) * (f (r * b + (1 - r) * a) - f a) >= r * (f b - f ( r * b + (1 - r) * a)) by lra.
    apply/Rle_ge.
    apply/(Rmult_le_reg_l (/(1-r))); first by apply/Rinv_0_lt_compat; lra.
    rewrite -!Rmult_assoc Rinv_l; try lra; rewrite Rmult_1_l.
    rewrite (Rmult_comm _ r).
    apply/(Rmult_le_reg_l (/r)); first by apply/Rinv_0_lt_compat; lra.
    rewrite -!Rmult_assoc Rinv_l; try lra; rewrite Rmult_1_l.
    apply/(Rmult_le_reg_r (/(b - a))); first by apply/Rinv_0_lt_compat; lra.
    have /=:= conc a (r * b + (1 - r) * a) b.
    have ->: b - ( r * b + (1 - r) * a) = (1 - r)* (b - a) by ring.
    have ->: r * b + (1 - r)* a - a = r * (b - a) by ring.
    rewrite !/Rdiv !Rinv_mult_distr; try lra.
    suff ineq': a < r * b + (1 - r) * a < b by lra.
    split; first by apply/Rle_lt_trans/Rplus_lt_le_compat/Rle_refl/Rmult_lt_compat_l/alb; lra.
    apply/Rlt_le_trans.
    - by apply/Rplus_le_lt_compat/Rmult_lt_compat_l/alb; try lra; apply/Rle_refl.
    lra.  
  Qed.

  Definition increasing_on (A: R -> Prop) f :=
    forall x y, A x -> A y -> x <= y -> f x <= f y.

  Lemma incn_inc f: increasing f <-> increasing_on (fun _ => True) f.
  Proof. by split => [inc x y _ _ | inc x y]; apply/inc. Qed.

  Definition decreasing_on (A: R -> Prop) f :=
    forall x y, A x -> A y -> x <= y -> f y <= f x.

  Lemma dec_inc A f:
    decreasing_on A f <-> increasing_on A (fun x => - f x).
  Proof.
    split => ass x y Ax Ay ineq .
    - have: f y <= f x by apply/ass.
      lra.
    have: - f x <= - f y by apply/ass.
    lra.
  Qed.

  Lemma continuity_pt_limit_in f a b x:
    continuity_pt f x -> limit_in R_met R_met f (fun x' => a <= x' <= b) x (f x).
  Proof.
    move => cont eps eg0.
    have [delta [dg0 prp]]:= cont eps eg0.
    exists delta; split => // y [_ dst].
    case E: (eqr x y); move: E => /eqP; first move ->; last by intros; apply/prp.
    suff -> : dist R_met (f y) (f y) = 0 by lra.
    by apply/dist_refl.
  Qed.

  Lemma out_limit_in f a b x:
    x < a \/ b < x -> limit_in R_met R_met f (fun x' => a <= x' <= b) x (f x).
  Proof.
    move => [] ineq eps eg0.
    - exists (a - x); split => [ | y []]; first lra.
      by rewrite/dist/=/R_dist/=; split_Rabs; lra.
    exists (x - b); split => [ | y []]; first lra.
    by rewrite/dist/=/R_dist/=; split_Rabs; lra.
  Qed.
    
  Lemma diff_decr_cncv_open f f' a b:
    (forall x, a < x < b -> derivable_pt_lim f x (f' x)) ->
    decreasing_on (fun x => a < x < b) f' -> concave_on (fun x => a < x < b) f.
  Proof.
    move => diff decr x y z /= xineq yineq zineq [] ygx zgy.
    have diffyz: forall x, y < x < z -> derivable_pt f x.
    - by move => x'; exists (f' x'); apply diff; lra.
    have [ | x' [ineqs prp]]:= mean_value_theorem zgy diffyz.
    - move => x'.
      case E: (Rltb x' y); first by apply/out_limit_in; left; move: E => /RltbP.
      case E': (Rltb z x'); first by apply/out_limit_in; right; move: E' => /RltbP.
      apply/continuity_pt_limit_in/derivable_continuous_pt.
      exists (f' x'); apply/diff.
      by move: E => /RltbP/Rnot_lt_le; move: E' => /RltbP/Rnot_lt_le;lra.
    rewrite (prp (f' x')) /Rdiv; last by apply/diff; lra.
    rewrite Rmult_assoc Rinv_r; try lra; rewrite Rmult_1_r.
    have diffxy: forall x', x < x' < y -> derivable_pt f x'.
    - by move => x''; exists (f' x''); apply diff; lra.
    have [ | x'' [ineqs' prp']]:= mean_value_theorem ygx diffxy.
    - move => x''.
      case E: (Rltb x'' x); first by apply/out_limit_in; left; move: E => /RltbP.
      case E': (Rltb y x''); first by apply/out_limit_in; right; move: E' => /RltbP.
      apply/continuity_pt_limit_in/derivable_continuous_pt.
      exists (f' x''); apply/diff.
      by move: E => /RltbP/Rnot_lt_le; move: E' => /RltbP/Rnot_lt_le;lra.
    rewrite (prp' (f' x'')) /Rdiv; last by apply/diff; lra.
    rewrite Rmult_assoc Rinv_r; try lra; rewrite Rmult_1_r.
    by apply/decr; lra.
  Qed.
End concave.
  
Section strictly_concave.   
  Definition strictly_concave_on A f :=
    forall x y z, A x -> A y -> A z -> x < y < z ->
                    (f z - f y)/(z - y) < (f y - f x)/ (y - x).

  Lemma cncv_scnc A f: strictly_concave_on A f -> concave_on A f.
  Proof. by move => cnc x y z Ax Ay Az ineq; apply/Rlt_le/cnc. Qed.

  Lemma scnc_subs A B f: (forall x, A x -> B x) ->
                         strictly_concave_on B f -> strictly_concave_on A f.
  Proof. by move => subs conc x y z /subs bx /subs yb /subs zb; apply/conc. Qed.
  
  Lemma scnc_prp f a b: a < b -> strictly_concave_on (fun x => a <= x <= b) f ->
                         forall r, 0 < r < 1 -> r * f b + (1 - r) * f a < f (r * b + (1 - r) * a).
  Proof.
    move => alb conc r ineq.
    suff: (1 - r) * (f (r * b + (1 - r) * a) - f a) > r * (f b - f ( r * b + (1 - r) * a)) by lra.
    apply/Rlt_gt.
    apply/(Rmult_lt_reg_l (/(1-r))); first by apply/Rinv_0_lt_compat; lra.
    rewrite -!Rmult_assoc Rinv_l; try lra; rewrite Rmult_1_l.
    rewrite (Rmult_comm _ r).
    apply/(Rmult_lt_reg_l (/r)); first by apply/Rinv_0_lt_compat; lra.
    rewrite -!Rmult_assoc Rinv_l; try lra; rewrite Rmult_1_l.
    apply/(Rmult_lt_reg_r (/(b - a))); first by apply/Rinv_0_lt_compat; lra.
    have /=:= conc a (r * b + (1 - r) * a) b.
    have ->: b - ( r * b + (1 - r) * a) = (1 - r)* (b - a) by ring.
    have ->: r * b + (1 - r)* a - a = r * (b - a) by ring.
    rewrite !/Rdiv !Rinv_mult_distr; try lra.
    suff ineq': a < r * b + (1 - r) * a < b by lra.
    split; first by apply/Rle_lt_trans/Rplus_lt_le_compat/Rle_refl/Rmult_lt_compat_l/alb; lra.
    apply/Rlt_le_trans.
    - by apply/Rplus_le_lt_compat/Rmult_lt_compat_l/alb; try lra; apply/Rle_refl.
    lra.  
  Qed.

  Definition strictly_increasing_on (A: R -> Prop) f:=
    forall x y, A x -> A y -> x < y -> f x < f y.

  Definition strictly_decreasing_on (A: R -> Prop) f:=
    forall x y, A x -> A y -> x < y -> f y < f x.

  Lemma sdec_sinc A f:
    strictly_decreasing_on A f <-> strictly_increasing_on A (fun x => - f x).
  Proof.
    split => ass x y Ax Ay ineq .
    - have: f y < f x by apply/ass.
      lra.
    have: - f x < - f y by apply/ass.
    lra.
  Qed.

    Lemma diff_sdec_scnc_open f f' a b:
    (forall x, a < x < b -> derivable_pt_lim f x (f' x)) ->
    strictly_decreasing_on (fun x => a < x < b) f' ->
    strictly_concave_on (fun x => a < x < b) f.
  Proof.
    move => diff decr x y z /= xineq yineq zineq [] ygx zgy.
    have diffyz: forall x, y < x < z -> derivable_pt f x.
    - by move => x'; exists (f' x'); apply diff; lra.
    have [ | x' [ineqs prp]]:= mean_value_theorem zgy diffyz.
    - move => x'.
      case E: (Rltb x' y); first by apply/out_limit_in; left; move: E => /RltbP.
      case E': (Rltb z x'); first by apply/out_limit_in; right; move: E' => /RltbP.
      apply/continuity_pt_limit_in/derivable_continuous_pt.
      exists (f' x'); apply/diff.
      by move: E => /RltbP/Rnot_lt_le; move: E' => /RltbP/Rnot_lt_le;lra.
    rewrite (prp (f' x')) /Rdiv; last by apply/diff; lra.
    rewrite Rmult_assoc Rinv_r; try lra; rewrite Rmult_1_r.
    have diffxy: forall x', x < x' < y -> derivable_pt f x'.
    - by move => x''; exists (f' x''); apply diff; lra.
    have [ | x'' [ineqs' prp']]:= mean_value_theorem ygx diffxy.
    - move => x''.
      case E: (Rltb x'' x); first by apply/out_limit_in; left; move: E => /RltbP.
      case E': (Rltb y x''); first by apply/out_limit_in; right; move: E' => /RltbP.
      apply/continuity_pt_limit_in/derivable_continuous_pt.
      exists (f' x''); apply/diff.
      by move: E => /RltbP/Rnot_lt_le; move: E' => /RltbP/Rnot_lt_le;lra.
    rewrite (prp' (f' x'')) /Rdiv; last by apply/diff; lra.
    rewrite Rmult_assoc Rinv_r; try lra; rewrite Rmult_1_r.
    by apply/decr; lra.
  Qed.
End strictly_concave.
  
Section ln_strictly_concave.
  Lemma ln_derivable_pt x: 0 < x -> derivable_pt ln x.
  Proof.
    rewrite /derivable_pt/derivable_pt_abs => ineq.
    by exists (/x); apply/derivable_pt_lim_ln.
  Qed.

  Lemma ln_scnc: strictly_concave_on (fun x => 0 < x) ln.
  Proof.
    suff scnc: forall y, strictly_concave_on (fun x => 0 < x < y) ln.
    - by move => x y z Ax Ay Az ineqs; apply/(scnc (2 * z)); lra.
    move => y.
    apply/diff_sdec_scnc_open => [x ineqs| ]; first by apply/derivable_pt_lim_ln; lra.
    by move => x' y' g0 _ ineq; apply/Rinv_lt_contravar/ineq/Rmult_lt_0_compat; lra.
  Qed.
  
  Lemma ln_le_inv x y: 0 < x -> 0 < y -> ln x <= ln y -> x <= y.
  Proof.
    move => x0 y0.
    case => [ineq | eq]; first exact/Rlt_le/ln_lt_inv.
    by rewrite (ln_inv x y) //; exact/Rle_refl.
  Qed.
End ln_strictly_concave.