Require Import Reals Qreals Psatz.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat ssrfun.
Require Import Rstruct mean_value_theorem.
From rlzrs Require Import mf_set.
From metric Require Import metric standard.
From Coquelicot Require Import Coquelicot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.
Local Open Scope mf_scope.
Local Notation "'[' a ';oo)'" := (make_subset (fun x => a <= x)).
Local  Notation "'(' a ';oo)'" := (make_subset (fun x => a < x)).
Local  Notation "'(oo;' b ']'" := (make_subset (fun x => x <= b)).
Local  Notation "'(oo;' b ')'" := (make_subset (fun x => x < b)).
Local Notation "'[' a ';' b ']'" := (make_subset (fun x => a <= x <= b)).
Local  Notation "'(' a ';' b ']'" := (make_subset (fun x => a < x <= b)).
Local  Notation "'[' a ';' b ')'" := (make_subset (fun x => a <= x < b)).
Local  Notation "'(' a ';' b ')'" := (make_subset (fun x => a < x < b)).

Section convex_sets.
  Definition convex (M: ModuleSpace R_AbsRing) (A: subset M):= forall x y,
    x \from A -> y \from A -> forall r, 0 < r < 1 -> (plus (scal r x)  (scal (1 - r) y)) \from A.

  Lemma cnvx_ineq x y r: x < y -> 0 < r < 1 -> x < r * x + (1 - r) * y < y.
  Proof.
    intros; split.
    - have {1}->: x = r * x + (1 - r) * x by lra.
      apply/Rplus_le_lt_compat; try lra.
      by apply/Rmult_lt_compat_l; lra.
    have {2}->: y = r * y + (1 - r) * y by lra.
    apply/Rplus_lt_le_compat; try lra.
    by apply/Rmult_lt_compat_l; lra.
  Qed.
 
  Lemma order_cnvx_spec (A: subset R): convex A <->
    forall x y z, A x -> A y -> x < z < y -> A z.
  Proof.
    split => [cnvx x z y Ax Ay ineq | cnv x y Ax Ay r ineq].
    - have ->: y = (y - x)/(z - x) * z + (1 - (y - x)/(z - x)) * x by field; lra.
      apply/cnvx => //; split; first by apply/Rdiv_lt_0_compat; lra.
      rewrite -(Rinv_r (z - x)); try lra.
      apply/Rmult_lt_compat_r; try lra.
      by apply/Rinv_0_lt_compat; lra.
    case: (total_order_T x y) => [[ineq' | ->] | ineq']; first exact/cnv/cnvx_ineq.
    - by rewrite /plus/=/scal/=/mult/=; have ->: r * y + (1 - r) * y = y by lra.
    apply/cnv; first exact/Ay; first exact/Ax.
    by rewrite /plus/=/scal/=/mult/=; have:= cnvx_ineq ineq' ineq; lra.
  Qed.
End convex_sets.                                   

Section concave.
  Arguments limit_in {X} {X'}.
  Implicit Types (f: R_met -> R_met) (A B: subset R).
  
  Definition concave_on A f :=
    forall x y z, A x -> A y -> A z -> x < y < z ->
                  (f z - f y) * (y - x) <= (f y - f x) * (z - y).
  
  Lemma cncv_subs A B f: (forall x, A x -> B x) -> concave_on B f -> concave_on A f.
  Proof. by move => subs conc x y z /subs bx /subs yb /subs zb; apply/conc. Qed.
  
  Lemma cncv_prp f a b: a <= b -> concave_on [a; b] f ->
      forall r, 0 < r < 1 -> r * f a + (1 - r) * f b <= f (r * a + (1 - r) * b).
  Proof.
    case => [alb conc r ineq | -> conc r ineq]; last first.
    - have prp: forall x, (r * x + (1 - r) * x) = x by move => x; ring.
      by rewrite !prp; apply/Rle_refl.
    apply/(Rmult_le_reg_r (b - a)); try lra.
    have arb:= cnvx_ineq alb ineq.
    have arb': a <= r * a + (1 - r) * b <= b by lra.
    by have := conc _ _ _ _ arb' _ arb => /=; lra.
  Qed.
   
  Lemma cncv_spec f A: convex A -> concave_on A f <->
    forall x y, A x -> A y -> x <= y ->
                forall r, 0 < r < 1 -> r * f x + (1 - r) * f y <= f (r * x + (1 - r) * y).
  Proof.
    move => /order_cnvx_spec cnvx; split => cncv.
    - intros; apply/cncv_prp => //; apply/cncv_subs/cncv.
      by move => z [[xlz | <-]]// [ylz | ->]//; apply(cnvx x y).
    move => x y z xineq yineq zineq [xly ylz].
    suff: (y - x) * f z + (z - y) * f x <= (z - x) * f y by lra.
    apply/(Rmult_le_reg_l (/(z - x))); first by apply/Rinv_0_lt_compat; lra.
    rewrite -Rmult_assoc Rinv_l; try lra; rewrite Rmult_1_l.
    have := cncv x z _ _ _ ((z - y)/(z - x)).
    have ->: 1 - (z - y) / (z - x) = (y - x)/(z - x) by field; lra.
    have -> : (z - y) / (z - x) * x + (y - x) / (z - x) * z = y by field; lra.
    move => prp.
    apply/Rle_trans/prp => //; try lra.  
    split; first by apply/Rdiv_lt_0_compat; lra.
    rewrite -(Rinv_r (z- x)); try lra.
    apply/Rmult_lt_compat_r; try lra.
    by apply/Rinv_0_lt_compat; lra.
  Qed.

  Lemma cond_leq x y: (forall eps, 0 < eps -> x <= y + eps) -> x <= y.
  Proof.
    move => prp.
    apply/Rnot_lt_le => xg0.
    suff: x = y by lra.
    apply/cond_eq => eps eg0.
    by have := prp (eps/2); split_Rabs; lra.
  Qed.
    
  Lemma cncv_closure_l f a b: a < b -> concave_on (a; b) f ->
    (forall x, limit_in f (a; b) x (f x)) -> concave_on [a; b) f.
  Proof.
    move => alb /cncv_spec cncv cont.
    have cnvx: convex (a; b) by apply/order_cnvx_spec => /=; intros; lra.
    specialize (cncv cnvx).
    apply/cncv_spec; first by apply/order_cnvx_spec => /=; intros; lra.
    move => x y [[/= | eq xlb [[| eq']]]]; last first; last by intros; apply/cncv => /=; lra.
    - rewrite -eq eq'; intros.
      have eq'': forall x', r * x' + (1 - r) * x' = x' by move => x'; lra.
      by rewrite !eq''; apply/Rle_refl.
    move => aly ylb xly r rineq.  
    apply/cond_leq => eps eg0.
    have [ | delta [dg0 prp]]:= cont x (eps/2); try lra.
    have [ | delta' [d'g0 prp']]:= cont (r * x + (1 - r) * y) (eps/2); try lra.
    pose dx := Rmin (Rmin ((y - x)/2) (delta/2)) (Rmin ((b - y)/2) (delta'/2)).
    have dxg0: 0 < dx by rewrite /dx; apply/Rmin_glb_lt; apply/Rmin_glb_lt; lra.
    have dxineq: x < x + dx < y.
    - split; first lra.
      suff : dx < y - x by lra.
      rewrite /dx; apply/Rle_lt_trans; first exact/Rmin_l.
      by apply/Rle_lt_trans; first exact/Rmin_l; lra.
    have dxld: dx < delta.
    - rewrite /dx; apply/Rle_lt_trans; first exact/Rmin_l.
      by apply/Rle_lt_trans; first exact/Rmin_r; lra.
    have dxld': dx < delta'.  
    - rewrite /dx; apply/Rle_lt_trans; first exact/Rmin_r.
      by apply/Rle_lt_trans; first exact/Rmin_r; lra.
    have ineq1: f x < f (x + dx) + eps/2.
      suff: Rabs (f (x + dx) - f x) < eps/2 by split_Rabs; lra.
      apply/prp => /=; split; try lra.
      rewrite /dist/=/R_dist/= Rplus_comm {1}/Rminus Rplus_assoc Rplus_opp_r Rplus_0_r.
      by rewrite Rabs_pos_eq; lra.
    have ineq2: f (r * (x + dx) + (1 - r) * y) < f (r * x + (1 - r) * y) + eps/2.
    - suff: Rabs (f (r * (x + dx) + (1 - r) * y) - f (r * x + (1 - r) * y)) < eps/2 by split_Rabs; lra.
      apply/prp'.
      split.
      + have r'ineq: 0 < 1 - r < 1 by lra.
        by have /=:= cnvx_ineq dxineq.2 r'ineq; lra.
      rewrite /dist/=/R_dist/= Rabs_pos_eq.
      + suff: r * dx < delta' by lra.
        by rewrite -(Rmult_1_l delta'); apply/Rmult_le_0_lt_compat; lra.
      suff: 0 <= r * dx by lra.
      by apply/Rmult_le_pos; lra.
    apply/Rle_trans.
    - apply/Rplus_le_compat_r/Rmult_le_compat_l; try lra.
      exact/Rlt_le/ineq1.
    suff : r * f (x + dx) + (1 - r) * f y <= f (r * x + (1 - r) * y) + (1- r/2) * eps by lra.
    apply/Rle_trans; first by apply/cncv => /=; lra.
    apply/Rle_trans; first apply/Rlt_le/ineq2.
    suff: 1/2 * eps <= (1 - r/2)* eps by lra.
    by apply/Rmult_le_compat_r; lra.
  Qed.

  Lemma cncv_closure_r f a b: a < b -> concave_on (a; b) f ->
    (forall x, limit_in f (fun c => a < c < b) x (f x)) -> concave_on (a; b] f.
  Proof.
    move => alb cncv cont.
    suff cncv': concave_on [-b; -a) (fun x => f (-x)).
    - by move => x y z/=; intros; have /=:= @cncv' (-z) (-y) (-x); rewrite !Ropp_involutive; lra.
    apply/cncv_closure_l => [ | x y z /=| x eps eg0]; try lra.      
    - by intros; have /=:= @cncv (-z) (-y) (-x); lra.
    have [delta [dg0 prp]]:= cont (-x) eps eg0.
    exists delta; split => //= y [ineq dst].
    rewrite /R_dist; apply/prp; split; try lra.
    move: dst; rewrite /dist/=/R_dist/=; split_Rabs; lra.
  Qed.
    
  Definition increasing_on A f :=
    forall x y, A x -> A y -> x <= y -> f x <= f y.

  Lemma incn_inc f: increasing f <-> increasing_on All f.
  Proof. by split => [inc x y _ _ | inc x y]; apply/inc. Qed.

  Definition decreasing_on A f :=
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
    continuity_pt f x -> limit_in f (fun x' => a <= x' <= b) x (f x).
  Proof.
    move => cont eps eg0.
    have [delta [dg0 prp]]:= cont eps eg0.
    exists delta; split => // y [_ dst].
    case E: (eqr x y); move: E => /eqP; first move ->; last by intros; apply/prp.
    suff -> : dist R_met (f y) (f y) = 0 by lra.
    by apply/dist_refl.
  Qed.

  Lemma limit_not_in f a b x:
    x < a \/ b < x -> limit_in f (fun x' => a <= x' <= b) x (f x).
  Proof.
    move => [] ineq eps eg0.
    - exists (a - x); split => [ | y []]; first lra.
      by rewrite/dist/=/R_dist/=; split_Rabs; lra.
    exists (x - b); split => [ | y []]; first lra.
    by rewrite/dist/=/R_dist/=; split_Rabs; lra.
  Qed.
    
  Lemma diff_decr_cncv_open f f' a b:
    (forall x, a < x < b -> derivable_pt_lim f x (f' x)) ->
    decreasing_on (a; b) f' -> concave_on (a; b) f.
  Proof.
    move => diff decr x y z /= xineq yineq zineq [] ygx zgy.
    have diffyz: forall x, y < x < z -> derivable_pt f x.
    - by move => x'; exists (f' x'); apply diff; lra.
    have [ | x' [ineqs prp]]:= mean_value_theorem zgy diffyz.
    - move => x'.
      case E: (Rltb x' y); first by apply/limit_not_in; left; move: E => /RltbP.
      case E': (Rltb z x'); first by apply/limit_not_in; right; move: E' => /RltbP.
      apply/continuity_pt_limit_in/derivable_continuous_pt.
      exists (f' x'); apply/diff.
      by move: E => /RltbP/Rnot_lt_le; move: E' => /RltbP/Rnot_lt_le;lra.
    rewrite (prp (f' x')); last by apply/diff; lra.
    have diffxy: forall x', x < x' < y -> derivable_pt f x'.
    - by move => x''; exists (f' x''); apply diff; lra.
    have [ | x'' [ineqs' prp']]:= mean_value_theorem ygx diffxy.
    - move => x''.
      case E: (Rltb x'' x); first by apply/limit_not_in; left; move: E => /RltbP.
      case E': (Rltb y x''); first by apply/limit_not_in; right; move: E' => /RltbP.
      apply/continuity_pt_limit_in/derivable_continuous_pt.
      exists (f' x''); apply/diff.
      by move: E => /RltbP/Rnot_lt_le; move: E' => /RltbP/Rnot_lt_le;lra.
    rewrite (prp' (f' x'')) /Rdiv; last by apply/diff; lra.
    rewrite Rmult_assoc (Rmult_comm (z-y)) -Rmult_assoc.
    do 2 (apply/Rmult_le_compat_r; try lra).
    by apply/decr => /=; lra.
  Qed.
End concave.

Section strictly_concave.
  Implicit Types (f: R_met -> R_met) (A B: subset R).
  Notation "'[' a ';' b ']'" := (make_subset (fun x => a <= x <= b)).
  Notation "'(' a ';' b ']'" := (make_subset (fun x => a < x <= b)).
  Notation "'[' a ';' b ')'" := (make_subset (fun x => a <= x < b)).
  Notation "'(' a ';' b ')'" := (make_subset (fun x => a < x < b)).

  Definition strictly_concave_on A f :=
    forall x y z, A x -> A y -> A z -> x < y < z ->
                    (f z - f y) * (y - x) < (f y - f x) * (z - y).

  Lemma cncv_scnc A f: strictly_concave_on A f -> concave_on A f.
  Proof. by move => cnc x y z Ax Ay Az ineq; apply/Rlt_le/cnc. Qed.

  Lemma scnc_subs A B f: A \is_subset_of B ->
     strictly_concave_on B f -> strictly_concave_on A f.
  Proof. by move => subs conc x y z /subs bx /subs yb /subs zb; apply/conc. Qed.

  Lemma scnc_prp f a b: a < b -> strictly_concave_on [a; b] f ->
      forall r, 0 < r < 1 -> r * f a + (1 - r) * f b < f (r * a + (1 - r) * b).
  Proof.
    move => alb conc r ineq.
    apply/(Rmult_lt_reg_r (b - a)); try lra.
    have arb:= cnvx_ineq alb ineq.
    have arb': a <= r * a + (1 - r) * b <= b by lra.
    by have := conc _ _ _ _ arb' _ arb => /=; lra.
  Qed.
   
  Lemma scnc_spec f A: convex A -> strictly_concave_on A f <->
    forall x y, A x -> A y -> x < y ->
                forall r, 0 < r < 1 -> r * f x + (1 - r) * f y < f (r * x + (1 - r) * y).
  Proof.
    move => /order_cnvx_spec cnvx; split => scnc.
    - intros; apply/scnc_prp => //; apply/scnc_subs/scnc.
      by move => z [[xlz | <-]]// [ylz | ->]//; apply(cnvx x y).
    move => x y z xineq yineq zineq [xly ylz].
    suff: (y - x) * f z + (z - y) * f x < (z - x) * f y by lra.
    apply/(Rmult_lt_reg_l (/(z - x))); first by apply/Rinv_0_lt_compat; lra.
    rewrite -Rmult_assoc Rinv_l; try lra; rewrite Rmult_1_l.
    have := scnc x z _ _ _ ((z - y)/(z - x)).
    have ->: 1 - (z - y) / (z - x) = (y - x)/(z - x) by field; lra.
    have -> : (z - y) / (z - x) * x + (y - x) / (z - x) * z = y by field; lra.
    move => prp.
    apply/Rle_lt_trans/prp => //; try lra.  
    split; first by apply/Rdiv_lt_0_compat; lra.
    rewrite -(Rinv_r (z- x)); try lra.
    apply/Rmult_lt_compat_r; try lra.
    by apply/Rinv_0_lt_compat; lra.
  Qed.  

  Definition strictly_increasing_on (A: subset R) f:=
    forall x y, A x -> A y -> x < y -> f x < f y.

  Definition strictly_decreasing_on (A: subset R) f:=
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
    strictly_decreasing_on (a; b) f' -> strictly_concave_on (a; b) f.
  Proof.
    move => diff decr x y z /= xineq yineq zineq [] ygx zgy.
    have diffyz: forall x, y < x < z -> derivable_pt f x.
    - by move => x'; exists (f' x'); apply diff; lra.
    have [ | x' [ineqs prp]]:= mean_value_theorem zgy diffyz.
    - move => x'.
      case E: (Rltb x' y); first by apply/limit_not_in; left; move: E => /RltbP.
      case E': (Rltb z x'); first by apply/limit_not_in; right; move: E' => /RltbP.
      apply/continuity_pt_limit_in/derivable_continuous_pt.
      exists (f' x'); apply/diff.
      by move: E => /RltbP/Rnot_lt_le; move: E' => /RltbP/Rnot_lt_le;lra.
    rewrite (prp (f' x')); last by apply/diff; lra.
    have diffxy: forall x', x < x' < y -> derivable_pt f x'.
    - by move => x''; exists (f' x''); apply diff; lra.
    have [ | x'' [ineqs' prp']]:= mean_value_theorem ygx diffxy.
    - move => x''.
      case E: (Rltb x'' x); first by apply/limit_not_in; left; move: E => /RltbP.
      case E': (Rltb y x''); first by apply/limit_not_in; right; move: E' => /RltbP.
      apply/continuity_pt_limit_in/derivable_continuous_pt.
      exists (f' x''); apply/diff.
      by move: E => /RltbP/Rnot_lt_le; move: E' => /RltbP/Rnot_lt_le;lra.
    rewrite (prp' (f' x'')) /Rdiv; last by apply/diff; lra.
    rewrite Rmult_assoc (Rmult_comm (z-y)) -Rmult_assoc.
    do 2 (apply/Rmult_lt_compat_r; try lra).
    by apply/decr => /=; lra.
  Qed.
End strictly_concave.
  
Section ln_strictly_concave.
  Lemma ln_derivable_pt x: 0 < x -> derivable_pt ln x.
  Proof.
    rewrite /derivable_pt/derivable_pt_abs => ineq.
    by exists (/x); apply/derivable_pt_lim_ln.
  Qed.
  
  Lemma ln_scnc: strictly_concave_on (0;oo) ln.
  Proof.
    suff scnc: forall y, strictly_concave_on (0; y) ln.
    - by move => x y z /= Ax Ay Az ineqs; apply/(scnc (2 * z)) => /=; lra.
    move => y.
    apply/diff_sdec_scnc_open => [x ineqs| ]; first by apply/derivable_pt_lim_ln; lra.
    by move => x' y'/= g0 _ ineq; apply/Rinv_lt_contravar/ineq/Rmult_lt_0_compat; lra.
  Qed.
  
  Lemma ln_le_inv x y: 0 < x -> 0 < y -> ln x <= ln y -> x <= y.
  Proof.
    move => x0 y0.
    case => [ineq | eq]; first exact/Rlt_le/ln_lt_inv.
    by rewrite (ln_inv x y) //; exact/Rle_refl.
  Qed.
End ln_strictly_concave.
  