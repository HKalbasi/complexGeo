Require Import Complex Geobase.

Structure Line := {
  Larz : R ; 
  Lshib :> Complex ; 
  Lshib_len1 : Cabs Lshib = 1%R ;
  Lshib_gt_C0 : (C0 < Lshib)%C
}.

Definition on_line ( a : Complex ) ( l : Line ) := (( Lshib l )*( a)+(Ccoj (Lshib l) )*(Ccoj a) = (Larz l , 0%R ))%C.

Lemma Ccojminus : forall a b : Complex , (Ccoj a - Ccoj b = Ccoj ( a - b ))%C.
Proof.
  intros.
  unfold Cminus.
  replace ( - Ccoj b )%C with ( Ccoj (- b) )%C.
  rewrite Ccojplus.
  auto.
  replace ( - b )%C with ( (- C1) * b )%C ; [ idtac | ring ].
  rewrite <- Ccojmult.
  replace ( Ccoj (- C1) )%C with (- C1)%C.
  ring.
  unfold C1.
  unfold Copp.
  unfold Ccoj.
  simpl.
  apply injective_projections.
  simpl.
  ring.
  simpl.
  ring.
Qed.

Lemma Cineq_plus : forall a b c : Complex , ( a < b -> a + c < b + c )%C.
Proof.
  intros.
  rewrite Cdecompose with (z:=a) in H.
  rewrite Cdecompose with (z:=b) in H.
  rewrite Cdecompose with (z:=a).
  rewrite Cdecompose with (z:=b).
  rewrite Cdecompose with (z:=c).
  rewrite ! Cplus_decompose.
  simpl.
  destruct ( Real_eq_dec (real_p a + real_p c) (real_p b + real_p c) ).
  apply Rplus_eq_reg_r in e.
  simpl in H.
  destruct ( Real_eq_dec (real_p a) (real_p b) ).
  apply Rplus_lt_compat_r.
  auto.
  contradiction.
  simpl in H.
  destruct ( Real_eq_dec (real_p a) (real_p b) ).
  apply Rplus_eq_compat_r with ( r := real_p c ) in e.
  contradiction.
  apply Rplus_lt_compat_r.
  auto.
Qed.

Lemma Cineq_eq : forall a b : Complex , (a < b)%C -> a <> b.
Proof.
  intros.
  unfold not.
  intros.
  rewrite Cdecompose with (z:=a) in H.
  rewrite Cdecompose with (z:=b) in H.
  simpl in H.
  destruct ( Real_eq_dec (real_p a) (real_p b) ).
  assert (imag_p a = imag_p b)%R.
  rewrite H0.
  auto.
  assert ( imag_p a <> imag_p b ).
  auto with real.
  contradiction.
  elim n.
  rewrite H0.
  auto.
Qed.

Lemma argstan_PI2 : (-PI < PI/2 <= PI)%R.
Proof.
  split.
  apply Rlt_trans with (r2:=0%R).
  apply Ropp_lt_gt_0_contravar.
  apply PI_RGT_0.
  apply PI2_RGT_0.
  left.
  apply PI2_Rlt_PI.
Qed.

Lemma Cineq0_arg : forall x : Complex , ( C0 < x -> (-PI/2 < Carg x <= PI/2)%R )%C.
Proof.
  intros.
  assert (C0 <> x)%C as nc0.
  apply Cineq_eq.
  auto.
  rewrite Cdecompose in H.
  simpl in H.
  destruct ( Real_eq_dec 0 (real_p x) ).
  assert ( Carg x = PI/2 )%R.
  apply eq_sym.
  apply Carg_uniq.
  unfold not.
  auto.
  split.
  apply argstan_PI2.
  rewrite cos_PI2.
  rewrite sin_PI2.
  replace ( Cabs x ) with ( imag_p x ).
  replace ( (imag_p x * 0)%R ) with ( real_p x ).
  replace ( (imag_p x * 1)%R ) with ( imag_p x ).
  apply Cdecompose.
  ring.
  rewrite <- e.
  ring.
  unfold Cabs.
  rewrite <- e.
  replace (0 * 0 + imag_p x * imag_p x)%R with ( imag_p x * imag_p x )%R ; [ idtac | ring ].
  rewrite sqrt_square.
  auto.
  left; auto.
  rewrite H0.
  split.
  rewrite Ropp_div.
  apply pos_opp_lt.
  apply PI2_RGT_0.
  right ; auto.
  assert ( (- PI < Carg x <= PI)%R ).
  apply Carg_def.
  apply Peirce.
  intros.
  apply not_and_or in H1.
  rewrite Creal_arg in H.
  replace 0%R with ( Cabs x * 0 )%R in H; [ idtac | ring ].
  apply Rmult_lt_reg_l in H.
  case H1.
  intros.
  apply Rnot_lt_le in H2.
  apply Rlt_not_le in H.
  elim H.
  replace 0%R with ( cos ( - (PI / 2) ) )%R.
  admit.
  rewrite cos_neg.
  rewrite cos_PI2.
  auto.
  intros.
  apply Rnot_le_lt in H2.
  apply Rlt_not_le in H.
  elim H.
  replace 0%R with ( cos (PI / 2 ) )%R.
  apply cos_decr_1.
  left ; apply PI2_RGT_0.
  left ; apply PI2_Rlt_PI.
  apply Rle_trans with ( r2 := (PI/2)%R ).
  left ; apply PI2_RGT_0.
  left; auto.
  apply Carg_def.
  left ; auto.
  rewrite cos_PI2 ; auto.
  apply Cneq0abs.
  auto.
Admitted.

Lemma Cpluscoj0 : forall x : Complex , (x + Ccoj x)%C = C0 -> real_p x = 0%R.
Proof.
  intros.
  assert ( x = - Ccoj x )%C.
  apply Ceq_side.
  ring_simplify.
  auto.
  unfold Ccoj in H0.
  unfold Copp in H0.
  assert (real_p x = - real_p x )%R.
  replace (- real_p x)%R with (real_p ((- real_p x)%R, (- - imag_p x)%R) ). 
  rewrite <- H0.
  auto.
  auto.
  apply Peirce.
  intros.
  apply Rdichotomy in H2.
  case H2.
  intros.
  apply Rlt_not_ge in H3.
  elim H3.
  left.
  apply Rnot_ge_lt in H3.
  rewrite H1.
  auto with real.
  intros.
  apply Rgt_not_le in H3.
  elim H3.
  left.
  apply Rnot_le_gt in H3.
  rewrite H1.
  auto with real.
Qed.

Lemma imag_p_abs : forall x : Complex , (x + Ccoj x)%C = C0 -> (0 <= imag_p x)%R -> x = (0,Cabs x)%R.
Proof.
  intros.
  assert ( real_p x = 0 )%R.
  apply Cpluscoj0.
  auto.
  unfold Cabs.
  rewrite H1.
  replace (0 * 0 + imag_p x * imag_p x)%R with ( imag_p x * imag_p x )%R ; [ idtac | ring ].
  rewrite sqrt_square.
  rewrite <- H1.
  apply Cdecompose.
  auto.
Qed.

Lemma imag_p_arg : forall x : Complex , Carg x = (PI/2)%R  -> x = (0,Cabs x)%R.
Proof.
  intros.
  assert ( x = ((Cabs x * cos (PI / 2))%R, (Cabs x * sin (PI / 2))%R) ).
  rewrite <- H.
  apply Carg_def.
  rewrite cos_PI2 in H0.
  rewrite sin_PI2 in H0.
  replace (Cabs x * 0)%R with 0%R in H0 ; [ idtac | ring ].
  replace (Cabs x * 1)%R with (Cabs x) in H0 ; [ idtac | ring ].
  auto.
Qed.

Lemma imag_p_arg_rev : forall x : R , (0<x)%R -> Carg (0,x)%R = (PI/2)%R.
Proof.
  intros.
  apply eq_sym.
  apply Carg_uniq.
  unfold not.
  intros.
  assert ( 0 <> x )%R.
  auto with real.
  elim H1.
  replace x with (snd (0%R, x) ).
  rewrite H0.
  auto.
  auto.
  split.
  apply argstan_PI2.
  rewrite cos_PI2.
  rewrite sin_PI2.
  unfold Cabs.
  simpl.
  apply injective_projections.
  simpl.
  ring.
  simpl.
  replace ( 0 * 0 + x * x )%R with ( x * x )%R ; [ idtac | ring ].
  rewrite sqrt_square.
  ring.
  left ; auto.
Qed.

Lemma imag_p_arg2_rev : forall x : R , (0<x)%R -> Carg (0,-x)%R = (-PI/2)%R.
Proof.
  intros.
  replace ( (0%R, (- x)%R) ) with ( - (0%R, x) )%C .
  rewrite Carg_neg.
  rewrite imag_p_arg_rev.
  unfold argplus.
  destruct ( total_order_T (PI / 2 + PI) PI ).
  destruct s.
  apply Rlt_not_le in r.
  elim r.
  left.
  apply Rminus_gt_0_lt.
  replace (PI / 2 + PI - PI)%R with (PI / 2)%R ; [ idtac | ring ].
  apply PI2_RGT_0.
  assert ( PI < (PI / 2 + PI)%R )%R.
  apply Rminus_gt_0_lt.
  replace (PI / 2 + PI - PI)%R with (PI / 2)%R ; [ idtac | ring ].
  apply PI2_RGT_0.
  assert ( ~ (PI / 2 + PI)%R = PI ).
  auto with real.
  contradiction.
  field.
  auto.
  assert ( 0 <> x )%R.
  auto with real.
  unfold not.
  intros.
  elim H0.
  replace x with (snd (0%R, x) ).
  rewrite H1.
  auto.
  auto.
  unfold Copp.
  apply injective_projections.
  simpl.
  ring.
  auto.
Qed.

Lemma imag_p_arg2 : forall x : Complex , Carg x = (-PI/2)%R  -> x = (0,-Cabs x)%R.
Proof.
  intros.
  assert ( x = ((Cabs x * cos (-(PI / 2)))%R, (Cabs x * sin (-(PI / 2)))%R) ).
  replace ( - PI /2 )%R with ( - (PI/2 ) )%R in H ; [ idtac | field ].
  rewrite <- H.
  apply Carg_def.
  rewrite cos_neg in H0.
  rewrite sin_neg in H0.
  rewrite cos_PI2 in H0.
  rewrite sin_PI2 in H0.
  replace (Cabs x * 0)%R with 0%R in H0 ; [ idtac | ring ].
  replace (Cabs x * -(1))%R with (-Cabs x)%R in H0 ; [ idtac | ring ].
  auto.
Qed.

Lemma Carg_imag_ineq : forall x : Complex , x <> C0 -> (0 <= imag_p x)%R -> (0<=Carg x)%R.
Proof.
  intros x xc0.
  intros.
  rewrite Cimag_arg in H.
  replace 0%R with ( Cabs x * 0 )%R in H; [ idtac | ring ].
  apply Rmult_le_reg_l in H.
  apply Peirce.
  intros.
  apply Rnot_le_lt in H0.
  apply Rle_not_lt in H.
  elim H.
  apply sin_lt_0_var.
  apply Carg_def.
  auto.
  apply Cneq0abs.
  auto.
Qed. 

Lemma Carg_imag_ineq2 : forall x : Complex , x <> C0 -> (imag_p x < 0)%R -> (Carg x<0)%R.
Proof.
  intros x xc0.
  intros.
  rewrite Cimag_arg in H.
  replace 0%R with ( Cabs x * 0 )%R in H; [ idtac | ring ].
  apply Rmult_lt_reg_l in H.
  apply Peirce.
  intros.
  apply Rnot_lt_le in H0.
  apply Rlt_not_le in H.
  elim H.
  apply sin_ge_0.
  auto.
  apply Carg_def.
  apply Cneq0abs.
  auto.
Qed. 

Lemma argplus1 : forall a b : R , (-PI/2 < a <= PI/2)%R -> (-PI/2 < b <= PI/2)%R -> a +^ b = (a + b)%R.
Proof.
  intros.
  destruct H as [ a1 a2 ].
  destruct H0 as [ b1 b2 ].
  assert (-PI < a + b )%R.
  replace ( - PI )%R with ( - PI / 2 + - PI/2 )%R ; [ idtac | field ].
  apply Rplus_lt_compat.
  auto.
  auto.
  assert ( a + b <= PI )%R.
  replace ( PI )%R with ( PI / 2 + PI/2 )%R ; [ idtac | field ].
  apply Rplus_le_compat.
  auto.
  auto.
  unfold argplus.
  destruct ( total_order_T (a + b) PI ).
  destruct ( total_order_T (a + b) (- PI) ).
  destruct s0.
  assert ( ~ - PI < - PI )%R.
  auto with real.
  elim H1.
  apply Rlt_trans with (r2 := (a+b)%R ).
  auto with real.
  auto with real.
  assert ( ~ - PI < - PI )%R.
  auto with real.
  rewrite e in H.
  contradiction.
  auto.
  apply Rle_not_gt in H0.
  contradiction.
Qed.

Lemma argstan_nPI2 : (-PI < -PI/2 <= PI)%R.
Proof.
  replace ( - PI / 2 )%R with ( - (PI/2) )%R ; [ idtac | field ].
  split.
  apply Ropp_lt_gt_contravar.
  apply PI2_Rlt_PI.
  apply Rle_trans with (r2:=0%R).
  replace 0%R with (-0)%R ; [ idtac|ring].
  apply Ropp_le_contravar.
  left ; apply PI2_RGT_0.
  left.
  apply PI_RGT_0.
Qed.

Lemma Carg_real0 : forall a : Complex , ( a <> C0 -> real_p a = 0 -> Carg a = PI / 2 \/ Carg a = - PI / 2 )%R.
Proof.
  intros.
  assert ( imag_p a <> 0 )%R.
  unfold not.
  intros.
  elim H.
  unfold C0.
  rewrite Cdecompose with (z:=a).
  rewrite H0.
  rewrite H1.
  auto.
  apply Rdichotomy in H1.
  case H1.
  intros.
  right.
  apply eq_sym.
  apply Carg_uniq.
  auto.
  split.
  apply argstan_nPI2.
  replace ( (- PI / 2))%R with ( - (PI / 2))%R ; [ idtac | field ].
  rewrite cos_neg.
  rewrite sin_neg.
  rewrite cos_PI2.
  rewrite sin_PI2.
  replace ( (Cabs a * 0))%R with 0%R ; [ idtac | ring ].
  unfold Cabs.
  rewrite H0.
  replace (0 * 0 + imag_p a * imag_p a)%R with ( (-imag_p a) * (-imag_p a) )%R ; [ idtac | ring ].
  rewrite sqrt_square.
  replace (- imag_p a * - (1))%R with ( imag_p a ) ; [ idtac|ring ].
  rewrite <- H0.
  apply Cdecompose.
  left.
  auto with real.
  intros.
  left.
  apply eq_sym.
  apply Carg_uniq.
  auto.
  split.
  apply argstan_PI2.
  rewrite cos_PI2.
  rewrite sin_PI2.
  replace ( (Cabs a * 0))%R with 0%R ; [ idtac | ring ].
  unfold Cabs.
  rewrite H0.
  replace (0 * 0 + imag_p a * imag_p a)%R with ( imag_p a * imag_p a )%R ; [ idtac | ring ].
  rewrite sqrt_square.
  rewrite <- H0.
  replace (imag_p a * 1)%R with (imag_p a) ; [ idtac | ring ].
  apply Cdecompose.
  left; auto.
Qed.

Lemma on_line_shib_c1 : forall l : Line , (0 <= imag_p l)%R ->  forall a b : Complex , ( b < a -> on_line a l -> on_line b l -> (a-b)*(Lshib l)=(0%R,Cabs(a-b)) )%C.
Proof.
  intros l il.
  unfold on_line.
  intros.
  rewrite <- H1 in H0.
  apply Ceq_side2 in H0.
  replace (l * a + Ccoj l * Ccoj a - (l * b + Ccoj l * Ccoj b))%C 
  with (l * (a - b) + ( Ccoj l * (Ccoj a - Ccoj b )))%C in H0; [ idtac | ring ].
  rewrite Ccojminus in H0.
  rewrite Ccojmult in H0.
  replace ( Cabs (a - b)%C ) with ( Cabs ((a - b)*l)%C ).
  apply imag_p_arg.
  assert ( real_p ((a - b) * l)%C = 0%R ).
  apply Cpluscoj0.
  rewrite Cmult_comm.
  auto.
  apply Carg_real0 in H2.
  case H2.
  auto.
  intros.
  assert ( Carg ((a - b) * l)%C > (- PI / 2)%R )%R.
  rewrite <- Cmultarg.
  rewrite argplus1.
  assert ( 0 <= Carg l )%R.
  apply Carg_imag_ineq.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Lshib_gt_C0.
  auto.
  replace ( (- PI / 2))%R with ( - (PI / 2))%R ; [ idtac | field ].
  rewrite <- Rminus_0_l.
  rewrite Rplus_comm.
  unfold Rminus.
  apply Rplus_ge_gt_compat.
  auto with real.
  replace ( -( PI / 2))%R with ( (-PI / 2))%R ; [ idtac | field ].
  apply Cineq0_arg.
  apply Cineq_plus with ( c := (-b)%C ) in H.
  ring_simplify in H.
  replace ( - b + a )%C with ( a - b )%C in H; [ idtac | ring ].
  auto.
  apply Cineq0_arg.
  apply Cineq_plus with ( c := (-b)%C ) in H.
  ring_simplify in H.
  replace ( - b + a )%C with ( a - b )%C in H; [ idtac | ring ].
  auto.
  apply Cineq0_arg.
  apply Lshib_gt_C0.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Cineq_plus with ( c := (-b)%C ) in H.
  ring_simplify in H.
  replace ( - b + a )%C with ( a - b )%C in H; [ idtac | ring ].
  auto.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Lshib_gt_C0.
  assert ( ~ Carg ((a - b) * l)%C = (- PI / 2)%R ).
  auto with real.
  contradiction.
  apply C0mult.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Cineq_plus with ( c := (-b)%C ) in H.
  ring_simplify in H.
  replace ( - b + a )%C with ( a - b )%C in H; [ idtac | ring ].
  auto.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Lshib_gt_C0.
  rewrite <- abs_mult.
  replace (Cabs l) with 1%R.
  ring.
  apply eq_sym.
  apply Lshib_len1.
Qed.

Lemma on_line_shib_c2 : forall l : Line , (imag_p l<0)%R ->  forall a b : Complex , ( b < a -> on_line a l -> on_line b l -> (a-b)*(Lshib l)=(0,-Cabs(a-b)%C)%R )%C.
Proof.
  intros l il.
  unfold on_line.
  intros.
  rewrite <- H1 in H0.
  apply Ceq_side2 in H0.
  replace (l * a + Ccoj l * Ccoj a - (l * b + Ccoj l * Ccoj b))%C 
  with (l * (a - b) + ( Ccoj l * (Ccoj a - Ccoj b )))%C in H0; [ idtac | ring ].
  rewrite Ccojminus in H0.
  rewrite Ccojmult in H0.
  replace ( Cabs (a - b)%C ) with ( Cabs ((a - b)*l)%C ).
  apply imag_p_arg2.
  assert ( real_p ((a - b) * l)%C = 0%R ).
  apply Cpluscoj0.
  rewrite Cmult_comm.
  auto.
  apply Carg_real0 in H2.
  case H2.
  intros.
  assert ( Carg ((a - b) * l)%C < (PI / 2)%R )%R.
  rewrite <- Cmultarg.
  rewrite argplus1.
  assert ( Carg l < 0 )%R.
  apply Carg_imag_ineq2.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Lshib_gt_C0.
  auto.
  replace ( ( PI / 2))%R with ( (PI / 2) + 0 )%R ; [ idtac | field ].
  apply Rplus_ge_gt_compat.
  apply Rle_ge.
  apply Cineq0_arg.
  apply Cineq_plus with ( c := (-b)%C ) in H.
  ring_simplify in H.
  replace ( - b + a )%C with ( a - b )%C in H; [ idtac | ring ].
  auto.
  auto with real.
  apply Cineq0_arg.
  apply Cineq_plus with ( c := (-b)%C ) in H.
  ring_simplify in H.
  replace ( - b + a )%C with ( a - b )%C in H; [ idtac | ring ].
  auto.
  apply Cineq0_arg.
  apply Lshib_gt_C0.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Cineq_plus with ( c := (-b)%C ) in H.
  ring_simplify in H.
  replace ( - b + a )%C with ( a - b )%C in H; [ idtac | ring ].
  auto.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Lshib_gt_C0.
  assert ( ~ Carg ((a - b) * l)%C = ( PI / 2)%R ).
  auto with real.
  contradiction.
  auto.
  apply C0mult.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Cineq_plus with ( c := (-b)%C ) in H.
  ring_simplify in H.
  replace ( - b + a )%C with ( a - b )%C in H; [ idtac | ring ].
  auto.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Lshib_gt_C0.
  rewrite <- abs_mult.
  replace (Cabs l) with 1%R.
  ring.
  apply eq_sym.
  apply Lshib_len1.
Qed.

Lemma argplusneg : forall a b : R , (-PI<a<=PI)%R -> (-PI<b<=PI)%R -> b +^ a = 0%R -> b = -^ a.
Proof.
  unfold argplus.
  intros.
  destruct ( total_order_T (b + a) PI ).
  destruct ( total_order_T (b + a) (-PI) ).
  assert ( b + a = -2 * PI )%R.
  apply Rminus_diag_uniq.
  rewrite <- H1.
  ring.
  assert ( (b + a > -2 * PI)%R ).
  replace ( - 2*PI )%R with ( - PI + -PI )%R ; [ idtac | ring ].
  apply Rplus_gt_compat.
  destruct H0.
  auto with real.
  destruct H.
  auto with real.
  assert ( (b + a <> -2 * PI)%R ).
  auto with real.
  contradiction.
  unfold argneg.
  assert ( b = - a )%R.
  apply Rminus_diag_uniq.
  rewrite <- H1.
  ring.
  destruct ( Real_eq_dec a PI ).
  destruct H0.
  apply Rlt_not_le in H0.
  elim H0.
  right; rewrite e in H2 ; auto.
  auto.
  destruct H.
  destruct H0.
  case H2.
  intros.
  assert ( a + b < 2*PI )%R.
  replace ( 2*PI )%R with (  PI + PI )%R ; [ idtac | ring ].
  apply Rplus_gt_ge_compat.
  auto with real.
  auto with real.
  assert ( (a + b <> 2 * PI)%R ).
  auto with real.
  elim H6.
  apply Rminus_diag_uniq.
  rewrite <- H1.
  ring.
  intros.
  assert ( b = PI ).
  apply Rminus_diag_uniq.
  rewrite <- H1.
  rewrite H4.
  ring.
  unfold argneg.
  destruct ( Real_eq_dec a PI ).
  auto.
  contradiction.
Qed.

Lemma argneginv : forall x : Complex , x <> C0 -> Carg (/ x)%C = -^ Carg x.
Proof.
  intros.
  apply argplusneg.
  apply Carg_def.
  apply Carg_def.
  rewrite Cmultarg.
  replace (/ x * x )%C with C1 ; [ idtac | field ].
  apply Carg_R.
  auto with real.
  auto.
  apply CinvnC0.
  auto.
  auto.
Qed.

Lemma argminusdiv : forall x y : Complex , x <> C0 -> y <> C0 -> Carg x -^ Carg y = Carg ( x/y )%C.
Proof.
  intros.
  unfold Cdiv.
  rewrite <- Cmultarg.
  rewrite argneginv.
  auto.
  auto.
  auto.
  apply CinvnC0.
  auto.
Qed.

Lemma line_Carg_c1 : forall l : Line , (0 <= imag_p l)%R ->  forall a b : Complex , ( b < a -> on_line a l -> on_line b l -> Carg(a-b)=((PI/2) -^ Carg l)%R )%C.
Proof.
  intros.
  assert ( (a-b)*(Lshib l)=(0%R,Cabs(a-b)) )%C.
  apply on_line_shib_c1.
  auto.
  auto.
  auto.
  auto.
  assert ( (a - b)%C = (a - b) * l / l)%C .
  field.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Lshib_gt_C0.
  rewrite H3 in H4.
  rewrite H4.
  rewrite <- argminusdiv.
  Search ( Carg _ = PI/2 )%R.
  rewrite imag_p_arg_rev.
  auto.
  apply Cneq0abs.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Cineq_plus with ( c := (-b)%C ) in H0.
  ring_simplify in H0.
  replace ( - b + a )%C with ( a - b )%C in H0; [ idtac | ring ].
  auto.
  unfold not.
  intros.
  assert ( 0 < Cabs (a - b)%C )%R.
  apply Cneq0abs.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Cineq_plus with ( c := (-b)%C ) in H0.
  ring_simplify in H0.
  replace ( - b + a )%C with ( a - b )%C in H0; [ idtac | ring ].
  auto.
  assert ( (0 <> Cabs (a - b)%C)%R ).
  auto with real.
  elim H7.
  replace ( Cabs (a - b)%C ) with ( snd (0%R, Cabs (a - b)%C) ).
  rewrite H5.
  auto.
  auto.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Lshib_gt_C0.
Qed.

Lemma line_Carg_c2 : forall l : Line , (imag_p l < 0)%R ->  forall a b : Complex , ( b < a -> on_line a l -> on_line b l -> Carg(a-b)=((-PI/2) -^ Carg l)%R )%C.
Proof.
  intros.
  assert ( (a-b)*(Lshib l)=(0%R,-Cabs(a-b)%C)%R )%C.
  apply on_line_shib_c2.
  auto.
  auto.
  auto.
  auto.
  assert ( (a - b)%C = (a - b) * l / l)%C .
  field.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Lshib_gt_C0.
  rewrite H3 in H4.
  rewrite H4.
  rewrite <- argminusdiv.
  rewrite imag_p_arg2_rev.
  auto.
  apply Cneq0abs.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Cineq_plus with ( c := (-b)%C ) in H0.
  ring_simplify in H0.
  replace ( - b + a )%C with ( a - b )%C in H0; [ idtac | ring ].
  auto.
  unfold not.
  intros.
  assert ( 0 > -Cabs (a - b)%C )%R.
  apply Ropp_0_lt_gt_contravar.
  apply Cneq0abs.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Cineq_plus with ( c := (-b)%C ) in H0.
  ring_simplify in H0.
  replace ( - b + a )%C with ( a - b )%C in H0; [ idtac | ring ].
  auto.
  assert ( (0 <> -Cabs (a - b)%C)%R ).
  auto with real.
  elim H7.
  replace ( -Cabs (a - b)%C )%R with ( snd (0%R, -Cabs (a - b)%C)%R ).
  rewrite H5.
  auto.
  auto.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Lshib_gt_C0.
Qed.

Lemma argminusxx : forall x : R , x -^ x = 0%R .
Proof.
  intros.
  unfold argminus.
  unfold argneg.
  destruct (  Real_eq_dec x PI ).
  rewrite e.
  unfold argplus.
  destruct ( total_order_T (PI + PI) PI ).
  destruct s.
  apply Rlt_not_le in r.
  elim r.
  left.
  apply Rminus_gt_0_lt.
  ring_simplify.
  apply PI_RGT_0.
  assert ( PI < (PI + PI)%R )%R.
  apply Rminus_gt_0_lt.
  ring_simplify.
  apply PI_RGT_0.
  assert ( (PI + PI)%R <> PI ).
  auto with real.
  contradiction.
  ring.
  unfold argplus.
  replace ( x + - x )%R with 0%R ; [ idtac | ring ].
  destruct ( total_order_T 0 PI ).
  destruct ( total_order_T 0 (- PI) ).
  destruct s0.
  replace ( -PI )%R with ( 0 - PI )%R in r; [ idtac | ring ].
  apply Rminus_gt_0_lt in r.
  apply Rlt_not_le in r.
  elim r.
  left; apply PI_RGT_0.
  assert ( 0 > - PI )%R.
  replace ( -PI )%R with ( 0 - PI )%R; [ idtac | ring ].
  apply Rminus_gt_0_lt.
  replace ( 0 - (0 - PI))%R with ( PI )%R; [ idtac | ring ].
  apply PI_RGT_0.
  assert ( (0 <> - PI)%R ).
  auto with real.
  contradiction.
  auto.
  apply Rgt_not_le in r.
  elim r.
  left ; apply PI_RGT_0.
Qed.

Lemma line_DAngle0 : forall l : Line , forall a b c : Complex , on_line a l -> on_line b l -> on_line c l -> (a < b -> a < c -> DAngle b a c = 0%R )%C.
Proof.
  intros.
  assert ( {imag_p l < 0} + {imag_p l = 0} + {imag_p l > 0} )%R.
  apply total_order_T.
  destruct H4.
  destruct s.
  unfold DAngle.
  rewrite ! line_Carg_c2 with (l:=l).
  rewrite argminusxx.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  unfold DAngle.
  rewrite ! line_Carg_c1 with (l:=l).
  rewrite argminusxx.
  auto.
  right; auto.
  auto.
  auto.
  auto.
  right; auto.
  auto.
  auto.
  auto.
  unfold DAngle.
  rewrite ! line_Carg_c1 with (l:=l).
  rewrite argminusxx.
  auto.
  left; auto.
  auto.
  auto.
  auto.
  left; auto.
  auto.
  auto.
  auto.
Qed.

Lemma argplus_comm : forall x y : R , x +^ y = y +^ x.
Proof.
  intros.
  unfold argplus.
  replace (x+y)%R with (y+x)%R ; [ idtac | ring ].
  auto.
Qed.

Lemma argplus_assoc : forall x y z : R , ( -PI < x <= PI )%R -> ( -PI < y <= PI )%R -> ( -PI < z <= PI )%R -> x +^ (y +^ z ) = (x +^ y) +^ z.
Proof.
Admitted.

Lemma argstan_PI : (-PI < PI <= PI)%R.
Proof.
  intros.
  split.
  apply Rlt_trans with (r2:=0%R).
  replace ( -PI )%R with ( 0 - PI )%R; [ idtac | ring ].
  apply Rminus_gt_0_lt.
  replace ( 0 - (0 - PI))%R with ( PI )%R; [ idtac | ring ].
  apply PI_RGT_0.
  apply PI_RGT_0.
  right; auto.
Qed.

Lemma line_DAnglePI : forall l : Line , forall a b c : Complex , on_line a l -> on_line b l -> on_line c l -> (b < a -> a < c -> DAngle b a c = PI)%C .
Proof.
  intros.
  assert ( {imag_p l < 0} + {imag_p l = 0} + {imag_p l > 0} )%R.
  apply total_order_T.
  destruct H4.
  destruct s.
  unfold DAngle.
  replace (b-a)%C with (-(a-b))%C ; [ idtac|ring ].
  rewrite Carg_neg.
  rewrite ! line_Carg_c2 with (l:=l).
  rewrite argplus_comm.
  unfold argminus.
  rewrite <- argplus_assoc.
  replace (((- PI / 2) +^ (-^ Carg l)) +^ (-^ ((- PI / 2) +^ (-^ Carg l)))%R ) with ( (((- PI / 2) +^ (-^ Carg l)) -^ ((- PI / 2) +^ (-^ Carg l))) ); [ idtac | auto ].
  rewrite argminusxx.
  rewrite argplus_comm.
  apply argplus0.
  apply argstan_PI.
  apply argstan_PI.
  Search ( -PI < _ <= PI )%R.
  apply argplusineq.
  apply argstan_nPI2.
  apply argnegineq.
  apply Carg_def.
  apply argnegineq.
  apply argplusineq.
  apply argstan_nPI2.
  apply argnegineq.
  apply Carg_def.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Cineq_plus with ( c := (-b)%C ) in H2.
  ring_simplify in H2.
  replace ( - b + a )%C with ( a - b )%C in H2; [ idtac | ring ].
  auto.
  unfold DAngle.
  replace (b-a)%C with (-(a-b))%C ; [ idtac|ring ].
  rewrite Carg_neg.
  rewrite ! line_Carg_c1 with (l:=l).
  rewrite argplus_comm.
  unfold argminus.
  rewrite <- argplus_assoc.
  replace (((PI / 2) +^ (-^ Carg l)) +^ (-^ ((PI / 2) +^ (-^ Carg l))) )%R with ( (((PI / 2) +^ (-^ Carg l)) -^ ((PI / 2) +^ (-^ Carg l))) ); [ idtac | auto ].
  rewrite argminusxx.
  rewrite argplus_comm.
  apply argplus0.
  apply argstan_PI.
  apply argstan_PI.
  apply argplusineq.
  apply argstan_PI2.
  apply argnegineq.
  apply Carg_def.
  apply argnegineq.
  apply argplusineq.
  apply argstan_PI2.
  apply argnegineq.
  apply Carg_def.
  right;auto.
  auto.
  auto.
  auto.
  right; auto.
  auto.
  auto.
  auto.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Cineq_plus with ( c := (-b)%C ) in H2.
  ring_simplify in H2.
  replace ( - b + a )%C with ( a - b )%C in H2; [ idtac | ring ].
  auto.
  unfold DAngle.
  replace (b-a)%C with (-(a-b))%C ; [ idtac|ring ].
  rewrite Carg_neg.
  rewrite ! line_Carg_c1 with (l:=l).
  rewrite argplus_comm.
  unfold argminus.
  rewrite <- argplus_assoc.
  replace (((PI / 2) +^ (-^ Carg l)) +^ (-^ ((PI / 2) +^ (-^ Carg l))) )%R with ( (((PI / 2) +^ (-^ Carg l)) -^ ((PI / 2) +^ (-^ Carg l))) ); [ idtac | auto ].
  rewrite argminusxx.
  rewrite argplus_comm.
  apply argplus0.
  apply argstan_PI.
  apply argstan_PI.
  apply argplusineq.
  apply argstan_PI2.
  apply argnegineq.
  apply Carg_def.
  apply argnegineq.
  apply argplusineq.
  apply argstan_PI2.
  apply argnegineq.
  apply Carg_def.
  left;auto.
  auto.
  auto.
  auto.
  left; auto.
  auto.
  auto.
  auto.
  apply not_eq_sym.
  apply Cineq_eq.
  apply Cineq_plus with ( c := (-b)%C ) in H2.
  ring_simplify in H2.
  replace ( - b + a )%C with ( a - b )%C in H2; [ idtac | ring ].
  auto.
Qed.


