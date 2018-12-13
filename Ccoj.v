Require Import Cbase Cabs Carg.

Local Open Scope R_scope.


Local Close Scope R_scope.

Definition Ccoj ( z : Complex ) : Complex := ( real_p z , - imag_p z )%R.

Lemma Ccojplus : forall a b : Complex , (Ccoj a + Ccoj b = Ccoj ( a + b ))%C.
Proof.
  intros.
  unfold Ccoj.
  apply injective_projections.
  simpl.
  rewrite Cplus_decompose.
  simpl.
  ring.
  simpl.
  rewrite Cplus_decompose.
  simpl.
  ring.
Qed.

Lemma Ccojmult : forall a b : Complex , (Ccoj a * Ccoj b = Ccoj ( a * b ))%C.
Proof.
  intros.
  unfold Ccoj.
  apply injective_projections.
  simpl.
  rewrite Cmult_decompose.
  simpl.
  ring.
  simpl.
  rewrite Cmult_decompose.
  simpl.
  ring.
Qed.

Lemma Cabscoj : forall a : Complex , Cabs a = Cabs ( Ccoj a ).
Proof.
  unfold Ccoj.
  unfold Cabs.
  simpl.
  intros.
  replace (  - imag_p a * - imag_p a )%R with (imag_p a * imag_p a )%R ; [idtac|ring].
  auto.
Qed.

Definition argneg ( x : R ) := if (Real_eq_dec x PI) then PI else (-x)%R.

Notation " -^ x " := (argneg x) (at level 20).

Lemma Ccoj0 : forall z : Complex , z <> C0 -> Ccoj z <> C0.
Proof.
  intros.
  unfold not.
  intros.
  elim H.
  apply Cabs0z0.
  rewrite Cabscoj.
  rewrite H0.
  unfold C0.
  unfold Cabs.
  simpl.
  replace ( (0 * 0 + 0 * 0)%R ) with 0%R ; [idtac|ring].
  apply sqrt_0.
Qed.

Lemma Ccojcoj : forall z : Complex , Ccoj (Ccoj z ) = z.
Proof.
  unfold Ccoj.
  simpl.
  intros.
  rewrite Cdecompose.
  replace (- - imag_p z)%R with (imag_p z)%R ; [ idtac | ring ].
  auto.
Qed. 

Lemma Ccojeq : forall z1 z2 : Complex , Ccoj z1 = Ccoj z2 -> z1 = z2.
Proof.
  intros.
  unfold Ccoj in H.
  apply injective_projections.
  replace ( fst z1 ) with ( fst (real_p z1, (- imag_p z1)%R) ).
  replace ( fst z2 ) with ( fst (real_p z2, (- imag_p z2)%R) ).
  rewrite H.
  auto.
  auto.
  auto.
  replace ( snd z1 ) with ( - snd (real_p z1, (- imag_p z1)%R) )%R.
  replace ( snd z2 ) with ( - snd (real_p z2, (- imag_p z2)%R) )%R.
  rewrite H.
  auto.
  simpl.
  unfold imag_p.
  ring.
  simpl.
  unfold imag_p.
  ring.
Qed.

Lemma Ccojarg : forall z : Complex , z <> C0 -> Carg (Ccoj z) = -^ Carg z.
Proof.
  intros z zn0.
  unfold argneg.
  destruct ( Real_eq_dec (Carg z) PI ).
  assert ( (-PI < Carg z <= PI)%R /\ z = (Cabs z*cos (Carg z),Cabs z*sin (Carg z))%R ).
  apply Carg_def.
  rewrite e in H.
  destruct H.
  rewrite cos_PI in H0.
  rewrite sin_PI in H0.
  apply eq_sym.
  apply Carg_uniq.
  apply Ccoj0.
  auto.
  split.
  auto.
  auto.
  apply Ccojeq.
  rewrite Ccojcoj.
  rewrite <- Cabscoj.
  unfold Ccoj.
  simpl.
  rewrite cos_PI.
  rewrite sin_PI.
  rewrite H0.
  apply injective_projections.
  simpl.
  rewrite <- H0.
  auto.
  simpl.
  rewrite <- H0.
  ring.
  assert ( (-PI < Carg z <= PI)%R /\ z = (Cabs z*cos (Carg z),Cabs z*sin (Carg z))%R ).
  apply Carg_def.
  destruct H.
  destruct H.
  assert ( (Carg z < PI)%R ).
  case H1.
  auto.
  intros.
  contradiction.
  apply eq_sym.
  apply Carg_uniq.
  apply Ccoj0.
  auto.
  split.
  split.
  apply Ropp_lt_contravar.
  auto.
  apply Ropp_le_cancel.
  left.
  ring_simplify.
  auto.
  rewrite cos_neg.
  rewrite sin_neg.
  rewrite <- Cabscoj.
  replace ( Ccoj z ) with ( Ccoj ((Cabs z * cos (Carg z))%R, (Cabs z * sin (Carg z))%R) ).
  unfold Ccoj.
  simpl.
  replace (- (Cabs z * sin (Carg z)))%R with (Cabs z * - sin (Carg z))%R ; [ idtac | ring ].
  auto.
  rewrite <- H0.
  auto.
Qed.

Lemma total_order_T2 ( x : R ) ( y : R ) : { (x < y)%R } + { (x >= y)%R }.
Proof.
  assert (  {x < y} + {x = y} + {x > y} )%R.
  apply total_order_T.
  destruct H.
  destruct s.
  left ; auto.
  right ; right ; auto.
  right ; left ; auto.
Qed.

Definition argplus ( x : R ) ( y : R ) := if (total_order_T (x+y) PI) then if (total_order_T (x+y) (-PI)) then (x+y+2*PI)%R else (x+y)%R else (x+y-2*PI)%R.

Infix " +^ " := argplus (at level 20).

Lemma argplusineq : forall x y : R , (-PI < x <= PI)%R -> (-PI < y <= PI)%R -> (-PI < ( x +^ y ) <= PI)%R.
Proof.
  intros.
  unfold argplus.
  destruct (total_order_T (x + y) (PI)).
  destruct (total_order_T (x + y) (-PI)).
  destruct s0.
  apply Rplus_lt_compat_r  with (r := (2*PI)%R ) in r.
  ring_simplify in r.
  split.
  apply Rplus_lt_reg_r with (r:=(-2*PI)%R).
  ring_simplify.
  apply Rlt_trans with ( r2 := ( - PI + - PI )%R ).
  ring_simplify.
  apply Rmult_lt_compat_r.
  apply PI_RGT_0.
  auto with real.
  apply Rplus_lt_compat.
  destruct H.
  auto.
  destruct H0.
  auto.
  apply Rlt_le.
  auto.
  rewrite e.
  split.
  ring_simplify.
  replace PI with ( 1 * PI )%R ; [idtac|ring].
  rewrite Ropp_mult_distr_l.
  apply Rmult_lt_compat_r.
  apply PI_RGT_0.
  apply Rplus_lt_reg_r  with (r := (1)%R ).
  ring_simplify.
  auto with real.
  ring_simplify.
  right; auto.
  (* case 2 *)
  split.
  auto.
  destruct s.
  left; auto.
  right; auto.
  (* case 3 *)
  split.
  apply Rplus_lt_reg_r with (r:=(2*PI)%R).
  ring_simplify.
  auto.
  apply Rplus_le_reg_r with (r:=(2*PI)%R).
  ring_simplify.
  apply Rle_trans with ( r2 := ( PI + PI )%R ).
  apply Rplus_le_compat.
  destruct H.
  auto.
  destruct H0.
  auto.
  ring_simplify.
  left.
  apply Rmult_lt_compat_r.
  apply PI_RGT_0.
  auto with real.
Qed.

Lemma argplussin : forall x y : R , sin ( x +^ y ) = sin ( x + y )%R.
Proof.
  intros.
  unfold argplus.
  destruct (total_order_T (x + y) (PI)).
  destruct (total_order_T (x + y) (-PI)).
  replace 2%R with ( 2 * INR 1 )%R.
  apply sin_period.
  unfold INR.
  ring.
  auto.
  rewrite sin_minus.
  rewrite cos_2PI.
  rewrite sin_2PI.
  ring.
Qed.

Lemma argpluscos : forall x y : R , cos ( x +^ y ) = cos ( x + y )%R.
Proof.
  intros.
  unfold argplus.
  destruct (total_order_T (x + y) (PI)).
  destruct (total_order_T (x + y) (-PI)).
  replace 2%R with ( 2 * INR 1 )%R.
  apply cos_period.
  unfold INR.
  ring.
  auto.
  rewrite cos_minus.
  rewrite cos_2PI.
  rewrite sin_2PI.
  ring.
Qed.

Lemma C0mult : forall x y : Complex , x <> C0 -> y <> C0 -> (x*y)%C <> C0.
Proof.
  intros.
  assert ( Cabs x <> 0%R ).
  unfold not.
  intros.
  elim H.
  apply Cabs0z0.
  auto.
  assert ( Cabs y <> 0%R ).
  unfold not.
  intros.
  elim H0.
  apply Cabs0z0.
  auto.
  unfold not.
  intros.
  assert ( Cabs (x*y)%C <> 0%R ).
  rewrite <- abs_mult.
  unfold not.
  intros.
  apply Rmult_integral in H4.
  case H4.
  auto.
  auto.
  elim H4.
  rewrite H3.
  unfold C0.
  unfold Cabs.
  simpl.
  replace ( 0 * 0 + 0 * 0 )%R with 0%R ; [ idtac | ring ].
  apply sqrt_0.
Qed.

Lemma Creal_arg : forall z : Complex , real_p z = (Cabs z * cos (Carg z))%R.
Proof.
  intros.
  assert ((-PI < Carg z <= PI)%R /\ z = (Cabs z*cos (Carg z),Cabs z*sin (Carg z)))%R.
  apply Carg_def.
  destruct H.
  rewrite H0.
  simpl.
  rewrite <- H0.
  auto.
Qed.

Lemma Cimag_arg : forall z : Complex , imag_p z = (Cabs z * sin (Carg z))%R.
Proof.
  intros.
  assert ((-PI < Carg z <= PI)%R /\ z = (Cabs z*cos (Carg z),Cabs z*sin (Carg z)))%R.
  apply Carg_def.
  destruct H.
  rewrite H0.
  simpl.
  rewrite <- H0.
  auto.
Qed.

Lemma Cmultarg : forall x y : Complex , x <> C0 -> y <> C0 -> Carg x +^ Carg y = Carg (x*y)%C.
Proof.
  intros.
  apply Carg_uniq.
  apply C0mult.
  auto.
  auto.
  split.
  apply argplusineq.
  apply Carg_def.
  apply Carg_def.
  rewrite argplussin.
  rewrite argpluscos.
  rewrite <- abs_mult.
  rewrite cos_plus.
  rewrite sin_plus.
  rewrite Cmult_decompose.
  apply injective_projections.
  simpl.
  rewrite ! Creal_arg.
  rewrite ! Cimag_arg.
  ring.
  simpl.
  rewrite ! Creal_arg.
  rewrite ! Cimag_arg.
  ring.
Qed.

