Require Import Cbase Cabs.

Local Open Scope R_scope.

Lemma unique_arg : forall a1 b1 a2 b2 : R , 0<b1 -> 0<b2 -> a1/b1 = a2/b2 -> a1*a1+b1*b1 = a2*a2+b2*b2 -> a1=a2 /\ b1=b2.
Proof.
  intros.
  remember (a1/b1) as t.
  assert ( a1 = t*b1 ).
  rewrite Heqt.
  field.
  auto with real.
  assert ( a2 = t*b2 ).
  rewrite H1.
  field.
  auto with real.
  rewrite H3 in H2.
  rewrite H4 in H2.
  ring_simplify in H2.
  replace ( t ^ 2 * b1 ^ 2 + b1 ^ 2 ) with ( (t ^ 2 + 1 ) * b1 ^ 2 ) in H2; [ idtac | ring ].
  replace ( t ^ 2 * b2 ^ 2 + b2 ^ 2 ) with ( (t ^ 2 + 1 ) * b2 ^ 2 ) in H2; [ idtac | ring ].
  apply Rmult_eq_reg_l in H2.
  assert ( b1 = b2 ).
  replace b1 with ( sqrt (b1^2) ).
  replace b2 with ( sqrt (b2^2) ).
  rewrite H2.
  auto.
  replace ( b2 ^ 2 ) with ( b2 * b2) ; [idtac|ring].
  apply sqrt_square.
  auto with real.
  replace ( b1 ^ 2 ) with ( b1 * b1) ; [idtac|ring].
  apply sqrt_square.
  auto with real.
  assert ( a1 = a2 ).
  rewrite H3.
  rewrite H4.
  rewrite H5.
  auto.
  auto.
  assert ( t^2+1 > 0 ).
  replace 0 with (0+0).
  apply Rplus_ge_gt_compat.
  apply Rle_ge.
  apply pow2_ge_0.
  auto with real.
  ring.
  auto with real.
Qed.

Lemma unique_arg2 : forall a1 b1 a2 b2 : R , 0>b1 -> 0>b2 -> a1/b1 = a2/b2 -> a1*a1+b1*b1 = a2*a2+b2*b2 -> a1=a2 /\ b1=b2.
Proof.
  intros.
  assert ( a1 = a2 /\ -b1 = -b2 ).
  apply unique_arg.
  auto with real.
  auto with real.
  replace ( a1 / - b1 ) with ( - (a1 / b1) ) ; [ idtac | field ].
  replace ( a2 / - b2 ) with ( - (a2 / b2) ) ; [ idtac | field ].
  rewrite H1.
  auto.
  auto with real.
  auto with real.
  ring_simplify.
  ring_simplify in H2.
  auto.
  destruct H3.
  assert( b1 = b2 ).
  replace b1 with ( - - b1 ) ; [ idtac | ring ].
  rewrite H4.
  ring.
  auto with real.
Qed.

Lemma atan_bound_help : forall a b : R , a<0 -> b < 0 -> 0<atan(a/b)<PI/2.
Proof.
  intros.
  assert ( 0 < - a / (-b) ).
  apply Rdiv_lt_0_compat.
  auto with real.
  auto with real.
  replace ( - a / - b ) with ( a / b ) in H1 ; [ idtac | field ].
  split.
  replace 0 with (atan 0).
  apply atan_increasing.
  auto.
  apply atan_0.
  apply atan_bound.
  auto with real.
Qed.

Lemma unique_arg2c : forall a1 b1 a2 b2 : R , 0>b1 -> 0>b2 -> a1/b1 = a2/b2 -> a1*a1+b1*b1 = a2*a2+b2*b2 -> ( a1 , b1 ) = (a2 , b2).
Proof.
  intros.
  assert(a1=a2 /\ b1=b2).
  apply unique_arg2.
  auto.
  auto.
  auto.
  auto.
  destruct H3.
  apply injective_projections.
  auto.
  auto.
Qed.

Lemma pow2_gt_0 : forall x : R , 0 <> x -> 0 < x^2.
Proof.
  intros.
  assert ( 0 <= x ^ 2 ).
  apply pow2_ge_0.
  case H0.
  auto.
  intros.
  elim H.
  assert ( sqrt 0 = sqrt ( x^2 ) ).
  rewrite H1.
  auto.
  rewrite sqrt_0 in H2.
  assert ( {x < 0} + {x = 0} + {x > 0} ).
  apply total_order_T.
  destruct H3.
  destruct s.
  assert ( 0 <= -x ).
  auto with real.
  replace (x^2) with ( (-x)^2 ) in H2.
  replace (sqrt ((- x) ^ 2)) with (-x) in H2.
  apply Ropp_eq_compat in H2.
  ring_simplify in H2.
  auto with real.
  apply eq_sym.
  apply sqrt_pow2.
  auto.
  ring.
  auto.
  replace (sqrt (x ^ 2)) with (x) in H2.
  auto.
  apply eq_sym.
  apply sqrt_pow2.
  auto with real.
Qed. 

Lemma tanminuspi : forall x : R , cos x <> 0 -> tan ( x - PI ) = tan (x).
Proof.
  intros.
  unfold tan.
  rewrite <- sin_period with ( k:=1%nat ).
  rewrite <- cos_period with ( k:=1%nat ).
  replace (x - PI + 2 * INR 1 * PI ) with ( x + PI ).
  rewrite neg_sin.
  rewrite neg_cos.
  field.
  auto.
  replace ( INR 1 ) with 1.
  ring.
  unfold INR.
  auto.
Qed.

Lemma sin2c1 : forall x : R , cos x * cos x + sin x * sin x = 1.
Proof.
  intros.
  rewrite <- sin2_cos2 with (x:=x).
  rewrite ! Rsqr_pow2.
  ring.
Qed.

Lemma cosabs : forall x : R , cos x = cos (Rabs x).
Proof.
  intros.
  assert (  {x < 0} + { x = 0} + {x > 0} )%R.
  apply total_order_T.
  destruct H.
  destruct s.
  rewrite Rabs_left.
  apply eq_sym.
  apply cos_neg.
  auto.
  rewrite e.
  rewrite Rabs_right.
  auto.
  auto with real.
  rewrite Rabs_right.
  auto.
  apply Rgt_ge.
  auto with real.
Qed.

Lemma coseq : forall x y : R , (-PI < x <= PI)%R -> (-PI < y <= PI)%R -> cos x = cos y -> Rabs x = Rabs y.
Proof.
  intros.
  rewrite cosabs in H1.
  apply eq_sym in H1.
  rewrite cosabs in H1.
  assert ( Rabs x <= PI ) as RxPi.
  apply Rabs_le.
  destruct H.
  split.
  apply Rlt_le.
  auto.
  auto.
  assert ( Rabs y <= PI ) as RyPi.
  apply Rabs_le.
  destruct H0.
  split.
  apply Rlt_le.
  auto.
  auto.
  apply Peirce.
  intros.
  apply Rdichotomy in H2.
  assert ( cos (Rabs y) <> cos (Rabs x) ).
  case H2.
  intros.
  assert ( cos (Rabs y) < cos (Rabs x) ).
  apply cos_decreasing_1.
  apply Rabs_pos.
  auto.
  apply Rabs_pos.
  auto.
  auto.
  auto with real.
  intros.
  assert ( cos (Rabs y) > cos (Rabs x) ).
  apply cos_decreasing_1.
  apply Rabs_pos.
  auto.
  apply Rabs_pos.
  auto.
  auto.
  auto with real.
  contradiction.
Qed.

Lemma Rabsposneg : forall x y : R , Rabs x = Rabs y -> x = y \/ x = - y.
Proof.
  intros.
  assert (  {x < 0} + { x = 0} + {x > 0} )%R.
  apply total_order_T.
  destruct H0.
  destruct s.
  rewrite Rabs_left in H.
  assert (  {y < 0} + { y = 0} + {y > 0} )%R.
  apply total_order_T.
  destruct H0.
  destruct s.
  rewrite Rabs_left in H.
  left ; ring [ H ].
  auto.
  rewrite Rabs_right in H.
  right ; ring [ H ].
  auto with real.
  rewrite Rabs_right in H.
  right ; ring [ H ].
  apply Rgt_ge.
  auto with real.
  auto.
  left.
  Search ( Rabs _ = 0 ).
  rewrite e.
  rewrite e in H.
  rewrite Rabs_R0 in H.
  apply eq_sym.
  apply Peirce.
  intros.
  apply Rabs_no_R0 in H0.
  apply eq_sym in H.
  contradiction.
  rewrite Rabs_right in H.
  assert (  {y < 0} + { y = 0} + {y > 0} )%R.
  apply total_order_T.
  destruct H0.
  destruct s.
  rewrite Rabs_left in H.
  right ; ring [ H ].
  auto.
  rewrite Rabs_right in H.
  left ; ring [ H ].
  auto with real.
  rewrite Rabs_right in H.
  left ; ring [ H ].
  apply Rgt_ge.
  auto with real.
  apply Rgt_ge.
  auto.
Qed.

Lemma PIlt2PI : PI < 2*PI.
Proof.
  replace PI with ( 1 * PI ) ; [ idtac | ring ].
  rewrite <- Rmult_assoc.
  apply Rmult_lt_compat_r.
  apply PI_RGT_0.
  ring_simplify.
  auto with real.
Qed.

Lemma cossineq : forall x y : R , (-PI < x <= PI)%R -> (-PI < y <= PI)%R -> sin x = sin y -> cos x = cos y -> x=y.
Proof.
  intros.
  assert ( x = y \/ x = - y ).
  apply Rabsposneg.
  apply coseq.
  auto.
  auto.
  auto.
  case H3.
  auto.
  intros.
  rewrite H4 in H1.
  rewrite sin_neg in H1.
  apply Rplus_eq_compat_l with (r:=sin y )in H1.
  ring_simplify in H1.
  apply eq_sym in H1.
  replace 0 with (2*0) in H1.
  apply Rmult_eq_reg_l in H1.
  assert ( sin x = 0 ).
  rewrite H4.
  rewrite sin_neg.
  ring [ H1 ].
  assert (  {y < 0} + { y = 0} + {y > 0} )%R.
  apply total_order_T.
  destruct H6.
  destruct s.
  assert ( 0 < x ).
  rewrite H4.
  auto with real.
  apply sin_eq_O_2PI_0 in H5.
  case H5.
  intros.
  assert ( x <> 0 ).
  auto with real.
  contradiction.
  intros.
  case H7.
  intros.
  rewrite H8 in H4.
  assert ( y = - PI ).
  ring [ H4 ].
  assert ( y <> - PI ).
  destruct H0.
  auto with real.
  contradiction.
  intros.
  rewrite H8 in H.
  destruct H.
  replace PI with ( 1 * PI ) in H9 ; [ idtac | ring ].
  rewrite <- Rmult_assoc in H9.
  apply Rmult_le_reg_r in H9.
  ring_simplify in H9.
  assert ( ~ (2<=1) ).
  auto with real.
  contradiction.
  apply PI_RGT_0.
  apply Rlt_le.
  auto.
  apply Rle_trans with (r2 := PI ).
  destruct H.
  auto.
  apply Rlt_le.
  apply PIlt2PI.
  rewrite e in H4.
  rewrite e.
  rewrite H4.
  ring.
  apply sin_eq_O_2PI_0 in H1.
  case H1.
  intros.
  rewrite H6.
  rewrite H4.
  ring [ H6 ].
  intros.
  case H6.
  intros.
  rewrite H7 in H4.
  assert ( - PI <> x ).
  destruct H.
  auto with real.
  apply eq_sym in H4.
  contradiction.
  intros.
  rewrite H7 in H0.
  destruct H0.
  replace PI with ( 1 * PI ) in H8 ; [ idtac | ring ].
  rewrite <- Rmult_assoc in H8.
  apply Rmult_le_reg_r in H8.
  ring_simplify in H8.
  assert ( ~ (2<=1) ).
  auto with real.
  contradiction.
  apply PI_RGT_0.
  apply Rlt_le.
  auto.
  apply Rle_trans with (r2 := PI ).
  destruct H0.
  auto.
  apply Rlt_le.
  apply PIlt2PI.
  auto.
  ring.
Qed.


Local Close Scope R_scope.



Lemma Cabs_bigger_0 : forall z : Complex , ( 0 <> real_p z \/ 0 <> imag_p z -> 0 < Cabs z )%R.
Proof.
  intros.
  unfold Cabs.
  apply sqrt_lt_R0.
  ring_simplify.
  assert ( 0 <= real_p z ^ 2 )%R.
  apply pow2_ge_0.
  assert ( 0 <= imag_p z ^ 2 )%R.
  apply pow2_ge_0.
  case H.
  intros.
  assert ( 0 < real_p z ^ 2 )%R.
  apply pow2_gt_0.
  auto.
  replace 0%R with (0+0)%R ; [idtac | ring ].
  apply Rplus_lt_le_compat.
  auto.
  auto.
  intros.
  assert ( 0 < imag_p z ^ 2 )%R.
  apply pow2_gt_0.
  auto.
  replace 0%R with (0+0)%R ; [idtac | ring ].
  apply Rplus_le_lt_compat.
  auto.
  auto.
Qed.

Lemma Cabs0z0 : forall z : Complex , Cabs z = 0%R -> z=C0.
Proof.
  intros.
  apply Peirce.
  intros.
  assert ( 0 <> real_p z \/ 0 <> imag_p z )%R.
  apply Peirce.
  intros.
  apply not_or_and in H1.
  destruct H1.
  apply NNPP in H1.
  apply NNPP in H2.
  elim H0.
  apply injective_projections.
  simpl.
  auto.
  auto.
  apply Cabs_bigger_0 in H1.
  assert ( Cabs z <> 0%R ).
  auto with real.
  contradiction.
Qed.

Definition preCarg ( z : Complex ) : {x : R | (-PI < x <= PI)%R /\ z = (Cabs z*cos x,Cabs z*sin x)%R }.
Proof.
  assert (  {real_p z < 0} + {real_p z = 0} + {real_p z > 0} )%R.
  apply total_order_T.
  assert (  {imag_p z < 0} + {imag_p z = 0} + {imag_p z > 0} )%R.
  apply total_order_T.
  destruct H.
  destruct s.
  destruct H0.
  destruct s.
  exists ( atan ( imag_p z / real_p z ) - PI )%R.
  split.
  split.
  replace (- PI)%R with ( 0 - PI )%R ; [ idtac | ring].
  apply Rplus_lt_compat_r.
  apply atan_bound_help.
  auto.
  auto.
  apply Rminus_le.
  replace (atan (imag_p z / real_p z) -PI-PI)%R with ( atan (imag_p z / real_p z)  -PI*2 )%R ; [ idtac | ring ].
  apply Rle_minus.
  apply Rlt_le.
  apply Rlt_trans with (r2:=(PI/2)%R).
  apply atan_bound.
  apply Rlt_trans with (r2:=(PI)%R).
  apply PI2_Rlt_PI.
  replace (PI) with (PI*1)%R ; [idtac|ring].
  rewrite Rmult_assoc.
  apply Rmult_lt_compat_l with (r:=PI).
  apply PI_RGT_0.
  replace (1*2)%R with (2)%R ; [idtac|ring].
  auto with real.
  assert ( ( real_p z , imag_p z ) =
((Cabs z * cos (atan (imag_p z / real_p z) - PI))%R,
(Cabs z * sin (atan (imag_p z / real_p z) - PI))%R)).
  assert ( 0 < Cabs z)%R.
  apply Cabs_bigger_0.
  right.
  auto with real.
  apply unique_arg2c.
  auto with real.
  replace (0)%R with (Cabs z*0)%R ; [idtac | ring].
  apply Rmult_lt_compat_l.
  auto.
  admit.
  field_simplify.
  replace ( cos (atan (imag_p z / real_p z) - PI) /
 sin (atan (imag_p z / real_p z) - PI))%R with (1/tan(atan (imag_p z / real_p z) - PI) )%R.
  rewrite tanminuspi.
  rewrite atan_right_inv.
  field.
  auto with real.
  admit.
  unfold tan.
  field.
  admit.
  split.
  admit.
  auto with real.
  auto with real.
  replace ( (Cabs z * cos (atan (imag_p z / real_p z) - PI) *
 (Cabs z * cos (atan (imag_p z / real_p z) - PI)) +
 Cabs z * sin (atan (imag_p z / real_p z) - PI) *
 (Cabs z * sin (atan (imag_p z / real_p z) - PI)))%R )
  with ( (Cabs z * Cabs z * (cos (atan (imag_p z / real_p z) - PI) *
  cos (atan (imag_p z / real_p z) - PI) +
  sin (atan (imag_p z / real_p z) - PI) 
 * sin (atan (imag_p z / real_p z) - PI)))%R ) ; [ idtac | ring ].
  rewrite sin2c1.
  unfold Cabs.
  rewrite sqrt_def.
  ring.
  apply Ra2b2pos.
  rewrite <- H.
  apply Cdecompose.
  (* other cases are similiar :) *)
Admitted.


Definition Carg x := let (v, _) := preCarg x in v.

Lemma Carg_def : forall z : Complex , (-PI < Carg z <= PI)%R /\ z = (Cabs z*cos (Carg z),Cabs z*sin (Carg z))%R.
Proof.
  intros.
  unfold Carg.
  destruct preCarg as [m H1].
  auto.
Qed.

Lemma Carg_uniq : forall z : Complex , z <> C0 -> forall x : R , (-PI < x <= PI)%R /\ z = (Cabs z*cos (x),Cabs z*sin (x))%R -> x = Carg z.
Proof.
  intros.
  assert((-PI < Carg z <= PI)%R /\ z = (Cabs z*cos (Carg z),Cabs z*sin (Carg z))%R).
  apply Carg_def.
  destruct H0.
  destruct H1.
  assert ( Cabs z <> 0 )%R as Cabs0.
  unfold not.
  intros.
  elim H.
  apply Cabs0z0.
  auto.
  assert ( (Cabs z * cos x)%R = (Cabs z * cos (Carg z))%R).
  replace ( (Cabs z * cos x)%R ) with ( fst z ).
  rewrite H3.
  simpl.
  rewrite <- H3.
  auto.
  rewrite H2.
  simpl.
  rewrite <- H2.
  auto.
  apply Rmult_eq_reg_l in H4 ; [idtac | auto].
  assert ( (Cabs z * sin x)%R = (Cabs z * sin (Carg z))%R).
  replace ( (Cabs z * sin x)%R ) with ( snd z ).
  rewrite H3.
  simpl.
  rewrite <- H3.
  auto.
  rewrite H2.
  simpl.
  rewrite <- H2.
  auto.
  apply Rmult_eq_reg_l in H5 ; [idtac | auto].
  apply cossineq.
  auto.
  auto.
  auto.
  auto.
Qed.
