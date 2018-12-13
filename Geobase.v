Require Import Complex.

Local Open Scope R_scope.


Local Close Scope R_scope.

Definition DAngle ( x : Complex ) ( o : Complex ) ( y : Complex ) := Carg ( x - o )%C -^ Carg ( y - o )%C.

Definition Angle ( x : Complex ) ( o : Complex ) ( y : Complex ) := Rabs ( DAngle x o y ).

Definition Triangle := (Complex * Complex * Complex)%type.

Definition vA ( t : Triangle ) := fst ( fst ( t)).
Definition vB ( t : Triangle ) := snd ( fst ( t)).
Definition vC ( t : Triangle ) := (snd ( t)).

Definition tri_is_simple ( t : Triangle ) := ( vA t <> vB t ) /\ ( vA t <> vC t ) /\ ( vB t <> vC t ).

Lemma tri_is_simple_plus : forall a b c d : Complex , tri_is_simple ( a, b, c ) -> tri_is_simple ( (a+d), (b+d), (c+d) )%C.
Proof.
  intros.
  unfold tri_is_simple in H.
  unfold vA in H.
  unfold vB in H.
  simpl in H.
  unfold tri_is_simple.
  unfold vA.
  unfold vB.
  simpl.
  destruct H as [sim1 sim].
  destruct sim as [sim2 sim3].
  split.
  unfold not.
  intros.
  apply Ceq_side2 in H.
  ring_simplify in H.
  apply Ceq_side in H.
  contradiction.
  split.
  unfold not.
  intros.
  apply Ceq_side2 in H.
  ring_simplify in H.
  apply Ceq_side in H.
  contradiction.
  unfold not.
  intros.
  apply Ceq_side2 in H.
  ring_simplify in H.
  apply Ceq_side in H.
  contradiction.
Qed.

Definition sAB ( x : Triangle ) := Cabs ( vA x - vB x )%C.
Definition sAC ( x : Triangle ) := Cabs ( vA x - vC x )%C.
Definition sBC ( x : Triangle ) := Cabs ( vB x - vC x )%C.


Definition TriSim ( x y : Triangle ) := ((tri_is_simple x) /\ (tri_is_simple y) /\ ( sAB x / sAB y = sAC x / sAC y )%R /\ ( sAC x / sAC y ) = (sBC x / sBC y ))%R .

Infix " ~~~ " := TriSim ( at level 20 ). 

Lemma tri_is_simple_def : forall x : Triangle , tri_is_simple x -> ( sAB x <> 0 /\ sAC x <> 0 /\ sBC x <> 0 )%R.
Proof.
  intros.
  unfold tri_is_simple in H.
  destruct H as [ ts1 H ].
  destruct H as [ ts2 H ].
  split.
  unfold not.
  intros.
  unfold sAB in H0.
  apply Cabs0z0 in H0.
  apply Ceq_side in H0.
  contradiction.
  split.
  unfold not.
  intros.
  unfold sAC in H0.
  apply Cabs0z0 in H0.
  apply Ceq_side in H0.
  contradiction.
  unfold not.
  intros.
  unfold sBC in H0.
  apply Cabs0z0 in H0.
  apply Ceq_side in H0.
  contradiction.
Qed.

Lemma vA_def : forall a b c : Complex , vA ( a,b,c ) = a.
Proof.
  intros.
  auto.
Qed.
Lemma vB_def : forall a b c : Complex , vB ( a,b,c ) = b.
Proof.
  intros.
  auto.
Qed.
Lemma vC_def : forall a b c : Complex , vC ( a,b,c ) = c.
Proof.
  intros.
  auto.
Qed.
Lemma sAB_def : forall a b c : Complex , sAB (a,b,c) = Cabs(a-b)%C.
Proof.
  intros.
  auto.
Qed.
Lemma sAC_def : forall a b c : Complex , sAC (a,b,c) = Cabs(a-c)%C.
Proof.
  intros.
  auto.
Qed.
Lemma sBC_def : forall a b c : Complex , sBC (a,b,c) = Cabs(b-c)%C.
Proof.
  intros.
  auto.
Qed.

Lemma Cabs_R : forall k : R , ( Cabs ( k , 0 ) = Rabs k )%R. 
Proof.
  intros.
  unfold Cabs.
  simpl.
  replace ( k * k + 0 * 0 )%R with ( k * k )%R ; [ idtac | ring ].
  replace ( k * k )%R with ( k² )%R.
  apply sqrt_Rsqr_abs.
  rewrite Rsqr_pow2.
  ring.
Qed.

Lemma Carg_R : forall k : R , ( 0 < k -> Carg ( k , 0 ) = 0 )%R. 
Proof.
  intros.
  apply eq_sym.
  apply Carg_uniq.
  unfold C0.
  unfold not.
  intros.
  assert ( k <> 0 )%R.
  auto with real.
  elim H1.
  replace k with ( fst (k, 0%R)%R ).
  rewrite H0.
  auto.
  auto.
  split.
  split.
  apply Ropp_lt_cancel.
  ring_simplify.
  apply PI_RGT_0.
  left.
  apply PI_RGT_0.
  rewrite cos_0.
  rewrite sin_0.
  rewrite Cabs_R.
  apply injective_projections.
  simpl.
  rewrite Rabs_right.
  ring.
  left.
  auto.
  simpl.
  ring.
Qed.

Lemma Cabs_neg : forall x : Complex , Cabs (- x)%C = Cabs ( x ).
Proof.
  intros.
  rewrite Cdecompose with ( z := x ).
  unfold Copp.
  unfold Cabs.
  simpl.
  assert (  (- real_p x * - real_p x + - imag_p x * - imag_p x) =
(real_p x * real_p x + imag_p x * imag_p x) )%R.
  ring.
  rewrite H.
  auto.
Qed.

Lemma Cabs_minus : forall x y : Complex , Cabs ( x - y )%C = Cabs ( y - x )%C.
Proof.
  intros.
  replace (x-y)%C with (-(y-x))%C.
  apply Cabs_neg.
  ring.
Qed.

Lemma Carg_neg : forall x : Complex , x <> C0 -> Carg ( - x )%C = Carg x +^ PI .
Proof.
  intros x xnc0.
  replace ( - x )%C with ( x * (- C1) )%C ; [ idtac | ring ].
  rewrite <- Cmultarg.
  replace ( Carg ( - C1 ) )%C with PI. 
  auto.
  apply Carg_uniq.
  unfold not.
  intros.
  unfold C1 in H.
  unfold Copp in H.
  assert ( -1 <> 0 )%R.
  auto with real.
  elim H0.
  replace (-1)%R with ( fst ((- (1))%R, (- 0)%R)).
  rewrite H.
  auto.
  auto.
  split.
  split.
  replace PI with ( 1 * PI )%R ; [idtac|ring].
  rewrite Ropp_mult_distr_l.
  apply Rmult_lt_compat_r.
  apply PI_RGT_0.
  apply Rplus_lt_reg_r  with (r := (1)%R ).
  ring_simplify.
  auto with real.
  auto with real.
  rewrite cos_PI.
  rewrite Cabs_neg.
  rewrite sin_PI.
  replace (Cabs C1) with 1%R.
  unfold C1.
  unfold Copp.
  apply injective_projections.
  simpl.
  ring.
  simpl.
  ring.
  unfold C1.
  unfold Cabs.
  simpl.
  apply eq_sym.
  replace (1 * 1 + 0 * 0)%R with 1%R. 
  apply sqrt_1.
  ring.
  auto.
  unfold not.
  intros.
  unfold C1 in H.
  unfold Copp in H.
  assert ( -1 <> 0 )%R.
  auto with real.
  elim H0.
  replace (-1)%R with ( fst ((- (1))%R, (- 0)%R)).
  rewrite H.
  auto.
  auto.
Qed.

Lemma Cabs_sum_eq2 : forall a b c d : Complex , a <> C0 -> c <> C0 -> Cabs a = Cabs b -> Cabs c = Cabs d -> Cabs (a-c)%C = Cabs (b-d)%C -> Rabs ( Carg a -^ Carg c )%R = Rabs ( Carg b -^ Carg d )%R.
Proof.
  intros.
  unfold Cminus in H3.
  apply coseq.
  apply argminusineq.
  apply Carg_def.
  apply Carg_def.
  apply argminusineq.
  apply Carg_def.
  apply Carg_def.
  rewrite ! argminuscos.
  rewrite ! Cosine_rule in H3.
  apply sqrt_inj in H3.
  rewrite ! Cabs_neg in H3.
  rewrite <- H1 in H3.
  rewrite <- H2 in H3.
  apply Rminus_diag_eq in H3.
  ring_simplify in H3.
  apply Rminus_diag_uniq_sym in H3.
  apply Rmult_eq_reg_l in H3.
  rewrite ! cos_minus in H3.
  rewrite ! Carg_neg in H3.
  rewrite ! argpluscos in H3.
  rewrite ! argplussin in H3.
  rewrite ! neg_cos in H3.
  rewrite ! neg_sin in H3.
  replace ( (cos (Carg b) * - cos (Carg d) + sin (Carg b) * - sin (Carg d))%R ) with ( - cos (Carg b - Carg d) )%R in H3.
  replace ( (cos (Carg a) * - cos (Carg c) + sin (Carg a) * - sin (Carg c))%R ) with ( - cos (Carg a - Carg c) )%R in H3.
  ring [ H3 ].
  rewrite ! cos_minus.
  ring.
  rewrite ! cos_minus.
  ring.
  auto.
  unfold not.
  intros.
  elim H0.
  apply Cabs0z0.
  rewrite H2.
  rewrite H4.
  unfold C0.
  unfold Cabs.
  simpl.
  replace (0 * 0 + 0 * 0)%R with 0%R ; [ idtac | ring ].
  apply sqrt_0.
  unfold not.
  intros.
  apply Rmult_integral in H4.
  case H4.
  intros.
  apply Rmult_integral in H5.
  case H5.
  intros.
  assert ( 2 <> 0 )%R.
  auto with real.
  contradiction.
  intros.
  apply Cabs0z0 in H6.
  contradiction.
  intros.
  apply Cabs0z0 in H5.
  contradiction.
  apply Cosine_rule_pos.
  apply Cosine_rule_pos.
Qed.

Lemma Cneq0 : forall z : Complex , Cabs z <> 0%R -> z <> C0.
Proof.
  intros.
  unfold not.
  intros.
  elim H.
  rewrite H0.
  unfold C0.
  unfold Cabs.
  simpl.
  replace (0 * 0 + 0 * 0)%R with 0%R ; [ idtac | ring ].
  apply sqrt_0.
Qed.

Lemma Cneq0abs : forall z : Complex , z <> C0 -> (0 < Cabs z)%R.
Proof.
  intros.
  apply Cabs_bigger_0.
  apply Peirce.
  intros.
  apply not_or_and in H0.
  destruct H0.
  apply NNPP in H0.
  apply NNPP in H1.
  elim H.
  unfold C0.
  apply injective_projections.
  simpl.
  rewrite H0.
  auto.
  simpl.
  rewrite H1.
  auto.
Qed.

Lemma argplus0 : forall a : R , (-PI<a<=PI)%R -> 0%R +^ a = a.
Proof.
  intros.
  unfold argplus.
  replace (0 + a)%R with a ; [ idtac | ring ].
  destruct ( total_order_T a PI ).
  destruct ( total_order_T a (-PI) )%R.
  destruct H.
  destruct s0.
  assert ( ~ a < a )%R.
  auto with real.
  elim H1.
  apply Rlt_trans with (r2:=(-PI)%R).
  auto.
  auto.
  assert ( ~ -PI < a )%R.
  rewrite e.
  auto with real.
  elim H1.
  auto.
  auto.
  destruct H.
  assert ( ~ a > PI )%R.
  apply Rle_not_gt.
  auto.
  contradiction.
Qed.

Lemma TriSim_angle_c1 : forall a b c d : Complex , ( a , C0 , b ) ~~~ ( c , C0 , d ) -> Angle (a) (C0) (b) = Angle (c) (C0) (d).
Proof.
  intros.
  unfold Angle.
  unfold DAngle.
  replace ( a - C0 )%C with a ; [ idtac | ring ].
  replace ( b - C0 )%C with b ; [ idtac | ring ].
  replace ( c - C0 )%C with c ; [ idtac | ring ].
  replace ( d - C0 )%C with d ; [ idtac | ring ].
  unfold TriSim in H.
  destruct H as [ spab H ].
  destruct H as [ spcd H ].
  rewrite ! sAB_def in H.
  rewrite ! sAC_def in H.
  rewrite ! sBC_def in H.
  replace ( a - C0 )%C with a in H ; [ idtac | ring ].
  replace ( C0 - b )%C with (-b)%C in H; [ idtac | ring ].
  replace ( c - C0 )%C with c in H; [ idtac | ring ].
  replace ( C0 - d )%C with (-d)%C in H; [ idtac | ring ].
  remember ( (Cabs a / Cabs c)%R ) as k.
  destruct H as [ ke1 ke2 ].
  rewrite <- ke1 in ke2.
  assert ( 0 < k )%R.
  rewrite Heqk.
  apply Rdiv_lt_0_compat.
  apply Cneq0abs.
  apply Cneq0.
  replace a with (a - C0)%C ; [ idtac | ring ].
  rewrite <- sAB_def with (c:=b).
  apply tri_is_simple_def.
  auto.
  apply Cneq0abs.
  apply Cneq0.
  replace c with (c - C0)%C ; [ idtac | ring ].
  rewrite <- sAB_def with (c:=d).
  apply tri_is_simple_def.
  auto.
  replace ( Carg c ) with ( Carg ( (k,0)%R * c ) )%C.
  replace ( Carg d ) with ( Carg ( (k,0)%R * d ) )%C.
  apply Cabs_sum_eq2.
  apply Cneq0.
  replace a with (a - C0)%C ; [ idtac | ring ].
  rewrite <- sAB_def with (c:=b).
  apply tri_is_simple_def.
  auto.
  apply Cneq0.
  rewrite <- Cabs_neg.
  replace (-b)%C with (C0-b)%C ; [ idtac | ring ].
  rewrite <- sBC_def with (a:=a).
  apply tri_is_simple_def.
  auto.
  rewrite <- abs_mult.
  rewrite Cabs_R.
  rewrite Rabs_right.
  rewrite Heqk.
  field.
  replace c with (c - C0)%C ; [ idtac | ring ].
  rewrite <- sAB_def with (c:=d).
  apply tri_is_simple_def.
  auto.
  left.
  auto.
  rewrite <- abs_mult.
  rewrite Cabs_R.
  rewrite Rabs_right.
  rewrite ke2.
  rewrite ! Cabs_neg. 
  field.
  rewrite <- Cabs_neg.
  replace (-d)%C with (C0 - d)%C ; [ idtac | ring ].
  rewrite <- sBC_def with (a:=c).
  apply tri_is_simple_def.
  auto.
  left.
  auto.
  replace ((k, 0%R) * c - (k, 0%R) * d)%C with ((k, 0%R) * (c - d))%C ; [ idtac | ring ].
  rewrite <- abs_mult.
  rewrite Cabs_R.
  rewrite Rabs_right.
  rewrite ke1.
  field.
  rewrite <- sAC_def with (b:=C0).
  apply tri_is_simple_def.
  auto.
  left.
  auto.
  rewrite <- Cmultarg.
  rewrite Carg_R.
  rewrite argplus0.
  auto.
  apply Carg_def.
  auto.
  apply Cneq0.
  rewrite Cabs_R.
  rewrite Rabs_right.
  auto with real.
  left ; auto.
  apply Cneq0.
  rewrite <- Cabs_neg.
  replace (-d)%C with (C0 - d)%C ; [ idtac | ring ].
  rewrite <- sBC_def with (a:=c).
  apply tri_is_simple_def.
  auto.
  rewrite <- Cmultarg.
  rewrite Carg_R.
  rewrite argplus0.
  auto.
  apply Carg_def.
  auto.
  apply Cneq0.
  rewrite Cabs_R.
  rewrite Rabs_right.
  auto with real.
  left ; auto.
  apply Cneq0.
  replace c with (c - C0)%C ; [ idtac | ring ].
  rewrite <- sAB_def with (c:=d).
  apply tri_is_simple_def.
  auto.
Qed.

Lemma DAngle_plus_eq : forall a b c d : Complex , DAngle a b c = (DAngle (a+d) (b+d) (c+d))%C.
Proof.
  intros.
  unfold DAngle.
  replace (a + d - (b + d))%C with (a-b)%C ; [ idtac | ring].
  replace (c + d - (b + d))%C with (c-b)%C ; [ idtac | ring].
  auto.
Qed.

Lemma Angle_plus_eq : forall a b c d : Complex , Angle a b c = (Angle (a+d) (b+d) (c+d))%C.
Proof.
  intros.
  unfold Angle.
  rewrite <- DAngle_plus_eq.
  auto.
Qed.

Lemma TriSim_sym : forall x y : Triangle , x ~~~ y -> y ~~~ x.
Proof.
  unfold TriSim.
  intros.
  destruct H as [ spx H ].
  destruct H as [ spy H ].
  destruct H as [ kxy1 kxy2 ].
  split ; auto.
  split ; auto.
  split.
  replace (sAB y / sAB x)%R with ( 1 / (sAB x / sAB y ) )%R ; [ idtac | field ].
  rewrite kxy1.
  field.
  split.
  apply tri_is_simple_def ; auto.
  apply tri_is_simple_def ; auto.
  split.
  apply tri_is_simple_def ; auto.
  apply tri_is_simple_def ; auto.
  replace (sAC y / sAC x)%R with ( 1 / (sAC x / sAC y ) )%R ; [ idtac | field ].
  rewrite kxy2.
  field.
  split.
  apply tri_is_simple_def ; auto.
  apply tri_is_simple_def ; auto.
  split.
  apply tri_is_simple_def ; auto.
  apply tri_is_simple_def ; auto.
Qed.

Lemma TriSim_trans : forall x y z : Triangle , x ~~~ y -> y ~~~ z -> x ~~~ z.
Proof.
  unfold TriSim.
  intros.
  destruct H as [ spx H ].
  destruct H as [ spy H ].
  destruct H as [ kxy1 kxy2 ].
  apply TriSim_sym in H0.
  unfold TriSim in H0.
  destruct H0 as [ spy2 H ].
  destruct H as [ spz H ].
  destruct H as [ kyz1 kyz2 ].
  split.
  auto.
  split.
  auto.
  split.
  replace ( (sAB x / sAB z)%R ) with ( ((sAB x / sAB y) / (sAB z / sAB y ))%R ) ; [ idtac | field ].
  rewrite kxy1.
  rewrite kyz1.
  field.
  split.
  apply tri_is_simple_def ; auto.
  apply tri_is_simple_def ; auto.
  split.
  apply tri_is_simple_def ; auto.
  apply tri_is_simple_def ; auto.
  replace ( (sAC x / sAC z)%R ) with ( ((sAC x / sAC y) / (sAC z / sAC y ))%R ) ; [ idtac | field ].
  rewrite kxy2.
  rewrite kyz2.
  field.
  split.
  apply tri_is_simple_def ; auto.
  apply tri_is_simple_def ; auto.
  split.
  apply tri_is_simple_def ; auto.
  apply tri_is_simple_def ; auto.
Qed.

Lemma Triangle_def : forall x : Triangle , x = (vA x,vB x,vC x).
Proof.
  intros.
  apply injective_projections.
  simpl.
  apply injective_projections.
  auto.
  auto.
  auto.
Qed.

Lemma tri_is_simple_plus2 : forall x : Triangle , forall z : Complex , tri_is_simple x -> tri_is_simple ( vA x + z, vB x + z , vC x + z )%C. 
Proof.
  intros.
  apply tri_is_simple_plus.
  rewrite <- Triangle_def.
  auto.
Qed.

Lemma TriSim_plus : forall x : Triangle , forall z : Complex , tri_is_simple x -> x ~~~ ( vA x + z, vB x + z , vC x + z )%C.
Proof.
  intros.
  unfold TriSim.
  split ; auto.
  split.
  apply tri_is_simple_plus2.
  auto.
  rewrite sAB_def.
  rewrite sAC_def.
  rewrite sBC_def.
  unfold sAB.
  unfold sAC.
  unfold sBC.
  replace ( vA x + z - (vB x + z))%C with ( vA x - vB x )%C ; [ idtac | ring ].
  replace ( vA x + z - (vC x + z))%C with ( vA x - vC x )%C ; [ idtac | ring ].
  replace ( vB x + z - (vC x + z))%C with ( vB x - vC x )%C ; [ idtac | ring ].
  split.
  field.
  split.
  apply tri_is_simple_def ; auto.
  apply tri_is_simple_def ; auto.
  field.
  split.
  apply tri_is_simple_def ; auto.
  apply tri_is_simple_def ; auto.
Qed.

Lemma TriSim_angle : forall x y : Triangle , x ~~~ y -> Angle (vA x) (vB x) (vC x) = Angle (vA y) (vB y) (vC y).
Proof.
  intros.
  rewrite Angle_plus_eq with ( d := ( - vB x )%C ).
  apply eq_sym.
  rewrite Angle_plus_eq with ( d := ( - vB y )%C ).
  replace (vB y + - vB y)%C with C0 ; [ idtac | ring ].
  replace (vB x + - vB x)%C with C0 ; [ idtac | ring ].
  apply TriSim_angle_c1.
  apply TriSim_trans with ( y := y ).
  replace C0 with (vB y + - vB y)%C ; [ idtac | ring ].
  apply TriSim_sym.
  apply TriSim_plus.
  destruct H.
  destruct H0.
  auto.
  apply TriSim_trans with ( y := x ).
  apply TriSim_sym.
  auto.
  replace C0 with (vB x + - vB x)%C ; [ idtac | ring ].
  apply TriSim_plus.
  destruct H.
  auto.
Qed.

Lemma TriSim_angle2 : forall a b c x y z : Complex , ( a , b , c ) ~~~ ( x , y , z ) -> Angle a b c = Angle x y z.
Proof.
  intros.
  apply TriSim_angle in H.
  unfold vA in H;unfold vB in H;unfold vC in H.
  simpl in H.
  auto.
Qed.

Lemma tri_is_simple_rot : forall a b c : Complex , tri_is_simple (a,b,c) -> tri_is_simple (c,a,b).
Proof.
  intros.
  destruct H.
  destruct H0.
  split ; auto.
Qed.

Lemma TriSim_rot : forall a b c x y z : Complex , (a,b,c) ~~~ (x,y,z) -> (c,a,b) ~~~ (z,x,y).
Proof.
  intros.
  destruct H as [ spx H ].
  destruct H as [ spy H ].
  split.
  apply tri_is_simple_rot.
  auto.
  split.
  apply tri_is_simple_rot.
  auto.
  rewrite ! sAB_def.
  rewrite ! sAC_def.
  rewrite ! sBC_def.
  rewrite ! sAB_def in H.
  rewrite ! sAC_def in H.
  rewrite ! sBC_def in H.
  destruct H.
  split.
  auto.
  auto.
  rewrite Cabs_minus.
  rewrite Cabs_minus with ( x := z ) ( y := x ).
  rewrite Cabs_minus with ( x := c ) ( y := b ).
  rewrite Cabs_minus with ( x := z ) ( y := y ).
  auto.
  rewrite Cabs_minus.
  rewrite Cabs_minus with ( x := z ) ( y := y ).
  rewrite H.
  auto.
Qed.

Lemma TriSim_facts : forall a b c x y z : Complex , (a,b,c) ~~~ (x,y,z) -> Angle a b c = Angle x y z /\ Angle b c a = Angle y z x /\ Angle c a b = Angle z x y.
Proof.
  intros.
  split.
  apply TriSim_angle2 ; auto.
  split.
  apply TriSim_angle2.
  apply TriSim_rot.
  apply TriSim_rot.
  auto.
  apply TriSim_angle2.
  apply TriSim_rot.
  auto.
Qed.
