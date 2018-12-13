Require Import Complex Geobase Geoline GeoParallel Geoconstruct.

Lemma ExPointLinelt (a : Complex) ( l : Line ) : on_line a l -> exists b : Complex , (b < a)%C /\ on_line b l.
Proof.
  intros.
  
Admitted.

Lemma ExPointLinegt (a : Complex) ( l : Line ) : on_line a l -> exists b : Complex , (a < b)%C /\ on_line b l.
Proof.
  intros.
  
Admitted.


Lemma argnegneg : forall x : R , x<>(-PI)%R -> -^ (-^ x) = x.
Proof.
  intros.
  unfold argneg.
  destruct (Real_eq_dec x PI).
  destruct (Real_eq_dec PI PI).
  auto.
  contradiction.
  destruct ( Real_eq_dec (- x) PI ).
  elim H.
  ring [e].
  ring.
Qed.

Lemma DAngleneg : forall a b c : Complex , DAngle a b c = -^ DAngle c b a.
Proof.
  intros.
  unfold DAngle.
  unfold argminus.
  rewrite argminusfactor.
  rewrite argnegneg.
  apply argplus_comm.
  assert ( Carg ( a-b)%C > - PI )%R.
  apply ( Carg_def ( a - b )%C ).
  auto with real.
  apply Carg_def.
  apply argnegineq.
  apply Carg_def.
Qed.

Lemma Parallel_angle2 : forall l1 l2 : Line,
       l1 ||| l2 ->
       forall a b c d : Complex,
       b <> c ->
       (a < b)%C ->
       (c < d)%C ->
       on_line a l1 ->
       on_line b l1 ->
       on_line c l2 -> on_line d l2 -> DAngle c b a = DAngle b c d.
Proof.
  intros.
  rewrite DAngleneg.
  rewrite DAngleneg with ( a:=b) (b:=c) (c:=d).
  f_equal.
  apply Parallel_angle with (l1:=l1) (l2:=l2).
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
Qed.

Lemma DAngleplus : forall a b c d : Complex , a <> b -> c<>b -> d<>b -> DAngle a b c +^ DAngle c b d = DAngle a b d.
Proof.
  intros.
  assert ( forall x y : Complex , x <> y -> x - y <> C0 )%C.
  intros.
  intros fk.
  apply Ceq_side in fk.
  elim H2.
  auto.
  apply H2 in H.
  apply H2 in H0.
  apply H2 in H1. 
  unfold DAngle.
  rewrite ! argminusdiv.
  rewrite Cmultarg.
  f_equal.
  field.
  auto.
  apply C0mult.
  auto.
  apply CinvnC0.
  auto.
  apply C0mult.
  auto.
  apply CinvnC0.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
Qed. 

Lemma DAngleineq : forall a b c : Complex , (-PI<DAngle a b c<=PI)%R.
Proof.
  intros.
  unfold DAngle.
  apply argminusineq.
  apply Carg_def.
  apply Carg_def.
Qed.

Lemma TrianglePIHelp : forall a b c : Complex , ( b < c )%C -> tri_is_simple (a,b,c) -> DAngle a b c +^ DAngle b c a +^ DAngle c a b = PI.
Proof.
  intros.
  remember (Line2P b c) as l1.
  remember (LineParP a l1) as l2.
  elim (ExPointLinelt a l2).
  intros d dH.
  elim (ExPointLinegt a l2).
  intros e eH.
  rewrite <- Parallel_angle2 with (l1:=l2) (l2:=l1) (a:=d) ( b:=a ) ( c:=b ) (d := c).
  rewrite argplus_comm.
  rewrite argplus_assoc.
  rewrite DAngleplus.
  rewrite Parallel_angle with (l1:=l1) (l2:=l2) (a:=b) ( b:=c ) ( c:=a ) (d := e).
  rewrite argplus_comm.
  rewrite DAngleplus.
  rewrite DAngleneg.
  rewrite line_DAnglePI with (l:=l2).
  unfold argneg.
  destruct ( Real_eq_dec PI PI ).
  auto.
  contradiction.
  rewrite Heql2; apply LineParP_def.
  destruct dH; auto.
  destruct eH; auto.
  destruct dH; auto.
  destruct eH; auto.
  apply not_eq_sym.
  apply Cineq_eq.
  destruct eH; auto.
  destruct H0.
  unfold vA, vB in H1.
  simpl in H1.
  destruct H1; auto.
  apply Cineq_eq.
  destruct dH; auto.
  rewrite Heql2.
  unfold Is_parallel.
  unfold LineParP.
  auto.
  destruct H0.
  unfold vA, vB in H1.
  simpl in H1.
  destruct H1; auto.
  auto.
  destruct eH; auto.
  rewrite Heql1; apply Line2P_def.
  rewrite Heql1; apply Line2P_def.
  rewrite Heql2; apply LineParP_def.
  destruct eH; auto.
  destruct H0.
  unfold vA, vB in H1.
  simpl in H1.
  destruct H1; auto.
  destruct H0.
  unfold vA, vB in H1.
  simpl in H1.
  destruct H1; auto.
  apply Cineq_eq;destruct dH; auto.
  apply DAngleineq.
  apply DAngleineq.
  apply DAngleineq.
  rewrite Heql2.
  unfold Is_parallel.
  unfold LineParP.
  auto.
  destruct H0.
  unfold vA, vB in H1.
  simpl in H1.
  destruct H1; auto.
  destruct dH; auto.
  auto.
  destruct dH; auto.
  rewrite Heql2; apply LineParP_def.
  rewrite Heql1; apply Line2P_def.
  rewrite Heql1; apply Line2P_def.
  rewrite Heql2; apply LineParP_def.
  rewrite Heql2; apply LineParP_def.
Qed.

Lemma TrianglePI : forall a b c : Complex , tri_is_simple (a,b,c) -> DAngle a b c +^ DAngle b c a +^ DAngle c a b = PI.
Proof.
  intros.
  assert ( b <> c ).
  unfold tri_is_simple in H.
  unfold vB,vC in H.
  simpl in H.
  apply H.
  destruct (Total_orderC b c).
  destruct s.
  apply TrianglePIHelp.
  auto.
  auto.
  contradiction.
  apply TrianglePIHelp with (a:=a) in c0.
  rewrite DAngleneg.
  rewrite DAngleneg with ( a := b ) (b:=c) (c:=a).
  rewrite <- argminusfactor.
  rewrite DAngleneg with ( a := c ) (b:=a) (c:=b).
  rewrite <- argminusfactor.
  rewrite argplus_comm with (x:=DAngle c b a) (y:=DAngle a c b).
  rewrite c0.
  unfold argneg.
  destruct (Real_eq_dec PI PI).
  auto.
  contradiction.
  apply argplusineq.
  apply DAngleineq.
  apply DAngleineq.
  apply DAngleineq.
  apply DAngleineq.
  apply DAngleineq.
  unfold tri_is_simple in H.
  unfold tri_is_simple.
  unfold vA,vB,vC.
  simpl.
  unfold vA,vB,vC in H.
  simpl in H.
  destruct H.
  destruct H1.
  split.
  auto.
  split.
  auto.
  auto.
Qed.

Local Open Scope R_scope.

Lemma SSSTriSim : forall a b c x y z : Complex , tri_is_simple (a,b,c) -> tri_is_simple (x,y,z) -> Cabs(a-b)%C/Cabs(x-y)%C = Cabs(a-c)%C/Cabs(x-z)%C -> Cabs(a-b)%C/Cabs(x-y)%C = Cabs(b-c)%C/Cabs(y-z)%C -> (a,b,c)~~~(x,y,z).
Proof.
  intros.
  unfold TriSim.
  split ; auto.
  split ; auto.
  rewrite ! sAB_def.
  rewrite ! sAC_def.
  rewrite ! sBC_def.
  split; auto.
  rewrite <- H1.
  auto.
Qed. 

Lemma SAScosruleHelp : forall a b c d x : R , d <>0 -> b <> 0 -> a / b = c / d -> a/b=sqrt(a ^ 2 + c ^2 + x * a * c)/(b ^2 + d ^ 2 + x * b * d).
Proof.
  intros.
  remember (a / b)%R as t.
  assert ( t * b = a ).
  rewrite Heqt.
  field.
  auto.
  assert ( t * d = c ).
  rewrite H1.
  field.
  auto.
  rewrite <- H2 , <- H3.
  
Admitted.

Lemma Cminusarg : forall a b : Complex , (b-a<>C0)%C -> Carg ( a - b )%C = Carg ( b - a )%C +^ PI.
Proof.
  intros.
  replace PI with (Carg (-C1) )%C.
  rewrite Cmultarg.
  f_equal.
  ring.
  auto.
  apply Cneq0.
  rewrite Cabs_neg.
  unfold Cabs.
  simpl.
  replace (1 * 1 + 0 * 0) with 1;[idtac | ring ].
  rewrite sqrt_1.
  auto with real.
  unfold C1.
  simpl.
  apply eq_sym.
  apply Carg_uniq.
  apply Cneq0.
  unfold Cabs.
  simpl.
  replace (- (1) * - (1) + -0 * -0) with 1;[idtac | ring ].
  rewrite sqrt_1.
  auto with real.
  split.
  apply argstan_PI.
  rewrite cos_PI.
  rewrite sin_PI.
  replace (Cabs (- (1), - 0)) with 1.
  apply injective_projections.
  simpl.
  ring.
  simpl.
  ring.
  unfold Cabs.
  simpl.
  replace (- (1) * - (1) + -0 * -0) with 1;[idtac | ring ].
  rewrite sqrt_1.
  auto with real.
Qed.

Lemma tri_is_simple_jay : forall a b c : Complex , tri_is_simple (a,b,c) -> tri_is_simple (a,c,b) /\ tri_is_simple (c,a,b).
Proof.
  intros.
  unfold tri_is_simple in H.
  unfold vA,vB,vC in H.
  simpl in H.
  destruct H.
  destruct H0.
  split.
  unfold tri_is_simple.
  unfold vA,vB,vC.
  simpl.
  auto.
  unfold tri_is_simple.
  unfold vA,vB,vC.
  simpl.
  auto.
Qed.

Lemma Anglerot: forall a b c : Complex , tri_is_simple (a,b,c) -> Angle a b c = Angle c b a.
Proof.
  intros.
  unfold Angle.
  rewrite DAngleneg.
  assert ( forall x : R , Rabs ( -^ x ) = Rabs x ).
  intros.
  unfold argneg.
  destruct (Real_eq_dec x PI).
  rewrite e.
  auto.
  apply Rabs_Ropp.
  apply H0.
Qed.

Lemma cosAngle : forall a b c : Complex , tri_is_simple (a,b,c) -> cos ( Carg ( a - b )%C - Carg ( b - c)%C ) = - cos ( Angle a b c ).
Proof.
  intros.
  rewrite <- argminuscos.
  rewrite Cminusarg.
  unfold argminus.
  rewrite argplus_comm.
  rewrite argplus_assoc.
  rewrite argpluscos.
  rewrite argplus_comm.
  rewrite neg_cos.
  f_equal.
  rewrite Anglerot.
  unfold Angle.
  rewrite <- cosabs.
  unfold DAngle.
  rewrite ! argpluscos.
  rewrite ! cos_plus.
  rewrite ! argminuscos.
  rewrite ! cos_minus.
  rewrite Cminusarg.
  rewrite Cminusarg with (a:=c) (b:=b).
  rewrite ! argpluscos.
  rewrite ! argplussin.
  rewrite ! neg_cos.
  rewrite ! neg_sin.
  rewrite argnegcos.
  rewrite cos_neg.
  rewrite argnegsin.
  rewrite sin_neg.
  ring.
  apply Cneq0.
  apply tri_is_simple_def in H.
  unfold sAB,sAC,sBC in H.
  unfold vA,vB,vC in H.
  simpl in H.
  destruct H.
  destruct H0.
  auto.
  apply Cneq0.
  apply tri_is_simple_def in H.
  unfold sAB,sAC,sBC in H.
  unfold vA,vB,vC in H.
  simpl in H.
  destruct H.
  destruct H0.
  auto.
  auto.
  apply argnegineq.
  apply Carg_def.
  apply Carg_def.
  apply argstan_PI.
  apply Cneq0.
  rewrite Cabs_minus.
  apply tri_is_simple_def in H.
  unfold sAB,sAC,sBC in H.
  unfold vA,vB,vC in H.
  simpl in H.
  destruct H.
  destruct H0.
  auto.
Qed.

Lemma Cosine_rule_Angle : forall x y z : Complex , tri_is_simple (x,y,z) -> sqrt ( Cabs (x - y)%C ^ 2 + Cabs (y - z)%C ^ 2 +
-2 * cos (Angle x y z) * Cabs (x - y)%C * Cabs (y - z)%C ) = Cabs ( x - z )%C.
Proof.
  intros.
  replace (x-z)%C with ((x-y)+(y-z))%C ; [ idtac | ring ].
  rewrite ! Cosine_rule.
  rewrite ! cosAngle.
  f_equal.
  ring.
  auto.
Qed.

Lemma tri_is_simple_def2 : forall a b c : Complex , tri_is_simple (a,b,c) -> a <> b /\ a <> c /\ b <> c.
Proof.
  intros.
  unfold tri_is_simple in H.
  unfold vA,vB,vC in H.
  simpl in H.
  auto.
Qed.

Lemma SASTriSim : forall a b c x y z : Complex , tri_is_simple (a,b,c) -> tri_is_simple (x,y,z) -> Cabs(a-b)%C/Cabs(x-y)%C = Cabs(b-c)%C/Cabs(y-z)%C -> Angle a b c = Angle x y z -> (a,b,c)~~~(x,y,z).
Proof.
  intros.
  apply SSSTriSim.
  auto.
  auto.
  replace (a-c)%C with ((a-b)+(b-c))%C ; [ idtac | ring ].
  replace (x-z)%C with ((x-y)+(y-z))%C ; [ idtac | ring ].
  rewrite ! Cosine_rule.
  rewrite ! cosAngle.
  rewrite H2.
  replace ( 2 * Cabs (a - b)%C * Cabs (b - c)%C * - cos (Angle x y z)) 
  with ( (-2*cos (Angle x y z)) * Cabs (a - b)%C * Cabs (b - c)%C);[idtac|ring].
  replace ( 2 * Cabs (x - y)%C * Cabs (y - z)%C * - cos (Angle x y z)) 
  with ( (-2*cos (Angle x y z)) * Cabs (x - y)%C * Cabs (y - z)%C);[idtac|ring].
  rewrite <- sqrt_div_alt.
  remember (Cabs (a - b)%C / Cabs (x - y)%C) as t.
  apply eq_sym.
  apply sqrt_lem_1.
  left; apply Rdiv_lt_0_compat.
  apply sqrt_lt_0_alt.
  rewrite sqrt_0.
  rewrite <- H2.
  rewrite Cosine_rule_Angle.
  apply Cneq0abs.
  intros fk.
  apply Ceq_side in fk.
  apply tri_is_simple_def2 in H.
  destruct H.
  destruct H3.
  apply H3;auto.
  auto.
  apply sqrt_lt_0_alt.
  rewrite sqrt_0.
  rewrite Cosine_rule_Angle.
  apply Cneq0abs.
  intros fk.
  apply Ceq_side in fk.
  apply tri_is_simple_def2 in H0.
  destruct H0.
  destruct H3.
  apply H3;auto.
  auto.
  rewrite Heqt.
  left; apply Rdiv_lt_0_compat.
  apply Cneq0abs.
  intros fk.
  apply Ceq_side in fk.
  apply tri_is_simple_def2 in H.
  destruct H.
  destruct H3.
  apply H;auto.
  auto.
  apply Cneq0abs.
  intros fk.
  apply Ceq_side in fk.
  apply tri_is_simple_def2 in H0.
  destruct H0.
  destruct H3.
  apply H0;auto.
  assert ( t * Cabs(x-y)%C = Cabs(a-b)%C ).
  rewrite Heqt.
  field.
  assert (Cabs(x-y)%C>0).
  apply Cneq0abs.
  intros fk.
  apply Ceq_side in fk.
  apply tri_is_simple_def2 in H0.
  destruct H0.
  destruct H3.
  apply H0;auto.
  auto with real.
  assert ( t * Cabs(y-z)%C = Cabs(b-c)%C ).
  rewrite H1.
  field.
  assert (Cabs(y-z)%C>0).
  apply Cneq0abs.
  intros fk.
  apply Ceq_side in fk.
  apply tri_is_simple_def2 in H0.
  destruct H0.
  destruct H4.
  apply H5;auto.
  auto with real.
  rewrite <- H3.
  rewrite <- H4.
  field.
  intros fk.
  assert ( sqrt 0 = 0 ).
  apply sqrt_0.
  rewrite <- fk in H5.
  rewrite Cosine_rule_Angle in H5.
  rewrite fk in H5.
  apply tri_is_simple_def2 in H0.
  destruct H0.
  destruct H6.
  elim H6.
  apply Ceq_side.
  apply Cabs0z0.
  auto.
  auto.
  apply sqrt_lt_0_alt.
  rewrite sqrt_0.
  rewrite Cosine_rule_Angle.
  apply Cneq0abs.
  intros fk.
  apply Ceq_side in fk.
  apply tri_is_simple_def2 in H0.
  destruct H0.
  destruct H3.
  apply H3;auto.
  auto.
  auto.
  auto.
  auto.
Qed. 


