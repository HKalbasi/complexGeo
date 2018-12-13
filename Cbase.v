Require Export Reals Omega.
Require Export Classical_Prop.

Definition Complex : Set := R*R.

Delimit Scope C_scope with C.

Definition Cplus ( x y : Complex ) : Complex := match x, y with
                                | (a,b) , (c,d) => (a+c,b+d)%R 
                              end.

Definition Cmult ( x y : Complex ) : Complex := match x, y with
                                | (a,b) , (c,d) => (a*c-b*d,a*d+b*c)%R 
                              end.

Definition C0 : Complex := (0,0)%R.
Definition C1 : Complex := (1,0)%R.
Definition Ci : Complex := (0,1)%R.

Definition Copp ( x: Complex ) : Complex := match x with
                                | (a,b) => (-a,-b)%R 
                              end. 
Definition Cinv ( x: Complex ) : Complex := match x with
                                | (a,b) => (a/(a*a+b*b),-b/(a*a+b*b))%R 
                              end. 

Theorem Real_eq_dec : forall r1 r2 : R , ({ r1 = r2 } + { r1 <> r2 })%R.
Proof.
  
  intros.
  assert ({r1 < r2} + {r1 = r2} + {r1 > r2})%R.
  apply total_order_T.
  destruct H in H.
  destruct s.
  right.
Admitted.  


Definition Clt ( x y : Complex ) : Prop := match x, y with
                                | (a,b) , (c,d) => if (Real_eq_dec a c)%R then (b<d)%R else (a<c)%R 
                              end.


Infix "+" := Cplus : C_scope.
Infix "*" := Cmult : C_scope.
Notation "- x" := (Copp x) : C_scope.
Notation "/ x" := (Cinv x) : C_scope.


Infix "<" := Clt : C_scope.


Definition Cgt (r1 r2:Complex) : Prop := (r2 < r1)%C.

Definition Cle (r1 r2:Complex) : Prop := (r1 < r2 \/ r1 = r2)%C.

Definition Cge (r1 r2:Complex) : Prop := (Cgt r1 r2 \/ r1 = r2)%C.

Definition Cminus (r1 r2:Complex) : Complex := (r1 + - r2)%C.

Definition Cdiv (r1 r2:Complex) : Complex := (r1 * / r2)%C.


Infix "-" := Cminus : C_scope.
Infix "/" := Cdiv : C_scope.

Infix "<=" := Cle : C_scope.
Infix ">=" := Cge : C_scope.
Infix ">" := Cgt : C_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : C_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : C_scope.
Notation "x < y < z" := (x < y /\ y < z) : C_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : C_scope.

(* end Cdefinition *)

Definition real_p ( z: Complex ) := fst z.
Definition imag_p ( z: Complex ) := snd z.

Lemma Cdecompose : forall z : Complex , z = ( real_p z , imag_p z ).
Proof.
  intros.
  apply surjective_pairing.
Qed.

Lemma Cplus_decompose : forall z1 z2 : Complex , ( z1 + z2 )%C = ( real_p z1 + real_p z2 , imag_p z1 + imag_p z2 )%R.
Proof.
  intros.
  replace (z1 + z2)%C with (( real_p z1 , imag_p z1 )+( real_p z2 , imag_p z2 ))%C.
  unfold Cplus.
  auto.
  rewrite <- ! Cdecompose.
  auto.
Qed. 

Lemma Cplus_comm : forall z1 z2:Complex, (z1 + z2 = z2 + z1)%C.
Proof.
  intros.
  rewrite ! Cplus_decompose.
  apply injective_projections.
  simpl.
  ring.
  simpl.
  ring.
Qed.

Hint Resolve Cplus_comm : complex.

Lemma Cplus_assoc : forall r1 r2 r3:Complex , (r1 + (r2 + r3) = r1 + r2 + r3)%C.
Proof.
  intros.
  rewrite ! Cplus_decompose.
  apply injective_projections.
  simpl.
  ring.
  simpl.
  ring.
Qed.

Hint Resolve Cplus_assoc: complex.

Lemma Cplus_opp_r : forall r:Complex, (r + -r = C0 )%C.
Proof.
  intros.
  replace (r) with ( real_p r , imag_p r ).
  unfold Copp.
  apply injective_projections.
  simpl.
  ring.
  simpl.
  ring.
  apply eq_sym.
  apply Cdecompose.
Qed.
Hint Resolve Cplus_opp_r: complex.

Lemma Cplus_0_l : forall r:Complex , (C0 + r = r)%C.
Proof.
  intros.
  rewrite ! Cplus_decompose.
  unfold real_p.
  unfold imag_p.
  apply injective_projections.
  simpl.
  ring.
  simpl.
  ring.
Qed.

Hint Resolve Cplus_0_l: complex.

Lemma Cmult_decompose : forall z1 z2 : Complex , ( z1 * z2 )%C = ( real_p z1 * real_p z2 - imag_p z1 * imag_p z2 , real_p z1 * imag_p z2 + imag_p z1 * real_p z2 )%R.
Proof.
  intros.
  replace (z1 * z2)%C with (( real_p z1 , imag_p z1 )*( real_p z2 , imag_p z2 ))%C.
  unfold Cplus.
  auto.
  rewrite <- ! Cdecompose.
  auto.
Qed. 

Lemma Cmult_comm : forall r1 r2:Complex, (r1 * r2 = r2 * r1)%C.
Proof.
  intros.
  rewrite ! Cmult_decompose.
  apply injective_projections.
  simpl.
  ring.
  simpl.
  ring.
Qed.
Hint Resolve Cmult_comm: complex.

Lemma Cmult_assoc : forall r1 r2 r3:Complex, (r1 * (r2 * r3) = r1 * r2 * r3)%C.
Proof.
  intros.
  rewrite ! Cmult_decompose.
  apply injective_projections.
  simpl.
  ring.
  simpl.
  ring.
Qed.
Hint Resolve Cmult_assoc: complex.

Local Open Scope R_scope.

Lemma Ra2b2n0 : forall a b : R , a<>0 \/ b<>0 -> 0<a*a+b*b.
Proof.
  intros.
  assert ( 0 <= a * a ).
  replace ( a * a ) with (a^2) ; [idtac | ring ].
  apply pow2_ge_0 with ( x := a ).
  assert ( 0 <= b * b ).
  replace ( b * b ) with (b^2) ; [idtac | ring ].
  apply pow2_ge_0 with ( x := b ).
  unfold Rle in H0.
  case H0.
  intros.
  replace 0 with (0+0); [ idtac | ring ].
  apply Rplus_gt_ge_compat.
  auto.
  apply Rle_ge.
  auto.
  intros.
  assert (b<>0).
  assert ( a=0).
  apply eq_sym in H2.
  apply Rmult_integral in H2.
  case H2.
  auto.
  auto.
  case H.
  contradiction.
  auto.
  assert ( b * b <> 0).
  auto.
  assert ( 0 < b * b ).
  case H1.
  auto.
  intros.
  apply eq_sym in H5.
  contradiction.
  replace 0 with (0+0); [ idtac | ring ].
  apply Rplus_ge_gt_compat.
  rewrite <- H2.
  auto with real.
  auto with real.
Qed.

Local Close Scope R_scope.

Lemma Cinv_l : forall r:Complex, (r <> C0 -> / r * r = C1)%C.
Proof.
  intros.
  replace (r) with ( real_p r , imag_p r ).
  assert ( real_p r <> 0 \/ imag_p r <> 0)%R as orenq.
  apply Peirce.
  intros.
  apply not_or_and in H0.
  destruct H0 as [rp0 ip0].
  apply NNPP in rp0.
  apply NNPP in ip0.
  elim H.
  replace (r) with ( real_p r , imag_p r ).
  unfold C0.
  apply injective_projections.
  auto.
  auto.
  apply eq_sym.
  apply Cdecompose.
  
  assert((real_p r * real_p r + imag_p r * imag_p r)%R <> 0%R).
  unfold not.
  intros.
  assert ( 0<(real_p r * real_p r + imag_p r * imag_p r)%R )%R. 
  apply Ra2b2n0.
  auto.
  rewrite H0 in H1.
  apply Rlt_irrefl in H1.
  auto.

  unfold Cinv.
  unfold C1.
  apply injective_projections.
  simpl.
  field.
  auto.
  simpl.
  field.
  auto.
  rewrite Cdecompose.
  auto.
Qed.
Hint Resolve Cinv_l: complex.

Lemma Cmult_1_l : forall r:Complex, (C1 * r = r)%C.
Proof.
  intros.
  replace (r) with ( real_p r , imag_p r ).
  rewrite ! Cmult_decompose.
  apply injective_projections.
  simpl.
  ring.
  simpl.
  ring.
  rewrite Cdecompose.
  auto.
Qed.
Hint Resolve Cmult_1_l: complex.

Lemma Cmult_0_l : forall r:Complex, (C0 * r = C0)%C.
Proof.
  intros.
  unfold C0.
  replace (r) with ( real_p r , imag_p r ).
  rewrite ! Cmult_decompose.
  apply injective_projections.
  simpl.
  ring.
  simpl.
  ring.
  rewrite Cdecompose.
  auto.
Qed.
Hint Resolve Cmult_0_l: complex.


Lemma C1_neq_C0 : C1 <> C0.
Proof.
  unfold not.
  intros.
  assert ( real_p C1 = 1 )%R.
  auto.
  assert ( real_p C1 = 0 )%R.
  rewrite H.
  auto.
  auto with real.
Qed.
Hint Resolve C1_neq_C0: complex.

Lemma Cmult_plus_distr_r : forall r2 r3 r1:Complex, ((r2 + r3)*r1 = r2*r1 + r3 * r1)%C.
Proof.
  intros.
  rewrite ! Cplus_decompose.
  rewrite ! Cmult_decompose.
  apply injective_projections.
  simpl.
  ring.
  simpl.
  ring.
Qed.
Hint Resolve Cmult_plus_distr_r: complex.

Lemma complexSRth : ring_theory C0 C1 Cplus Cmult Cminus Copp (@eq Complex).
 Proof.
  constructor. exact Cplus_0_l. exact Cplus_comm. exact Cplus_assoc.
  exact Cmult_1_l. exact Cmult_comm. exact Cmult_assoc.
  exact Cmult_plus_distr_r. auto. exact Cplus_opp_r.
 Qed.

Add Ring complexr : complexSRth.
