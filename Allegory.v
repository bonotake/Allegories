Require Export Category.

Set Implicit Arguments.
Unset Strict Implicit.

Section allegory.

Variable C : Category.
Variable Op_intersect : forall a b : Ob C, Map2 (Hom a b) (Hom a b) (Hom a b).
Variable Op_converse \u00a0: forall a b : Ob C, Map (Hom a b) (Hom b a).

Definition Al_intersect (a b : Ob C) (f g : Hom a b) : Hom a b := 
  Op_intersect a b f g.
Definition Al_converse (a b : Ob C) (f : Hom a b) : Hom b a :=
  Op_converse a b f.

Definition Included (a b : Ob C) (R S : Hom a b) : Prop :=
  R =_S Al_intersect R S.

Definition Intersect_Assoc_law :=
  forall (a b : Ob C) (R S T : Hom a b),
    Al_intersect R (Al_intersect S T) =_S Al_intersect (Al_intersect R S) T.
Definition Distr_law1 :=
  forall (a b c : Ob C) (R : Hom a b) (S : Hom b c),
    Al_converse (R o S) =_S Al_converse S o Al_converse R.
Definition Distr_law2 :=
  forall (a b : Ob C) (R : Hom a b) (S : Hom a b),
    Al_converse (Al_intersect R S) =_S Al_intersect (Al_converse S) (Al_converse R).
Definition SemiDistr_l :=
  forall (a b c : Ob C) (R : Hom a b) (S T : Hom b c), 
    Included (R o Al_intersect S T) (Al_intersect (R o S) (R o T)).
Definition SemiDistr_r :=
  forall (a b c : Ob C) (R S : Hom a b) (T : Hom b c),
    Included (Al_intersect R S o T) (Al_intersect (R o T) (S o T)).

End allegory.

Definition isIdempotent (S : Setoid) (f : Map2 S S S) : Prop :=
  forall (a : S), f a a =_S a.
Definition isCommutative (S : Setoid) (f : Map2 S S S) : Prop :=
  forall (a b : S), f a b =_S f b a.

Structure Allegory : Type :=\u00a0
  { Al_Cat :> Category
  ; Op_converse : forall a b : Ob Al_Cat, Map (Hom a b) (Hom b a)
  ; Op_intersect : forall a b : Ob Al_Cat, Map2 (Hom a b) (Hom a b) (Hom a b)
  ; Prf_intersect_ass : Intersect_Assoc_law Op_intersect
  ; Prf_intersect_idem : forall a b : Ob Al_Cat, isIdempotent (Op_intersect a b)
  ; Prf_intersect_comm : forall a b : Ob Al_Cat, isCommutative (Op_intersect a b)
  ; Prf_Distr_law1 : Distr_law1 Op_converse
  ; Prf_Distr_law2 : Distr_law2 Op_intersect Op_converse
  ; Prf_SemiDistr_l : SemiDistr_l Op_intersect
  ; Prf_SemiDistr_r : SemiDistr_r Op_intersect
}.

Definition Intersect (C : Allegory) := Al_intersect (Op_intersect (a:=C)).
Definition Converse (C : Allegory) := Al_converse (Op_converse (a:=C)).
Definition Inclusion (C: Allegory) := Included (Op_intersect (a:=C)).

Section inclusion.
(* S1 �� S2 �� R1 �� R2 \u21db (S1 o R1) �� (S2 o R2) �����������ł����� *)
Variable a: Allegory.
Variable x y z: a.
Variable s1 s2 s3: Hom x y.
Variable t1 t2: Hom y z.

Lemma Incl_Reflexive: forall r: Hom x y, Inclusion  r r.
Proof.
intros.
unfold Inclusion.
unfold Included.
unfold Al_intersect.
apply Sym.
apply Prf_intersect_idem.
Qed.

Lemma Eq_Intersect_r: forall s1 s2 s3: Hom x y, s1 =_S s2 -> (Intersect s1 s3) =_S (Intersect s2 s3).
Proof.
intros.
unfold Intersect.
unfold Al_intersect.
unfold Op_intersect.
destruct a.
apply Op_intersect0.
apply H.
Qed.

Lemma Intersect_comm: forall s1 s2: x --> y, (Intersect s1 s2) =_S (Intersect s2 s1).
Proof.
apply Prf_intersect_comm.
Qed.

Lemma Intersect_Eq_comm_r: forall s1 s2 s3: x --> y, s3 =_S (Intersect s1 s2) -> s3 =_S (Intersect s2 s1).
Proof.
Lemma Intersect_Eq_comm_r1: 
  forall s1 s2 s3: x --> y, s3 =_S (Intersect s1 s2) -> (Intersect s1 s2) =_S (Intersect s2 s1) -> s3 =_S (Intersect s2 s1).
Proof.
intros.
revert H0.
revert H.
apply Trans.
Qed.
intros.
apply Intersect_Eq_comm_r1.
exact H.
apply Intersect_comm.
Qed.

Lemma Intersect_Eq_comm_l: forall s1 s2 s3: x --> y, (Intersect s1 s2) =_S s3 -> (Intersect s2 s1) =_S s3.
Proof.
intros.
apply Sym.
apply Intersect_Eq_comm_r.
apply Sym.
exact H.
Qed.

Lemma Eq_Intersect_l: forall s1 s2 s3: Hom x y, s1 =_S s2 -> (Intersect s3 s1) =_S (Intersect s3 s2).
Proof.
intros.
apply Intersect_Eq_comm_r.
apply Intersect_Eq_comm_l.
apply Eq_Intersect_r.
exact H.
Qed.

Lemma Def_Incl_1: forall x y: a, forall s1 s2: x --> y, Inclusion s1 s2 -> s1 =_S Intersect s1 s2.
Proof.
unfold Inclusion.
unfold Included.
intros.
unfold Intersect.
exact H.
Qed.

Lemma Def_Incl_2: forall x y: a, forall s1 s2: x --> y, s1 =_S Intersect s1 s2 -> Inclusion s1 s2.
Proof.
unfold Intersect.
intros.
unfold Inclusion.
unfold Included.
exact H.
Qed.

Lemma Def_Incl_Conj: forall x y z w: a, forall s1 s2: x --> y, forall t1 t2: z --> w,
  s1 =_S Intersect s1 s2 /\ t1 = Intersect t1 t2 -> Inclusion s1 s2 /\ Inclusion t1 t2.
Proof.
intros.
split.
apply Def_Incl_2.
(* 1/2 *)
destruct H.
exact H.
(* 2/2 *)
apply Def_Incl_2.
destruct H.
destruct H0.
apply Refl.
Qed.

Lemma Incl_Restrict: forall s1 s2: x --> y, Inclusion (Intersect s1 s2) s2.
Proof.
  intros.
  apply Def_Incl_2.
  Lemma H2: forall s1 s2: x --> y, Intersect s1 s2 =_S Intersect s1 (Intersect s2 s2)
      -> Intersect s1 (Intersect s2 s2) =_S Intersect (Intersect s1 s2) s2 
      -> Intersect s1 s2 =_S Intersect (Intersect s1 s2) s2.
  Proof.
    intro ; intro.
    apply Trans.
  Qed.
  apply H2.
  Lemma H3: forall s1 s2: Hom x y, s2 =_S Intersect s2 s2  -> Intersect s1 s2 =_S Intersect s1 (Intersect s2 s2).
  Proof.
    intros.
    apply Eq_Intersect_l.
    exact H.
  Qed.
  apply H3.
  (* 1/2 *)
  apply Def_Incl_1.
  apply Incl_Reflexive.
  (* 2/2 *)
  apply Prf_intersect_ass.
Qed.


(* S1 �� S2 �� R1 �� R2 \u21db (S1 o R1) �� (S2 o R2)  *)
Theorem PartiallyOrderd1: Inclusion s1 s2 /\ Inclusion t1 t2 -> Inclusion (s1 o t1) (s2 o t2).
Proof.
  intros.
  destruct H.
  Lemma H1: Inclusion (s1 o t1) 
  


End inclusion.