Require Export Category.

Set Implicit Arguments.
Unset Strict Implicit.

Section allegory.

Variable C : Category.
Variable Op_intersect : forall a b : Ob C, Map2 (Hom a b) (Hom a b) (Hom a b).
Variable Op_converse  : forall a b : Ob C, Map (Hom a b) (Hom b a).

Definition Al_intersect (a b : Ob C) (f g : Hom a b) : Hom a b :=
  Op_intersect a b f g.
Definition Al_converse (a b : Ob C) (f : Hom a b) : Hom b a :=
  Op_converse a b f.

Definition Included (a b : Ob C) (R S : Hom a b) : Prop :=
  R =_S Al_intersect R S.

Definition intersect_Assoc_law :=
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

Structure Allegory : Type := 
  { Al_Cat :> Category
  ; Op_converse  : forall a b : Ob Al_Cat, Map (Hom a b) (Hom b a)
  ; Op_intersect : forall a b : Ob Al_Cat, Map2 (Hom a b) (Hom a b) (Hom a b)
  ; Prf_intersect_ass  : intersect_Assoc_law Op_intersect
  ; Prf_intersect_idem : forall a b : Ob Al_Cat, isIdempotent (Op_intersect a b)
  ; Prf_intersect_comm : forall a b : Ob Al_Cat, isCommutative (Op_intersect a b)
  ; Prf_Distr_law1     : Distr_law1 Op_converse
  ; Prf_Distr_law2     : Distr_law2 Op_intersect Op_converse
  ; Prf_SemiDistr_l    : SemiDistr_l Op_intersect
  ; Prf_SemiDistr_r    : SemiDistr_r Op_intersect
  }.

Definition Intersect (C : Allegory) := Al_intersect (Op_intersect (a:=C)).
Definition Converse (C : Allegory) := Al_converse (Op_converse (a:=C)).
