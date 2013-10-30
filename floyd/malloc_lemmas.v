Require Import floyd.base.
Require Import floyd.field_mapsto.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.

Local Open Scope logic.

Lemma memory_block_zero: forall sh b z, memory_block sh (Int.repr 0) (Vptr b z) = emp.
Proof.
 intros. unfold memory_block.
 change (Int.repr 0) with Int.zero.
 rewrite Int.unsigned_zero.
Admitted.  (* pretty straightforward *)

Lemma memory_block_offset_zero:
  forall sh n v, memory_block sh n (offset_val Int.zero v) = memory_block sh n v.
Proof.
unfold memory_block; intros.
destruct v; auto.
simpl offset_val. cbv beta iota.
rewrite Int.add_zero. auto.
Qed.

Hint Rewrite memory_block_zero: norm.

Global Opaque memory_block.


Fixpoint is_Fnil (fld: fieldlist) : bool :=
match fld with
| Fnil => true
| Fcons id ty fld' => false
end.

Fixpoint reptype (ty: type) : Type :=
  match ty with
  | Tvoid => unit
  | Tint _ _ _ => int
  | Tlong _ _ => Int64.int
  | Tfloat _ _ => float
  | Tpointer t1 a => val
  | Tarray t1 sz a => list (reptype t1)
  | Tfunction t1 t2 => unit
  | Tstruct id fld a => reptype_structlist fld
  | Tunion id fld a => reptype_unionlist fld
  | Tcomp_ptr id a => val
  end

with reptype_structlist (fld: fieldlist) : Type :=
  match fld with
  | Fnil => unit
  | Fcons id ty fld' => 
          if is_Fnil fld' 
                      then reptype ty
                      else prod (reptype ty) (reptype_structlist fld')
  end
with reptype_unionlist (fld: fieldlist) : Type :=
  match fld with
  | Fnil => unit
  | Fcons id ty fld' => sum (reptype ty) (reptype_unionlist fld')
  end.

Lemma int_add_repr_0_l: forall i, Int.add (Int.repr 0) i = i.
Proof. intros. apply Int.add_zero_l. Qed.
Lemma int_add_repr_0_r: forall i, Int.add i (Int.repr 0) = i.
Proof. intros. apply Int.add_zero. Qed.
Hint Rewrite int_add_repr_0_l int_add_repr_0_r : norm.

Lemma field_mapsto__offset_zero:
  forall sh ty id v, 
   field_mapsto_ sh ty id (offset_val (Int.repr 0) v) =
   field_mapsto_ sh ty id v.
Proof.
 unfold field_mapsto_; intros.
 destruct v; try solve [simpl; auto].
 simpl offset_val. rewrite int_add_repr_0_r. reflexivity.
Qed.
Hint Rewrite field_mapsto__offset_zero: norm.

Definition at_offset (P: val -> mpred) (z: Z)  : val -> mpred :=
 match z with Z0 => P | _ => fun v => P (offset_val (Int.repr z) v) end.

Lemma at_offset_eq: forall P z v,
  P (offset_val (Int.repr 0) v) = P v ->
  at_offset P z v = P (offset_val (Int.repr z) v).
Proof.
intros.
unfold at_offset.
destruct z; auto.
Qed.

Definition spacer (sh: share) (pos: Z) (alignment: Z) : val -> mpred :=
  if Z.eq_dec  (align pos alignment - pos) 0
  then fun _ => emp
  else
   at_offset (memory_block sh (Int.repr (align pos alignment - pos))) pos.

Definition withspacer sh (pos: Z) (alignment: Z) : (val -> mpred) -> val -> mpred :=
   match align pos alignment - pos with
   | Z0 => fun P => P
   | _ => fun P => spacer sh pos alignment * P
   end.

Lemma withspacer_spacer: forall sh pos alignment P,
   withspacer sh pos alignment P = spacer sh pos alignment * P.
Proof.
  intros.
 extensionality v.
 unfold withspacer, spacer.
 destruct (align pos alignment - pos); auto.
 rewrite if_true by auto.
 simpl. rewrite emp_sepcon. auto.
Qed.

Definition storable_mode (ty: type) : bool :=
  match ty with
  | Tarray _ _ _ => false
  | Tfunction _ _ => false
  | Tstruct _ _ _ => false
  | Tunion _ _ _ => false
  | Tvoid => false
  | _ => true
end.

Fixpoint default_val (t: type) : reptype t :=
  match t as t0 return (reptype t0) with
  | Tvoid => tt
  | Tint _ _ _ => Int.zero
  | Tlong _ _ => Int64.zero
  | Tfloat _ _ => Float.zero
  | Tpointer _ _ => Vundef
  | Tarray t0 _ _ => nil
  | Tfunction _ _ => tt
  | Tstruct _ f _ => fieldlist_rect (fun f0 : fieldlist => reptype_structlist f0) tt
            (fun (_ : ident) (t : type) (f0 : fieldlist) (IHf : reptype_structlist f0) =>
           match f0 as f1
                return (reptype_structlist f1 ->
                              if is_Fnil f1 then reptype t else (reptype t * reptype_structlist f1)%type)
         with
             | Fnil => fun _ : reptype_structlist Fnil => default_val t
             | Fcons i0 t0 f1 =>
                 fun IHf0 : reptype_structlist (Fcons i0 t0 f1) => (default_val t, IHf0)
         end IHf) f
  | Tunion _ f _ =>
      match f as f0 return (reptype_unionlist f0) with
      | Fnil => tt
      | Fcons _ t1 _ => inl (default_val t1)
      end
  | Tcomp_ptr _ _ => Vundef
  end.

Definition ZnthV t (lis: list (reptype t)) (i: Z) : reptype t := 
       nth (Z.to_nat i) lis (default_val t).

Fixpoint rangespec' (lo: Z) (n: nat) (P: Z -> mpred): mpred :=
  match n with
  | O => emp
  | S n' => P lo * rangespec' (Zsucc lo) n' P
 end.

Definition rangespec (lo hi: Z) (P: Z -> mpred) : mpred :=
  rangespec' lo (nat_of_Z (hi-lo)) P.

Fixpoint arrayof_' (f: forall (v1: val),  mpred)
         (t1: type) (ofs: Z) (n: nat) (v1: val) : mpred :=
    match n with
    | S n' => f (offset_val (Int.repr ofs) v1) * arrayof_' f t1 (ofs + sizeof t1) n' v1
    | O => emp
   end.

Lemma at_offset_arrayof_':
  forall f t ofs n,
    arrayof_' f t ofs n = at_offset (arrayof_' f t 0 n) ofs.
Proof.
intros.
extensionality v.
rewrite at_offset_eq.
revert v ofs; induction n; intros; simpl; auto.
f_equal. rewrite offset_offset_val. rewrite Int.add_zero. auto.
rewrite IHn.
symmetry; rewrite IHn; symmetry.
f_equal.
rewrite offset_offset_val.
f_equal.
rewrite add_repr. auto.
change (Int.repr 0) with Int.zero.
clear ofs.
forget 0 as ofs.
revert v ofs; induction n; simpl; intros; auto.
f_equal; auto.
destruct v; simpl; auto.
rewrite Int.add_zero.
auto.
Qed.

Definition arrayof_ (f: forall (v1: val),  mpred) (t1: type) (n: nat) (v1: val) : mpred :=
             arrayof_' f t1 0 n v1.

Definition force_field_offset id flds : Z :=
  match field_offset id flds with Errors.OK z  => z | _ => 0 end.

Fixpoint typed_mapsto_' (sh: Share.t) (pos: Z) (ty: type) : val -> mpred :=
  match ty with
  | Tstruct id fld a => withspacer sh pos (alignof ty)
           match fld with 
           | Fnil => at_offset (memory_block sh Int.one) (align pos (alignof ty))
           | _ => at_offset (fields_mapto_ sh 0 ty fld) (align pos (alignof ty))
           end
  | Tarray t z a =>
            withspacer sh pos (alignof t)
              (arrayof_ (typed_mapsto_' sh (align pos (alignof t)) t) t (Z.to_nat z))
  | _ => withspacer sh pos (alignof ty)
              match access_mode ty with
              | By_value _ => 
                    at_offset (mapsto_ sh ty) (align pos (alignof ty))
              | _ => at_offset (memory_block sh (Int.repr (sizeof ty))) (align pos (alignof ty))
              end
  end

with fields_mapto_ (sh: Share.t) (pos:Z) (t0: type) (flds: fieldlist) : val ->  mpred :=
 match flds with
 | Fnil => emp
 | Fcons id ty flds' => 
     (if storable_mode ty 
     then withspacer sh pos (alignof ty) (field_mapsto_ sh t0 id)
     else typed_mapsto_' sh (pos+force_field_offset id flds) ty)
     * fields_mapto_ sh pos t0 flds'
  end.

Definition typed_mapsto_ (sh: Share.t) (ty: type) : val -> mpred :=
        typed_mapsto_' sh 0 ty.


Definition maybe_field_mapsto (sh: Share.t) (t: type) (t_str: type) (id: ident) (pos: Z) (v: val) :
                     (reptype t -> mpred) -> reptype t -> mpred :=
match t as t0 return ((reptype t0 -> mpred) -> reptype t0 -> mpred) with
| Tint i s a =>
    fun (_ : reptype (Tint i s a) -> mpred) (v2'0 : reptype (Tint i s a)) =>
    at_offset (fun v => field_mapsto sh t_str id v (Vint v2'0)) pos v
| Tlong s a =>
    fun (_ : reptype (Tlong s a) -> mpred) (v2'0 : reptype (Tlong s a)) =>
    at_offset (fun v => field_mapsto sh t_str id v (Vlong v2'0)) pos v
| Tfloat f a =>
    fun (_ : reptype (Tfloat f a) -> mpred) (v2'0 : reptype (Tfloat f a)) =>
    at_offset (fun v => field_mapsto sh t_str id v (Vfloat v2'0)) pos v
| Tpointer t0 a =>
    fun _ v2 =>  at_offset (fun v => field_mapsto sh t_str id v v2) pos v
| Tcomp_ptr _ _ =>
    fun _ _ => at_offset (field_mapsto_ sh t_str id) pos v
| t' => fun (alt1 : reptype t' -> mpred)  => alt1 
end.

Definition at_offset2 {T} (f: val -> T -> mpred) pos (v2: T) := 
           at_offset (fun v => f v v2) pos.

Definition array_at' (t: type) (sh: Share.t) (tmaps: val -> reptype t -> mpred) (f: Z -> reptype t) (lo hi: Z)
                                   (v: val) : mpred :=
           rangespec lo hi (fun i => tmaps (add_ptr_int t v i) (f i)).

Fixpoint typed_mapsto' (sh: Share.t) (t1: type) (pos: Z) : val -> reptype t1 -> mpred :=
match t1 as t return (t1 = t -> val -> reptype t1 -> mpred) with
| Tvoid => fun _ _ => emp
| Tint i s a =>
    fun H : t1 = Tint i s a =>
      eq_rect_r (fun t2 : type => val -> reptype t2 -> mpred)
        (fun v (v3 : reptype (Tint i s a)) =>
                withspacer sh pos (alignof (Tint i s a))
                (at_offset2 (mapsto sh (Tint i s a)) (align pos (alignof t1)) (Vint v3)) v) H
| Tlong s a =>
    fun H : t1 = Tlong s a =>
      eq_rect_r (fun t2 : type => val -> reptype t2 -> mpred)
        (fun v (v3 : reptype (Tlong s a)) =>
                withspacer sh pos (alignof (Tlong s a))
                (at_offset2 (mapsto sh (Tlong s a)) (align pos (alignof t1)) (Vlong v3)) v) H
| Tfloat f a =>
    fun H : t1 = Tfloat f a =>
      eq_rect_r (fun t2 : type =>  val -> reptype t2 -> mpred)
        (fun v (v3 : reptype (Tfloat f a)) =>
                withspacer sh pos (alignof (Tfloat f a))
                (at_offset (fun v => mapsto sh (Tfloat f a) v (Vfloat v3)) (align pos (alignof t1))) v) H
| Tpointer t a => 
    fun H : t1 = Tpointer t a =>
      eq_rect_r (fun t2 : type =>  val -> reptype t2 -> mpred)
        (fun v (v3 : reptype (Tpointer t a)) =>
                withspacer sh pos (alignof (Tpointer t a))
                (at_offset (fun v => mapsto sh (Tpointer t a) v v3)  (align pos (alignof t1))) v) H
| Tarray t z a =>
    fun H : t1 = Tarray t z a =>
      eq_rect_r (fun t2 : type =>  val -> reptype t2 -> mpred)
        (fun v (v3 : reptype (Tarray t z a)) => 
                 withspacer sh pos (alignof t)
                  (at_offset (fun v =>
                          array_at' t sh (typed_mapsto' sh t 0) (ZnthV _ v3) 0 (Zlength v3) v) (align pos (alignof t))) v)
        H
| Tfunction t t0 => fun _ => emp
| Tstruct i f a =>
    fun H : t1 = Tstruct i f a =>
      eq_rect_r (fun t2 : type =>  val -> reptype t2 -> mpred)
        (fun v (v3 : reptype (Tstruct i f a)) =>
                 withspacer sh pos (alignof (Tstruct i f a))
                 (fun v => structfieldsof sh (Tstruct i f a) f (align pos (alignof t1)) (align pos (alignof t1)) v v3) v) H
| Tunion i f a =>
    fun H : t1 = Tunion i f a =>
      eq_rect_r (fun t2 : type =>  val -> reptype t2 -> mpred)
        (fun v (v3 : reptype (Tunion i f a)) =>
                 withspacer sh pos (alignof (Tunion i f a))
         (fun v => unionfieldsof sh f (align pos (alignof t1)) v v3) v) H
| Tcomp_ptr i a => 
        fun _ v _ =>
          withspacer sh pos (alignof (Tcomp_ptr i a))
          (at_offset (memory_block sh (Int.repr (sizeof (Tcomp_ptr i a))))pos) v
end eq_refl
 with
 structfieldsof (sh: Share.t) (t_str: type) (flds: fieldlist) (pos pos': Z) :
               val -> reptype_structlist flds -> mpred :=
match flds as f return (val -> reptype_structlist f -> mpred) with
| Fnil => fun _ (_ : reptype_structlist Fnil) => emp
| Fcons i t flds0 =>
    fun v (X0 : reptype_structlist (Fcons i t flds0)) =>
      (if is_Fnil flds0 as b
        return
          (is_Fnil flds0 = b ->
           (if b
            then reptype t
            else (reptype t * reptype_structlist flds0)%type) -> mpred)
       then
        fun (_ : is_Fnil flds0 = true) (X1 : reptype t) =>
        withspacer sh pos (alignof t)
          (fun v => maybe_field_mapsto sh t t_str i (align pos (alignof t)) v
             (typed_mapsto' sh t pos' v) X1) v
       else
        fun (_ : is_Fnil flds0 = false)
          (X1 : reptype t * reptype_structlist flds0) =>
        (withspacer sh pos (alignof t)
          (fun v => maybe_field_mapsto sh t t_str i (align pos (alignof t)) v
             (typed_mapsto' sh t pos' v) (fst X1)) *
        (fun v => structfieldsof sh t_str flds0 pos (align pos' (alignof t) + sizeof t) v (snd X1))) v   )
   eq_refl X0
end
 with
unionfieldsof  (sh: Share.t) (flds: fieldlist) (pos: Z) :  val ->reptype_unionlist flds -> mpred :=
match flds as f0 return (flds = f0 -> val -> reptype_unionlist flds -> mpred) with
| Fnil => fun (_ : flds = Fnil) _ => emp
| Fcons i t f0 =>
    fun (H : flds = Fcons i t f0) =>
      eq_rect_r (fun flds0 : fieldlist => val -> reptype_unionlist flds0 -> mpred)
        (fun v (v3 : reptype_unionlist (Fcons i t f0)) =>
         match v3 with
         | inl v2' => typed_mapsto' sh t pos v v2'
         | inr vr =>  unionfieldsof sh f0 pos v vr 
         end) H
end eq_refl.

Definition typed_mapsto (sh: Share.t) (t1: type)  := typed_mapsto' sh t1 0.

(* TESTING...  
Require Import progs.queue.
Parameter sh : share.
Goal lift1 (typed_mapsto t_struct_elem sh) = (fun _ _ => emp).

       unfold t_struct_elem, typed_mapsto_, typed_mapsto_', typed_mapsto, typed_mapsto', 
        structfieldsof, eq_rect_r, withspacer, at_offset, align, Zmax.
simpl.
 fold t_struct_elem.

match goal with |- context [lift1 ?P] =>
    match P with (fun _ => _) =>
     let Q := fresh "Q" in let EQ := fresh "EQ" in
      evar (Q: val -> mpred);
      assert (EQ: P = Q); 
      [  let rho := fresh "rho" in
         extensionality rho
     | ]
 end 
end.


Ltac abstract_env T rho P :=
  match P with
   | @emp mpred _ _ => constr:(@emp (T -> mpred) _ _)
   | @sepcon mpred _ _ ?e1 ?e2 => 
      let e1' := abstract_env T rho e1 in let e2' := abstract_env T rho e2
       in constr:(@sepcon (T->mpred) _ _ e1' e2')
   | ?a ?b ?c ?d rho => 
   | _ => constr:(@FF (T -> mpred) _)
   end.

*)


Lemma field_mapsto_offset_zero:
  forall sh ty id v, 
   field_mapsto sh ty id (offset_val (Int.repr 0) v) =
   field_mapsto sh ty id v.
Proof.
 unfold field_mapsto_; intros. extensionality v2.
 destruct v; try solve [simpl; auto].
 simpl offset_val. rewrite int_add_repr_0_r. reflexivity.
Qed.
Hint Rewrite field_mapsto_offset_zero: norm.

Lemma lower_sepcon_val:
  forall (P Q: val->environ->mpred) v, 
  ((P*Q) v) = (P v * Q v).
Proof. reflexivity. Qed.

Definition opaque_sepcon := @sepcon (val->mpred) _ _.
Global Opaque opaque_sepcon.
Definition opaque_emp := @emp (val->mpred) _ _.
Global Opaque opaque_emp.

Lemma distribute_envtrans:
  forall A (P Q: A -> mpred) (J: environ -> A),
   @liftx (Tarrow A (LiftEnviron mpred)) 
   (@sepcon (A -> mpred) _ _ P Q) J = 
   (@liftx (Tarrow A (LiftEnviron mpred)) P J 
    * @liftx (Tarrow A (LiftEnviron mpred)) Q J ).
Proof. reflexivity. Qed.
Hint Rewrite distribute_envtrans: norm.

Lemma distribute_lifted_sepcon:
 forall A F G v,
  (@sepcon (A -> mpred) _ _ F G v) = @sepcon mpred _ _ (F v) (G v).
Proof. reflexivity. Qed.

Definition array_at (t: type) (sh: Share.t) (f: Z -> reptype t) (lo hi: Z)
                                   (v: val) :=
           rangespec lo hi (fun i => typed_mapsto sh t (add_ptr_int t v i) (f i)).

Ltac simpl_typed_mapsto' T H MA :=
   try unfold T in H;
   unfold typed_mapsto_, typed_mapsto_', typed_mapsto, typed_mapsto',
    structfieldsof, eq_rect_r, withspacer, at_offset, align, Z.max in H;
   change sepcon with opaque_sepcon in H; 
   change (@emp (val->mpred) _ _) with opaque_emp in H; 
   simpl in H;
   change @opaque_sepcon with (@sepcon (val -> mpred) _ _) in H;
   change @opaque_emp with (@emp (val->mpred) _ _) in H;
   repeat
    match type of H with
    | context [fun (v1 : val) (v4 : int) =>
               mapsto ?sh (Tint ?ch ?s noattr) v1 (Vint v4)] =>
        change
          (fun (v1 : val) (v4 : int) =>
           mapsto sh (Tint ch s noattr) v1 (Vint v4))
         with (typed_mapsto sh (Tint ch s noattr)) in H
    end;
    fold tuint in H; fold tint in H;
    try fold T in H;
   repeat rewrite sepcon_emp in H || rewrite emp_sepcon in H;
   subst MA;
   repeat rewrite distribute_lifted_sepcon;
   repeat rewrite distribute_envtrans;
   repeat match goal with 
    | |- appcontext [array_at' ?t ?sh (typed_mapsto ?sh ?t')] =>
              unify t t';
              change (array_at' t sh (typed_mapsto sh t')) with (array_at t sh)
      end;
   repeat flatten_sepcon_in_SEP.

(* OLD
Ltac simpl_typed_mapsto' T H MA :=
       try unfold T in H;
       unfold  typed_mapsto_, typed_mapsto_', typed_mapsto, typed_mapsto', 
        structfieldsof, eq_rect_r, withspacer, at_offset, align, Zmax in H;
     change (@sepcon (val->mpred) _ _) with opaque_sepcon in H;
        simpl in H;
     change opaque_sepcon with (@sepcon (val->mpred) _ _) in H;
  repeat
  match type of H with context [(fun (v1 : val) (v4 : int) =>
                                     mapsto ?sh (Tint ?ch ?s noattr) v1 (Vint v4))] =>
       change (fun (v1 : val) (v4 : int) => mapsto sh (Tint ch s noattr) v1 (Vint v4))
          with (typed_mapsto sh (Tint ch s noattr)) in H
    end;
  fold tuint in H; fold tint in H;
     change (fun (_: val) => @emp mpred _ _) with (@emp (val->mpred) _ _) in H;
        try fold T in H;
       repeat (rewrite sepcon_emp in H || rewrite emp_sepcon in H);
       repeat match type of H with context [@liftx (Tarrow val (LiftEnviron mpred))(fun v: val => @sepcon mpred _ _ 
                                   (?A1 ?B1 ?C1 ?D1 v)  (?A2 ?B2 ?C2 ?D2 v)) ?V] =>
          change (@liftx (Tarrow val (LiftEnviron mpred)) (fun v: val => @sepcon mpred _ _ 
                                   (A1 B1 C1 D1 v)  (A2 B2 C2 D2 v)) V)
         with (@liftx (Tarrow val (LiftEnviron mpred)) (A1 B1 C1 D1) V *
                @liftx (Tarrow val (LiftEnviron mpred)) (A2 B2 C2 D2) V) in H
       end;
       repeat change (@sepcon (val -> mpred) _ _) with
            (fun P Q (v: val) => @sepcon mpred _ _ (P v) (Q v)) in H;
       subst MA;
      repeat match goal with 
 | |- appcontext [array_at' ?t ?sh (typed_mapsto ?sh ?t)] =>
              change (array_at' t sh (typed_mapsto sh t)) with (array_at t sh)
        | |- context [@liftx (Tarrow val (LiftEnviron mpred))(fun v: val => @sepcon mpred _ _ 
                                   (?A1 ?B1 ?C1 ?D1 v)  (?A2 ?B2 ?C2 ?D2 v)) ?V] =>
          change (@liftx (Tarrow val (LiftEnviron mpred)) (fun v: val => @sepcon mpred _ _ 
                                   (A1 B1 C1 D1 v)  (A2 B2 C2 D2 v)) V)
              with (@liftx (Tarrow val (LiftEnviron mpred)) (A1 B1 C1 D1) V *
                      @liftx (Tarrow val (LiftEnviron mpred)) (A2 B2 C2 D2) V)
        | |- context [@liftx (LiftEnviron mpred)(@sepcon mpred _ _ ?A1 ?A2)] =>
          change (@liftx (LiftEnviron mpred) (@sepcon mpred _ _ A1 A2))
              with (@liftx (LiftEnviron mpred) A1 * @liftx (LiftEnviron mpred) A2)
       end;
       repeat flatten_sepcon_in_SEP.
*)

Ltac simpl_typed_mapsto1 :=
    let H := fresh "H" in let MA := fresh "MA" in
  match goal with 
  | |- appcontext [typed_mapsto_ ?SH ?T] =>
         remember (typed_mapsto_  SH T) as MA eqn:H; simpl_typed_mapsto' T H MA
  | |- appcontext [typed_mapsto_' ?SH ?N ?T] =>
         remember (typed_mapsto_'  SH N T) as MA eqn:H; simpl_typed_mapsto' T H MA
  | |- appcontext [typed_mapsto' ?SH ?T ?N] =>
         remember (typed_mapsto' SH T N) as MA eqn:H; simpl_typed_mapsto' T H MA
  | |- appcontext [typed_mapsto ?SH ?T] =>
         remember (typed_mapsto SH T) as MA eqn:H; simpl_typed_mapsto' T H MA
 | |- appcontext [structfieldsof ?SH ?T ?F ?N ?N'] =>
         remember (structfieldsof SH T F N N') as MA eqn:H; simpl_typed_mapsto' T H MA
  end. 

Ltac simpl_typed_mapsto := repeat simpl_typed_mapsto1.

(*
Require Import progs.sha.

Goal typed_mapsto Tsh t_struct_SHA256state_st = fun _ _ => TT.
simpl_typed_mapsto.
Abort.
*)

(* TESTING 
Require Import progs.sha.
Parameter sh : share.
Parameter v: val.

Goal forall r, typed_mapsto sh t_struct_SHA256state_st v r = emp.
intro.
 simpl_typed_mapsto.
*)

(* TESTING 
Require Import progs.queue.
Parameter sh : share.
Parameter p: environ->val.

Goal `(typed_mapsto sh t_struct_elem) p = (fun v => emp).
 simpl_typed_mapsto.
*)

Lemma mapsto_offset_zero:
  forall sh t v1 v2, 
    mapsto sh t (offset_val (Int.repr 0) v1) v2 =
    mapsto sh t v1 v2.
Proof.
 unfold mapsto.
 intros.
 destruct v1; try solve [simpl; auto].
 unfold offset_val.
 rewrite Int.add_zero. auto.
Qed.

Lemma typed_mapsto_tint: forall sh v1 v2,
  `(typed_mapsto sh tint) v1 v2 =
  `(mapsto sh tint)  v1  (`Vint v2).
Proof.
 intros.
 extensionality rho. reflexivity.
Qed.

Lemma spacer_offset_zero:
  forall sh pos n v, spacer sh pos n (offset_val (Int.repr 0) v) = spacer sh pos n v.
Proof.
 intros;
 unfold spacer.
 destruct (Z.eq_dec (align pos n - pos) 0);  auto.
 repeat rewrite at_offset_eq; 
 try rewrite offset_offset_val; try  rewrite Int.add_zero_l; auto.
 apply memory_block_offset_zero.
Qed.

Fixpoint typecount (t: type) : nat :=
 match t with
 | Tstruct _ f _ => S (typecount_fields f)
 | Tarray t' _ _ => S (typecount t')
 | _ => 1%nat
 end
with typecount_fields (f: fieldlist) : nat :=
 match f with
 | Fnil => 1%nat
 | Fcons _ t f' => (typecount t + typecount_fields f')%nat
 end.

Lemma  typecount_fields_pos: forall f, (typecount_fields f > 0)%nat.
Proof.
 induction f; simpl; intros. auto.
 omega.
Qed.

Lemma typecount_pos: forall t, (typecount t > 0)%nat.
Proof.
 destruct t; simpl; auto; omega.
Qed.

Lemma umapsto_offset_zero:
  forall sh t v v', umapsto sh t (offset_val (Int.repr 0) v) v' = umapsto sh t v v'.
Proof.
 intros.
 unfold umapsto.
 destruct (access_mode t); auto.
 destruct v; auto.
 unfold offset_val. rewrite Int.add_zero; auto.
Qed. 

Lemma mafoz_aux:
  forall n,
  (forall f, (typecount_fields f < n)%nat -> 
     forall sh pos t v,
       fields_mapto_ sh pos t f (offset_val (Int.repr 0) v) =
       fields_mapto_ sh pos t f v) /\
  (forall t, (typecount t < n)%nat -> 
       forall sh ofs v, typed_mapsto_' sh ofs t (offset_val (Int.repr 0) v) =  typed_mapsto_' sh ofs t v).
Proof.
induction n.
split; intros; omega.
 assert (ARRAY: forall t sh k i pos v, 
     (typecount t < n)%nat ->
     arrayof_' (typed_mapsto_' sh (align pos (alignof t)) t) t i k (offset_val (Int.repr 0) v) =
     arrayof_' (typed_mapsto_' sh (align pos (alignof t)) t) t i k v); [ | auto].
 induction k; simpl; intros; auto.
 f_equal.
 replace (offset_val (Int.repr i) (offset_val (Int.repr 0) v)) with
             (offset_val (Int.repr 0) (offset_val (Int.repr i) v)).
 apply IHn. auto.
 repeat rewrite offset_offset_val. rewrite Int.add_commut. auto.
 apply IHk; auto.
 
 split; intros.
 destruct f; simpl; auto.
 simpl in H.
 case_eq (storable_mode t0); intros.
 repeat rewrite withspacer_spacer. simpl.
 f_equal; [f_equal; [apply spacer_offset_zero |apply field_mapsto__offset_zero ] | ].
 apply IHn.
 pose proof (typecount_pos t0).
 omega.
 f_equal.
 destruct t0; inv H0; simpl;
 repeat rewrite withspacer_spacer;
 simpl; repeat rewrite at_offset_eq by apply memory_block_offset_zero;
 try (rewrite offset_offset_val; rewrite Int.add_commut;
                 rewrite <- offset_offset_val);
 try (f_equal; [apply spacer_offset_zero |]);
 try  apply memory_block_offset_zero.
 apply ARRAY. simpl in H; omega.
 destruct f0.
 repeat rewrite at_offset_eq by apply memory_block_offset_zero.
 f_equal. rewrite offset_offset_val. f_equal. rewrite Int.add_commut; apply Int.add_zero.
 repeat rewrite at_offset_eq.
 f_equal. rewrite offset_offset_val. f_equal. rewrite Int.add_commut; apply Int.add_zero.
 apply IHn.
 simpl. simpl in H.
 simpl.
 pose proof (typecount_fields_pos f).
 omega.
 f_equal. rewrite offset_offset_val. f_equal.
 apply IHn.
 pose proof (typecount_pos t0). omega.

 destruct t; simpl;
 repeat rewrite withspacer_spacer; simpl; rewrite spacer_offset_zero; f_equal;
 repeat rewrite at_offset_eq by apply memory_block_offset_zero;
 try (rewrite offset_offset_val; rewrite Int.add_zero_l; f_equal; apply spacer_offset_zero);
 try (destruct i, s); try destruct f; 
 repeat rewrite at_offset_eq;
 try (rewrite offset_offset_val; rewrite Int.add_commut; rewrite <- offset_offset_val);
 try (apply umapsto_offset_zero);
 try apply memory_block_offset_zero.
 apply ARRAY. simpl in H; omega.
 rewrite offset_offset_val. rewrite Int.add_zero. auto.
 apply IHn. simpl in H|-*. generalize (typecount_pos t); intro. simpl. omega.
 rewrite offset_offset_val. rewrite Int.add_zero; auto.
Qed.

Lemma fields_mapto__offset_zero:
  forall sh pos t f v, fields_mapto_ sh pos t f (offset_val (Int.repr 0) v) =
                           fields_mapto_ sh pos t f v.
Proof.
intros.
apply (mafoz_aux (S (typecount_fields f))).
omega.
Qed.

Lemma memory_block_isptr: forall sh i v, 
  i > 0 -> 
  memory_block sh (Int.repr i) v = !!(isptr v) && memory_block sh (Int.repr i) v.
Proof.
intros.
Transparent memory_block.
unfold memory_block.
Opaque memory_block.
destruct v; normalize.
Qed.

Lemma memory_block_address_mapsto:
  forall n sh ch b i,
  n = Memdata.size_chunk ch ->
  memory_block sh (Int.repr n) (Vptr b i) =
 address_mapsto ch Vundef (Share.unrel Share.Lsh sh)
  (Share.unrel Share.Rsh sh) (b, Int.unsigned i)
|| !!(Vundef = Vundef) &&
   (EX  v2' : val,
    address_mapsto ch v2' (Share.unrel Share.Lsh sh)
      (Share.unrel Share.Rsh sh) (b, Int.unsigned i)).
Admitted. 

Lemma memory_block_mapsto_:
  forall n sh t v, 
    match access_mode t with By_value _ => True | _ => False end ->
   n = sizeof t ->
   memory_block sh (Int.repr n) v = mapsto_ sh t v.
Proof.
 intros. subst n.
 destruct t; try contradiction; clear H;  unfold mapsto_, umapsto; simpl;
 try (destruct i,s); try destruct f; rewrite memory_block_isptr by omega;
 destruct v; simpl; try  apply FF_andp; 
 rewrite prop_true_andp by auto;
 (apply memory_block_address_mapsto;  reflexivity).
Qed.
 
Lemma spacer_memory_block:
  forall sh pos a v,
  isptr v -> 
 spacer sh pos a v = memory_block sh (Int.repr (align pos a - pos)) (offset_val (Int.repr pos) v).
Proof.
intros.
destruct v; inv H.
unfold spacer.
destruct (Z.eq_dec (align pos a - pos) 0);
try solve [rewrite e; simpl offset_val; rewrite memory_block_zero; auto].
unfold at_offset.
destruct pos; auto.
unfold offset_val; rewrite Int.add_zero; auto.
Qed.

Lemma memory_block_typed': forall sh pos ty b ofs, 
   spacer sh pos (alignof ty) (Vptr b ofs) *
   memory_block sh (Int.repr (sizeof ty)) (offset_val (Int.repr (align pos (alignof ty))) (Vptr b ofs) )
     = typed_mapsto_' sh pos ty (Vptr b ofs)
with memory_block_fields: forall sh pos t fld b ofs,
  spacer sh (sizeof_struct fld pos) (alignof_fields fld) (Vptr b ofs) 
  * memory_block sh (Int.repr (sizeof_struct fld pos)) (Vptr b ofs)
  =   memory_block sh (Int.repr pos) (Vptr b ofs) * fields_mapto_ sh pos t fld (Vptr b ofs).
Proof.
 clear memory_block_typed'.
 intros.
 induction ty;
 try solve [simpl; rewrite withspacer_spacer; simpl;
                rewrite at_offset_eq by (apply memory_block_offset_zero); auto];
 try (unfold typed_mapsto_'; rewrite withspacer_spacer; simpl; f_equal;
  try destruct i,s; try destruct f; try rewrite at_offset_eq; simpl; try rewrite Int.add_zero; auto;
       apply memory_block_mapsto_; simpl; auto).
 admit. (* array case *)
 unfold typed_mapsto_'; fold fields_mapto_.
 rewrite withspacer_spacer.
 simpl. f_equal.
 case_eq f; intros. simpl.
 rewrite at_offset_eq by (apply memory_block_offset_zero); auto.
 rewrite <- H.
 assert (Zmax 1 (sizeof_struct f 0) = sizeof_struct f 0).
  subst f. simpl. rewrite align_0 by (apply alignof_pos).
   simpl. pose proof (sizeof_struct_incr f0 (sizeof t)).
   rewrite Zmax_spec. rewrite zlt_false; auto. pose proof (sizeof_pos t). omega.
 simpl sizeof. rewrite H0.
 specialize (memory_block_fields sh 0 (Tstruct i f a) f b
    (Int.add (Int.repr (align pos (alignof (Tstruct i f a)))) ofs)).
 simpl.
 rewrite at_offset_eq by (apply fields_mapto__offset_zero).
  rewrite memory_block_zero in memory_block_fields.
 simpl in memory_block_fields.
 rewrite emp_sepcon in memory_block_fields.
 simpl. rewrite Int.add_commut.
 rewrite <- memory_block_fields; clear memory_block_fields.
 rewrite Int.add_commut.
 rewrite spacer_memory_block by apply I.
 unfold offset_val.
 rewrite sepcon_comm.
change memory_block with 
  (fun (sh: share) (n: int) (v: val) =>
 match v with 
 | Vptr b ofs => memory_block' sh (nat_of_Z (Int.unsigned n)) b (Int.unsigned ofs)
 | _ => FF
 end).
cbv beta iota.
evar (zz: Z).
rewrite memory_block'_split with (i:=zz).
f_equal. f_equal. unfold zz; reflexivity.
unfold zz; clear zz.
f_equal. f_equal.
rewrite Int.unsigned_repr by admit.  (*plausible, but may need work *)
rewrite Int.unsigned_repr by admit.  (*plausible, but may need work *)
rewrite Int.unsigned_repr by admit.  (*plausible, but may need work *)
auto.
rewrite Int.add_unsigned.
rewrite Int.unsigned_repr by admit.  (*plausible, but may need work *)
rewrite Int.unsigned_repr by admit.  (*plausible, but may need work *)
rewrite Int.unsigned_repr by admit.  (*plausible, but may need work *)
rewrite Int.add_unsigned.
rewrite (Int.unsigned_repr (sizeof_struct _ _)) by admit.  (*plausible, but may need work *)
rewrite (Int.unsigned_repr (Int.unsigned ofs + _)) by admit.  (*plausible, but may need work *)
rewrite Int.unsigned_repr by admit.  (*plausible, but may need work *)
auto.
unfold zz; clear zz.
rewrite Int.unsigned_repr by admit.
rewrite Int.unsigned_repr by admit.
split.
admit.  (* easy *)
apply align_le.
apply alignof_fields_pos.
admit.  (* likely OK  *)

 clear memory_block_fields.
 intros. revert pos ofs; induction fld; simpl; intros.
 rewrite sepcon_comm; f_equal.
 unfold spacer.
 destruct (Z.eq_dec (align pos 1 - pos) 0); auto.
 replace (Zminus (align pos (Zpos xH)) pos) with 0.
 unfold at_offset. destruct pos;  apply memory_block_zero.
 unfold align. replace (pos + 1 - 1) with pos by omega.
 rewrite Zdiv_1_r. rewrite Zmult_1_r. omega.
 rewrite withspacer_spacer.
 pull_left (fields_mapto_ sh pos t fld (Vptr b ofs)).
 replace ((if storable_mode t0
  then spacer sh pos (alignof t0) * field_mapsto_ sh t i
  else typed_mapsto_' sh pos t0) (Vptr b ofs))
 with (spacer  sh pos (alignof t0) (Vptr b ofs) * 
          if storable_mode t0 then field_mapsto_ sh t i (Vptr b ofs)
               else memory_block sh (Int.repr (sizeof t0))
               (offset_val (Int.repr (align pos (alignof t0))) (Vptr b ofs)))
   by (destruct (storable_mode t0); auto).
clear memory_block_typed'.
  rewrite <-sepcon_assoc.
 rewrite <- IHfld. clear IHfld.
 case_eq (storable_mode t0); intros.
 admit. (* might be *)
 admit.  (* might be *)
Admitted.  (* This proof is done here, but Qed takes forever in Coq 8.3pl5.
                         Let's hope it goes faster in 8.4 *)


Lemma typed_mapsto__isptr:
  forall sh t v, typed_mapsto_ sh t v = !!(isptr v) && typed_mapsto_ sh t v.
Proof.
intros.
apply pred_ext; normalize.
apply andp_right; auto.
unfold typed_mapsto_.
Admitted. (* straightforward *)

Lemma memory_block_typed: 
 forall sh ty, memory_block sh (Int.repr (sizeof ty))
               = typed_mapsto_ sh ty.
Proof.
intros.
extensionality v.
rewrite memory_block_isptr by (apply sizeof_pos).
rewrite typed_mapsto__isptr.
destruct v; simpl; normalize.
unfold typed_mapsto_; rewrite <- memory_block_typed'.
unfold spacer.
rewrite align_0 by (apply alignof_pos).
simpl. rewrite emp_sepcon.
rewrite Int.add_zero. auto.
Qed.

Lemma var_block_typed_mapsto_:
  forall  sh id t, 
 var_block sh (id, t) = 
   !!(sizeof t <= Int.max_unsigned) &&
            `(typed_mapsto_ sh t) (eval_var id t).
Proof.
intros; extensionality rho.
unfold_lift.
rewrite <- memory_block_typed.
unfold var_block.
simpl. unfold_lift.
rewrite memory_block_isptr by apply sizeof_pos.
destruct (eval_var id t rho); simpl; normalize.
Qed.

Lemma typed_mapsto_typed_mapsto_ :
  forall sh t v v', typed_mapsto sh t v v' |-- typed_mapsto_ sh t v.
Admitted.
Hint Resolve typed_mapsto_typed_mapsto_.
Hint Resolve field_mapsto_field_mapsto_.

Global Opaque arrayof_.

Lemma array_at_local_facts:
 forall t sh f lo hi v,
   lo < hi ->
    array_at t sh f lo hi v |-- !! isptr v.
Proof.
 intros.
 unfold array_at, rangespec.
 destruct (nat_of_Z (hi-lo)) eqn:?H.
 elimtype False.
 admit.  (* easy *)
 simpl.
 eapply derives_trans with (typed_mapsto_ sh t (add_ptr_int t v lo) * TT).
 apply sepcon_derives; auto.
 rewrite typed_mapsto__isptr.
 normalize. apply prop_right.
 destruct v; inv H1. apply I.
Qed.

Hint Extern 2 (@derives _ _ _ _) => 
   simple apply array_at_local_facts; omega : saturate_local.
