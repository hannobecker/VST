Require Import VST.msl.msl_standard.
Require Import VST.msl.seplog.
Require Import VST.veric.base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.juicy_mem_ops.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.semax.
Require Import VST.veric.semax_call.
Require Import VST.veric.semax_ext.
Require Import VST.veric.juicy_safety.
Require Import VST.veric.Clight_new.
Require Import VST.veric.res_predicates.
Require Import VST.veric.SeparationLogic.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.extspec.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.jmeq_lemmas.
Require Import VST.concurrency.lksize.
Require Import VST.concurrency.semax_conc_pred.

Set Bullet Behavior "Strict Subproofs".

(* Variables to be instantiated once the program is known. *)
Definition _f := 1%positive.      (* alpha-convertible *)
Definition _args := 2%positive.   (* alpha-convertible *)
Definition _lock := 1%positive.   (* alpha-convertible *)
Definition _cond := 2%positive.   (* alpha-convertible *)
Definition _lock_t := 2%positive. (* 2 (* or sometimes 3 -WM *) is the number given by
clightgen when threads.h is included first *)

Definition voidstar_funtype := Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default.
(* Definition tlock := Tstruct _lock_t noattr. *)
Definition tlock := (Tarray (Tpointer Tvoid noattr) 1 noattr).
(* Notation tlock := tuint (only parsing). *)

Definition selflock_fun Q sh p : (unit -> mpred) -> (unit -> mpred) :=
  fun R _ => (Q * lock_inv sh p (|> R tt))%logic.

Definition selflock' Q sh p : unit -> mpred := HORec (selflock_fun Q sh p).
Definition selflock Q sh p : mpred := selflock' Q sh p tt.

Lemma nonexpansive_entail (F: pred rmap -> pred rmap) : nonexpansive F -> forall P Q, (P <=> Q |-- F P <=> F Q)%logic.
Proof.
  intros N P Q.
  specialize (N P Q).
  eapply derives_trans; [ eapply derives_trans | ]; [ | apply N | ];
  apply derives_refl.
Qed.

Lemma HOnonexpansive_nonexpansive: forall F: mpred -> mpred, nonexpansive F <-> HOnonexpansive (fun P (_ : unit) => F (P tt)).
Proof.
  intros.
  split; intros; hnf in H |- *.
  + intros P Q.
    specialize (H (P tt) (Q tt)).
    rewrite !allp_unit.
    auto.
  + intros P Q.
    specialize (H (fun x => P) (fun x => Q)).
    rewrite !allp_unit in H.
    auto.
Qed.

Lemma lock_inv_later sh p R : lock_inv sh p R |-- lock_inv sh p (|> R)%logic.
Admitted.

Lemma selflock'_eq Q sh p : selflock' Q sh p =
  selflock_fun Q sh p (selflock' Q sh p).
Proof.
  apply HORec_fold_unfold, prove_HOcontractive.
  intros P1 P2 u.
  apply subp_sepcon; [ apply subp_refl | ].
  eapply derives_trans.
  + apply HOnonexpansive_nonexpansive; apply (nonexpansive_lock_inv sh p).
  + apply allp_left with tt, fash_derives, andp_left1, derives_refl.
Qed.

Lemma selflock_eq Q sh p : selflock Q sh p = (Q * lock_inv sh p (|> selflock Q sh p))%logic.
Proof.
  unfold selflock at 1.
  rewrite selflock'_eq.
  reflexivity.
Qed.

(* In fact we need locks to two resources:
   1) the resource invariant, for passing the resources
   2) the join resource invariant, for returning all resources, including itself
   for this we need to define them in a mutually recursive fashion: *)

Definition res_invariants_fun Q sh1 p1 sh2 p2 : (bool -> mpred) -> (bool -> mpred) :=
  fun R b =>
    if b then
      (Q * lock_inv sh2 p2 (|> R false))%logic
    else
      (Q * lock_inv sh1 p1 (|> R true) * lock_inv sh2 p2 (|> R false))%logic.

Definition res_invariants Q sh1 p1 sh2 p2 : bool -> mpred := HORec (res_invariants_fun Q sh1 p1 sh2 p2).
Definition res_invariant Q sh1 p1 sh2 p2 : mpred := res_invariants Q sh1 p1 sh2 p2 true.
Definition join_res_invariant Q sh1 p1 sh2 p2 : mpred := res_invariants Q sh1 p1 sh2 p2 false.

Lemma res_invariants_eq Q sh1 p1 sh2 p2 : res_invariants Q sh1 p1 sh2 p2 =
  res_invariants_fun Q sh1 p1 sh2 p2 (res_invariants Q sh1 p1 sh2 p2).
Proof.
  apply HORec_fold_unfold, prove_HOcontractive.
  intros P1 P2 b.
  destruct b.
    (* resource invariant *)
    apply subp_sepcon; try apply subp_refl.
    apply allp_left with false.
    eapply derives_trans.
      apply nonexpansive_entail, nonexpansive_lock_inv.
      apply fash_derives, andp_left1, derives_refl.

    (* join resource invariant *)
    repeat apply subp_sepcon; try apply subp_refl.
      apply allp_left with true.
      eapply derives_trans.
        apply nonexpansive_entail, nonexpansive_lock_inv.
        apply fash_derives, andp_left1, derives_refl.

      apply allp_left with false.
      eapply derives_trans.
        apply nonexpansive_entail, nonexpansive_lock_inv.
        apply fash_derives, andp_left1, derives_refl.
Qed.

Lemma res_invariant_eq Q sh1 p1 sh2 p2 :
  res_invariant Q sh1 p1 sh2 p2 =
  (Q *
  lock_inv sh2 p2 (|> join_res_invariant Q sh1 p1 sh2 p2))%logic.
Proof.
  unfold res_invariant at 1.
  rewrite res_invariants_eq.
  reflexivity.
Qed.

Lemma join_res_invariant_eq Q sh1 p1 sh2 p2 :
  join_res_invariant Q sh1 p1 sh2 p2 =
  (Q *
  lock_inv sh1 p1 (|> res_invariant Q sh1 p1 sh2 p2) *
  lock_inv sh2 p2 (|> join_res_invariant Q sh1 p1 sh2 p2))%logic.
Proof.
  unfold join_res_invariant at 1.
  rewrite res_invariants_eq.
  reflexivity.
Qed.

(* Condition variables *)
(*Definition _cond_t := 4%positive.*)
Definition tcond := tint.

(* Does this need to be anything special? *)
Definition cond_var {cs} sh v := @data_at_ cs sh tcond v.

(*+ Specification of each concurrent primitive *)

Lemma approx_eq_i':
  forall (P Q : pred rmap) n,
  (|> (P <=> Q))%pred n -> approx n P = approx n Q.
Proof.
  intros.
apply pred_ext'; extensionality m'.
unfold approx.
apply and_ext'; auto; intros.
specialize (H (level m')); spec H; [simpl; apply later_nat; auto |].
specialize (H m').
spec H; [omega |].
destruct H.
specialize (H m').
specialize (H1 m').
apply prop_ext; split; auto.
Qed.

Lemma fash_equiv_approx: forall n (R: pred rmap),
  (|> (R <=> approx n R))%pred n.
Proof.
  intros.
  intros m ? x ?; split; intros y ? ?.
  + apply approx_lt; auto.
    apply necR_level in H1.
    apply later_nat in H; omega.
  + eapply approx_p; eauto.
Qed.

Lemma nonexpansive_super_non_expansive: forall (F: mpred -> mpred),
  nonexpansive F ->
  forall R n,
  approx n (F R) = approx n (F (approx n R)).
Proof.
  intros.
  apply approx_eq_i'.
  intros m ?.
  pose proof nonexpansive_entail _ H R (approx n R) m.
  apply H1.
  clear - H0.
  apply (fash_equiv_approx n R m); auto.
Qed.

Lemma nonexpansive2_super_non_expansive: forall (F: mpred -> mpred -> mpred),
  (forall P, nonexpansive (fun Q => F P Q)) ->
  (forall Q, nonexpansive (fun P => F P Q)) ->
  forall P Q n,
  approx n (F P Q) = approx n (F (approx n P) (approx n Q)).
Proof.
  intros.
  apply approx_eq_i'.
  intros m ?.
  pose proof nonexpansive_entail _ (H P) Q (approx n Q) m; cbv beta in H2.
  spec H2; [apply (fash_equiv_approx n Q m); auto |].
  pose proof nonexpansive_entail _ (H0 (approx n Q)) P (approx n P) m; cbv beta in H3.
  spec H3; [apply (fash_equiv_approx n P m); auto |].
  remember (F P Q) as X1.
  remember (F P (approx n Q)) as X2.
  remember (F (approx n P) (approx n Q)) as X3.
  clear - H2 H3.
  change ((X1 <=> X2)%pred m) in H2.
  change ((X2 <=> X3)%pred m) in H3.
  intros y H; specialize (H2 y H); specialize (H3 y H).
  destruct H2 as [H2A H2B], H3 as [H3A H3B].
  split; intros z H0.
  + specialize (H2A z H0); specialize (H3A z H0); auto.
  + specialize (H2B z H0); specialize (H3B z H0); auto.
Qed.

(*
Lemma nonexpansive_2super_non_expansive: forall {A B: Type} (F: (A -> B -> mpred) -> mpred),
  (forall a b, nonexpansive (fun Q => F P Q)) ->
  (forall Q, nonexpansive (fun P => F P Q)) ->
  forall P Q n,
  approx n (F P Q) = approx n (F (approx n P) (approx n Q)).
*)
Definition acquire_arg_type: rmaps.TypeTree := rmaps.ProdType (rmaps.ConstType (val * share)) rmaps.Mpred.

Definition acquire_pre: val * share * mpred -> environ -> mpred :=
  fun args =>
  match args with
  | (v, sh, R) =>
     PROP (readable_share sh)
     LOCAL (temp _lock v)
     SEP (lock_inv sh v R)
  end.

Notation acquire_post :=
  (fun args =>
  match args with
  | (v, sh, R) =>
     PROP ()
     LOCAL ()
     SEP (lock_inv sh v R; R)
  end).

Lemma NP_acquire_pre: @super_non_expansive acquire_arg_type (fun _ => acquire_pre).
Proof.
  hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP (readable_share sh)  LOCAL (temp _lock v)  SEP (lock_inv sh v R)) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          ((fun _ => readable_share sh) :: nil)
          ((temp _lock v) :: nil)
          ((fun R => lock_inv sh v R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + unfold compose. apply const_nonexpansive.
  + apply nonexpansive_lock_inv.
Qed.

Lemma NP_acquire_post: @super_non_expansive acquire_arg_type (fun _ => acquire_post).
Proof.
  hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP ()  LOCAL ()  SEP (lock_inv sh v R; R)) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          nil
          nil
          ((fun R => lock_inv sh v R) :: (fun R => R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + apply nonexpansive_lock_inv.
  + apply identity_nonexpansive.
Qed.

Definition acquire_spec: funspec := mk_funspec
  ((_lock OF tptr Tvoid)%formals :: nil, tvoid)
  cc_default
  acquire_arg_type
  (fun _ => acquire_pre)
  (fun _ => acquire_post)
  NP_acquire_pre
  NP_acquire_post
.

Definition release_arg_type: rmaps.TypeTree := rmaps.ProdType (rmaps.ConstType (val * share)) rmaps.Mpred.

Definition release_pre: val * share * mpred -> environ -> mpred :=
  fun args =>
  match args with
  | (v, sh, R) =>
     PROP (readable_share sh)
     LOCAL (temp _lock v)
     SEP (weak_precise_mpred R && weak_positive_mpred R && emp; lock_inv sh v R; R)
  end.

Notation release_post :=
  (fun args =>
  match args with
  | (v, sh, R) =>
     PROP ()
     LOCAL ()
     SEP (lock_inv sh v R)
  end).

Lemma NP_release_pre: @super_non_expansive release_arg_type (fun _ => release_pre).
Proof.
  hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP (readable_share sh)  LOCAL (temp _lock v)  SEP (weak_precise_mpred R && weak_positive_mpred R && emp; lock_inv sh v R; R)) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          ((fun _ => readable_share sh) :: nil)
          ((temp _lock v) :: nil)
          ((fun R => weak_precise_mpred R && weak_positive_mpred R && emp)%logic :: (fun R => lock_inv sh v R) :: (fun R => R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply (conj_nonexpansive (fun R => weak_precise_mpred R && weak_positive_mpred R)%logic); [apply (conj_nonexpansive weak_precise_mpred) |].
    - apply precise_mpred_nonexpansive.
    - apply positive_mpred_nonexpansive.
    - apply const_nonexpansive.
  + apply nonexpansive_lock_inv.
  + apply identity_nonexpansive.
Qed.

Lemma NP_release_post: @super_non_expansive release_arg_type (fun _ => release_post).
Proof.
  hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP ()  LOCAL ()  SEP (lock_inv sh v R)) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          nil
          nil
          ((fun R => lock_inv sh v R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  apply nonexpansive_lock_inv.
Qed.

Definition release_spec: funspec := mk_funspec
  ((_lock OF tptr Tvoid)%formals :: nil, tvoid)
  cc_default
  release_arg_type
  (fun _ => release_pre)
  (fun _ => release_post)
  NP_release_pre
  NP_release_post
.

Program Definition makelock_spec cs: funspec := mk_funspec
  ((_lock OF tptr Tvoid)%formals :: nil, tvoid)
  cc_default
  (rmaps.ProdType (rmaps.ConstType (val * share)) rmaps.Mpred)
  (fun _ x =>
   match x with
   | (v, sh, R) =>
     PROP (writable_share sh)
     LOCAL (temp _lock v)
     SEP (@data_at_ cs sh tlock v)
   end)
  (fun _ x =>
   match x with
   | (v, sh, R) =>
     PROP ()
     LOCAL ()
     SEP (lock_inv sh v R)
   end)
  _
  _
.
Next Obligation.
  intros cs; hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  auto.
Qed.
Next Obligation.
  intro cs; hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP ()  LOCAL ()  SEP (lock_inv sh v R)) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          nil
          nil
          ((fun R => lock_inv sh v R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  apply nonexpansive_lock_inv.
Qed.

Program Definition freelock_spec cs: funspec := mk_funspec
  ((_lock OF tptr Tvoid)%formals :: nil, tvoid)
  cc_default
  (rmaps.ProdType (rmaps.ConstType (val * share)) rmaps.Mpred)
  (fun _ x =>
   match x with
   | (v, sh, R) =>
     PROP (writable_share sh)
     LOCAL (temp _lock v)
     SEP (weak_positive_mpred R && emp; lock_inv sh v R; R)
   end)
  (fun _ x =>
   match x with
   | (v, sh, R) =>
     PROP ()
     LOCAL ()
     SEP (@data_at_ cs sh tlock v; R)
   end)
  _
  _
.
Next Obligation.
  intro cs; hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP (writable_share sh)
    LOCAL (temp _lock v)
    SEP (weak_positive_mpred R && emp; lock_inv sh v R; R)) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          ((fun _ => writable_share sh) :: nil)
          (temp _lock v :: nil)
          ((fun R => weak_positive_mpred R && emp)%logic :: (fun R => lock_inv sh v R) :: (fun R => R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply (conj_nonexpansive weak_positive_mpred).
    - apply positive_mpred_nonexpansive.
    - apply const_nonexpansive.
  + apply nonexpansive_lock_inv.
  + apply identity_nonexpansive.
Qed.
Next Obligation.
  intro cs; hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP ()  LOCAL ()  SEP (data_at_ sh tlock v; R)) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          nil
          nil
          ((fun _ => data_at_ sh tlock v) :: (fun R => R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply identity_nonexpansive.
Qed.

(* versions that give away all their resources *)

Lemma selflock_rec : forall sh v R, rec_inv sh v R (selflock R sh v).
Proof.
  intros; unfold rec_inv.
  apply selflock_eq.
Qed.

Lemma lock_inv_later_eq : forall sh v R, (|> lock_inv sh v R = lock_inv sh v (|> R))%logic.
Proof.
Admitted.

Lemma later_rec_lock : forall sh v (Q R: mpred), rec_inv sh v Q R -> rec_inv sh v (later Q) (later R).
Proof.
  unfold rec_inv; intros.
  rewrite H at 1.
  rewrite later_sepcon, lock_inv_later_eq; auto.
Qed.

Program Definition freelock2_spec cs: funspec := mk_funspec
  ((_lock OF tptr Tvoid)%formals :: nil, tvoid)
  cc_default
  (rmaps.ProdType (rmaps.ProdType (rmaps.ConstType (val * share * share)) rmaps.Mpred) rmaps.Mpred)
  (fun _ x =>
   match x with
   | (v, sh, sh', Q, R) =>
     PROP (writable_share sh)
     LOCAL (temp _lock v)
     SEP (weak_positive_mpred R && weak_rec_inv sh' v Q R && emp; lock_inv sh v R)
   end)
  (fun _ x =>
   match x with
   | (v, sh, sh', Q, R) =>
     PROP ()
     LOCAL ()
     SEP (@data_at_ cs sh tlock v)
   end)
  _
  _
.
Next Obligation.
  intro cs; hnf.
  intros.
  destruct x as [[[[v sh] sh'] Q] R]; simpl in *.
  apply (nonexpansive2_super_non_expansive
   (fun Q R => (PROP (writable_share sh)
     LOCAL (temp _lock v)
     SEP (weak_positive_mpred R && weak_rec_inv sh' v Q R && emp; lock_inv sh v R)) rho));
  [ clear Q R; intros Q;
    apply (PROP_LOCAL_SEP_nonexpansive
            ((fun _ => writable_share sh) :: nil)
            (temp _lock v :: nil)
            ((fun R => weak_positive_mpred R && weak_rec_inv sh' v Q R && emp)%logic :: (fun R => lock_inv sh v R) :: nil))
  | clear Q R; intros R;
    apply (PROP_LOCAL_SEP_nonexpansive
            ((fun _ => writable_share sh) :: nil)
            (temp _lock v :: nil)
            ((fun Q => weak_positive_mpred R && weak_rec_inv sh' v Q R && emp)%logic :: (fun _ => lock_inv sh v R) :: nil))];
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply (conj_nonexpansive (fun R => weak_positive_mpred R && weak_rec_inv sh' v Q R)%logic); [apply (conj_nonexpansive weak_positive_mpred) |].
    - apply positive_mpred_nonexpansive.
    - apply rec_inv1_nonexpansive.
    - apply const_nonexpansive.
  + apply nonexpansive_lock_inv.
  + apply const_nonexpansive.
  + apply (conj_nonexpansive (fun Q => weak_positive_mpred R && weak_rec_inv sh' v Q R)%logic); [apply (conj_nonexpansive (fun _ => weak_positive_mpred R)) |].
    - apply const_nonexpansive.
    - apply rec_inv2_nonexpansive.
    - apply const_nonexpansive.
  + apply const_nonexpansive.
Qed.
Next Obligation.
  intro cs; hnf.
  intros.
  destruct x as [[[[v sh] sh'] Q] R]; simpl in *.
  auto.
Qed.

Program Definition release2_spec: funspec := mk_funspec
  ((_lock OF tptr Tvoid)%formals :: nil, tvoid)
  cc_default
  (rmaps.ProdType (rmaps.ProdType (rmaps.ConstType (val * share)) rmaps.Mpred) rmaps.Mpred)
  (fun _ x =>
   match x with
   | (v, sh, Q, R) =>
     PROP (readable_share sh)
     LOCAL (temp _lock v)
     SEP (weak_precise_mpred R && weak_positive_mpred R && weak_rec_inv sh v Q R && emp; R)
   end)
  (fun _ x =>
   match x with
   | (v, sh, Q, R) =>
     PROP ()
     LOCAL ()
     SEP (emp)
   end)
  _
  _
.
Next Obligation.
  intro cs; hnf.
  intros.
  destruct x as [[[v sh] Q] R]; simpl in *.
  apply (nonexpansive2_super_non_expansive
   (fun Q R => (PROP (readable_share sh)
     LOCAL (temp _lock v)
     SEP (weak_precise_mpred R && weak_positive_mpred R && weak_rec_inv sh v Q R && emp; R)) rho));
  [ clear Q R; intros Q;
    apply (PROP_LOCAL_SEP_nonexpansive
            ((fun _ => readable_share sh) :: nil)
            (temp _lock v :: nil)
            ((fun R => weak_precise_mpred R && weak_positive_mpred R && weak_rec_inv sh v Q R && emp)%logic :: (fun R => R) :: nil))
  | clear Q R; intros R;
    apply (PROP_LOCAL_SEP_nonexpansive
            ((fun _ => readable_share sh) :: nil)
            (temp _lock v :: nil)
            ((fun Q => weak_precise_mpred R && weak_positive_mpred R && weak_rec_inv sh v Q R && emp)%logic :: (fun _ => R) :: nil))];
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply (conj_nonexpansive (fun R => weak_precise_mpred R && weak_positive_mpred R && weak_rec_inv sh v Q R)%logic); [apply (conj_nonexpansive (fun R => weak_precise_mpred R && weak_positive_mpred R)%logic); [apply (conj_nonexpansive weak_precise_mpred) |] |].
    - apply precise_mpred_nonexpansive.
    - apply positive_mpred_nonexpansive.
    - apply rec_inv1_nonexpansive.
    - apply const_nonexpansive.
  + apply identity_nonexpansive.
  + apply const_nonexpansive.
  + apply (conj_nonexpansive (fun Q => weak_precise_mpred R && weak_positive_mpred R && weak_rec_inv sh v Q R)%logic); [apply (conj_nonexpansive (fun Q => weak_precise_mpred R && weak_positive_mpred R)%logic) |].
    - apply const_nonexpansive.
    - apply rec_inv2_nonexpansive.
    - apply const_nonexpansive.
  + apply const_nonexpansive.
Qed.
Next Obligation.
  intro cs; hnf.
  intros.
  destruct x as [[[v sh] Q] R]; simpl in *.
  auto.
Qed.

(* condition variables *)
Definition makecond_spec cs :=
   WITH v : val, sh : share
   PRE [ _cond OF tptr tcond ]
     PROP (writable_share sh)
     LOCAL (temp _cond v)
     SEP (@data_at_ cs sh tcond v)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (cond_var sh v).

Definition freecond_spec cs :=
   WITH v : val, sh : share
   PRE [ _cond OF tptr tcond ]
     PROP (writable_share sh)
     LOCAL (temp _cond v)
     SEP (@cond_var cs sh v)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (@data_at_ cs sh tcond v).

Program Definition wait_spec cs: funspec := mk_funspec
  ((_cond OF tptr tcond)%formals :: (_lock OF tptr Tvoid)%formals :: nil, tvoid)
  cc_default
  (rmaps.ProdType (rmaps.ConstType (val * val * share * share)) rmaps.Mpred)
  (fun _ x =>
   match x with
   | (c, l, shc, shl, R) =>
     PROP (readable_share shc)
     LOCAL (temp _cond c; temp _lock l)
     SEP (@cond_var cs shc c; lock_inv shl l R; R)
   end)
  (fun _ x =>
   match x with
   | (c, l, shc, shl, R) =>
     PROP ()
     LOCAL ()
     SEP (cond_var shc c; lock_inv shl l R; R)
   end)
  _
  _
.
Next Obligation.
  intros cs; hnf.
  intros.
  destruct x as [[[[c l] shc] shl] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP (readable_share shc)
    LOCAL (temp _cond c; temp _lock l)
    SEP (cond_var shc c; lock_inv shl l R; R)) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          ((fun _ => readable_share shc) :: nil)
          (temp _cond c :: temp _lock l :: nil)
          ((fun R => cond_var shc c) :: (fun R => lock_inv shl l R) :: (fun R => R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply const_nonexpansive.
  + apply nonexpansive_lock_inv.
  + apply identity_nonexpansive.
Qed.
Next Obligation.
  intros cs; hnf.
  intros.
  destruct x as [[[[c l] shc] shl] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP ()
    LOCAL ()
    SEP (cond_var shc c; lock_inv shl l R; R)) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          nil
          nil
          ((fun R => cond_var shc c) :: (fun R => lock_inv shl l R) :: (fun R => R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply nonexpansive_lock_inv.
  + apply identity_nonexpansive.
Qed.

Program Definition wait2_spec cs: funspec := mk_funspec
  ((_cond OF tptr tcond)%formals :: (_lock OF tptr Tvoid)%formals :: nil, tvoid)
  cc_default
  (rmaps.ProdType (rmaps.ConstType (val * val * share * share)) rmaps.Mpred)
  (fun _ x =>
   match x with
   | (c, l, shc, shl, R) =>
     PROP (readable_share shc)
     LOCAL (temp _cond c; temp _lock l)
     SEP (lock_inv shl l R; R && (@cond_var cs shc c * TT))
   end)
  (fun _ x =>
   match x with
   | (c, l, shc, shl, R) =>
     PROP ()
     LOCAL ()
     SEP (lock_inv shl l R; R)
   end)
  _
  _
.
Next Obligation.
  intros cs; hnf.
  intros.
  destruct x as [[[[c l] shc] shl] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP (readable_share shc)
    LOCAL (temp _cond c; temp _lock l)
    SEP (lock_inv shl l R; R && (@cond_var cs shc c * TT))) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          ((fun _ => readable_share shc) :: nil)
          (temp _cond c :: temp _lock l :: nil)
          ((fun R => lock_inv shl l R) :: (fun R => R && (@cond_var cs shc c * TT))%logic :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply nonexpansive_lock_inv.
  + apply (conj_nonexpansive (fun R => R) (fun _ => (cond_var shc c * TT)%logic)).
    - apply identity_nonexpansive.
    - apply const_nonexpansive.
Qed.
Next Obligation.
  intros cs; hnf.
  intros.
  destruct x as [[[[c l] shc] shl] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP ()
    LOCAL ()
    SEP (lock_inv shl l R; R)) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          nil
          nil
          ((fun R => lock_inv shl l R) :: (fun R => R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + apply nonexpansive_lock_inv.
  + apply identity_nonexpansive.
Qed.

Definition signal_spec cs :=
   WITH c : val, shc : share
   PRE [ _cond OF tptr tcond ]
     PROP (readable_share shc)
     LOCAL (temp _cond c)
     SEP (@cond_var cs shc c)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (@cond_var cs shc c).



(* Notes about spawn_thread:

As in makelock/acquire/... we get a universe inconsistency when we add
"WITH P" to the specification.  This universe inconsistency will
eventually disappear in a different model for rmaps tracking
covariance and contravariance.  In the meantime, we use a the deep
embedding [Pred] and an embedding [PrePost] of the pre- and
post-condition depending on Type term [ty].

The spawned function has for argument name [_y], which is
existentially quantified.  The function also can use a list of global
variables [globals].

For now, the specification of the spawned function has to be exactly
of the form that you can see below (inside the "match PrePost ...").
Cao Qinxiang is working on a notion of sub-specification that might
enable us to have smoother specifications.

The postcondition might not be emp, so we have potential memory leaks
when a thread exists (those maps are still handled by the concurrent
machine).

To enable joinable threads, the postcondition would be [tptr tthread]
with a type [tthread] related to the postcondition through a [thread]
predicate in the logic.  The [join] would then also be implemented
using the oracle, as [acquire] is.  The postcondition would be [match
PrePost with existT ty (w, pre, post) => thread th (Interp (post w b))
end] *)

Definition gvars := map (fun x => gvar (fst x) (snd x)).

Local Open Scope logic.

Definition spawn_arg_type :=
  (rmaps.ProdType (rmaps.ProdType (rmaps.ConstType (val * val)) (rmaps.DependentType 0)) (rmaps.ArrowType (rmaps.DependentType 0) (rmaps.ArrowType (rmaps.ConstType val) rmaps.Mpred))).

Definition spawn_pre :=
  (fun (ts: list Type) (x: val * val * nth 0 ts unit * (nth 0 ts unit -> val -> mpred)) =>
   match x with
   | (f, b, w, pre) =>
     PROP ()
     LOCAL (temp _args b)
     SEP (
       EX _y : ident, EX globals : nth 0 ts unit -> list (ident * val),
         (func_ptr'
           (WITH y : val, x : nth 0 ts unit
             PRE [ _y OF tptr tvoid ]
               PROP ()
               (LOCALx (temp _y y :: map (fun x => gvar (fst x) (snd x)) (globals x))
               (SEP   (pre x y)))
             POST [tptr tvoid]
               PROP  ()
               LOCAL ()
               SEP   (emp))
           f);
         pre w b)
   end).

Lemma spawn_pre_nonexpansive: @super_non_expansive spawn_arg_type spawn_pre.
  replace spawn_pre with
    (fun (ts: list Type) (x: val * val * nth 0 ts unit * (nth 0 ts unit -> val -> mpred)) (rho: environ) =>
     PROP ()
     LOCAL (
       match x with
       | (f, b, w, pre) => temp _args b
       end)
     SEP (
       match x with
       | (f, b, w, pre) =>
         EX _y : ident, EX globals : nth 0 ts unit -> list (ident * val),
         (func_ptr'
           (WITH y : val, x : nth 0 ts unit
             PRE [ _y OF tptr tvoid ]
               PROP ()
               (LOCALx (temp _y y :: map (fun x => gvar (fst x) (snd x)) (globals x))
               (SEP   (pre x y)))
             POST [tptr tvoid]
               PROP  ()
               LOCAL ()
               SEP   (emp))
           f)
       end;
       match x with
       | (f, b, w, pre) =>
         pre w b
       end)
     rho).
  Focus 2. {
    extensionality ts x rho.
    destruct x as [[[f b] w] pre].
    reflexivity.
  } Unfocus.
  apply (PROP_LOCAL_SEP_super_non_expansive
   (rmaps.ProdType (rmaps.ProdType (rmaps.ConstType (val * val)) (rmaps.DependentType 0)) (rmaps.ArrowType (rmaps.DependentType 0) (rmaps.ArrowType (rmaps.ConstType val) rmaps.Mpred)))
    nil
    ((fun ts x =>
        match x with
        | (f, b, w, pre) => temp _args b
        end) :: nil)
    ((fun (ts: list Type) x =>
       match x with
       | (f, b, w, pre) =>
         EX _y : ident, EX globals : nth 0 ts unit -> list (ident * val),
           (func_ptr'
             (WITH y : val, x : nth 0 ts unit
               PRE [ _y OF tptr tvoid ]
                 PROP ()
                 (LOCALx (temp _y y :: map (fun x => gvar (fst x) (snd x)) (globals x))
                 (SEP   (pre x y)))
               POST [tptr tvoid]
                 PROP  ()
                 LOCAL ()
                 SEP   (emp))
             f)
       end) ::
     (fun ts x =>
       match x with
       | (f, b, w, pre) => pre w b
       end) :: nil)); repeat constructor.
  + hnf; intros.
    destruct x as [[[f b] w] pre]; auto.
  + hnf; intros.
    destruct x as [[[f b] w] pre].
    simpl.
    rewrite !approx_exp.
    f_equal; extensionality _y.
    rewrite !approx_exp.
    f_equal; extensionality globals.
    rewrite approx_func_ptr'.
    symmetry.
    rewrite approx_func_ptr'.
    symmetry.
    f_equal.
    f_equal.
    f_equal.
    clear rho.
    extensionality a rho. destruct a as [y x].
    apply (nonexpansive_super_non_expansive
       (fun R => (PROP ( )
                  (LOCALx
                   (temp _y y
                     :: map (fun x0 => gvar (fst x0) (snd x0)) (globals x))
                   SEP (R))) rho)).
    apply (PROP_LOCAL_SEP_nonexpansive
          nil
          (temp _y y
                     :: map (fun x0 => gvar (fst x0) (snd x0)) (globals x))
          ((fun R => R) :: nil));
    repeat apply Forall_cons; try apply Forall_nil.
    apply identity_nonexpansive.
  + hnf; intros.
    destruct x as [[[f b] w] pre].
    simpl.
    apply (nonexpansive_super_non_expansive (fun R => R)).
    apply identity_nonexpansive.
Qed.

Definition spawn_post :=
  (fun (ts: list Type) (x: val * val * nth 0 ts unit * (nth 0 ts unit -> val -> mpred)) =>
   match x with
   | (f, b, w, pre) =>
     PROP ()
     LOCAL ()
     SEP ()
   end).

Lemma spawn_post_nonexpansive: @super_non_expansive spawn_arg_type spawn_post.
Proof.
  hnf; intros.
  destruct x as [[[f b] w] pre].
  auto.
Qed.

Definition spawn_spec := mk_funspec
  ((_f OF tptr voidstar_funtype)%formals :: (_args OF tptr tvoid)%formals :: nil, tvoid)
  cc_default
  spawn_arg_type
  spawn_pre
  spawn_post
  spawn_pre_nonexpansive
  spawn_post_nonexpansive.

(*+ Adding the specifications to a void ext_spec *)

(*! The void ext_spec *)
Definition void_spec T : external_specification juicy_mem external_function T :=
    Build_external_specification
      juicy_mem external_function T
      (fun ef => False)
      (fun ef Hef ge tys vl m z => False)
      (fun ef Hef ge ty vl m z => False)
      (fun rv m z => False).

Definition ok_void_spec (T : Type) : OracleKind.
 refine (Build_OracleKind T (Build_juicy_ext_spec _ (void_spec T) _ _ _)).
Proof.
  simpl; intros; contradiction.
  simpl; intros; contradiction.
  simpl; intros; intros ? ? ? ?; contradiction.
Defined.

Definition concurrent_simple_specs (cs : compspecs) (ext_link : string -> ident) :=
  (ext_link "acquire"%string, acquire_spec) ::
  (ext_link "release"%string, release_spec) ::
  nil.

Definition concurrent_simple_ext_spec Z (cs : compspecs) (ext_link : string -> ident) :=
  add_funspecs_rec
    ext_link
    (ok_void_spec Z).(@OK_ty)
    (ok_void_spec Z).(@OK_spec)
    (concurrent_simple_specs cs ext_link).

Definition Concurrent_Simple_Espec Z cs ext_link :=
  Build_OracleKind
    Z
    (concurrent_simple_ext_spec Z cs ext_link).

Lemma strong_nat_ind (P : nat -> Prop) (IH : forall n, (forall i, lt i n -> P i) -> P n) n : P n.
Proof.
  apply IH; induction n; intros i li; inversion li; eauto.
Qed.

Set Printing Implicit.
Require Import VST.sepcomp.step_lemmas.

Lemma at_external_not_halted (G C M : Type) (csem : semantics.CoreSemantics G C M) (q : C) :
  semantics.at_external csem q <> None -> semantics.halted csem q = None.
Proof.
  destruct (@semantics.at_external_halted_excl G C _ csem q); tauto.
Qed.

(*
Lemma semax_conc' cs (ext_link: string -> ident) id sig cc A P Q :
  let fs := threadspecs cs ext_link in
  let f := mk_funspecOracle Oracle sig cc A P Q in
  In (ext_link id, f) fs ->
  list_norepet (map fst fs) ->
  (forall n,
      semax_external_oracle
        (Concurrent_Espec cs ext_link) (fst (split (fst sig)))
        (EF_external id (funsig2signature sig cc)) _ P Q n).
Proof.
  intros.
  apply semax_ext'_oracle; auto.
Qed.

Lemma semax_conc cs (ext_link: string -> ident) id ids sig sig' cc A P Q :
  let fs := threadspecs cs ext_link in
  let f := mk_funspecOracle Oracle sig  cc A P Q in
  In (ext_link id,f) fs ->
  list_norepet (map fst fs) ->
  ids = fst (split (fst sig)) ->
  sig' = funsig2signature sig cc ->
  (forall n, semax_external_oracle (Concurrent_Espec cs ext_link) ids (EF_external id sig') _ P Q n).
Proof.
  intros.
  subst.
  apply semax_conc'; hnf; auto.
Qed.
 *)

Definition concurrent_specs (cs : compspecs) (ext_link : string -> ident) :=
  (ext_link "acquire"%string, acquire_spec) ::
  (ext_link "release"%string, release_spec) ::
  (ext_link "makelock"%string, makelock_spec cs) ::
  (ext_link "freelock"%string, freelock_spec cs) ::
  (ext_link "spawn"%string, spawn_spec) ::
  nil.

Definition concurrent_ext_spec Z (cs : compspecs) (ext_link : string -> ident) :=
  add_funspecs_rec
    ext_link
    (ok_void_spec Z).(@OK_ty)
    (ok_void_spec Z).(@OK_spec)
    (concurrent_specs cs ext_link).

Definition Concurrent_Espec Z cs ext_link :=
  Build_OracleKind
    Z
    (concurrent_ext_spec Z cs ext_link).
